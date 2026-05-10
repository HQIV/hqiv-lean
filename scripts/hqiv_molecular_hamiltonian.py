#!/usr/bin/env python3
"""
First-principles molecular electronic Hamiltonian in a minimal Gaussian basis.

**s-only primitives** are implemented in this module. **Cartesian s + p** shells (standard
``(x-Ax)^lx … exp(-α|r-A|²)`` with ``Σℓ≤1``) live in ``hqiv_cartesian_gaussian.py``: separable
overlap/kinetic, analytic nuclear derivatives + Boys ``F_n``, and mixed ERIs via derivatives
of the existing s-type four-center integral (FD ERIs are best-effort; LiH benchmarks there
prefer PySCF ``int2e`` when installed — see ``example_lih_sto3g_fci``).

This module is **NumPy-first** for the electronic-structure **integrals**: it
implements the usual non-relativistic Born–Oppenheimer Hamiltonian in a
second-quantized spatial orbital basis by

1. Evaluating **unnormalized** primitive s-Gaussian integrals (overlap, kinetic,
   nuclear attraction, [ss|ss] electron repulsion) using Gaussian product
   identities and **Boys** F_0.
2. **Contracting** primitives to shells (STO-3G-style coefficients, including
   primitive normalization factors).
3. Forming the AO **core Hamiltonian** h = T + V_ne and four-index ERIs (pq|rs)
   in chemist notation.
4. **Symmetric orthogonalization** X = S^{-1/2} and integral transform to an
   orthonormal spatial basis (MO coefficients = columns of X unless you supply
   another orthogonalization).

The **exact** electronic Hamiltonian in that basis is fixed by the tensors
``h1[p,q]`` and ``eri[p,q,r,s]`` (chemist). **Full CI** energies use a **dense**
NumPy diagonalization whose ``H|c⟩`` matches PySCF’s ``direct_nosym`` convention:
``absorb_h1e`` (1e folded into an effective 2e tensor) plus ``fci_slow``-style
``contract_2e`` (ported from PySCF under Apache-2.0, see source comments). This
keeps the default path **NumPy-only**; PySCF is not required for regression
targets like H₂ (STO-3G).

The implementation is meant as an HQIV-side reference pipeline (debuggable,
ablation-friendly) to pair with Lean finite-site scaffolding — not to compete
with optimized integral engines.

References (standard QC texts):
  • Szabo & Ostlund, *Modern Quantum Chemistry*
  • Helgaker et al., *Molecular Electronic-Structure Theory*
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from typing import Iterator, Sequence

import numpy as np

# ---------------------------------------------------------------------------
# Boys function F_n(t) = \int_0^1 u^{2n} exp(-t u^2) du ; we need mostly F_0.


def boys_f0(t: float) -> float:
    """Stable F_0(t) for t >= 0."""
    if t < 1e-14:
        # Taylor: 1 - t/3 + t^2/10 - ...
        return 1.0 - t / 3.0 + t * t / 10.0 - t**3 / 42.0
    return 0.5 * math.sqrt(math.pi / t) * math.erf(math.sqrt(t))


# ---------------------------------------------------------------------------
# Geometry helpers (atomic units: Bohr, Hartree)


def dist2(a: np.ndarray, b: np.ndarray) -> float:
    d = np.asarray(a, dtype=float) - np.asarray(b, dtype=float)
    return float(np.dot(d, d))


# ---------------------------------------------------------------------------
# Primitive s-Gaussian integrals (unnormalized φ = exp(-α |r-A|^2))


def primitive_overlap_s(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
) -> tuple[float, float, np.ndarray]:
    """Return (S, Kab, P) for unnormalized s primitives."""
    rab2 = dist2(a, b)
    p = alpha + beta
    mu = alpha * beta / p
    pref = (math.pi / p) ** 1.5
    kab = math.exp(-mu * rab2)
    s = pref * kab
    p_inv = 1.0 / p
    p_vec = alpha * a + beta * b
    p_center = p_vec * p_inv
    return float(s), float(kab), p_center


def primitive_kinetic_s(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
) -> float:
    """Kinetic matrix element <a|-½∇²|b> between unnormalized s primitives."""
    s, _, _ = primitive_overlap_s(alpha, beta, a, b)
    rab2 = dist2(a, b)
    p = alpha + beta
    mu_p = alpha * beta / p
    # T = (αβ/p) (3 - 2 μ R^2) S  for unnormalized s–s (see e.g. S&O, Obara–Saika base)
    return float(mu_p * (3.0 - 2.0 * mu_p * rab2) * s)


def primitive_nuclear_s(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    z: float,
    r_nuc: np.ndarray,
) -> float:
    """Nuclear attraction -Z * <a|1/r_C|b> for one nucleus."""
    s, kab, p = primitive_overlap_s(alpha, beta, a, b)
    if abs(z) < 1e-16:
        return 0.0
    p_sum = alpha + beta
    rpc2 = dist2(p, r_nuc)
    t = p_sum * rpc2
    # V = -Z * 2π/p * Kab * F_0(t) with Kab absorbed in S — use explicit prefactor
    # Standard: V = -Z * (2π/p) * exp(-μ R_AB^2) * F_0(t); exp factor is kab * pref overlap / pref...
    # From overlap: S = (π/p)^(3/2) * kab; nuclear uses 2π/p * kab * F0(t)
    rab2 = dist2(a, b)
    mu = alpha * beta / p_sum
    kab_check = math.exp(-mu * rab2)
    assert math.isclose(kab, kab_check, rel_tol=0, abs_tol=1e-12)
    return float(-z * (2.0 * math.pi / p_sum) * kab * boys_f0(t))


def primitive_eri_ssss(
    alpha: float,
    beta: float,
    gamma: float,
    delta: float,
    a: np.ndarray,
    b: np.ndarray,
    c: np.ndarray,
    d: np.ndarray,
) -> float:
    """
    (ab|cd) in chemist notation for unnormalized s primitives.

    Uses the usual reduction to two center distributions (Helgaker 9.10).
    """
    zeta = alpha + beta
    eta = gamma + delta
    p = zeta
    q = eta
    pq = p + q
    rp = (alpha * a + beta * b) / zeta
    rq = (gamma * c + delta * d) / eta
    rpq2 = dist2(rp, rq)
    kab = math.exp(-(alpha * beta / zeta) * dist2(a, b))
    kcd = math.exp(-(gamma * delta / eta) * dist2(c, d))
    rho = p * q / pq
    t = rho * rpq2
    # Helgaker (9.10.22): [Ω_ab|Ω_cd] = 2 π^(5/2) / (p q √(p+q)) K_AB K_CD F_0(T)
    return float(
        (2.0 * math.pi ** 2.5) / (p * q * math.sqrt(pq)) * kab * kcd * boys_f0(t)
    )


# ---------------------------------------------------------------------------
# Contracted shells


def _normalized_primitive_weight(alpha: float, c: float) -> float:
    """
    Scale coefficient c (from basis tables for **normalized** s primitives) to match
    our **unnormalized** primitive convention φ_raw = exp(-α|r-R|^2).

    N(α) = (2α/π)^(3/4) gives ∫ |N φ_raw|^2 d^3r = 1.
    """
    return float(c * (2.0 * alpha / math.pi) ** 0.75)


@dataclass(frozen=True)
class ContractedS:
    """Single contracted s shell (STO-nG style): sum_k c_k N(α_k) exp(-α_k |r-R|^2)."""

    center: np.ndarray
    exponents: tuple[float, ...]
    coefficients: tuple[float, ...]

    def __post_init__(self) -> None:
        assert len(self.exponents) == len(self.coefficients)
        c = np.asarray(self.center, dtype=float).reshape(3)


def contracted_overlap(c1: ContractedS, c2: ContractedS) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _normalized_primitive_weight(a, ca)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _normalized_primitive_weight(b, cb)
            s, _, _ = primitive_overlap_s(a, b, c1.center, c2.center)
            tot += wa * wb * s
    return float(tot)


def contracted_kinetic(c1: ContractedS, c2: ContractedS) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _normalized_primitive_weight(a, ca)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _normalized_primitive_weight(b, cb)
            tot += wa * wb * primitive_kinetic_s(a, b, c1.center, c2.center)
    return float(tot)


def contracted_nuclear(
    c1: ContractedS, c2: ContractedS, charges: np.ndarray, positions: np.ndarray
) -> float:
    tot = 0.0
    for iz in range(charges.shape[0]):
        z = float(charges[iz])
        r = positions[iz]
        for a, ca in zip(c1.exponents, c1.coefficients):
            wa = _normalized_primitive_weight(a, ca)
            for b, cb in zip(c2.exponents, c2.coefficients):
                wb = _normalized_primitive_weight(b, cb)
                tot += wa * wb * primitive_nuclear_s(a, b, c1.center, c2.center, z, r)
    return float(tot)


def contracted_eri(c1: ContractedS, c2: ContractedS, c3: ContractedS, c4: ContractedS) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _normalized_primitive_weight(a, ca)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _normalized_primitive_weight(b, cb)
            for c, cc in zip(c3.exponents, c3.coefficients):
                wc = _normalized_primitive_weight(c, cc)
                for d, cd in zip(c4.exponents, c4.coefficients):
                    wd = _normalized_primitive_weight(d, cd)
                    tot += (
                        wa
                        * wb
                        * wc
                        * wd
                        * primitive_eri_ssss(a, b, c, d, c1.center, c2.center, c3.center, c4.center)
                    )
    return float(tot)


# ---------------------------------------------------------------------------
# STO-3G parameters (H, He) — standard contraction over three primitives


def sto3g_hydrogen_shell(center: np.ndarray | Sequence[float]) -> ContractedS:
    """STO-3G minimal basis on hydrogen (exponents from Pople et al.)."""
    ctr = np.asarray(center, dtype=float).reshape(3)
    ex = (3.42525091, 0.62391373, 0.16885540)
    c = (0.15432897, 0.53532814, 0.44463454)
    return ContractedS(ctr, ex, c)


def sto3g_helium_shell(center: np.ndarray | Sequence[float]) -> ContractedS:
    """STO-3G for helium (effective minimal basis)."""
    ctr = np.asarray(center, dtype=float).reshape(3)
    ex = (9.294654, 1.689180, 0.455632)
    c = (0.15432897, 0.53532814, 0.44463454)
    return ContractedS(ctr, ex, c)


# ---------------------------------------------------------------------------
# Molecule + AO integral matrices


@dataclass
class MoleculeSpec:
    """Point charges (atomic numbers as floats) and Cartesian positions (Bohr)."""

    charges: np.ndarray  # shape (natom,)
    positions: np.ndarray  # shape (natom, 3)


def build_ao_matrices(shells: Sequence[ContractedS], mol: MoleculeSpec) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return ``S``, ``h_core`` (T + V_ne), and ``eri`` with ``eri[p,q,r,s] = (pq|rs)`` chemist."""
    n = len(shells)
    s = np.zeros((n, n), dtype=float)
    t = np.zeros((n, n), dtype=float)
    v = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(i, n):
            s_ij = contracted_overlap(shells[i], shells[j])
            t_ij = contracted_kinetic(shells[i], shells[j])
            v_ij = contracted_nuclear(shells[i], shells[j], mol.charges, mol.positions)
            s[i, j] = s_ij
            t[i, j] = t_ij
            v[i, j] = v_ij
            if i != j:
                s[j, i] = s_ij
                t[j, i] = t_ij
                v[j, i] = v_ij
    eri = np.zeros((n, n, n, n), dtype=float)
    for p in range(n):
        for q in range(n):
            for r in range(n):
                for sidx in range(n):
                    eri[p, q, r, sidx] = contracted_eri(shells[p], shells[q], shells[r], shells[sidx])
    h_core = t + v
    return s, h_core, eri


def symmetric_orthogonalizer(s: np.ndarray, eps: float = 1e-10) -> np.ndarray:
    """X = S^{-1/2} in the eigenbasis of S."""
    w, v = np.linalg.eigh(s)
    w_inv_sqrt = np.array([1.0 / math.sqrt(x) if x > eps else 0.0 for x in w])
    return (v * w_inv_sqrt) @ v.T


def ao_to_mo_integrals(
    x: np.ndarray, h_core: np.ndarray, eri: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Transform to an orthonormal spatial basis: h' and (pq|rs)' (all four indices)."""
    n = h_core.shape[0]
    # h'_pq = sum_mu,nu X_mu,p X_nu,nu h_mu,nu  — careful: X is S^{-1/2}, columns are new basis
    # Standard: h' = X.T @ h @ X if MO coeffs C = X (columns orthonormal AOs mix to MOs)
    h_mo = x.T @ h_core @ x
    eri_mo = np.zeros_like(eri)
    for p in range(n):
        for q in range(n):
            for r in range(n):
                for s in range(n):
                    acc = 0.0
                    for mu in range(n):
                        for nu in range(n):
                            for lam in range(n):
                                for sig in range(n):
                                    acc += (
                                        x[mu, p]
                                        * x[nu, q]
                                        * x[lam, r]
                                        * x[sig, s]
                                        * eri[mu, nu, lam, sig]
                                    )
                    eri_mo[p, q, r, s] = acc
    return h_mo, eri_mo


# ---------------------------------------------------------------------------
# Full CI (NumPy dense): PySCF-compatible absorb_h1e + fci_slow.contract_2e
#
# The following routines are adapted from PySCF (fci/{fci_slow.py,cistring.py},
# direct_nosym.absorb_h1e), Apache License 2.0, Copyright 2014-2021 The PySCF
# Developers. They implement the same ``H|c⟩`` as PySCF's FCI for spin-adapted
# spatial orbitals in chemist ERI notation.

FCI_DENSE_MAX_DIM = 4096


class _OIndexList(np.ndarray):
    pass


def _fci_num_strings(norb: int, nelec: int) -> int:
    return math.comb(norb, nelec)


def _fci_gen_occslst(orb_list: list[int], nelec: int) -> _OIndexList:
    if nelec < 0:
        raise ValueError("nelec must be non-negative")
    if nelec == 0:
        return np.zeros((1, 0), dtype=np.int32).view(_OIndexList)
    if nelec > len(orb_list):
        return np.zeros((0, nelec), dtype=np.int32).view(_OIndexList)

    def gen_occs_iter(orb_list: list[int], nelec: int) -> list[list[int]]:
        if nelec == 1:
            return [[i] for i in orb_list]
        if nelec >= len(orb_list):
            return [orb_list]
        restorb = orb_list[:-1]
        thisorb = orb_list[-1]
        res = gen_occs_iter(restorb, nelec)
        for n in gen_occs_iter(restorb, nelec - 1):
            res.append(n + [thisorb])
        return res

    occslst = gen_occs_iter(orb_list, nelec)
    return np.asarray(occslst, dtype=np.int32).view(_OIndexList)


def _fci_gen_linkstr_index_o1(
    orb_list: Sequence[int], nelec: int, strs: _OIndexList | None = None
) -> np.ndarray:
    """Python link table (same layout as PySCF ``gen_linkstr_index_o1``)."""
    if nelec == 0:
        return np.zeros((0, 0, 4), dtype=np.int32)
    if strs is None:
        strs = _fci_gen_occslst(list(orb_list), nelec)
    occslst = strs
    orb_list_arr = np.asarray(orb_list)
    norb = len(orb_list_arr)
    if not np.all(np.arange(norb) == orb_list_arr):
        raise ValueError("orb_list must be [0,1,...,norb-1]")
    strdic = {tuple(s): i for i, s in enumerate(occslst)}
    nvir = norb - nelec

    def propgate1e(str0: np.ndarray) -> np.ndarray:
        addr0 = strdic[tuple(str0)]
        tab = np.empty((nelec, 4), dtype=np.int32)
        tab[:, 0] = tab[:, 1] = str0
        tab[:, 2] = addr0
        tab[:, 3] = 1
        linktab = [tab]

        virmask = np.ones(norb, dtype=bool)
        virmask[str0] = False
        vir = orb_list_arr[virmask]
        str0_arr = np.asarray(str0)
        where_vir = np.sum(str0_arr.reshape(-1, 1) < vir, axis=0)
        parity_occ_orb = 1
        for n, i in enumerate(str0):
            reorder_to_ov = vir > i
            str1s = np.empty((nvir, nelec), dtype=int)
            str1s[:] = str0_arr
            str1s[:, n] = vir
            str1s.sort(axis=1)
            addr = [strdic[tuple(s)] for s in str1s]
            parity = (where_vir + reorder_to_ov + 1) % 2
            parity[parity == 0] = -1
            parity *= parity_occ_orb
            tab = np.empty((nvir, 4), dtype=np.int32)
            tab[:, 0] = vir
            tab[:, 1] = i
            tab[:, 2] = addr
            tab[:, 3] = parity
            linktab.append(tab)
            parity_occ_orb *= -1
        return np.vstack(linktab)

    lidx = [propgate1e(s) for s in occslst]
    return np.asarray(lidx, dtype=np.int32)


def _fci_absorb_h1e(
    h1e: np.ndarray, eri: np.ndarray, norb: int, nelec: int | tuple[int, int], fac: float = 1.0
) -> np.ndarray:
    """Fold one-electron part into the effective 2e tensor (PySCF ``direct_nosym``)."""
    if isinstance(nelec, tuple):
        nelec_sum = int(nelec[0] + nelec[1])
    else:
        nelec_sum = int(nelec)
    h2e = np.asarray(eri, dtype=float).copy()
    f1e = h1e - np.einsum("jiik->jk", h2e) * 0.5
    f1e = f1e * (1.0 / (nelec_sum + 1e-100))
    for k in range(norb):
        h2e[k, k, :, :] += f1e
        h2e[:, :, k, k] += f1e
    return h2e * fac


def _fci_contract_2e(
    eri: np.ndarray,
    fcivec: np.ndarray,
    norb: int,
    nelec: int | tuple[int, int],
    link_indexa: np.ndarray,
    link_indexb: np.ndarray,
) -> np.ndarray:
    """``E_pq E_rs eri[pq,rs] |CI⟩`` in PySCF's spin-summed convention (``fci_slow``)."""
    if isinstance(nelec, int):
        nelecb = nelec // 2
        neleca = nelec - nelecb
    else:
        neleca, nelecb = nelec
    na = _fci_num_strings(norb, neleca)
    nb = _fci_num_strings(norb, nelecb)
    ci0 = fcivec.reshape(na, nb)
    t1 = np.zeros((norb, norb, na, nb), dtype=fcivec.dtype)
    for str0, tab in enumerate(link_indexa):
        for row in tab:
            a, i, str1, sign = int(row[0]), int(row[1]), int(row[2]), int(row[3])
            t1[a, i, str1] += sign * ci0[str0]
    for str0, tab in enumerate(link_indexb):
        for row in tab:
            a, i, str1, sign = int(row[0]), int(row[1]), int(row[2]), int(row[3])
            t1[a, i, :, str1] += sign * ci0[:, str0]
    eri4 = eri.reshape(norb, norb, norb, norb)
    t1 = np.einsum("bjai,aiAB->bjAB", eri4, t1, optimize=True)
    fcinew = np.zeros_like(ci0, dtype=fcivec.dtype)
    for str0, tab in enumerate(link_indexa):
        for row in tab:
            a, i, str1, sign = int(row[0]), int(row[1]), int(row[2]), int(row[3])
            fcinew[str1] += sign * t1[a, i, str0]
    for str0, tab in enumerate(link_indexb):
        for row in tab:
            a, i, str1, sign = int(row[0]), int(row[1]), int(row[2]), int(row[3])
            fcinew[:, str1] += sign * t1[a, i, :, str0]
    return fcinew.reshape(fcivec.shape)


def _fci_link_index(norb: int, neleca: int, nelecb: int) -> tuple[np.ndarray, np.ndarray]:
    occ_a = _fci_gen_occslst(list(range(norb)), neleca)
    occ_b = _fci_gen_occslst(list(range(norb)), nelecb)
    la = _fci_gen_linkstr_index_o1(range(norb), neleca, occ_a)
    lb = _fci_gen_linkstr_index_o1(range(norb), nelecb, occ_b)
    return la, lb


def fci_electronic_energy_numpy(
    h1: np.ndarray,
    eri: np.ndarray,
    n_alpha: int,
    n_beta: int,
    *,
    max_dim: int = FCI_DENSE_MAX_DIM,
) -> float:
    """
    Lowest **electronic** full-CI energy (Hartree) by dense ``eigh`` on the FCI Hamiltonian.

    Uses the same operator as PySCF ``direct_nosym`` FCI with ``ecore=0``. Intended for
    small active spaces (dimension ``C(norb,nα)·C(norb,nβ)``).
    """
    h1 = np.asarray(h1, dtype=float)
    eri = np.asarray(eri, dtype=float)
    norb = h1.shape[0]
    neleca, nelecb = int(n_alpha), int(n_beta)
    na = _fci_num_strings(norb, neleca)
    nb = _fci_num_strings(norb, nelecb)
    dim = na * nb
    if dim > max_dim:
        raise ValueError(
            f"FCI Hilbert space dimension {dim} exceeds max_dim={max_dim}; "
            "use a smaller basis or an external FCI driver."
        )
    nelec = (neleca, nelecb)
    h2e = _fci_absorb_h1e(h1, eri, norb, nelec, 0.5)
    la, lb = _fci_link_index(norb, neleca, nelecb)
    h_mat = np.zeros((dim, dim), dtype=float)
    for j in range(dim):
        c = np.zeros(dim, dtype=float)
        c[j] = 1.0
        h_mat[:, j] = _fci_contract_2e(h2e, c, norb, nelec, la, lb).ravel()
    return float(np.linalg.eigvalsh(h_mat)[0])


def _combinations(n: int, k: int) -> Iterator[tuple[int, ...]]:
    yield from itertools.combinations(range(n), k)


def enumerate_determinants(n_mo: int, n_alpha: int, n_beta: int) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    """All (occ_α, occ_β) pairs with fixed particle numbers (α×β lex order)."""
    if n_alpha > n_mo or n_beta > n_mo:
        raise ValueError("electron count exceeds orbital count")
    dets: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for occ_a in _combinations(n_mo, n_alpha):
        for occ_b in _combinations(n_mo, n_beta):
            dets.append((occ_a, occ_b))
    return dets


def fci_electronic_energy(
    h1: np.ndarray,
    eri: np.ndarray,
    n_alpha: int,
    n_beta: int,
) -> float:
    """
    Lowest **electronic** full-CI energy in the orthonormal spatial basis (Hartree).

    Uses dense NumPy diagonalization (same operator convention as PySCF ``direct_nosym``
    with ``ecore=0``). The tensors ``h1`` and ``eri`` are the usual second-quantized
    Hamiltonian in chemist ERI notation ``eri[p,q,r,s] = (pq|rs)``.
    """
    return fci_electronic_energy_numpy(h1, eri, n_alpha, n_beta)


# ---------------------------------------------------------------------------
# Example: H₂ STO-3G (minimal)


def example_h2_sto3g_fci(bond_bohr: float = 1.4) -> dict[str, float]:
    """Bond length in Bohr; R = 1.4 is a common regression point."""
    r = float(bond_bohr)
    h1 = sto3g_hydrogen_shell(np.array([-r / 2, 0.0, 0.0]))
    h2 = sto3g_hydrogen_shell(np.array([r / 2, 0.0, 0.0]))
    mol = MoleculeSpec(np.array([1.0, 1.0]), np.array([[-r / 2, 0.0, 0.0], [r / 2, 0.0, 0.0]]))
    s, h_core, eri = build_ao_matrices([h1, h2], mol)
    x = symmetric_orthogonalizer(s)
    h_mo, eri_mo = ao_to_mo_integrals(x, h_core, eri)
    e_el = fci_electronic_energy(h_mo, eri_mo, n_alpha=1, n_beta=1)
    e_nuc = 1.0 / r
    return {
        "electronic_fci_hartree": e_el,
        "nuclear_repulsion_hartree": float(e_nuc),
        "total_energy_hartree": float(e_el + e_nuc),
        "bond_bohr": r,
    }


def main() -> None:
    out = example_h2_sto3g_fci(1.4)
    print("H2 STO-3G minimal-basis (integrals: NumPy; FCI: NumPy dense)")
    for k, v in out.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
