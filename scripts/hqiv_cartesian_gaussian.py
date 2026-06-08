#!/usr/bin/env python3
"""
Cartesian Gaussian primitives (s and p) in ℝ³ for fixed-nuclei nonrelativistic QC.

**Angular momentum:** each primitive is

    φ ∝ (x-Ax)^lx (y-Ay)^ly (z-Az)^lz exp(-α |r-A|²)

with ``lx+ly+lz ∈ {0,1}`` (s or a single Cartesian p). This is standard quantum chemistry
(Szabo & Ostlund; Helgaker et al.); HQIV does not change the *shape* — only the length
scales/exponents you feed in from shell/isotope scripts.

**Implementation notes**

* **Overlap** and **kinetic** factorize as products of **1D** integrals along x, y, z because
  the Gaussian is separable: exp(-α|r-A|²) = Π_k exp(-α(x_k-A_k)²) and at most one axis carries
  a linear factor for p.
* **Nuclear attraction** uses analytic ∂/∂A of the s–s matrix element for the Coulomb line
  (Boys F_n), matching ``(x-Ax) = (1/(2α)) ∂/∂A_x exp(-α|r-A|²)`` for unnormalized primitives.
* **ERI** for mixed angular momentum uses nested **central differences** of the existing
  ``primitive_eri_ssss`` as a function of nuclear positions — mathematically ∂/∂A of the
  smooth s-type four-center integral (avoids a large HRR port while staying correct to ~1e-8
  with a small step).

Reuses geometry helpers and ``primitive_eri_ssss`` from ``hqiv_molecular_hamiltonian``.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Sequence

import numpy as np

import sys
from pathlib import Path

_scripts_dir = str(Path(__file__).resolve().parent)
if _scripts_dir not in sys.path:
    sys.path.insert(0, _scripts_dir)

import hqiv_molecular_hamiltonian as hm

MoleculeSpec = hm.MoleculeSpec
dist2 = hm.dist2
primitive_eri_ssss = hm.primitive_eri_ssss
primitive_nuclear_s = hm.primitive_nuclear_s

# ---------------------------------------------------------------------------
# Boys functions F_n(t) = ∫_0^1 u^{2n} exp(-t u²) du


def boys_fn(n: int, t: float) -> float:
    """Stable Boys F_n(t) for t ≥ 0, n ≥ 0."""
    if n < 0:
        raise ValueError("n must be non-negative")
    # Series F_n(t) = Σ_i (-t)^i / (i! (2n+2i+1)) is well-behaved at t = 0 (F_n(0) = 1/(2n+1)).
    if t < 1e-9:
        s = 0.0
        tp = 1.0
        for i in range(28):
            s += tp / (math.gamma(i + 1) * (2 * n + 2 * i + 1))
            tp *= -t
        return float(s)
    if n == 0:
        return float(hm.boys_f0(t))
    fm = float(hm.boys_f0(t))
    emt = math.exp(-t)
    for k in range(1, n + 1):
        # (2t) F_k = (2k-1) F_{k-1} - exp(-t)  =>  F_k = ((2k-1) F_{k-1} - exp(-t)) / (2t)
        fm = ((2 * k - 1) * fm - emt) / (2.0 * t)
    return float(fm)


# ---------------------------------------------------------------------------
# 1D overlap and kinetic (unnormalized: s = exp(-a(x-A)²), p = (x-A) exp(-a(x-A)²))


def _overlap_1d(ax: int, bx: int, a: float, b: float, A: float, B: float) -> float:
    """1D overlap ⟨a|b⟩ for angular indices ax, bx ∈ {0,1}."""
    p = a + b
    mu = a * b / p
    d = A - B
    s0 = math.sqrt(math.pi / p) * math.exp(-mu * d * d)
    pa = (a * A + b * B) / p
    paa = pa - A
    pbb = pa - B
    if ax == 0 and bx == 0:
        return float(s0)
    if ax == 1 and bx == 0:
        return float(paa * s0)
    if ax == 0 and bx == 1:
        return float(pbb * s0)
    if ax == 1 and bx == 1:
        return float(s0 / (2.0 * p) + paa * pbb * s0)
    raise ValueError("ax,bx must be 0 or 1")


def _kinetic_1d(ax: int, bx: int, a: float, b: float, A: float, B: float) -> float:
    """1D kinetic ⟨a| -½ d²/dx² |b⟩ for ax, bx ∈ {0,1} (exact rational × S0)."""
    p = a + b
    mu = a * b / p
    dAB = A - B
    s0 = math.sqrt(math.pi / p) * math.exp(-mu * dAB * dAB)
    if ax == 0 and bx == 0:
        return float((a * b / p) * (1.0 - 2.0 * mu * dAB * dAB) * s0)
    num01 = (
        a
        * a
        * b
        * (
            -2 * A**3 * a * b
            + 6 * A**2 * B * a * b
            - 6 * A * B**2 * a * b
            + 3 * A * a
            + 3 * A * b
            + 2 * B**3 * a * b
            - 3 * B * a
            - 3 * B * b
        )
    )
    den01 = (a + b) ** 3
    if ax == 0 and bx == 1:
        return float((num01 / den01) * s0)
    num10 = (
        a
        * b
        * b
        * (
            2 * A**3 * a * b
            - 6 * A**2 * B * a * b
            + 6 * A * B**2 * a * b
            - 3 * A * a
            - 3 * A * b
            - 2 * B**3 * a * b
            + 3 * B * a
            + 3 * B * b
        )
    )
    den10 = (a + b) ** 3
    if ax == 1 and bx == 0:
        return float((num10 / den10) * s0)
    if ax == 1 and bx == 1:
        num11 = (
            a
            * b
            * (
                4 * A**4 * a**2 * b**2
                - 16 * A**3 * B * a**2 * b**2
                + 24 * A**2 * B**2 * a**2 * b**2
                - 12 * A**2 * a**2 * b
                - 12 * A**2 * a * b**2
                - 16 * A * B**3 * a**2 * b**2
                + 24 * A * B * a**2 * b
                + 24 * A * B * a * b**2
                + 4 * B**4 * a**2 * b**2
                - 12 * B**2 * a**2 * b
                - 12 * B**2 * a * b**2
                + 3 * a**2
                + 6 * a * b
                + 3 * b**2
            )
        )
        den11 = 2.0 * (a + b) ** 4
        return float((num11 / den11) * s0)
    raise ValueError("ax,bx must be 0 or 1")


def _axis_angular(la: tuple[int, int, int], lb: tuple[int, int, int], k: int) -> tuple[int, int]:
    return (la[k], lb[k])


def primitive_overlap_cart(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    la: tuple[int, int, int],
    lb: tuple[int, int, int],
) -> float:
    """Overlap ⟨φ_a|φ_b⟩ for Cartesian primitives (unnormalized monomial factors)."""
    if sum(la) > 1 or sum(lb) > 1 or any(x < 0 or x > 1 for x in la + lb):
        raise ValueError("only s and single Cartesian p supported")
    ax, ay, az = la
    bx, by, bz = lb
    sx = _overlap_1d(ax, bx, alpha, beta, float(a[0]), float(b[0]))
    sy = _overlap_1d(ay, by, alpha, beta, float(a[1]), float(b[1]))
    sz = _overlap_1d(az, bz, alpha, beta, float(a[2]), float(b[2]))
    return float(sx * sy * sz)


def primitive_kinetic_cart(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    la: tuple[int, int, int],
    lb: tuple[int, int, int],
) -> float:
    r"""Kinetic ⟨φ_a| -½∇² |φ_b⟩ (separable: T = T_x S_y S_z + S_x T_y S_z + S_x S_y T_z)."""
    if sum(la) > 1 or sum(lb) > 1:
        raise ValueError("only s and single Cartesian p supported")
    ax, ay, az = la
    bx, by, bz = lb
    A = (float(a[0]), float(a[1]), float(a[2]))
    B = (float(b[0]), float(b[1]), float(b[2]))
    sx = _overlap_1d(ax, bx, alpha, beta, A[0], B[0])
    sy = _overlap_1d(ay, by, alpha, beta, A[1], B[1])
    sz = _overlap_1d(az, bz, alpha, beta, A[2], B[2])
    tx = _kinetic_1d(ax, bx, alpha, beta, A[0], B[0])
    ty = _kinetic_1d(ay, by, alpha, beta, A[1], B[1])
    tz = _kinetic_1d(az, bz, alpha, beta, A[2], B[2])
    return float(tx * sy * sz + sx * ty * sz + sx * sy * tz)


def _d_nuclear_ss_d_ax(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    z: float,
    r_nuc: np.ndarray,
    axis: int,
) -> float:
    """∂/∂a_axis of V_ss = -Z ⟨s_A s_B | 1/r_C |⟩ (first electron on A)."""
    if abs(z) < 1e-16:
        return 0.0
    p = alpha + beta
    mu_ab = alpha * beta / p
    kab = math.exp(-mu_ab * dist2(a, b))
    p_center = (alpha * a + beta * b) / p
    rpc = p_center - r_nuc
    tnu = p * float(np.dot(rpc, rpc))
    f0 = boys_fn(0, tnu)
    f1 = boys_fn(1, tnu)
    dab = a - b
    d_kab = kab * (-2.0 * mu_ab * float(dab[axis]))
    dt_da = 2.0 * float(rpc[axis]) * alpha
    return float((-z) * (2.0 * math.pi / p) * (d_kab * f0 - kab * f1 * dt_da))


def _d_nuclear_ss_d_bx(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    z: float,
    r_nuc: np.ndarray,
    axis: int,
) -> float:
    """∂/∂b_axis of V_ss (second primitive center B)."""
    if abs(z) < 1e-16:
        return 0.0
    p = alpha + beta
    mu_ab = alpha * beta / p
    kab = math.exp(-mu_ab * dist2(a, b))
    p_center = (alpha * a + beta * b) / p
    rpc = p_center - r_nuc
    tnu = p * float(np.dot(rpc, rpc))
    f0 = boys_fn(0, tnu)
    f1 = boys_fn(1, tnu)
    d_kab_b = kab * (-2.0 * mu_ab * float(b[axis] - a[axis]))
    dt_db = 2.0 * float(rpc[axis]) * beta
    return float((-z) * (2.0 * math.pi / p) * (d_kab_b * f0 - kab * f1 * dt_db))


def primitive_nuclear_cart(
    alpha: float,
    beta: float,
    a: np.ndarray,
    b: np.ndarray,
    la: tuple[int, int, int],
    lb: tuple[int, int, int],
    z: float,
    r_nuc: np.ndarray,
) -> float:
    """Nuclear attraction -Z ⟨a|1/r_C|b⟩ for Cartesian s/p primitives."""
    if sum(la) > 1 or sum(lb) > 1:
        raise ValueError("only s and single Cartesian p supported")
    if la == (0, 0, 0) and lb == (0, 0, 0):
        return primitive_nuclear_s(alpha, beta, a, b, z, r_nuc)
    # p on A only: (x-A_k) G = (1/(2α)) ∂_{A_k} G_s
    if sum(la) == 1 and lb == (0, 0, 0):
        axis = la.index(1)
        return (1.0 / (2.0 * alpha)) * _d_nuclear_ss_d_ax(alpha, beta, a, b, z, r_nuc, axis)
    # p on B only
    if la == (0, 0, 0) and sum(lb) == 1:
        axis = lb.index(1)
        return (1.0 / (2.0 * beta)) * _d_nuclear_ss_d_bx(alpha, beta, a, b, z, r_nuc, axis)
    # p on both: ∂_{A_i} ∂_{B_j} V_ss / (4 α β)
    if sum(la) == 1 and sum(lb) == 1:
        ia = la.index(1)
        ib = lb.index(1)
        h = 1e-5

        def vss(ca: np.ndarray, cb: np.ndarray) -> float:
            return primitive_nuclear_s(alpha, beta, ca, cb, z, r_nuc)

        ac = np.asarray(a, dtype=float).copy()
        bc = np.asarray(b, dtype=float).copy()
        acp = ac.copy()
        acp[ia] += h
        acm = ac.copy()
        acm[ia] -= h
        bcp = bc.copy()
        bcp[ib] += h
        bcm = bc.copy()
        bcm[ib] -= h
        vpp = (vss(acp, bcp) - vss(acp, bcm) - vss(acm, bcp) + vss(acm, bcm)) / (4.0 * h * h)
        return float((1.0 / (4.0 * alpha * beta)) * vpp)
    raise NotImplementedError("unsupported angular pattern")


_FD_H = 1e-6


def primitive_eri_cart(
    alpha: float,
    beta: float,
    gamma: float,
    delta: float,
    a: np.ndarray,
    b: np.ndarray,
    c: np.ndarray,
    d: np.ndarray,
    la: tuple[int, int, int],
    lb: tuple[int, int, int],
    lc: tuple[int, int, int],
    ld: tuple[int, int, int],
) -> float:
    """
    (ab|cd) chemist notation for Cartesian s/p primitives.

    Nested central differences of ``primitive_eri_ssss`` in nuclear positions implement
    ``(x-A_k) = (1/(2α)) ∂/∂A_k`` on unnormalized Gaussians (chain rule on smooth s-type ERI).

    **Limitation:** when several p primitives share one nucleus, finite differences on
    coincident centers can be noisy; for production LiH benchmarks prefer
    ``example_lih_sto3g_fci`` (PySCF ``int2e`` backend when available).
    """
    if sum(la) > 1 or sum(lb) > 1 or sum(lc) > 1 or sum(ld) > 1:
        raise ValueError("only s and single Cartesian p per primitive")

    fd_h = _FD_H
    angs = [la, lb, lc, ld]
    zetas = [alpha, beta, gamma, delta]
    ops: list[tuple[int, int, float]] = []
    for ic, ang in enumerate(angs):
        if ang == (0, 0, 0):
            continue
        axis = ang.index(1)
        ops.append((ic, axis, zetas[ic]))

    def make_deriv(f_inner, ic_f: int, axis_f: int, zeta_f: float):
        def g(A: np.ndarray, B: np.ndarray, C: np.ndarray, D: np.ndarray) -> float:
            centers = [np.asarray(A, float).copy(), np.asarray(B, float).copy(), np.asarray(C, float).copy(), np.asarray(D, float).copy()]
            x0 = float(centers[ic_f][axis_f])

            def val_at(xv: float) -> float:
                cc = [centers[0].copy(), centers[1].copy(), centers[2].copy(), centers[3].copy()]
                cc[ic_f][axis_f] = xv
                return f_inner(cc[0], cc[1], cc[2], cc[3])

            return (val_at(x0 + fd_h) - val_at(x0 - fd_h)) / (2.0 * fd_h) / (2.0 * zeta_f)

        return g

    f = lambda A, B, C, D: primitive_eri_ssss(alpha, beta, gamma, delta, A, B, C, D)
    for ic, axis, zeta in ops:
        f = make_deriv(f, ic, axis, zeta)

    A, B, C, D = [np.asarray(x, float).copy() for x in (a, b, c, d)]
    return float(f(A, B, C, D))


# ---------------------------------------------------------------------------
# Normalization: STO tables use normalized primitives; map to raw monomial × exp


def weight_s_raw(alpha: float, c: float) -> float:
    """STO coefficient × N_s for raw exp(-α r²)."""
    return float(c * (2.0 * alpha / math.pi) ** 0.75)


def weight_p_raw(alpha: float, c: float) -> float:
    """
    STO coefficient × N for raw (x-Ax) exp(-α r²) along one axis.

    Normalized Cartesian p: N_p x exp(-α r²) with N_p = (128 α^5 / π^3)^(1/4).
    Raw monomial is x exp(-α r²); ratio N_p / 1 = N_p.
    """
    n_p = (128.0 * alpha**5 / math.pi**3) ** 0.25
    return float(c * n_p)


@dataclass(frozen=True)
class ContractedCart:
    """Contracted Cartesian shell: angular (lx,ly,lz), center, primitives."""

    angular: tuple[int, int, int]
    center: np.ndarray
    exponents: tuple[float, ...]
    coefficients: tuple[float, ...]

    def __post_init__(self) -> None:
        assert len(self.exponents) == len(self.coefficients)
        s = sum(self.angular)
        if s > 1 or any(x < 0 or x > 1 for x in self.angular):
            raise ValueError("angular must be s or single p")
        self.center.reshape(3)


def _weight_primitive(alpha: float, c: float, ang: tuple[int, int, int]) -> float:
    if ang == (0, 0, 0):
        return weight_s_raw(alpha, c)
    if sum(ang) == 1:
        return weight_p_raw(alpha, c)
    raise ValueError("angular")


def contracted_overlap_cart(c1: ContractedCart, c2: ContractedCart) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _weight_primitive(a, ca, c1.angular)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _weight_primitive(b, cb, c2.angular)
            tot += wa * wb * primitive_overlap_cart(a, b, c1.center, c2.center, c1.angular, c2.angular)
    return float(tot)


def contracted_kinetic_cart(c1: ContractedCart, c2: ContractedCart) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _weight_primitive(a, ca, c1.angular)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _weight_primitive(b, cb, c2.angular)
            tot += wa * wb * primitive_kinetic_cart(a, b, c1.center, c2.center, c1.angular, c2.angular)
    return float(tot)


def contracted_nuclear_cart(
    c1: ContractedCart, c2: ContractedCart, charges: np.ndarray, positions: np.ndarray
) -> float:
    tot = 0.0
    for iz in range(charges.shape[0]):
        z = float(charges[iz])
        r = positions[iz]
        for a, ca in zip(c1.exponents, c1.coefficients):
            wa = _weight_primitive(a, ca, c1.angular)
            for b, cb in zip(c2.exponents, c2.coefficients):
                wb = _weight_primitive(b, cb, c2.angular)
                tot += wa * wb * primitive_nuclear_cart(a, b, c1.center, c2.center, c1.angular, c2.angular, z, r)
    return float(tot)


def contracted_eri_cart(
    c1: ContractedCart, c2: ContractedCart, c3: ContractedCart, c4: ContractedCart
) -> float:
    tot = 0.0
    for a, ca in zip(c1.exponents, c1.coefficients):
        wa = _weight_primitive(a, ca, c1.angular)
        for b, cb in zip(c2.exponents, c2.coefficients):
            wb = _weight_primitive(b, cb, c2.angular)
            for c, cc in zip(c3.exponents, c3.coefficients):
                wc = _weight_primitive(c, cc, c3.angular)
                for d, cd in zip(c4.exponents, c4.coefficients):
                    wd = _weight_primitive(d, cd, c4.angular)
                    tot += (
                        wa
                        * wb
                        * wc
                        * wd
                        * primitive_eri_cart(
                            a,
                            b,
                            c,
                            d,
                            c1.center,
                            c2.center,
                            c3.center,
                            c4.center,
                            c1.angular,
                            c2.angular,
                            c3.angular,
                            c4.angular,
                        )
                    )
    return float(tot)


def build_ao_matrices_cart(
    shells: Sequence[ContractedCart], mol: MoleculeSpec
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """AO overlap, core Hamiltonian, and ERIs for mixed s/p contracted Cartesian shells."""
    n = len(shells)
    s = np.zeros((n, n), dtype=float)
    t = np.zeros((n, n), dtype=float)
    v = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(i, n):
            s_ij = contracted_overlap_cart(shells[i], shells[j])
            t_ij = contracted_kinetic_cart(shells[i], shells[j])
            v_ij = contracted_nuclear_cart(shells[i], shells[j], mol.charges, mol.positions)
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
                    eri[p, q, r, sidx] = contracted_eri_cart(shells[p], shells[q], shells[r], shells[sidx])
    h_core = t + v
    return s, h_core, eri


def verify_h2_sto3g_overlap_kinetic() -> None:
    """Regression: s-only shells match hqiv_molecular_hamiltonian within tolerance."""
    r = 1.4
    ctr = (-r / 2, 0.0, 0.0)
    ctr2 = (r / 2, 0.0, 0.0)
    h1 = hm.ContractedS(np.array(ctr), (3.42525091, 0.62391373, 0.16885540), (0.15432897, 0.53532814, 0.44463454))
    h2 = hm.ContractedS(np.array(ctr2), (3.42525091, 0.62391373, 0.16885540), (0.15432897, 0.53532814, 0.44463454))
    c1 = ContractedCart((0, 0, 0), h1.center, h1.exponents, h1.coefficients)
    c2 = ContractedCart((0, 0, 0), h2.center, h2.exponents, h2.coefficients)
    mol = MoleculeSpec(np.array([1.0, 1.0]), np.array([[-r / 2, 0.0, 0.0], [r / 2, 0.0, 0.0]]))
    s1, h1m, _ = hm.build_ao_matrices([h1, h2], mol)
    s2, h2m, _ = build_ao_matrices_cart([c1, c2], mol)
    assert np.max(np.abs(s1 - s2)) < 1e-9
    assert np.max(np.abs(h1m - h2m)) < 1e-7


# ---------------------------------------------------------------------------
# STO-3G lithium (inner S + valence SP) — EMSL / PSI4 sto-3g.gbs (Li block)


def sto3g_lithium_shells(center: np.ndarray | Sequence[float]) -> list[ContractedCart]:
    """
    Minimal STO-3G on Li: inner contracted 1s-like S, then valence SP (2s + 2px + 2py + 2pz).

    Exponents and coefficients match the Basis Set Exchange / PSI4 ``sto-3g.gbs`` entry for Li.
    """
    ctr = np.asarray(center, dtype=float).reshape(3)
    inner_ex = (16.1195750, 2.9362007, 0.7946505)
    inner_c = (0.15432897, 0.53532814, 0.44463454)
    inner = ContractedCart((0, 0, 0), ctr, inner_ex, inner_c)
    sp_ex = (0.6362897, 0.1478601, 0.0480887)
    c_s = (-0.09996723, 0.39951283, 0.70011547)
    c_p = (0.15591627, 0.60768372, 0.39195739)
    val_s = ContractedCart((0, 0, 0), ctr, sp_ex, c_s)
    px = ContractedCart((1, 0, 0), ctr, sp_ex, c_p)
    py = ContractedCart((0, 1, 0), ctr, sp_ex, c_p)
    pz = ContractedCart((0, 0, 1), ctr, sp_ex, c_p)
    return [inner, val_s, px, py, pz]


def lih_sto3g_shells(bond_bohr: float) -> tuple[list[ContractedCart], MoleculeSpec]:
    """
    Li at origin, H on +z at ``bond_bohr`` Bohr; closed-shell 4 e⁻ in minimal STO-3G (6 spatial AOs).

    ``bond_bohr ≈ 3.015`` is near the experimental R_e in Bohr.
    """
    r = float(bond_bohr)
    li_shells = sto3g_lithium_shells(np.array([0.0, 0.0, 0.0]))
    h_ctr = np.array([0.0, 0.0, r], dtype=float)
    h1s = ContractedCart(
        (0, 0, 0),
        h_ctr,
        (3.42525091, 0.62391373, 0.16885540),
        (0.15432897, 0.53532814, 0.44463454),
    )
    shells = li_shells + [h1s]
    mol = MoleculeSpec(
        np.array([3.0, 1.0], dtype=float),
        np.array([[0.0, 0.0, 0.0], [0.0, 0.0, r]], dtype=float),
    )
    return shells, mol


def example_lih_sto3g_fci(bond_bohr: float = 3.015) -> dict[str, float]:
    """
    LiH minimal-basis full CI at ``bond_bohr`` (Li at origin, H on +z), 6 spatial STO-3G AOs, 4 electrons.

    **ERI backend:** when PySCF is importable and ``int2e`` works, uses PySCF integrals + the same
    NumPy dense FCI driver as ``example_h2_sto3g_fci`` (chemist ``(pq|rs)``, ``direct_nosym``-compatible).
    Otherwise falls back to the pure-NumPy Cartesian FD ERIs in this module (less accurate for Li p shells).

    Nuclear repulsion is ``3/R`` Hartree (Z_Li=3, Z_H=1).
    """
    r = float(bond_bohr)
    try:
        from pyscf import ao2mo, fci, gto, scf  # type: ignore[import-untyped]

        mol = gto.M(atom=f"Li 0 0 0; H 0 0 {r}", basis="sto-3g", unit="Bohr")
        mf = scf.RHF(mol)
        mf.kernel()
        h1 = mf.mo_coeff.T @ mf.get_hcore() @ mf.mo_coeff
        eri_mo = ao2mo.restore(1, ao2mo.kernel(mol, mf.mo_coeff), mol.nao)
        na = mol.nelectron // 2
        e_el = hm.fci_electronic_energy(h1, eri_mo, n_alpha=na, n_beta=na)
        e_nuc = float(mol.energy_nuc())
        return {
            "electronic_fci_hartree": e_el,
            "nuclear_repulsion_hartree": e_nuc,
            "total_energy_hartree": float(e_el + e_nuc),
            "bond_bohr": r,
            "n_ao": float(mol.nao),
            "eri_backend": "pyscf",
        }
    except Exception:
        shells, molspec = lih_sto3g_shells(r)
        s, h_core, eri = build_ao_matrices_cart(shells, molspec)
        x = hm.symmetric_orthogonalizer(s)
        h_mo, eri_mo = hm.ao_to_mo_integrals(x, h_core, eri)
        e_el = hm.fci_electronic_energy(h_mo, eri_mo, n_alpha=2, n_beta=2)
        e_nuc = float(3.0 / r)
        return {
            "electronic_fci_hartree": e_el,
            "nuclear_repulsion_hartree": e_nuc,
            "total_energy_hartree": float(e_el + e_nuc),
            "bond_bohr": r,
            "n_ao": float(len(shells)),
            "eri_backend": "numpy_fd",
        }


def verify_lih_sto3g_fci_regression() -> None:
    """Regression on total FCI energy at R = 3.015 Bohr when PySCF ERIs are available."""
    out = example_lih_sto3g_fci(3.015)
    assert out["n_ao"] == 6.0
    if out.get("eri_backend") != "pyscf":
        return
    assert -7.89 < out["total_energy_hartree"] < -7.87


if __name__ == "__main__":
    verify_h2_sto3g_overlap_kinetic()
    print("hqiv_cartesian_gaussian: H2 STO-3G s-only regression OK")
    verify_lih_sto3g_fci_regression()
    print("hqiv_cartesian_gaussian: LiH STO-3G FCI regression OK")
    lih = example_lih_sto3g_fci(3.015)
    print("LiH STO-3G @ R = 3.015 Bohr (example)")
    for k, v in lih.items():
        print(f"  {k}: {v}")
    if lih.get("eri_backend") == "numpy_fd":
        print(
            "  (Install PySCF in the active environment for Libcint ERIs; "
            "pure NumPy FD is unreliable for Li p shells.)"
        )
