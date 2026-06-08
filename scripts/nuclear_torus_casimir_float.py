"""
Float mirror of `Hqiv/Geometry/NuclearTorusPerturbation.lean` + `S7MetahorizonCasimir`.

Uses the same 8×8 left-multiplication matrices as `Hqiv/OctonionLeftMultiplication.lean`
(Fano-plane octonions).  Intended for optional diagnostics from Python (e.g.
`predictive_patch_prune_trace`), not as a proof.

Hydrogen anchor: 13.6 eV per λ-unit at ℓ = 1 (`eVPerLambdaUnit_S7HydrogenAnchor = 13.6/7`).
"""

from __future__ import annotations

import math
from typing import Any, Iterable

Vec8 = list[float]

# Identity 8×8
def _eye8() -> list[list[float]]:
    return [[1.0 if i == j else 0.0 for j in range(8)] for i in range(8)]


def _mat_sum_scaled(
    mats: list[list[list[float]]], coeffs: list[float]
) -> list[list[float]]:
    out = [[0.0] * 8 for _ in range(8)]
    for c, m in zip(coeffs, mats):
        for i in range(8):
            for j in range(8):
                out[i][j] += c * m[i][j]
    return out


def _matvec(m: list[list[float]], v: Vec8) -> Vec8:
    return [sum(m[i][j] * v[j] for j in range(8)) for i in range(8)]


# L(e_1) .. L(e_7) from `Hqiv/OctonionLeftMultiplication.lean` (same row-major order as Lean !![...]).
def _L_octonion() -> list[list[list[float]]]:
    L1 = [
        [0, -1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
    ]
    L2 = [
        [0, 0, -1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
    ]
    L3 = [
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
    ]
    L4 = [
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
        [0, 0, -1, 0, 0, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
    ]
    L5 = [
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
    ]
    L6 = [
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0,  0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
    ]
    L7 = [
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
    ]
    return [L1, L2, L3, L4, L5, L6, L7]


_L_STORE = _L_octonion()


def left_mul_vec(x: Vec8, y: Vec8) -> Vec8:
    """Octonion product x * y with x = Σ x_i e_i, using L(x) = x0 I + Σ_{i=1}^7 x_i L(e_i)."""
    coeffs = [x[0]] + [x[i] for i in range(1, 8)]
    mats = [_eye8()] + _L_STORE
    lx = _mat_sum_scaled(mats[1:], coeffs[1:])
    # L(x) = x0 * I + sum_{i=1..7} xi Li
    for i in range(8):
        for j in range(8):
            lx[i][j] += coeffs[0] * (1.0 if i == j else 0.0)
    return _matvec(lx, y)


def octonion_associator(x: Vec8, y: Vec8, z: Vec8) -> Vec8:
    xy_z = left_mul_vec(left_mul_vec(x, y), z)
    x_yz = left_mul_vec(x, left_mul_vec(y, z))
    return [xy_z[i] - x_yz[i] for i in range(8)]


def octonion_associator_norm_sq(x: Vec8, y: Vec8, z: Vec8) -> float:
    a = octonion_associator(x, y, z)
    return sum(t * t for t in a)


def spherical_harmonic_dim_s7(ell: int) -> int:
    """dim ℋ_ℓ on S⁷ (same combinatorial formula as Lean `sphericalHarmonicDimS7`)."""
    from math import comb

    return (2 * ell + 6) * comb(ell + 5, 5) // 6


def laplace_beltrami_eigenvalue_nat(ell: int) -> int:
    return ell * (ell + 6)


def fill_lambda_sum(remaining: int, ell: int, acc: int) -> int:
    if remaining == 0:
        return acc
    rem = remaining - 1
    d = spherical_harmonic_dim_s7(ell)
    if rem + 1 <= d:
        return acc + (rem + 1) * laplace_beltrami_eigenvalue_nat(ell)
    return fill_lambda_sum(rem + 1 - d, ell + 1, acc + d * laplace_beltrami_eigenvalue_nat(ell))


def occupation_list(n: int) -> list[int]:
    """Greedy lowest-ℓ-first occupation (matches Lean `fillOccupation`)."""

    def fill(rem: int, ell: int, acc: list[int]) -> list[int]:
        if rem == 0:
            return list(reversed(acc))
        d = spherical_harmonic_dim_s7(ell)
        if rem <= d:
            return list(reversed([ell] * rem + acc))
        return fill(rem - d, ell + 1, [ell] * d + acc)

    return fill(n, 0, [])


def nuclear_torus_f(angles: tuple[float, float, float]) -> Vec8:
    t0, _, _ = angles
    v = [0.0] * 8
    v[1] = math.cos(t0)
    v[2] = math.sin(t0)
    return v


def nuclear_torus_x(angles: tuple[float, float, float]) -> Vec8:
    _, t1, _ = angles
    v = [0.0] * 8
    v[3] = math.cos(t1)
    v[4] = math.sin(t1)
    return v


def nuclear_torus_l(angles: tuple[float, float, float]) -> Vec8:
    _, _, t2 = angles
    v = [0.0] * 8
    v[5] = math.cos(t2)
    v[6] = math.sin(t2)
    return v


DEFAULT_UUD_ANGLES_RAD = (0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0)


def associator_perturbation(ell: int, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD) -> float:
    """Δλ shell term: ℓ × ‖(xy)z − x(yz)‖² with (F,X,L) on three orthogonal imaginary planes."""
    f = nuclear_torus_f(angles)
    x = nuclear_torus_x(angles)
    l = nuclear_torus_l(angles)
    return float(ell) * octonion_associator_norm_sq(f, x, l)


def noninteracting_fermion_lambda_sum(n: int) -> int:
    return fill_lambda_sum(n, 0, 0)


def perturbed_casimir_energy(
    n: int, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD
) -> float:
    base = float(noninteracting_fermion_lambda_sum(n))
    occ = occupation_list(n)
    corr = sum(associator_perturbation(ell, angles) for ell in occ)
    return base + corr


EV_PER_LAMBDA_UNIT = 13.6 / 7.0  # `eVPerLambdaUnit_S7HydrogenAnchor`


def perturbed_casimir_energy_ev(
    n: int, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD
) -> float:
    return perturbed_casimir_energy(n, angles) * EV_PER_LAMBDA_UNIT


def perturbed_ionization_ip_ev(
    z: int, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD
) -> float:
    """Incremental IP for adding the Z-th electron (Z ≥ 1), hydrogen-anchor eV."""
    if z <= 0:
        raise ValueError("Z must be positive")
    return (perturbed_casimir_energy(z, angles) - perturbed_casimir_energy(z - 1, angles)) * EV_PER_LAMBDA_UNIT


def first_perturbed_ionization_ips_ev(
    count: int = 8, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for z in range(1, max(0, count) + 1):
        out.append(
            {
                "Z": z,
                "perturbed_ionization_ip_eV": perturbed_ionization_ip_ev(z, angles),
                "perturbed_total_lambda_sum": perturbed_casimir_energy(z, angles),
            }
        )
    return out


def casimir_rows_for_kept_j(
    kept_j: Iterable[int],
    *,
    electron_count_for_j: Any | None = None,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> list[dict[str, Any]]:
    """
    Attach perturbed Casimir diagnostics to patch indices (toy map: which electron count to use).

    Default: ``N = min(j + 1, 256)`` so large ``j`` do not explode the greedy fill.
    """

    fn = electron_count_for_j
    if fn is None:

        def _default(j: int) -> int:
            return min(int(j) + 1, 256)

        fn = _default

    rows: list[dict[str, Any]] = []
    for j in sorted(set(int(x) for x in kept_j)):
        n = int(fn(j))
        if n < 0:
            continue
        rows.append(
            {
                "j": j,
                "N_electrons": n,
                "noninteracting_lambda_sum": noninteracting_fermion_lambda_sum(n),
                "perturbed_casimir_energy_dimless": perturbed_casimir_energy(n, angles),
                "perturbed_casimir_energy_eV": perturbed_casimir_energy_ev(n, angles),
            }
        )
    return rows


__all__ = [
    "DEFAULT_UUD_ANGLES_RAD",
    "associator_perturbation",
    "occupation_list",
    "perturbed_casimir_energy",
    "perturbed_casimir_energy_ev",
    "perturbed_ionization_ip_ev",
    "first_perturbed_ionization_ips_ev",
    "casimir_rows_for_kept_j",
]
