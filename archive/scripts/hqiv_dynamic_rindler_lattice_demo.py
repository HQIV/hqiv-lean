#!/usr/bin/env python3
"""
Dynamic-Rindler / eff / next-lattice-step demo (Python mirror of Lean numerics).

**Lean alignment**
  - `effCorrected δ m` = `(m+1)(m+2) / (1 + c_rindler·m + δ)` with `c_rindler_shared = γ/2 = 1/5`
    (`GlobalDetuning.c_rindler_shared_eq_one_fifth`, `γ = 2/5`).
  - `delta_auxiliary_phi_per_shell` = `deltaGlobal + β_cum * (φ·t)` (`GlobalDetuning`).
  - `delta_theta_prime(E')` = `arctan(E') * (π/2)` with surrogate `E' = m` as in `OctonionicZeta`.

**Fixes vs a common snippet mistake:** do **not** use `c_rindler = 0.4`; that is `γ`, not `γ/2`.

**Not in Lean:** There is **no** theorem that a rational prime `p` factors into `eff` products on shells.
Do not use any “factor_rational_prime” style loop as mathematics — only as rejected folklore.

Run from repo root:
  python3 archive/scripts/hqiv_dynamic_rindler_lattice_demo.py
"""

from __future__ import annotations

import cmath
import math
from typing import Optional, Tuple

# Optional: numpy not required for this file (stdlib `cmath` for zeta phase).
try:
    import numpy as np
except ImportError:
    np = None  # type: ignore

# ─── HQIV scalars (match Lean) ───
GAMMA_HQIV = 2.0 / 5.0
C_RINDLER = GAMMA_HQIV / 2.0  # 1/5 = 0.2  (NOT 0.4)


def eff_corrected(delta: float, m: int) -> float:
    """`effCorrected δ m` — same denominator as `rindlerDenWithDelta δ m`."""
    m = int(m)
    return (m + 1) * (m + 2) / (1.0 + C_RINDLER * m + delta)


def delta_auxiliary_phi_per_shell(
    phi: float,
    t: float,
    beta_cum: float,
    delta_global: float = 0.0,
) -> float:
    """`delta_auxiliary_phi_per_shell`: δ_global + β_cum * (φ·t). Default δ_global=0 for minimal demo."""
    return delta_global + beta_cum * phi * t


def delta_theta_prime_surrogate(m: float) -> float:
    """`delta_theta_prime (m : ℝ)` with E' = m (`OctonionicZeta` / Maxwell tipping)."""
    return math.atan(m) * (math.pi / 2.0)


def next_lattice_prime(
    current_m: int,
    phi: float,
    t: float,
    beta_cum: float = 0.05,
    delta_global: float = 0.0,
    threshold: float = 1.5,
    max_m: int = 1_000_000,
) -> Optional[Tuple[int, float, float]]:
    """
    Smallest m' > current_m with eff(m')/eff(current_m) >= threshold
    (same predicate as Lean `effJumpThresholdPred` / `next_lattice_prime` idea).

    Requires eff(current_m) > 0 (Lean `RindlerDenDeltaPos`); raises if denominator <= 0.
    """
    delta = delta_auxiliary_phi_per_shell(phi, t, beta_cum, delta_global)
    cur = eff_corrected(delta, current_m)
    if cur <= 0:
        raise ValueError("non-positive eff at current_m — denominator sign problem")
    m = current_m + 1
    while m <= max_m:
        e = eff_corrected(delta, m)
        if e >= cur * threshold:
            return m, e, delta
        m += 1
    return None


def zeta_term(
    m: int,
    s: complex,
    phi: float,
    t: float,
    beta_cum: float = 0.05,
    delta_global: float = 0.0,
) -> complex:
    """One shell term: eff^{-s} * exp(i * φ * t * δθ'(m)) — matches `zetaHQIVTerm` shape."""
    delta = delta_auxiliary_phi_per_shell(phi, t, beta_cum, delta_global)
    eff = eff_corrected(delta, m)
    phase = cmath.exp(1j * phi * t * delta_theta_prime_surrogate(float(m)))
    return complex(eff ** (-s)) * phase


def chain_next_shells(
    start_m: int,
    steps: int,
    phi: float,
    t: float,
    beta_cum: float,
    threshold: float = 1.5,
) -> None:
    m = start_m
    print(f"chain from m={m}, φ={phi}, t={t}, β_cum={beta_cum}, threshold={threshold}")
    for i in range(steps):
        nxt = next_lattice_prime(m, phi, t, beta_cum, threshold=threshold)
        if nxt is None:
            print(f"  step {i + 1}: no m' <= max_m")
            return
        m_new, eff_n, delta = nxt
        ratio = eff_n / eff_corrected(delta, m)
        print(
            f"  step {i + 1}: m={m} → m'={m_new}  eff ratio={ratio:.6g}  δ={delta:.6g}  "
            f"fano line (m'%7)+1 = {(m_new % 7) + 1}"
        )
        m = m_new


def main() -> None:
    print("HQIV dynamic Rindler lattice demo (Lean-aligned eff / δ / phase)\n")
    print(f"γ = {GAMMA_HQIV}, c_rindler = γ/2 = {C_RINDLER}\n")

    phi, t = 1.0, 1.0e19
    beta = 0.05
    delta = delta_auxiliary_phi_per_shell(phi, t, beta, 0.0)
    print(f"δ_aux(φ={phi}, t={t}, β_cum={beta}) = {delta:.6g}\n")

    # Huge δ = β·φ·t makes eff tiny (still positive); print in scientific notation.
    for m in (0, 4, 8):
        print(f"eff(δ, m={m}) = {eff_corrected(delta, m):.6e}")

    phi_s, t_s = 1.0, 1.0
    delta_s = delta_auxiliary_phi_per_shell(phi_s, t_s, beta, 0.0)
    print(f"\n(readable scale) δ_aux(φ=1, t=1, β_cum={beta}) = {delta_s}")
    for m in (0, 4, 8):
        print(f"  eff(δ, m={m}) = {eff_corrected(delta_s, m):.6f}")

    print()
    chain_next_shells(0, 4, phi, t, beta)

    print()
    s = complex(2.0, 0.0)
    z = zeta_term(4, s, phi, t, beta)
    print(f"zeta_term example: m=4, s={s}, |term| = {abs(z):.6g}")

    if np is not None:
        zs = zeta_term(4, np.complex128(2.0), phi, t, beta)
        print(f"(numpy complex128 cross-check) |term| = {abs(zs):.6g}")

    print(
        "\nNote: rational-prime 'factorization' via eff products is **not** part of the formal HQIV "
        "proof target; use mod-7 / Fano residue partition for the seven-way zeta split instead."
    )


if __name__ == "__main__":
    main()
