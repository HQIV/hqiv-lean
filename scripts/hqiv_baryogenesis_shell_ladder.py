#!/usr/bin/env python3
"""Discrete shell-ladder baryogenesis η(m) = Ω_k(m)·δ_E(m) — mirrors BaryogenesisShellLadder."""

from __future__ import annotations

import math

ALPHA = 3 / 5
REFERENCE_M = 4
CURVATURE_NORM = (6**7) * math.sqrt(3)


def shell_shape(m: int) -> float:
    return (1 / (m + 1)) * (1 + ALPHA * math.log(m + 1))


def curvature_integral(n: int) -> float:
    return sum(shell_shape(k) for k in range(n))


def omega_k_partial(m: int) -> float:
    denom = curvature_integral(REFERENCE_M)
    return curvature_integral(m) / denom if denom else 0.0


def delta_e(m: int) -> float:
    return CURVATURE_NORM * shell_shape(m)


def eta_at_shell(m: int) -> float:
    return omega_k_partial(m) * delta_e(m)


def main() -> None:
    print("HQIV shell-ladder baryogenesis η(m) = omegaKPartial(m) * deltaE(m)")
    print(f"referenceM = {REFERENCE_M}, α = {ALPHA}")
    rows = []
    prev = -1.0
    for m in range(REFERENCE_M + 1):
        eta = eta_at_shell(m)
        rows.append((m, omega_k_partial(m), delta_e(m), eta))
        if m > 0:
            assert eta > prev, f"η should climb: η({m - 1})={prev} ≥ η({m})={eta}"
        prev = eta
    print(f"{'m':>3}  {'Ω_k(m)':>12}  {'δ_E(m)':>14}  {'η(m)':>14}")
    for m, ok, de, eta in rows:
        print(f"{m:3d}  {ok:12.6f}  {de:14.6f}  {eta:14.6f}")
    lock = rows[REFERENCE_M]
    print(f"\nlock-in η(4) = δ_E(4) when Ω_k=1: ratio η(4)/δ_E(4) = {lock[3] / lock[2]:.6f}")
    print("strict monotonicity 0 < m₁ < m₂ ≤ 4: OK")


if __name__ == "__main__":
    main()
