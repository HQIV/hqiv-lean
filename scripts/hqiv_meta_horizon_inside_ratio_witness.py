#!/usr/bin/env python3
"""
Regenerate certified ℚ witnesses for meta-horizon inside-ratio computation.

Emits:
  - `realLogAtIntegerWitness` table (log at integer shells)
  - `nucleusCurvatureTargetWitness` table (A^(1/3) at stable isotope A)
  - inside-ratio spot checks vs Python float spine

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_meta_horizon_inside_ratio_witness.py
"""

from __future__ import annotations

import math
from fractions import Fraction

import hqiv_excited_states as hes

REFERENCE_M = hes.REFERENCE_M
ALPHA = Fraction(3, 5)


def real_log_witness(n: int, *, denom: int = 10**9) -> Fraction:
    if n <= 1:
        return Fraction(0, 1)
    return Fraction(math.log(n)).limit_denominator(denom)


def shell_shape_q(m: int, logs: dict[int, Fraction]) -> Fraction:
    x = m + 1
    return Fraction(1, x) * (1 + ALPHA * logs[x])


def curvature_volume_q(m: int, logs: dict[int, Fraction]) -> Fraction:
    return sum(shell_shape_q(k, logs) for k in range(m + 1))


def inside_ratio_q(m_exc: int, logs: dict[int, Fraction], m_ref: int = REFERENCE_M) -> Fraction:
    return (
        curvature_volume_q(m_exc, logs) / curvature_volume_q(m_ref, logs)
        * Fraction(m_exc + 1, m_ref + 1)
    )


def cube_root_target_witness(a: int, *, denom: int = 10**9) -> Fraction:
    return Fraction(a ** (1.0 / 3.0)).limit_denominator(denom)


def argmin_shell(a: int, logs: dict[int, Fraction]) -> int:
    target = float(a ** (1.0 / 3.0))
    return min(
        range(REFERENCE_M + 8),
        key=lambda m: abs(float(inside_ratio_q(m, logs)) - target),
    )


def emit_lean_log_table(logs: dict[int, Fraction]) -> None:
    print("def realLogAtIntegerWitness : ℕ → ℚ")
    print("  | 0 => 0")
    for n in range(1, 15):
        q = logs[n]
        print(f"  | {n} => {q.numerator} / {q.denominator}")
    print("  | _ => 0")


def emit_lean_target_table(rows: dict[int, Fraction]) -> None:
    print("def nucleusCurvatureTargetWitness : ℕ → ℚ")
    print("  | 0 | 1 => 1")
    for a in sorted(rows):
        q = rows[a]
        print(f"  | {a} => {q.numerator} / {q.denominator}")
    print("  | _ => 1")


def main() -> None:
    logs = {n: real_log_witness(n) for n in range(1, 15)}
    benchmark_a = [4, 7, 9, 11, 12, 14, 16, 19, 23, 35, 56]
    targets = {a: cube_root_target_witness(a) for a in benchmark_a}

    print("# realLogAtIntegerWitness (paste into MetaHorizonInsideRatioComputational.lean)")
    emit_lean_log_table(logs)
    print()
    print("# nucleusCurvatureTargetWitness (paste into AtomNucleusCurvatureShell.lean)")
    emit_lean_target_table(targets)
    print()

    print("# float spine reconciliation")
    for m in range(REFERENCE_M + 8):
        rq = float(inside_ratio_q(m, logs))
        rf = hes.meta_horizon_trapped_inside_ratio(m, REFERENCE_M)
        rel = abs(rq - rf) / max(rf, 1e-30)
        print(f"m={m:2d}  Q/float rel={rel:.3e}  Q={rq:.12f}  float={rf:.12f}")

    print("\n# argmin panel")
    expected = {4: 6, 12: 8, 16: 8, 23: 9, 56: 11}
    for a in sorted(set(benchmark_a) | set(expected)):
        m = argmin_shell(a, logs)
        flag = "OK" if expected.get(a, m) == m else "CHECK"
        print(f"A={a:2d} -> m={m} [{flag}]")


if __name__ == "__main__":
    main()
