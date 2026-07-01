#!/usr/bin/env python3
"""
Casimir inner/outer balance pins ξ_lock = 5 — Python mirror of CasimirClosureAction.lean.

  ratio(m) = trapped(m) · ξ(m) · γ / S(m) = 8(m+1)²/5
  V_C(m)   = (ratio(m) − C)² / (2C)     C = 40
  ṁ        = −∂V_C/∂m                    no spring toward 5

Run:
  python3 scripts/hqiv_casimir_closure_action.py
  python3 scripts/hqiv_casimir_closure_action.py --trials 200 --m0-sweep
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass

REFERENCE_M = 4
XI_LOCK = REFERENCE_M + 1
CARRIER = 8
SECTOR_CLOSURE_CAPACITY = 40
GAMMA_HQIV = 2.0 / 5.0


def xi_of_shell(m: float) -> float:
    return m + 1.0


def trapped_energy(m: float) -> float:
    s = (m + 1.0) * (m + 2.0)
    return 4.0 * s * (m + 1.0)


def outer_area(m: float) -> float:
    return (m + 1.0) * (m + 2.0)


def casimir_balance_ratio(m: float) -> float:
    return trapped_energy(m) * xi_of_shell(m) * GAMMA_HQIV / outer_area(m)


def casimir_mismatch(m: float) -> float:
    return casimir_balance_ratio(m) - float(SECTOR_CLOSURE_CAPACITY)


def V_casimir(m: float) -> float:
    d = casimir_mismatch(m)
    return d * d / (2.0 * SECTOR_CLOSURE_CAPACITY)


def dV_casimir_dm(m: float) -> float:
    h = 1e-6
    return (V_casimir(m + h) - V_casimir(m - h)) / (2.0 * h)


@dataclass
class RunSummary:
    m0: float
    m_final: float
    xi_final: float
    settled: bool


def evolve(m0: float, *, steps: int, dt: float, damping: float) -> RunSummary:
    m = float(m0)
    mdot = 0.0
    for _ in range(steps):
        grad = dV_casimir_dm(m)
        mdot = mdot - dt * grad - damping * mdot
        m = max(0.0, min(m + dt * mdot, 12.0))
    return RunSummary(
        m0=m0,
        m_final=m,
        xi_final=xi_of_shell(m),
        settled=abs(m - REFERENCE_M) < 0.35 and abs(xi_of_shell(m) - XI_LOCK) < 0.35,
    )


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--trials", type=int, default=100)
    p.add_argument("--steps", type=int, default=600)
    p.add_argument("--dt", type=float, default=0.05)
    p.add_argument("--damping", type=float, default=0.12)
    p.add_argument("--m0-sweep", action="store_true")
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    print("HQIV Casimir closure (CasimirClosureAction.lean mirror)")
    print(f"  ratio = 8(m+1)²/5,  V_C = (ratio−C)²/(2C),  ξ = m+1")
    print(f"  lock-in: m={REFERENCE_M}, ξ_lock={XI_LOCK}, ratio@4={casimir_balance_ratio(4):.1f}")
    print()

    assert abs(casimir_mismatch(REFERENCE_M)) < 1e-9
    print("# lock-in: casimir mismatch = 0 OK")

    rng = random.Random(args.seed)
    if args.m0_sweep:
        grid = [i * 0.5 for i in range(25)]
        hits = sum(1 for m0 in grid if evolve(m0, steps=args.steps, dt=args.dt, damping=args.damping).settled)
        print(f"m0 sweep {len(grid)} values → {hits}/{len(grid)} settle at m≈{REFERENCE_M}, ξ≈{XI_LOCK}")
        for m0 in [0.0, 2.0, 4.0, 6.0, 8.0]:
            r = evolve(m0, steps=args.steps, dt=args.dt, damping=args.damping)
            print(f"  m0={m0:.1f} → m={r.m_final:.2f}  ξ={r.xi_final:.2f}")
    else:
        results = [evolve(rng.uniform(0, 10), steps=args.steps, dt=args.dt, damping=args.damping) for _ in range(args.trials)]
        near = sum(1 for r in results if r.settled)
        mean_m = sum(r.m_final for r in results) / len(results)
        print(f"trials={args.trials}  settled={near}/{len(results)}  mean m_final={mean_m:.2f}")


if __name__ == "__main__":
    main()
