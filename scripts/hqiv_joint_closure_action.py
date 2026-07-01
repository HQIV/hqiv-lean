#!/usr/bin/env python3
"""
Joint shell + Casimir closure — Python mirror of JointClosureAction.lean.

  V_joint(m) = V_budget(m) + V_Casimir(m)
  both share lock-in drive; ξ = m+1 tracked alongside m.

Optional: reuse hopf carrier from hqiv_hopf_delta_action.py (import as module).

Run:
  python3 scripts/hqiv_joint_closure_action.py
  python3 scripts/hqiv_joint_closure_action.py --trials 150 --with-carrier
"""

from __future__ import annotations

import argparse
import random
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from hqiv_hopf_delta_action import (  # noqa: E402
    REFERENCE_M,
    SECTOR_CLOSURE_CAPACITY,
    CARRIER,
    V_budget,
    dV_budget_dm,
    build_g2_delta_basis,
    evolve_action,
    ActionCoeffs,
    random_unit_octonion,
)

from hqiv_casimir_closure_action import (  # noqa: E402
    V_casimir,
    dV_casimir_dm,
    xi_of_shell,
    XI_LOCK,
)


def V_joint(m: float) -> float:
    return V_budget(m) + V_casimir(m)


def dV_joint_dm(m: float) -> float:
    return dV_budget_dm(m) + dV_casimir_dm(m)


@dataclass
class ScalarSummary:
    m0: float
    m_final: float
    xi_final: float
    V_joint_final: float
    settled: bool


def evolve_scalar(m0: float, *, steps: int, dt: float, damping: float) -> ScalarSummary:
    m = float(m0)
    mdot = 0.0
    for _ in range(steps):
        grad = dV_joint_dm(m)
        mdot = mdot - dt * grad - damping * mdot
        m = max(0.0, min(m + dt * mdot, 12.0))
    return ScalarSummary(
        m0=m0,
        m_final=m,
        xi_final=xi_of_shell(m),
        V_joint_final=V_joint(m),
        settled=abs(m - REFERENCE_M) < 0.35,
    )


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--trials", type=int, default=100)
    p.add_argument("--steps", type=int, default=600)
    p.add_argument("--dt", type=float, default=0.05)
    p.add_argument("--damping", type=float, default=0.12)
    p.add_argument("--with-carrier", action="store_true")
    p.add_argument("--seed", type=int, default=1)
    args = p.parse_args()

    print("HQIV joint closure (JointClosureAction.lean mirror)")
    print(f"  V_joint = V_budget + V_Casimir,  N(m)={CARRIER}(m+1),  C={SECTOR_CLOSURE_CAPACITY}")
    print(f"  lock-in m={REFERENCE_M}, ξ_lock={XI_LOCK}")
    print(f"  V_joint({REFERENCE_M}) = {V_joint(REFERENCE_M):.6f}")
    print()

    rng = random.Random(args.seed)
    results = [evolve_scalar(rng.uniform(0, 10), steps=args.steps, dt=args.dt, damping=args.damping) for _ in range(args.trials)]
    near = sum(1 for r in results if r.settled)
    mean_m = sum(r.m_final for r in results) / len(results)
    print(f"scalar trials={args.trials}  settled={near}/{len(results)}  mean m={mean_m:.2f}")

    if args.with_carrier:
        g2, delta = build_g2_delta_basis()
        coeffs = ActionCoeffs()
        carrier_hits = 0
        for _ in range(min(args.trials, 80)):
            v0 = random_unit_octonion(rng)
            m0 = rng.uniform(0.0, 9.0)
            tr = evolve_action(
                v0, m0, g2, delta, coeffs,
                steps=args.steps, dt=args.dt, first_order=True, closure_only_shell=True,
            )
            if tr.settled_near_lockin:
                carrier_hits += 1
        print(f"carrier+closure trials={min(args.trials, 80)}  settled≈{REFERENCE_M}: {carrier_hits}")


if __name__ == "__main__":
    main()
