#!/usr/bin/env python3
"""
HQIV dynamic BBN + baryogenesis runner (Lean-aligned primitives).

Uses ``hqiv_lean_physics_primitives`` for ωK(ξ), Casimir scale, η laws, and
shell reaction opportunity.  For the full bulk+BBN integrator see
``hqiv_dynamic_bulk_bbn.py``.

Run:
  python3 scripts/hqiv_dynamic_bbn_baryogenesis.py
  python3 scripts/hqiv_dynamic_bulk_bbn.py
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import hqiv_dynamic_bulk_bbn as bulk
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "bbn_witnesses_dynamic.json"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--h0", type=float, default=bulk.DEFAULT_H0_KM_S_MPC)
    parser.add_argument("--network-steps", type=int, default=400)
    parser.add_argument("--out", type=Path, default=OUT)
    args = parser.parse_args()

    payload = bulk.build_payload(args.h0, args.network_steps)
    witness = {
        "source": "HQIV dynamic BBN + baryogenesis (Lean-aligned via hqiv_lean_physics_primitives)",
        "lean_modules": [
            "Hqiv.Physics.DynamicBBNBaryogenesis",
            "Hqiv.Physics.BBNEpochNetwork",
            "Hqiv.Physics.BaryogenesisWitness",
            "Hqiv.Physics.HopfShellBeltramiMassBridge",
        ],
        "eta_paper": lean.ETA_PAPER,
        "eta_lean_curvature": payload["eta_from_lean_curvature_laws"],
        "eta_from_dynamic_bulk": payload["eta_from_dynamic_bulk"],
        "dynamic_bbn": payload["dynamic_bbn"],
        "legacy_comparison": payload["legacy_eta_comparison"],
        "note": "Primary pipeline: hqiv_dynamic_bulk_bbn.py",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(witness, indent=2) + "\n")
    print(f"Wrote {args.out}")
    print(json.dumps(witness["eta_from_dynamic_bulk"], indent=2))
    print(json.dumps(witness["dynamic_bbn"]["cooling_network"], indent=2))


if __name__ == "__main__":
    main()
