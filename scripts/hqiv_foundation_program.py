#!/usr/bin/env python3
"""
Foundation validation program — full ladder audit (Lean-aligned spine).

Runs tier-0 binding + condensed witnesses, tier-1+ foundation audit, and
exports reference catalog.  Literature values grade readouts only.

Usage:
  PYTHONPATH=scripts:. python3 scripts/hqiv_foundation_program.py
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent


def _run(module: str, *args: str) -> None:
    env = {**dict(__import__("os").environ), "PYTHONPATH": f"scripts:{_REPO_ROOT}"}
    subprocess.run([sys.executable, str(_SCRIPT_DIR / module), *args], check=True, env=env)


def main() -> int:
    parser = argparse.ArgumentParser(description="HQIV foundation validation program")
    parser.add_argument("--skip-binding", action="store_true")
    parser.add_argument("--skip-tier0-condensed", action="store_true")
    parser.add_argument("--protein-path", type=Path, default=None, help="PROtien src for peptide geometry")
    args = parser.parse_args()

    print("HQIV foundation program")
    print("=" * 60)
    print("Policy: Lean-derived readouts; NIST/COD witnesses for comparison only")
    print()

    _run("hqiv_foundation_references.py")
    if not args.skip_binding:
        print()
        _run("hqiv_dynamic_binding_chart.py")
    if not args.skip_tier0_condensed:
        print()
        _run("hqiv_condensed_phase_audit.py")
    print()
    _run("hqiv_foundation_audit.py")
    print()
    _run("hqiv_miniprotein_fold_audit.py")

    if args.protein_path is not None:
        env = {**dict(__import__("os").environ), "PYTHONPATH": str(args.protein_path)}
        print()
        print("Peptide fold foundation (PROtien)")
        subprocess.run(
            [
                sys.executable,
                "-m",
                "horizon_physics.proteins.examples.run_fold_tests",
                "--targets",
                "gg,ace_ala_nme",
                "--method",
                "radical",
            ],
            check=False,
            env=env,
            cwd=args.protein_path.parent,
        )

    audit = json.loads((_REPO_ROOT / "data" / "foundation_audit.json").read_text())
    s = audit["summary"]
    print()
    print("Foundation program summary")
    print(f"  Condensed audited: {s['condensed_audited']}")
    if s.get("mean_density_error_pct") is not None:
        print(f"  Mean |Δρ|: {s['mean_density_error_pct']:.2f}%")
    print(f"  Artifacts: data/foundation_references.json, data/foundation_audit.json")
    fold_path = _REPO_ROOT / "data" / "miniprotein_fold_audit.json"
    if fold_path.is_file():
        fold = json.loads(fold_path.read_text())
        fs = fold["summary"]
        print(f"  Miniprotein fold: mean Cα RMSD={fs['mean_ca_rmsd_angstrom']:.2f} Å  passed={fs['passed']}/{fs['targets']}")
        print(f"  Artifacts: data/miniprotein_witnesses.json, data/miniprotein_fold_audit.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
