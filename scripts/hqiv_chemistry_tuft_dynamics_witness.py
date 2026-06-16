#!/usr/bin/env python3
"""
Export nested-WF bond geometry witnesses (derived Å/° vs tabulated comparison).

Run:
  python3 scripts/hqiv_chemistry_tuft_dynamics_witness.py
  python3 scripts/hqiv_chemistry_tuft_dynamics_witness.py --json-out data/nested_wf_geometry.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_dynamic_binding_chart as chart
import hqiv_nested_wf_bond_geometry as nwbg

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "nested_wf_geometry.json"


def build_payload() -> dict:
    ref_lengths = {
        b.name.upper(): list(chart.reference_bond_lengths_angstrom(b))
        for b in chart.ALL_MOLECULE_BENCHMARKS
    }
    names = tuple(k for k in ref_lengths if k in nwbg._BENCHMARK_TOPOLOGY)
    rows = nwbg.geometry_witness_table(names, reference_lengths={k: tuple(v) for k, v in ref_lengths.items()})
    abs_err = [abs(r["error_pct"]) for r in rows if r.get("error_pct") is not None]
    return {
        "source": "scripts/hqiv_chemistry_tuft_dynamics_witness.py",
        "parameter_policy": "no_tabulated_angstrom_or_degrees_as_inputs",
        "lean_modules": [
            "Hqiv.QuantumChemistry.CentreGeometryFromTuft",
            "Hqiv.QuantumChemistry.ChemistryBindingRoutes",
            "Hqiv.Physics.DynamicCentreGeometry",
        ],
        "constants": {
            "informational_monogamy_length_factor": ctd.INFORMATIONAL_MONOGAMY_LENGTH_FACTOR,
            "bohr_radius_angstrom": ctd.BOHR_RADIUS_ANGSTROM,
        },
        "bond_witness": rows,
        "summary": {
            "count": len(abs_err),
            "mean_abs_error_pct": sum(abs_err) / len(abs_err) if abs_err else 0.0,
            "max_abs_error_pct": max(abs_err) if abs_err else 0.0,
            "within_5pct": sum(1 for e in abs_err if e <= 5.0),
            "within_15pct": sum(1 for e in abs_err if e <= 15.0),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Nested-WF geometry witness exporter")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    s = payload["summary"]
    print(f"Wrote {args.json_out}")
    print(
        f"bonds={s['count']} mean|err|={s['mean_abs_error_pct']:.2f}% "
        f"≤5%={s['within_5pct']}/{s['count']}"
    )


if __name__ == "__main__":
    main()
