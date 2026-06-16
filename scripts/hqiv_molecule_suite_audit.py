#!/usr/bin/env python3
"""
Unified non-quantum molecule suite audit — binding chart + contact networks.

Runs the parameter-free dynamic binding readout and curvature contact network
witness for the core GMTKN55 panel, expanded ionic/polyatomic set, and
open-shell diagnostics. No QAOA / OSH carrier peaking.

Run:
  PYTHONPATH=scripts:. python3 scripts/hqiv_molecule_suite_audit.py
  PYTHONPATH=scripts:. python3 scripts/hqiv_molecule_suite_audit.py --json-out data/molecule_suite_audit.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import hqiv_curvature_contact_network as ccn
import hqiv_dynamic_binding_chart as chart
import hqiv_thermodynamic_phase_from_tp as tptp

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "molecule_suite_audit.json"


def _panel(name: str, benches: tuple[chart.MoleculeBenchmark, ...]) -> dict[str, Any]:
    binding_rows = [chart.dynamic_binding_for_benchmark(b) for b in benches]
    networks = [
        ccn.contact_report(
            ccn.build_network_from_molecule(
                b.name,
                b.fragments,
                b.bonds,
                environment=tptp.ThermodynamicEnvironment.stp(),
            )
        )
        for b in benches
    ]
    summary = chart._summary_stats(binding_rows)
    return {
        "name": name,
        "count": len(benches),
        "molecules": [b.name for b in benches],
        "binding": [chart._molecule_row_dict(b, r) for b, r in zip(benches, binding_rows, strict=True)],
        "networks": networks,
        "summary": summary,
    }


def build_audit_payload() -> dict[str, Any]:
    panels = (
        _panel("core_gmtkn55", chart.GMTKN55_SUITE),
        _panel("expanded", chart.EXPANDED_MOLECULE_SUITE),
        _panel("open_shell", chart.OPEN_SHELL_DIAGNOSTIC_SUITE),
    )
    all_benches = chart.ALL_MOLECULE_BENCHMARKS
    all_binding = [chart.dynamic_binding_for_benchmark(b) for b in all_benches]
    return {
        "program": "hqiv_molecule_suite_audit",
        "parameter_policy": "no_fitted_coefficients",
        "lean_modules": [
            "Hqiv.QuantumChemistry.CurvatureContactNetwork",
            "Hqiv.QuantumChemistry.DynamicBindingChart",
        ],
        "scripts": [
            "scripts/hqiv_dynamic_binding_chart.py",
            "scripts/hqiv_curvature_contact_network.py",
        ],
        "panels": panels,
        "summary": {
            "total_molecules": len(all_benches),
            "core": panels[0]["summary"],
            "expanded": panels[1]["summary"],
            "open_shell": panels[2]["summary"],
            "combined_core_plus_expanded": chart._summary_stats(
                [chart.dynamic_binding_for_benchmark(b) for b in chart.GMTKN55_SUITE + chart.EXPANDED_MOLECULE_SUITE]
            ),
        },
        "all_binding_errors_pct": {r.name: r.error_pct for r in all_binding},
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV molecule suite audit (non-quantum spine)")
    print("=" * 72)
    for panel in payload["panels"]:
        s = panel["summary"]
        print(f"\n[{panel['name']}] n={panel['count']}")
        for row, net in zip(panel["binding"], panel["networks"], strict=True):
            ionic = any(c.get("kind") == "ionic_bond" for c in net["contacts"])
            tag = " ionic" if ionic else ""
            print(
                f"  {row['name']:<6} {row['kind']:<14} "
                f"pred={row['binding_ev']:8.3f} eV  ref={row['reference_ev']:8.3f} eV  "
                f"err={row['error_pct']:+7.2f}%{tag}"
            )
        print(
            f"  mean|err|={s['mean_abs_error_pct']:.2f}%  "
            f"≤5%: {s['within_5pct']}/{s['count']}  "
            f"≤15%: {s['within_15pct']}/{s['count']}"
        )
    cs = payload["summary"]["combined_core_plus_expanded"]
    print(
        f"\nCore+expanded: n={cs['count']}  mean|err|={cs['mean_abs_error_pct']:.2f}%  "
        f"≤15%: {cs['within_15pct']}/{cs['count']}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV non-quantum molecule suite audit")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    payload = build_audit_payload()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print_report(payload)
    print(f"\nWrote {args.json_out}")


if __name__ == "__main__":
    main()
