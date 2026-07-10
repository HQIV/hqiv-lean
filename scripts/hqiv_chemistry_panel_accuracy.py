#!/usr/bin/env python3
"""Public chemistry panel accuracy runner for the light-cone chemistry paper.

Reports final HQIV predictions against quarantined NIST/CRC comparisons on a
wide diatomic / carbon panel.  Laboratory constants never enter the solve.

Usage (from repository root or the paper scripts/ bundle):

  python3 scripts/hqiv_chemistry_panel_accuracy.py
  python3 scripts/hqiv_chemistry_panel_accuracy.py HF CO N2 Cl2
  python3 scripts/hqiv_chemistry_panel_accuracy.py --list
  python3 scripts/hqiv_chemistry_panel_accuracy.py --json-out data/chemistry_panel_accuracy.json

Any name known to the spectroscopy suite (see --list) can be tested, including
molecules not tabulated in the paper.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_graphene_mass_pin as gmp
import hqiv_molecular_spectroscopy as ms
import hqiv_spectral_scale_anchor_feedback as ssa

DEFAULT_JSON = _REPO_ROOT / "data" / "chemistry_panel_accuracy.json"
PAPER_SPECTRAL_PANEL = ("LiH", "HF", "LiF", "HCl", "CO", "N2", "O2", "F2", "Cl2")


def _fmt(x: float | None, digits: int = 4) -> str:
    if x is None or not math.isfinite(float(x)):
        return "—"
    return f"{float(x):.{digits}f}"


def _fmt_pct(x: float | None) -> str:
    if x is None:
        return "—"
    return f"{x:+.2f}%"


def list_available_molecules() -> list[str]:
    suite = {b.name for b in ms.diatomic_benchmarks()}
    return sorted(set(ms.NIST_COMPARISON) | suite)


def spectral_accuracy_rows(names: tuple[str, ...] | None) -> dict[str, Any]:
    payload = ssa.build_payload(names)
    rows_out: list[dict[str, Any]] = []
    for row in payload["rows"]:
        cq = row["comparison_quarantine"]
        out = row["unpinned_outputs"]
        ref = ms.NIST_COMPARISON.get(row["name"], {})
        rows_out.append(
            {
                "name": row["name"],
                "geometry_reliable": row["geometry_reliable"],
                "r_e_angstrom": out["r_e_angstrom"],
                "r_e_nist_angstrom": ref.get("r_e"),
                "r_e_error_pct": cq.get("r_e_error_pct_anchor"),
                "D_e_ev": out["D_e_ev_inverse_length_proxy"],
                "D_e_nist_ev": ref.get("D_e"),
                "D_e_error_pct": cq.get("D_e_error_pct_anchor"),
                "B_e_cm1": out["B_e_cm1"],
                "B_e_nist_cm1": ref.get("B_e"),
                "B_e_error_pct": cq.get("B_e_error_pct_anchor"),
            }
        )
    reliable = [r for r in rows_out if r["geometry_reliable"]]
    geo = payload["summary"]["geometric_error_reliable_geometry"]
    return {
        "panel": "spectral_scale_anchor",
        "count": len(rows_out),
        "reliable_count": len(reliable),
        "geometric_mean_error_pct": {
            "r_e": geo["r_e"]["geometric_mean_error_pct_anchor"],
            "D_e": geo["D_e"]["geometric_mean_error_pct_anchor"],
            "B_e": geo["B_e"]["geometric_mean_error_pct_anchor"],
        },
        "rows": rows_out,
        "comparison_policy": (
            "NIST/CRC constants are comparison quarantine only; omega_e may be used "
            "as an in-situ spectral scale pin"
        ),
    }


def carbon_accuracy_rows() -> dict[str, Any]:
    payload = gmp.build_payload(mass_mode="known_12", use_inert_core=True, em_feedback=True)
    rows_out: list[dict[str, Any]] = []
    for row in payload["rows"]:
        if row["coordination"] not in (3, 4):
            continue
        cq = row.get("comparison_quarantine") or {}
        if row["coordination"] == 3:
            rows_out.append(
                {
                    "name": "graphene",
                    "quantity": "areal_density_mg_m2",
                    "pred": row["areal_density_mg_m2"],
                    "nist": cq.get("areal_density_mg_m2"),
                    "error_pct": cq.get("areal_density_error_pct"),
                    "bond_angstrom": row["bond_length_angstrom"],
                    "bond_nist_angstrom": cq.get("bond_angstrom"),
                    "bond_error_pct": cq.get("bond_error_pct"),
                }
            )
        else:
            rows_out.append(
                {
                    "name": "diamond",
                    "quantity": "volumetric_density_g_cm3",
                    "pred": row["volumetric_density_g_cm3"],
                    "nist": cq.get("density_g_cm3"),
                    "error_pct": cq.get("density_error_pct"),
                    "bond_angstrom": row["bond_length_angstrom"],
                    "bond_nist_angstrom": cq.get("bond_angstrom"),
                    "bond_error_pct": cq.get("bond_error_pct"),
                }
            )
    return {
        "panel": "carbon_network_packing",
        "count": len(rows_out),
        "rows": rows_out,
        "comparison_policy": (
            "CRC/NIST bond lengths and densities are comparison quarantine only"
        ),
    }


def build_payload(names: tuple[str, ...] | None = None) -> dict[str, Any]:
    spectral_names = names if names else PAPER_SPECTRAL_PANEL
    return {
        "source": "scripts/hqiv_chemistry_panel_accuracy.py",
        "role": (
            "Public accuracy panel for the light-cone chemistry paper: final "
            "predictions vs quarantined laboratory comparisons"
        ),
        "spectral": spectral_accuracy_rows(tuple(spectral_names)),
        "carbon": carbon_accuracy_rows(),
    }


def print_report(payload: dict[str, Any]) -> None:
    spectral = payload["spectral"]
    print("=== HQIV chemistry panel accuracy ===")
    print(
        "Laboratory constants are comparison quarantine only "
        "(never derivation inputs)."
    )
    print()
    print(
        f"-- Spectral panel ({spectral['reliable_count']}/{spectral['count']} "
        "geometry-reliable)"
    )
    geo = spectral["geometric_mean_error_pct"]
    print(
        "   geometric-mean |error|: "
        f"r_e {geo['r_e']:.2f}%  "
        f"D_e {geo['D_e']:.2f}%  "
        f"B_e {geo['B_e']:.2f}%"
    )
    print(
        f"{'name':<6} {'r_e':>8} {'NIST':>8} {'err%':>8} "
        f"{'D_e':>8} {'NIST':>8} {'err%':>8} "
        f"{'B_e':>8} {'NIST':>8} {'err%':>8}"
    )
    for row in spectral["rows"]:
        flag = "" if row["geometry_reliable"] else " *"
        print(
            f"{row['name']:<6}{_fmt(row['r_e_angstrom']):>8}"
            f"{_fmt(row['r_e_nist_angstrom']):>8}"
            f"{_fmt_pct(row['r_e_error_pct']):>8} "
            f"{_fmt(row['D_e_ev'], 3):>8}"
            f"{_fmt(row['D_e_nist_ev'], 3):>8}"
            f"{_fmt_pct(row['D_e_error_pct']):>8} "
            f"{_fmt(row['B_e_cm1'], 3):>8}"
            f"{_fmt(row['B_e_nist_cm1'], 3):>8}"
            f"{_fmt_pct(row['B_e_error_pct']):>8}{flag}"
        )
    print()
    carbon = payload["carbon"]
    print("-- Carbon network packing")
    print(
        f"{'motif':<10} {'quantity':<22} {'pred':>10} {'NIST':>10} {'err%':>8} "
        f"{'r (Å)':>8} {'err%':>8}"
    )
    for row in carbon["rows"]:
        print(
            f"{row['name']:<10}{row['quantity']:<22}"
            f"{_fmt(row['pred'], 4):>10}"
            f"{_fmt(row['nist'], 4):>10}"
            f"{_fmt_pct(row['error_pct']):>8} "
            f"{_fmt(row['bond_angstrom']):>8}"
            f"{_fmt_pct(row['bond_error_pct']):>8}"
        )
    print()
    print(
        "Tip: pass molecule names to test cases beyond the paper panel, e.g. "
        "`python3 hqiv_chemistry_panel_accuracy.py HF CO NaCl`."
    )
    print("Use --list to see available spectroscopy names.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Public HQIV chemistry panel accuracy: final predictions vs "
            "quarantined NIST/CRC comparisons."
        )
    )
    parser.add_argument(
        "names",
        nargs="*",
        help="Optional diatomic subset (default: paper spectral panel)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List available spectroscopy molecule names and exit",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help=f"Optional JSON path (default when writing: {DEFAULT_JSON})",
    )
    parser.add_argument(
        "--write-default",
        action="store_true",
        help=f"Write JSON to {DEFAULT_JSON}",
    )
    args = parser.parse_args()

    if args.list:
        for name in list_available_molecules():
            print(name)
        return

    suite = {b.name for b in ms.diatomic_benchmarks()}
    unknown = [n for n in args.names if n not in suite and n not in ms.NIST_COMPARISON]
    if unknown:
        print(
            "Unknown molecule name(s): "
            + ", ".join(unknown)
            + "\nUse --list for available names.",
            file=sys.stderr,
        )
        sys.exit(2)

    payload = build_payload(tuple(args.names) or None)
    print_report(payload)

    out = args.json_out
    if args.write_default and out is None:
        out = DEFAULT_JSON
    if out is not None:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
