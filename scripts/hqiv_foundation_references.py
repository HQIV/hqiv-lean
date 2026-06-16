#!/usr/bin/env python3
"""
Export foundation validation reference witnesses (sugars, polyols, peptides).

External literature values are **comparison only** — never imported by HQIV builders.

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_foundation_references.py
  PYTHONPATH=scripts python3 scripts/hqiv_foundation_references.py --json data/foundation_references.json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_dynamic_binding_chart as chart
from hqiv_lab.foundation_panel import (
    PEPTIDE_FOLD_REFERENCES,
    PEPTIDE_GEOMETRY_REFERENCES,
    POLYOL_FOUNDATION_REFERENCES,
    SUGAR_FOUNDATION_REFERENCES,
    PEPTIDE_CRYSTAL_REFERENCES,
    ComparisonPolicy,
)
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL


def _binding_tier() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for bench in chart.GMTKN55_SUITE:
        rows.append(
            {
                "name": bench.name,
                "kind": bench.kind,
                "reference_binding_ev": bench.reference_ev,
                "reference_source": bench.reference_source,
                "hqiv_spec_available": True,
            }
        )
    return rows


def _condensed_tier0() -> list[dict[str, Any]]:
    return [
        {
            "name": e.molecule,
            "allotrope": e.allotrope,
            "motif_label": e.motif_label,
            "witness_temperature_k": e.witness_temperature_k,
            "reference_density_g_cm3": e.nist_solid_density_g_cm3,
            "reference_refractive_index": e.nist_refractive_index,
            "reference_melt_k": e.nist_melt_k,
            "reference_source": "NIST/CRC condensed panel",
            "hqiv_spec_available": True,
        }
        for e in CONDENSED_SPECIES_PANEL
    ]


def _condensed_rows(entries: tuple[Any, ...]) -> list[dict[str, Any]]:
    return [asdict(e) for e in entries]


def build_payload() -> dict[str, Any]:
    polyols = _condensed_rows(POLYOL_FOUNDATION_REFERENCES)
    sugars = _condensed_rows(SUGAR_FOUNDATION_REFERENCES)
    peptide_crystal = _condensed_rows(PEPTIDE_CRYSTAL_REFERENCES)
    pending_audit = sum(
        1
        for row in polyols + sugars + peptide_crystal
        if not row.get("hqiv_spec_available")
    )
    return {
        "source": "scripts/hqiv_foundation_references.py",
        "comparison_policy": ComparisonPolicy,
        "builder_policy": (
            "HQIV geometry/binding/packing/folding modules must not read reference_* "
            "fields from this file as inputs or fit targets"
        ),
        "tiers": {
            "tier0_binding": _binding_tier(),
            "tier0_condensed": _condensed_tier0(),
            "tier1_polyols": polyols,
            "tier1_sugars": sugars,
            "tier2_peptide_crystal": peptide_crystal,
            "tier2_peptide_geometry": [asdict(r) for r in PEPTIDE_GEOMETRY_REFERENCES],
            "tier3_peptide_fold": [asdict(r) for r in PEPTIDE_FOLD_REFERENCES],
        },
        "summary": {
            "tier0_binding_count": len(chart.GMTKN55_SUITE),
            "tier0_condensed_count": len(CONDENSED_SPECIES_PANEL),
            "tier1_polyol_count": len(POLYOL_FOUNDATION_REFERENCES),
            "tier1_sugar_count": len(SUGAR_FOUNDATION_REFERENCES),
            "tier2_peptide_crystal_count": len(PEPTIDE_CRYSTAL_REFERENCES),
            "tier2_peptide_geometry_count": len(PEPTIDE_GEOMETRY_REFERENCES),
            "tier3_peptide_fold_count": len(PEPTIDE_FOLD_REFERENCES),
            "reference_only_condensed_pending_spec": pending_audit,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Export foundation reference witnesses")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO_ROOT / "data" / "foundation_references.json",
        help="Output JSON path",
    )
    args = parser.parse_args()
    payload = build_payload()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")
    s = payload["summary"]
    print("HQIV foundation reference witnesses")
    print("=" * 60)
    print(f"Policy: {payload['comparison_policy']}")
    print(
        f"Tier 0: {s['tier0_binding_count']} binding + {s['tier0_condensed_count']} condensed"
    )
    print(
        f"Tier 1: {s['tier1_polyol_count']} polyols + {s['tier1_sugar_count']} sugars "
        f"({s['reference_only_condensed_pending_spec']} pending MoleculeSpec)"
    )
    print(
        f"Tier 2: {s['tier2_peptide_crystal_count']} peptide crystal + "
        f"{s['tier2_peptide_geometry_count']} geometry refs"
    )
    print(f"Tier 3: {s['tier3_peptide_fold_count']} peptide fold targets")
    print(f"Wrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
