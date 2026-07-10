#!/usr/bin/env python3
"""
Dry-wall spectrum → shared tribo / localDefect factor.

Lean: ``Hqiv.QuantumChemistry.OutsideContactReducedDeltas.dryWallTriboChannel``
      ``Hqiv.QuantumChemistry.VoltageGenerationLedger.triboVoltageChannel``

One wall polarity / coordination spectrum ⇒ one tribo channel
(identity on pristine wall).  Motif comparisons cancel the shared wall.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_wall_tribo_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_wall_tribo_readout.py \\
    --json-out data/wall_tribo_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_lean_physics_primitives as lean
import hqiv_outside_contact_reduced_deltas as ocrd
import hqiv_preferred_axis_dress as pad
import hqiv_voltage_generation_ledger as vgl

DEFAULT_JSON = _REPO_ROOT / "data" / "wall_tribo_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA


def dry_wall_tribo_channel(wall: ocrd.DryWallSpectrum) -> float:
    """Lean ``dryWallTriboChannel``."""
    return vgl.tribo_voltage_channel(wall.spectral_gap, wall.defect_stress)


def wall_row(
    *,
    label: str,
    wall_polarities: tuple[float, ...] = (),
    wall_excess: float = 0.0,
) -> dict[str, Any]:
    wall = ocrd.DryWallSpectrum(
        wall_polarities=wall_polarities,
        wall_coordination_excess=wall_excess,
    )
    tribo = dry_wall_tribo_channel(wall)
    dress = wall.dress
    return {
        "label": label,
        "wall_polarities": list(wall_polarities),
        "wall_coordination_excess": wall_excess,
        "spectral_gap": wall.spectral_gap,
        "defect_stress": wall.defect_stress,
        "dry_wall_dress": dress,
        "tribo_channel": tribo,
        "shared_factor": tribo,  # one wall ⇒ one localDefect/tribo factor
        "formula": "tribo = voltage(g_wall) · localDefect(stress_wall)",
    }


def build_wall_tribo_audit() -> dict[str, Any]:
    # Pristine, unit excess, polarity-gap wall, and a mixed interface.
    rows = [
        wall_row(label="pristine"),
        wall_row(label="unit_excess", wall_excess=1.0),
        wall_row(
            label="polarity_gap",
            wall_polarities=(0.0, 1.0),  # preferred-axis gap from two slots
        ),
        wall_row(
            label="mixed_interface",
            wall_polarities=(0.2, 0.8),
            wall_excess=GAMMA,
        ),
    ]
    pristine = next(r for r in rows if r["label"] == "pristine")
    unit = next(r for r in rows if r["label"] == "unit_excess")
    # Motif ratio with shared wall cancels wall factor.
    ambient = ocrd.DILUTE_AMBIENT
    wall = ocrd.DryWallSpectrum(wall_coordination_excess=0.25)
    motifs = ocrd.carbon_motif_deltas()
    g_red = ocrd.reduced_outside_dress(ambient, wall, motifs["graphene"])
    d_red = ocrd.reduced_outside_dress(ambient, wall, motifs["diamond"])
    g_bare = motifs["graphene"].dress
    d_bare = motifs["diamond"].dress
    identity = {
        "pristine_tribo_one": abs(pristine["tribo_channel"] - 1.0) < 1e-12,
        "pristine_dress_one": abs(pristine["dry_wall_dress"] - 1.0) < 1e-12,
        "unit_excess_dress": abs(unit["dry_wall_dress"] - (1.0 + GAMMA * STRONG))
        < 1e-12,
        "unit_tribo_gt_one": unit["tribo_channel"] > 1.0,
        "motif_ratio_cancels_wall": abs(g_red / d_red - g_bare / d_bare) < 1e-12,
        "gap_nonneg": all(r["spectral_gap"] >= 0.0 for r in rows),
    }
    return {
        "source": "scripts/hqiv_wall_tribo_readout.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.OutsideContactReducedDeltas",
            "Hqiv.QuantumChemistry.VoltageGenerationLedger",
        ],
        "formula": {
            "dry_wall_stress": "max(wall_excess, preferred_axis_gap(polarities))",
            "dry_wall_dress": "localDefect(stress)",
            "tribo": "voltage(clamp(gap)) · localDefect(stress)",
            "shared": "one wall spectrum ⇒ one tribo/localDefect factor",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "carbon_motif_ratio_with_shared_wall": {
            "graphene_over_diamond_reduced": g_red / d_red,
            "graphene_over_diamond_motif_only": g_bare / d_bare,
        },
        "comparison_policy": "no handbook fit; wall is structural spectrum only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_wall_tribo_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        print(
            f"  {r['label']:16} gap={r['spectral_gap']:.4f}  "
            f"dress={r['dry_wall_dress']:.4f}  tribo={r['tribo_channel']:.4f}"
        )


if __name__ == "__main__":
    main()
