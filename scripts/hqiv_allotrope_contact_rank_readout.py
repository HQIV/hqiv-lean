#!/usr/bin/env python3
"""
Contact-network allotrope ranking (periodic image × bond order).

Lean-aligned score (no fitted allotrope tables):

  score = w_c · inc · p · (1 + γ · (4/8) · δ)

with ``p`` the network bond order ``cap/k``, ``inc`` the periodic-image
increment (3D lattice > monolayer), ``δ`` ionic character (0 for homo C),
and ``w_c`` a contact weight (coordination persistence).

Ranks carbon diamond / graphite / carbyne from the same allotrope network
spine as ``hqiv_allotrope_network.py``.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_allotrope_contact_rank_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_allotrope_contact_rank_readout.py \\
    --json-out data/allotrope_contact_rank_audit.json
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

import hqiv_allotrope_network as an
import hqiv_lean_physics_primitives as lean
import hqiv_selection_weights as sw

DEFAULT_JSON = _REPO_ROOT / "data" / "allotrope_contact_rank_audit.json"
STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA


def contact_network_allotrope_score(
    bond_order: float,
    *,
    periodic_increment: float = 1.0,
    contact_weight: float = 1.0,
    ionic_character: float = 0.0,
) -> float:
    """
    ``score = w_c · inc · p · (1 + γ · (4/8) · δ)``.

    Higher is better for ranking condensed allotropes at fixed composition.
    """
    delta = max(0.0, min(1.0, float(ionic_character)))
    return (
        float(contact_weight)
        * float(periodic_increment)
        * float(bond_order)
        * (1.0 + GAMMA * STRONG * delta)
    )


def periodic_increment_for_coordination(coordination: int) -> float:
    """
    Periodic-image increment proxy from coordination dimensionality.

    k=4 (3D diamond) → full lattice images; k=3 (2D sheet) → planar;
    k=2 (1D chain) → line.  Uses HQIV α/γ slots, not fitted dims.
    """
    if coordination >= 4:
        return 1.0 + lean.ALPHA  # 3D periodic
    if coordination == 3:
        return 1.0 + lean.ALPHA * GAMMA  # sheet
    if coordination == 2:
        return 1.0 + lean.ALPHA * GAMMA * STRONG  # chain
    return 1.0


def contact_weight_for_coordination(coordination: int) -> float:
    """Persistence weight ∝ coordination / max spectrum (cap window)."""
    return float(coordination) / 4.0


def rank_element_allotropes(z: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    ionic = sw.bond_ionic_character(z, z)  # 0 for homo
    for ro in an.element_allotropes(z):
        inc = periodic_increment_for_coordination(ro.coordination)
        w = contact_weight_for_coordination(ro.coordination)
        score = contact_network_allotrope_score(
            ro.bond_order,
            periodic_increment=inc,
            contact_weight=w,
            ionic_character=ionic,
        )
        rows.append(
            {
                "element_z": z,
                "name": ro.name,
                "coordination": ro.coordination,
                "bond_order": ro.bond_order,
                "bond_angle_deg": ro.bond_angle_deg,
                "bond_length_angstrom": ro.bond_length_angstrom,
                "periodic_increment": inc,
                "contact_weight": w,
                "ionic_character": ionic,
                "network_score": score,
                "hybridization": ro.hybridization,
            }
        )
    rows.sort(key=lambda r: r["network_score"], reverse=True)
    for i, r in enumerate(rows):
        r["rank"] = i + 1
    return rows


def build_allotrope_contact_rank_audit() -> dict[str, Any]:
    carbon = rank_element_allotropes(6)
    silicon = rank_element_allotropes(14)
    # Diamond (k=4) should outrank graphite (k=3) and carbyne (k=2) on
    # contact-network score (3D periodic × coordination weight).
    c_by_k = {r["coordination"]: r for r in carbon}
    identity = {
        "carbon_has_three": len(carbon) >= 3,
        "diamond_outranks_graphite": (
            c_by_k[4]["network_score"] > c_by_k[3]["network_score"]
        ),
        "graphite_outranks_carbyne": (
            c_by_k[3]["network_score"] > c_by_k[2]["network_score"]
        ),
        "top_is_diamond": carbon[0]["coordination"] == 4,
        "score_positive": all(r["network_score"] > 0 for r in carbon),
        "homo_ionic_zero": all(abs(r["ionic_character"]) < 1e-15 for r in carbon),
    }
    return {
        "source": "scripts/hqiv_allotrope_contact_rank_readout.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.AllotropeNetwork",
            "Hqiv.QuantumChemistry.PhaseElasticity",
        ],
        "formula": {
            "bond_order": "p = cap(Z)/k",
            "network_score": "w_c · inc · p · (1 + γ · (4/8) · δ)",
            "periodic_increment": "1+α (3D), 1+αγ (2D), 1+αγ·(4/8) (1D)",
            "contact_weight": "k/4",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "carbon_ranking": carbon,
        "silicon_ranking": silicon,
        "comparison_policy": "NIST/CRC allotrope names are labels only; scores are derived",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_allotrope_contact_rank_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["carbon_ranking"]:
        print(
            f"  #{r['rank']} k={r['coordination']} {r['name']:28s} "
            f"p={r['bond_order']:.3f}  score={r['network_score']:.4f}"
        )


if __name__ == "__main__":
    main()
