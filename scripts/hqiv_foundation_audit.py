#!/usr/bin/env python3
"""
Foundation panel audit: HQIV readouts vs literature witnesses (comparison only).

Runs derived geometry for foundation-tier specs and grades against
``hqiv_lab.foundation_panel`` reference data — never uses references as inputs.

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_foundation_audit.py
  PYTHONPATH=scripts python3 scripts/hqiv_foundation_audit.py --json data/foundation_audit.json
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

import hqiv_phase_geometry_density as pgd
import hqiv_phase_material_response as pmr
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.foundation_panel import (
    PEPTIDE_GEOMETRY_REFERENCES,
    all_condensed_foundation_references,
)
from hqiv_lab.foundation_specs import foundation_spec
from hqiv_lab.spec import resolve_spec

# Map foundation panel names → spec registry keys
_SPEC_KEYS: dict[str, str] = {
    "CH3OH": "CH3OH",
    "C3H8O3": "C3H8O3",
    "C6H12O6_alpha": "C6H12O6_alpha",
    "C12H22O11": "C12H22O11",
    "GlyGly": "GlyGly",
}


def _pct_err(pred: float | None, ref: float | None) -> float | None:
    if pred is None or ref is None or ref == 0:
        return None
    return abs(pred - ref) / ref * 100.0


def audit_condensed_entry(entry: Any) -> dict[str, Any]:
    key = _SPEC_KEYS.get(entry.name)
    if key is None:
        return {
            "name": entry.name,
            "tier": entry.tier,
            "status": "reference_only",
            "hqiv_spec_available": False,
        }
    spec = foundation_spec(key)
    mono = infer_monomer_geometry(spec)
    is_liquid = entry.allotrope == "liquid"
    if is_liquid:
        mat = pmr.material_response_readout(
            spec.name,
            allotrope=None,
            phase="liquid",
            temperature_k=entry.witness_temperature_k,
        )
        pred_rho = mat.get("density_g_cm3")
        pred_n = mat.get("refractive_index")
        pred_t = None
    else:
        geom = pgd.melt_readout_with_phase_geometry(
            spec.name,
            allotrope=entry.allotrope,
            temperature_at_melt_k=entry.witness_temperature_k,
        )
        mat = pmr.material_response_readout(
            spec.name,
            allotrope=entry.allotrope or geom["allotrope"],
            phase="solid",
            temperature_k=entry.witness_temperature_k,
        )
        pred_rho = geom["density_g_cm3"]
        pred_n = mat.get("refractive_index")
        pred_t = geom.get("T_sl_at_pressure_K")

    return {
        "name": entry.name,
        "tier": entry.tier,
        "status": "audited",
        "hqiv_spec_available": True,
        "spec_name": spec.name,
        "monomer_motif": mono.motif.value,
        "intermolecular_contacts": mono.intermolecular_contacts,
        "witness_temperature_K": entry.witness_temperature_k,
        "phase": "liquid" if is_liquid else "solid",
        "hqiv": {
            "density_g_cm3": pred_rho,
            "refractive_index": pred_n,
            "T_sl_K": pred_t,
        },
        "reference": {
            "density_g_cm3": entry.reference_density_g_cm3,
            "refractive_index": entry.reference_refractive_index,
            "melt_K": entry.reference_melt_k,
            "source": entry.reference_source,
        },
        "benchmark": {
            "density_error_pct": _pct_err(pred_rho, entry.reference_density_g_cm3),
            "refractive_index_error_pct": _pct_err(pred_n, entry.reference_refractive_index),
            "T_sl_error_pct": _pct_err(pred_t, entry.reference_melt_k),
        },
    }


def audit_peptide_geometry() -> list[dict[str, Any]]:
    """Compare PROtien/HQIV backbone readout to Engh & Huber witnesses."""
    import os
    import sys

    protein_src = os.environ.get("PROTIEN_SRC")
    if protein_src and protein_src not in sys.path:
        sys.path.insert(0, protein_src)
    try:
        from horizon_physics.proteins.peptide_backbone import backbone_bond_lengths, ramachandran_alpha
    except ImportError:
        default = _REPO_ROOT.parent / "PROtien" / "src"
        if default.is_dir() and str(default) not in sys.path:
            sys.path.insert(0, str(default))
        try:
            from horizon_physics.proteins.peptide_backbone import backbone_bond_lengths, ramachandran_alpha
        except ImportError:
            return [{"status": "skipped", "reason": "PROtien not on PYTHONPATH"}]

    bonds = backbone_bond_lengths()
    phi_a, psi_a = ramachandran_alpha()
    hqiv_map = {
        "N_CA": bonds.get("N_Calpha"),
        "CA_C": bonds.get("Calpha_C"),
        "C_N_peptide": bonds.get("C_N"),
        "C_O": bonds.get("C_O"),
        "phi_alpha": phi_a,
        "psi_alpha": psi_a,
    }
    rows: list[dict[str, Any]] = []
    for ref in PEPTIDE_GEOMETRY_REFERENCES:
        pred = hqiv_map.get(ref.name)
        rows.append(
            {
                "name": ref.name,
                "quantity": ref.quantity,
                "hqiv_value": pred,
                "reference_value": ref.reference_value,
                "unit": ref.unit,
                "error_pct": _pct_err(pred, ref.reference_value),
                "reference_source": ref.reference_source,
            }
        )
    return rows


def build_payload() -> dict[str, Any]:
    condensed = [audit_condensed_entry(e) for e in all_condensed_foundation_references()]
    peptide_geom = audit_peptide_geometry()
    audited = [r for r in condensed if r.get("status") == "audited"]
    rho_errs = [r["benchmark"]["density_error_pct"] for r in audited if r["benchmark"]["density_error_pct"] is not None]
    n_errs = [
        r["benchmark"]["refractive_index_error_pct"]
        for r in audited
        if r["benchmark"]["refractive_index_error_pct"] is not None
    ]
    return {
        "source": "scripts/hqiv_foundation_audit.py",
        "comparison_policy": "Literature witnesses grade HQIV readouts only",
        "condensed": condensed,
        "peptide_geometry": peptide_geom,
        "summary": {
            "condensed_audited": len(audited),
            "condensed_reference_only": len(condensed) - len(audited),
            "mean_density_error_pct": sum(rho_errs) / len(rho_errs) if rho_errs else None,
            "mean_refractive_index_error_pct": sum(n_errs) / len(n_errs) if n_errs else None,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Foundation panel HQIV audit")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO_ROOT / "data" / "foundation_audit.json",
    )
    args = parser.parse_args()
    payload = build_payload()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")
    s = payload["summary"]
    print("HQIV foundation audit (predict vs literature witness)")
    print("=" * 60)
    for row in payload["condensed"]:
        if row.get("status") != "audited":
            print(f"  {row['name']:16s}  reference-only")
            continue
        rho_e = row["benchmark"]["density_error_pct"]
        n_e = row["benchmark"]["refractive_index_error_pct"]
        rho_s = f"{rho_e:.1f}%" if rho_e is not None else "n/a"
        n_s = f"{n_e:.1f}%" if n_e is not None else "n/a"
        print(
            f"  {row['name']:16s}  motif={row['monomer_motif']:14s}  "
            f"|Δρ|={rho_s}  |Δn|={n_s}  ρ={row['hqiv']['density_g_cm3']:.4f}"
        )
    if s["mean_density_error_pct"] is not None:
        print(f"Summary: mean |Δρ|={s['mean_density_error_pct']:.2f}%  audited={s['condensed_audited']}")
    print(f"Wrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
