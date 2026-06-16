#!/usr/bin/env python3
"""
Condensed-phase trace audit: geometry → ρ → n → κ₆ @ species melt temperature.

Exports ``data/hqiv_lab_witnesses.json`` for paper tables and bundle sync.
Validates Compton-triplet contact ξ, motif contacts, and NIST panel gaps.

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_condensed_phase_audit.py
  PYTHONPATH=scripts python3 scripts/hqiv_condensed_phase_audit.py --json data/hqiv_lab_witnesses.json
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
import hqiv_lean_physics_primitives as lean
import hqiv_phase_geometry_density as pgd
import hqiv_phase_material_response as pmr
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.packing import (
    neighbor_covalent_lapse_overlap_factor,
    halogen_strong_hbond_leg_factor,
    linear_chain_zigzag_lattice_open_factor,
)
from hqiv_lab.spec import MoleculeSpec
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL, panel_entry

# H₂ uses (1,1,1); all panel species use chemistry Compton triplet (4,3,1).
_EXPECTED_XI = lean.xi_from_compton_triplet((4, 3, 1))


def _chart_row(name: str):
    for row in chart.GMTKN55_SUITE:
        if row.name.upper() == name.upper():
            return row
    raise KeyError(name)


def audit_species(entry: Any) -> dict[str, Any]:
    spec = MoleculeSpec.from_chart_name(entry.molecule)
    mono = infer_monomer_geometry(spec)
    chart_row = _chart_row(entry.molecule)
    compton_triplet = chart.chemistry_compton_triplet(chart_row)
    geom = pgd.melt_readout_with_phase_geometry(
        entry.molecule,
        allotrope=entry.allotrope,
        temperature_at_melt_k=entry.witness_temperature_k,
    )
    mat = pmr.material_response_readout(
        entry.molecule,
        allotrope=entry.allotrope,
        phase="solid",
        temperature_k=entry.witness_temperature_k,
    )
    rho_err_pct = abs(geom["density_g_cm3"] - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 * 100.0
    n_err_pct = abs(mat["refractive_index"] - entry.nist_refractive_index) / entry.nist_refractive_index * 100.0
    t_sl_err_pct = abs(geom["T_sl_at_pressure_K"] - entry.nist_melt_k) / entry.nist_melt_k * 100.0
    xi = geom["contact_xi"]
    trace_ok = abs(xi - _EXPECTED_XI) < 1e-9 and abs(mat["contact_xi"] - xi) < 1e-9
    return {
        "molecule": entry.molecule,
        "motif_label": entry.motif_label,
        "allotrope": entry.allotrope,
        "witness_temperature_K": entry.witness_temperature_k,
        "gmtkn55_compton_triplet": list(compton_triplet),
        "contact_xi": xi,
        "intermolecular_contacts": mono.intermolecular_contacts,
        "monomer_motif": mono.motif.value,
        "geometry": {
            "density_g_cm3": geom["density_g_cm3"],
            "curvature_density_fraction": geom["curvature_density_fraction"],
            "phase_curvature_density_fraction": geom["phase_curvature_density_fraction"],
            "kappa6_feedback": geom["kappa6_feedback"],
            "T_sl_at_pressure_K": geom["T_sl_at_pressure_K"],
            "refractive_index_solid": geom["refractive_index_solid"],
            "neighbor_lapse_overlap_factor": neighbor_covalent_lapse_overlap_factor(mono),
            "halogen_strong_hbond_leg_factor": halogen_strong_hbond_leg_factor(mono),
            "linear_chain_zigzag_lattice_open_factor": linear_chain_zigzag_lattice_open_factor(
                mono
            ),
        },
        "material_response": {
            "refractive_index": mat["refractive_index"],
            "thermal_conductivity_W_mK": mat["thermal_conductivity_W_mK"],
            "molar_heat_capacity_J_per_mol_K": mat["molar_heat_capacity_J_per_mol_K"],
            "optical_phase_eta": mat["optical_phase_eta"],
            "optical_geff": mat["optical_geff"],
            "B_hom": mat["B_hom"],
        },
        "nist_reference": {
            "solid_density_g_cm3": entry.nist_solid_density_g_cm3,
            "refractive_index": entry.nist_refractive_index,
            "melt_K": entry.nist_melt_k,
        },
        "benchmark": {
            "density_error_pct": rho_err_pct,
            "refractive_index_error_pct": n_err_pct,
            "T_sl_error_pct": t_sl_err_pct,
            "contact_xi_trace_consistent": trace_ok,
        },
    }


def build_payload() -> dict[str, Any]:
    rows = [audit_species(e) for e in CONDENSED_SPECIES_PANEL]
    rho_errs = [r["benchmark"]["density_error_pct"] for r in rows]
    n_errs = [r["benchmark"]["refractive_index_error_pct"] for r in rows]
    t_errs = [r["benchmark"]["T_sl_error_pct"] for r in rows]
    return {
        "source": "scripts/hqiv_condensed_phase_audit.py",
        "comparison_policy": "NIST/CRC values used for benchmark only, not HQIV fit",
        "expected_contact_xi_compton_431": _EXPECTED_XI,
        "species": rows,
        "summary": {
            "mean_density_error_pct_vs_nist": sum(rho_errs) / len(rho_errs),
            "mean_refractive_index_error_pct_vs_nist": sum(n_errs) / len(n_errs),
            "mean_T_sl_error_pct_vs_nist": sum(t_errs) / len(t_errs),
            "all_contact_xi_traces_consistent": all(
                r["benchmark"]["contact_xi_trace_consistent"] for r in rows
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Condensed-phase trace audit → JSON witness.")
    parser.add_argument(
        "--json",
        type=Path,
        default=_REPO_ROOT / "data" / "hqiv_lab_witnesses.json",
    )
    args = parser.parse_args()
    payload = build_payload()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")
    s = payload["summary"]
    print("HQIV condensed-phase trace audit")
    print("=" * 60)
    for row in payload["species"]:
        b = row["benchmark"]
        g = row["geometry"]
        m = row["material_response"]
        print(
            f"{row['molecule']:4} @ {row['witness_temperature_K']:6.1f} K  "
            f"ρ={g['density_g_cm3']:.4f}  n={m['refractive_index']:.4f}  "
            f"T_sl={g['T_sl_at_pressure_K']:.2f}  "
            f"|Δρ|={b['density_error_pct']:.2f}%  ξ={row['contact_xi']:.4f}"
        )
    print(
        f"\nSummary: mean |Δρ|={s['mean_density_error_pct_vs_nist']:.2f}%  "
        f"mean |Δn|={s['mean_refractive_index_error_pct_vs_nist']:.2f}%  "
        f"mean |ΔT_sl|={s['mean_T_sl_error_pct_vs_nist']:.2f}%  "
        f"ξ trace OK={s['all_contact_xi_traces_consistent']}"
    )
    print(f"Wrote {args.json}")


if __name__ == "__main__":
    main()
