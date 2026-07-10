#!/usr/bin/env python3
"""
Audit two-way feedback candidates in the chemistry/material stack.

The goal is to separate:

* loops that should be promoted into live dynamics;
* shared ambient factors that should cancel in comparisons;
* diagnostic-only probes that should not become fits yet.

This is not a fitting script.  It records structural dependencies and, where the
current witness gives a numerical sanity check, the before/after effect.
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

import hqiv_graphene_mass_pin as gmp
import hqiv_phase_material_feedback_fixed_point as pmff
import hqiv_spectral_residual_audit as sra
import hqiv_spectral_scale_anchor_feedback as ssaf

DEFAULT_JSON = _REPO_ROOT / "data" / "two_way_feedback_audit.json"


def _pct_improvement(old_abs_pct: float, new_abs_pct: float) -> float:
    """Relative reduction in absolute error."""
    if old_abs_pct <= 0:
        return 0.0
    return 100.0 * (old_abs_pct - new_abs_pct) / old_abs_pct


def carbon_em_density_witness() -> dict[str, Any]:
    """Current numerical evidence for mass-anchor + EM length feedback."""
    live = gmp.build_payload(em_feedback=True)
    frozen = gmp.build_payload(em_feedback=False)

    def row(payload: dict[str, Any], name: str) -> dict[str, Any]:
        return next(r for r in payload["rows"] if r["name"].startswith(name))

    gr_live = row(live, "graphene")
    gr_frozen = row(frozen, "graphene")
    dia_live = row(live, "diamond")
    dia_frozen = row(frozen, "diamond")

    gr_old = abs(gr_frozen["comparison_quarantine"]["areal_density_error_pct"])
    gr_new = abs(gr_live["comparison_quarantine"]["areal_density_error_pct"])
    dia_old = abs(dia_frozen["comparison_quarantine"]["density_error_pct"])
    dia_new = abs(dia_live["comparison_quarantine"]["density_error_pct"])

    return {
        "loop": "EM/BE dress -> contact length -> mass-density packing",
        "lean": [
            "OutsideContactReducedDeltas.contactLengthFromEmFeedback",
            "OutsideContactReducedDeltas.volumetricDensityWithEmFeedback",
            "OutsideContactReducedDeltas.arealDensityWithEmFeedback",
        ],
        "python": ["scripts/hqiv_graphene_mass_pin.py"],
        "status": "promote-live",
        "reason": (
            "Mass is an in-situ scale anchor, not a freeze. The EM/BE channel "
            "feeds back into r via r_eff = r_bare · em^α · (1 + base·open²), and "
            "density follows the packing power law."
        ),
        "numerical_check": {
            "em": live["fork"]["em_feedback"]["em"],
            "r_scale": live["fork"]["em_feedback"]["r_scale"],
            "sigma_scale": live["fork"]["em_feedback"]["sigma_scale"],
            "rho_scale": live["fork"]["em_feedback"]["rho_scale"],
            "graphene_packing_scale": gr_live.get("network_open_channel_packing_scale"),
            "diamond_packing_scale": dia_live.get("network_open_channel_packing_scale"),
            "graphene_areal_error_pct_frozen": gr_frozen["comparison_quarantine"][
                "areal_density_error_pct"
            ],
            "graphene_areal_error_pct_feedback": gr_live["comparison_quarantine"][
                "areal_density_error_pct"
            ],
            "graphene_abs_error_reduction_pct": _pct_improvement(gr_old, gr_new),
            "diamond_density_error_pct_frozen": dia_frozen["comparison_quarantine"][
                "density_error_pct"
            ],
            "diamond_density_error_pct_feedback": dia_live["comparison_quarantine"][
                "density_error_pct"
            ],
            "diamond_abs_error_reduction_pct": _pct_improvement(dia_old, dia_new),
        },
        "next_action": (
            "Generic covalent_network_em_packing_dress is live with continuous "
            "w=(2/P)^cap and open^(w²); period-2 keeps full EM×open, deeper periods "
            "fade onto the nuclear/CM branch (no length_reliable hard gate)."
        ),
    }


def phase_material_fixed_point_witness() -> dict[str, Any]:
    """Current numerical evidence for rho_curv/material-response feedback."""
    payload = pmff.build_payload()
    rows = payload["rows"]
    ranked = sorted(
        rows,
        key=lambda row: abs(
            float(row["trace"]["final_state"]) - float(row["trace"]["initial_state"])
        ),
        reverse=True,
    )
    return {
        "summary": payload["summary"],
        "largest_shift": {
            "molecule": ranked[0]["molecule"],
            "phase": ranked[0]["phase"],
            "allotrope": ranked[0]["allotrope"],
            "rho_curv_initial": ranked[0]["trace"]["initial_state"],
            "rho_curv_final": ranked[0]["trace"]["final_state"],
            "refractive_index_delta": ranked[0]["response_delta"]["refractive_index"],
            "thermal_conductivity_delta": ranked[0]["response_delta"][
                "thermal_conductivity_W_mK"
            ],
            "B_hom_delta": ranked[0]["response_delta"]["B_hom"],
        },
    }


def spectral_scale_anchor_witness() -> dict[str, Any]:
    """Current numerical evidence for omega* -> em* scale-anchor feedback."""
    payload = ssaf.build_payload()
    residual = sra.build_payload()
    rows = payload["rows"]
    if not rows:
        return {"summary": payload["summary"], "largest_unpinned_shift": None}
    ranked = sorted(
        rows,
        key=lambda row: abs(
            row["comparison_quarantine"]["multiplicative"]["B_e"]["factor_anchor"]
            - row["comparison_quarantine"]["multiplicative"]["B_e"]["factor_baseline"]
        ),
        reverse=True,
    )
    top = ranked[0]
    top_mult = top["comparison_quarantine"]["multiplicative"]
    return {
        "summary": payload["summary"],
        "residual_audit": residual["summary"],
        "largest_unpinned_shift": {
            "name": top["name"],
            "s_star": top["pin"]["s_star"],
            "em_star": top["pin"]["em_star"],
            "geometry_reliable": top["geometry_reliable"],
            "r_e_error_pct_baseline": top["comparison_quarantine"][
                "r_e_error_pct_baseline"
            ],
            "r_e_error_pct_anchor": top["comparison_quarantine"]["r_e_error_pct_anchor"],
            "D_e_error_pct_baseline": top["comparison_quarantine"][
                "D_e_error_pct_baseline"
            ],
            "D_e_error_pct_anchor": top["comparison_quarantine"]["D_e_error_pct_anchor"],
            "B_e_error_pct_baseline": top["comparison_quarantine"][
                "B_e_error_pct_baseline"
            ],
            "B_e_error_pct_anchor": top["comparison_quarantine"]["B_e_error_pct_anchor"],
            "multiplicative": top_mult,
        },
    }


def audit_rows() -> list[dict[str, Any]]:
    """Ranked feedback candidates."""
    return [
        carbon_em_density_witness(),
        {
            "loop": "spectral scale anchor -> em -> contact length -> BE / density / transport",
            "lean": [
                "OutsideContactReducedDeltas.spectralConcentrationWeight",
                "OutsideContactReducedDeltas.outsideEmFromConcentrationWeight",
                "OutsideContactReducedDeltas.contactLengthFromEmFeedback",
            ],
            "python": [
                "scripts/hqiv_molecular_spectroscopy.py",
                "scripts/hqiv_outside_contact_reduced_deltas.py",
                "scripts/hqiv_spectral_scale_anchor_feedback.py",
            ],
            "status": "promote-live-scale-anchor",
            "reason": (
                "A spectral pin should set an in-situ scale, then score other "
                "outputs. It should not be evaluated by re-scoring the pinned omega."
            ),
            "numerical_check": spectral_scale_anchor_witness(),
            "next_action": (
                "Spectral panel is near-closed; keep shell length closed unless a "
                "new reliable row exceeds the near-closed band, and score packing "
                "through the live EM/open-channel dress."
            ),
        },
        {
            "loop": "phase density -> B_hom -> polarizability/material response -> phase density",
            "lean": [
                "PhaseGeometryDensity.phaseCurvatureDensityFraction",
                "HomogeneousCurvatureSecondOrder.homogeneousCurvatureBudgetAtXi",
            ],
            "python": [
                "scripts/hqiv_phase_geometry_density.py",
                "scripts/hqiv_phase_material_response.py",
                "scripts/hqiv_phase_material_feedback_fixed_point.py",
            ],
            "status": "promote-live-fixed-point",
            "reason": (
                "Material response already uses rho_curv to compute polarizability, "
                "thermal conductivity, heat capacity, and viscosity. Some of those "
                "responses change the effective phase density or contact scale, so "
                "one pass is structurally incomplete."
            ),
            "numerical_check": phase_material_fixed_point_witness(),
            "next_action": (
                "Fixed-point iterator now converges with full updates; use the "
                "converged rho_curv as the material-table state, and keep one-way "
                "tables only for comparison."
            ),
        },
        {
            "loop": "strain / piezo -> contact length -> stiffness -> strain",
            "lean": [
                "VoltageGenerationLedger.piezoVoltageChannel",
                "PhaseElasticity.contactBindingStiffnessPa",
                "PhaseElasticity.strainFromStressStiffness",
            ],
            "python": [
                "scripts/hqiv_voltage_generation_ledger.py",
                "scripts/hqiv_crystal_fracture_witness.py",
            ],
            "status": "promote-live-fixed-point",
            "reason": (
                "Strain is a mechanical equilibrium variable: ε moves r, r changes "
                "stiffness k∝1/r³, and ε' = clamp(thermal + (1−thermal)·strong·σ/k) "
                "is iterated to a bounded fixed point. No residual-inferred strain."
            ),
            "next_action": (
                "piezo_stiffness_equilibrium_strain is live; seed with Lindemann "
                "thermal strain and optional external stress_Pa. Wire wall-spectrum "
                "stress when the shared wall factor lands."
            ),
        },
        {
            "loop": "conductivity -> Joule/thermal release -> thermo voltage -> conductivity",
            "lean": [
                "VoltageGenerationLedger.thermoVoltageChannel",
                "VoltageGenerationLedger.jouleReleaseContrast",
                "VoltageGenerationLedger.carrierThermoConductivityDress",
                "MolecularTransport.nernstEinsteinConductivitySlot",
            ],
            "python": [
                "scripts/hqiv_phase_material_response.py",
                "scripts/hqiv_voltage_generation_ledger.py",
            ],
            "status": "promote-live-when-carriers",
            "reason": (
                "Neutral pure media correctly keep carrier_fraction=0 (identity). "
                "With carriers, jouleReleaseContrast = clamp(carrier)·clamp(cage)·γ "
                "dresses σ through thermoVoltageChannel — no SI mash, no molecule case."
            ),
            "next_action": (
                "carrier_thermo_conductivity_dress is live on ionic_conductivity_s_m; "
                "pass explicit carrier_fraction for electrolytes / doped sheets."
            ),
        },
        {
            "loop": "thermal conductivity -> temperature profile -> B_hom / release contrast -> thermal conductivity",
            "lean": [
                "HomogeneousCurvatureSecondOrder.homogeneousCurvatureBudgetAtXi",
                "VoltageGenerationLedger.thermoVoltageChannel",
            ],
            "python": ["scripts/hqiv_phase_material_response.py"],
            "status": "promote-for-driven-or-gradient-assays",
            "reason": (
                "k_th currently reads rho_curv and B_hom one-way. Under a gradient, "
                "temperature profile and release contrast are dynamic state variables."
            ),
            "next_action": (
                "Keep isothermal material tables one-way; add a gradient assay mode "
                "with finite update steps."
            ),
        },
        {
            "loop": "wall spectrum -> localDefect / tribo -> contact length -> wall spectrum",
            "lean": [
                "OutsideContactReducedDeltas.DryWallSpectrum",
                "VoltageGenerationLedger.triboVoltageChannel",
            ],
            "python": ["scripts/hqiv_outside_contact_reduced_deltas.py"],
            "status": "shared-wall-factor-first",
            "reason": (
                "Wall/interface should generally be a shared spectrum, not a separate "
                "per-molecule fit. Only if adsorption deforms the wall should this "
                "become two-way."
            ),
            "next_action": (
                "Treat wall as shared factor by default; add two-way adsorption only "
                "for explicit surface reconstruction / defect growth assays."
            ),
        },
        {
            "loop": "BE -> literal mass defect -> density",
            "lean": ["MolecularEnergyBridge", "AtomFromCharge / atom mass readouts"],
            "python": ["scripts/hqiv_atom_construction.py"],
            "status": "defer-small-effect",
            "reason": (
                "The literal eV/c^2 mass defect is real but far too small to explain "
                "chemistry-scale density residuals. The important mass feedback is "
                "through EM-dressed contact length, not direct mass subtraction."
            ),
            "next_action": (
                "Record as precision bookkeeping for isotope/mass-ledger work, not "
                "as a primary materials feedback."
            ),
        },
    ]


def build_payload() -> dict[str, Any]:
    rows = audit_rows()
    return {
        "source": "scripts/hqiv_two_way_feedback_audit.py",
        "policy": (
            "Promote feedback only when the dependent readout changes the channel "
            "that generated it; keep shared ambient and wall factors out of motif fits."
        ),
        "summary": {
            "promote_now": [r["loop"] for r in rows if r["status"].startswith("promote")],
            "shared_or_defer": [
                r["loop"]
                for r in rows
                if r["status"].startswith("shared") or r["status"].startswith("defer")
            ],
            "top_priority": rows[0]["loop"],
        },
        "rows": rows,
    }


def print_report(payload: dict[str, Any]) -> None:
    print("=== Two-way feedback audit ===")
    print(payload["policy"])
    print()
    for idx, row in enumerate(payload["rows"], 1):
        print(f"{idx}. {row['loop']}")
        print(f"   status: {row['status']}")
        print(f"   why: {row['reason']}")
        if "numerical_check" in row:
            n = row["numerical_check"]
            if "graphene_areal_error_pct_frozen" in n:
                print(
                    "   carbon check: "
                    f"graphene σ err {n['graphene_areal_error_pct_frozen']:+.2f}% -> "
                    f"{n['graphene_areal_error_pct_feedback']:+.2f}%; "
                    f"diamond ρ err {n['diamond_density_error_pct_frozen']:+.2f}% -> "
                    f"{n['diamond_density_error_pct_feedback']:+.2f}%"
                )
            elif n.get("largest_unpinned_shift"):
                s = n["largest_unpinned_shift"]
                reliable = n["summary"]["geometric_error_reliable_geometry"]["B_e"]
                residual = n["residual_audit"]
                print(
                    "   spectral check: "
                    f"reliable-geometry B_e geometric error "
                    f"{reliable['geometric_mean_error_pct_baseline']:.2f}% -> "
                    f"{reliable['geometric_mean_error_pct_anchor']:.2f}%; "
                    f"B_e independent residual "
                    f"{residual['mean_B_e_independent_multiplicative_pct_reliable']:.2f}%"
                )
                print(
                    "   residual slots: "
                    + ", ".join(
                        f"{slot}={count}"
                        for slot, count in sorted(residual["slot_counts"].items())
                        if count
                    )
                )
            elif n.get("largest_shift"):
                s = n["largest_shift"]
                print(
                    "   fixed-point check: "
                    f"{s['molecule']} {s['phase']} rho "
                    f"{s['rho_curv_initial']:.4f} -> {s['rho_curv_final']:.4f}; "
                    f"Δn={s['refractive_index_delta']['absolute']:+.5f}"
                )
        print(f"   next: {row['next_action']}")
        print()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    print_report(payload)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"wrote {args.json_out}")


if __name__ == "__main__":
    main()
