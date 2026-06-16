#!/usr/bin/env python3
"""
Provenance for dynamic-binding surplus routes (Python ↔ Lean chart alignment).

Each dress / divisor must cite a Lean definition or be flagged ``python_scaffold``
until certified in ``Hqiv.QuantumChemistry.ChemistryBindingRoutes``.
"""

from __future__ import annotations

from typing import Any, Literal

RouteStatus = Literal["lean_certified", "chart_derived", "python_scaffold"]

# Lean module witnesses (proved or definitional spine).
LEAN_CERTIFIED: dict[str, str] = {
    "strong_channel_fraction": "Hqiv.Physics.HQIVNuclei.strongChannelFraction",
    "constructive_valley_cap": "Hqiv.Physics.NuclearContactClosure.constructiveValleyCap",
    "dynamic_lone_pair_dress": "Hqiv.QuantumChemistry.CentreGeometryFromTuft.dynamicLonePairSurplusDress",
    "dynamic_bent_hyperclosure": "Hqiv.QuantumChemistry.CentreGeometryFromTuft.dynamicBentHyperclosureDress",
    "centre_lone_pair_count": "Hqiv.Physics.DynamicCentreGeometry.centreLonePairCount",
    "electronic_compton_shells": "Hqiv.QuantumChemistry.ElectronicValenceFromTuftChart",
    "bond_horizon_surplus": "Hqiv.Geometry.BondedHorizonCasimir.bondHorizonSurplusDimless",
    "metallic_peel_surplus": "Hqiv.Geometry.BondedHorizonCasimir.metallicPeelSurplusDimless",
    "covalent_dimer_surplus": "Hqiv.Geometry.BondedHorizonCasimir.covalentDimerTwoElectronSurplusDimless",
    "steric_repulsion_scaffold": "Hqiv.QuantumChemistry.CurvatureContactNetwork.stericRepulsionMultiplierScaffold",
    "neighbor_lapse_overlap": "Hqiv.QuantumChemistry.PhaseAllotropeDerivation.neighborCovalentLapseOverlapFactor",
    "halogen_hbond_leg": "Hqiv.QuantumChemistry.PhaseAllotropeDerivation.halogenStrongHbondLegFactor",
    "nested_wf_covalent_radius": "Hqiv.QuantumChemistry.CentreGeometryFromTuft.dynamicContactRadiusDimless",
    "informational_monogamy_length": "Hqiv.Geometry.OctonionicLightCone.alpha",
    "dynamic_centre_angle": "Hqiv.Physics.DynamicCentreGeometry.dynamicCentreAngleRad",
}

# Routes applied in ``hqiv_electronic_valence_shells`` / ``hqiv_shell_aware_binding``.
BINDING_ROUTE_REGISTRY: dict[str, dict[str, Any]] = {
    "lone_pair_surplus_dress": {
        "status": "lean_certified",
        "lean": LEAN_CERTIFIED["dynamic_lone_pair_dress"],
        "formula": "1 + (4/8) · n_LP · η_p",
    },
    "bent_hyperclosure_dress": {
        "status": "lean_certified",
        "lean": LEAN_CERTIFIED["dynamic_bent_hyperclosure"],
        "formula": "1 + (4/8)/4 when n_centre_bonds = 2",
    },
    "bent_hyperclosure_period3_channel": {
        "status": "python_scaffold",
        "lean": None,
        "formula": "1 + (4/8)/2 for period ≥ 3 bent dihydrides (H₂S); pending CentreGeometryFromTuft",
        "note": "Lean certifies only (4/8)/4; period-3 extension not yet in Lean",
    },
    "centre_coordination_graph_dress": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["constructive_valley_cap"],
        "formula": "1 ± 2·(4/8) / (constructiveValleyCap · n) for n = 3, 4",
        "note": "Increment class strong/constructiveValleyCap; sign by coordination",
    },
    "period_hydride_rung_dress": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["electronic_compton_shells"],
        "formula": "m_s(period 2) / m_s(heavy)",
    },
    "period_hydride_sp_coupling_dissociation": {
        "status": "python_scaffold",
        "lean": LEAN_CERTIFIED["electronic_compton_shells"],
        "formula": "(1 − 4/8/m_s)(1 − 4/8/(m_s+m_p)) on period-3 H–X dissociation only",
        "note": "Slots from TUFT chart; coupling exponents mirror halogen σ-hole pattern — pending Lean",
    },
    "homonuclear_closed_shell_divisor": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["constructive_valley_cap"],
        "formula": "bond_horizon / (bond_order · (1 + (4/8)/constructiveValleyCap))",
        "note": "bond_order from valence; divisor increment matches NuclearCurvatureBinding valley step",
    },
    "homonuclear_open_shell_exponent": {
        "status": "python_scaffold",
        "lean": None,
        "formula": "bond_horizon / (2 · bond_order^(2 + (4/8)/constructiveValleyCap))",
        "note": "Open-shell O₂ routing; exponent scaffold pending BondedHorizonCasimir extension",
    },
    "homonuclear_halogen_dimer": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["halogen_hbond_leg"],
        "formula": "bond_order · covalent_dimer / (v − offset); / (1 + (4/8)/(m_s2 + period − 2))",
        "note": "offset 4 (period 2) or 5 (period ≥ 3) from valence σ-hole bookkeeping",
    },
    "h2_ladder_closure": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["covalent_dimer_surplus"],
        "formula": "covalentDimer / (1 + (4/8)/(2·(m_H + m_s2)))",
    },
    "heteronuclear_atomization_bond_order": {
        "status": "python_scaffold",
        "lean": None,
        "formula": "octet + (4/8)/2 · (conjugated − octet) for CO",
        "note": "Pending Lean heteronuclear atomization divisor",
    },
    "conjugated_heavy_heavy_dress": {
        "status": "python_scaffold",
        "lean": "Hqiv.QuantumChemistry.BondStateNetwork.hyperWeight",
        "formula": "1/√(bond_order); homonuclear alkynyl dual-centre boost",
        "note": "Graph hyperclosure mirror; homonuclear C₂H₂ boost pending Lean",
    },
    "ionic_inert_core_dress": {
        "status": "chart_derived",
        "lean": "Hqiv.QuantumChemistry.CentreGeometryFromTuft.dynamicBondDistanceWeight",
        "formula": "n_val/n_tot · √(R_m/(R_m+d)) period ≥ 3 salts",
    },
    "metallic_peel_lattice_binding": {
        "status": "lean_certified",
        "lean": LEAN_CERTIFIED["metallic_peel_surplus"],
        "formula": "max(|peel|, |merge|/2) · 1/(1+d/a₀) · (1+(4/8)/n_coord) · n_val/n_tot",
        "note": "peel = metallicPeelSurplus(n_val,n_core); merge = bondHorizonSurplus(2n,n,n)",
    },
    "metallic_melt_density_ratio": {
        "status": "lean_certified",
        "lean": "Hqiv.QuantumChemistry.PhaseGeometryDensity.metallicMeltDensityRatio",
        "formula": "max(γ/4, 1 − (γ/α)/n_coord · contactLock · (1 − 1/(1+d/a₀)))",
    },
    "horizon_atomization_split_gate": {
        "status": "python_scaffold",
        "lean": "Hqiv.Geometry.BondedHorizonCasimirMoleculeBench",
        "formula": "bond_horizon split when period ≥ 3 and n_bonds ≥ 3",
        "note": "Split tuples certified per molecule; gate rule is Python witness policy",
    },
    "centre_vsepr_period3": {
        "status": "python_scaffold",
        "lean": LEAN_CERTIFIED["centre_lone_pair_count"],
        "formula": "Period ≥ 3 uses (V − X)/2; period 2 uses Lean (V − 2X)/2",
        "note": "Lean centreLonePairCount uses (V − n_bonds)/2 — Python period split diverges",
    },
    "nested_wf_bond_equilibrium": {
        "status": "lean_certified",
        "lean": LEAN_CERTIFIED["nested_wf_covalent_radius"],
        "formula": "r_cov = R_m/Z; r_eq from monogamy (1−α/2) + homonuclear/open-shell/halogen routing",
    },
    "nested_wf_centre_angle": {
        "status": "lean_certified",
        "lean": LEAN_CERTIFIED["dynamic_centre_angle"],
        "formula": "dynamicCentreAngleRad(Z, n_bonds) — steric domains + bent dress",
    },
    "nested_wf_bond_order_contraction": {
        "status": "chart_derived",
        "lean": LEAN_CERTIFIED["strong_channel_fraction"],
        "formula": "r × 1/(1 + (bond_order−1)·(4/8)/4) for explicit π bonds (C≡C, C≡N)",
    },
}


def scaffold_routes() -> list[str]:
    return [k for k, v in BINDING_ROUTE_REGISTRY.items() if v["status"] == "python_scaffold"]


def binding_chart_provenance_payload() -> dict[str, Any]:
    return {
        "parameter_policy": (
            "no_fitted_coefficients; chart-derived rationals (4/8, γ, constructiveValleyCap, "
            "TUFT Compton shells) only. Routes marked python_scaffold are audit witnesses "
            "not yet discharged in Lean."
        ),
        "lean_certified_constants": {
            "strongChannelFraction": "4/8",
            "gamma_HQIV": "2/5",
            "constructiveValleyCap": "6",
        },
        "scaffold_route_count": len(scaffold_routes()),
        "scaffold_routes": scaffold_routes(),
        "route_registry": BINDING_ROUTE_REGISTRY,
    }
