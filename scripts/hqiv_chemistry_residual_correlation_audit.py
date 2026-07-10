#!/usr/bin/env python3
"""
Residual-correlation audit for the light-cone chemistry paper.

This script does not introduce corrections or fit coefficients.  It only maps
comparison residuals already present in the witness JSON files against derived HQIV
features, so second-order targets stay tied to existing structural slots:
ionic character, curvature density, contact count, monogamy defect, concentration
weight, and bracket position.

Usage:
  python3 scripts/hqiv_chemistry_residual_correlation_audit.py
  python3 scripts/hqiv_chemistry_residual_correlation_audit.py --json data/chemistry_residual_correlation_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
from collections import defaultdict
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DEFAULT_JSON = DATA / "chemistry_residual_correlation_audit.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _finite(value: Any) -> bool:
    return isinstance(value, int | float) and math.isfinite(float(value))


def pearson(xs: list[float], ys: list[float]) -> dict[str, Any]:
    pairs = [(float(x), float(y)) for x, y in zip(xs, ys) if _finite(x) and _finite(y)]
    if len(pairs) < 3:
        return {"available": False, "n": len(pairs), "reason": "fewer_than_three_points"}
    xvals = [p[0] for p in pairs]
    yvals = [p[1] for p in pairs]
    mx = mean(xvals)
    my = mean(yvals)
    dx = [x - mx for x in xvals]
    dy = [y - my for y in yvals]
    sx = math.sqrt(sum(d * d for d in dx))
    sy = math.sqrt(sum(d * d for d in dy))
    if sx == 0.0 or sy == 0.0:
        return {"available": False, "n": len(pairs), "reason": "zero_variance"}
    r = sum(a * b for a, b in zip(dx, dy)) / (sx * sy)
    return {"available": True, "n": len(pairs), "pearson_r": r, "abs_r": abs(r)}


def _mean(values: list[float]) -> float | None:
    clean = [float(v) for v in values if _finite(v)]
    return sum(clean) / len(clean) if clean else None


def _group_means(rows: list[dict[str, Any]], group_key: str, residual_keys: list[str]) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[str(row[group_key])].append(row)
    out: dict[str, Any] = {}
    for group, group_rows in sorted(grouped.items()):
        out[group] = {
            "n": len(group_rows),
            "mean_abs_error_pct": {
                key: _mean([r[key] for r in group_rows if key in r]) for key in residual_keys
            },
        }
    return out


def condensed_phase_panel(lab: dict[str, Any]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for row in lab["species"]:
        geom = row["geometry"]
        mat = row["material_response"]
        bench = row["benchmark"]
        ref_n = row["nist_reference"]["refractive_index"]
        n_one_way = mat.get("refractive_index_one_way", mat["refractive_index"])
        n_one_way_err = abs(n_one_way - ref_n) / ref_n * 100.0
        rows.append(
            {
                "molecule": row["molecule"],
                "motif": row["monomer_motif"],
                "intermolecular_contacts": row["intermolecular_contacts"],
                "contact_xi": row["contact_xi"],
                "curvature_density_fraction": geom["curvature_density_fraction"],
                "phase_curvature_density_fraction": geom["phase_curvature_density_fraction"],
                "neighbor_lapse_overlap_factor": geom["neighbor_lapse_overlap_factor"],
                "halogen_strong_hbond_leg_factor": geom["halogen_strong_hbond_leg_factor"],
                "linear_chain_zigzag_lattice_open_factor": geom[
                    "linear_chain_zigzag_lattice_open_factor"
                ],
                "B_hom": mat["B_hom"],
                "optical_coupling_level": mat.get("optical_coupling_level", "feed_forward"),
                "missing_optical_coupled_relaxation_flag": mat.get(
                    "missing_optical_coupled_relaxation_flag", 0
                ),
                "density_abs_error_pct": bench["density_error_pct"],
                "refractive_index_abs_error_pct": bench["refractive_index_error_pct"],
                "refractive_index_one_way_abs_error_pct": n_one_way_err,
                "refractive_index_coupled_improvement_abs_pct": n_one_way_err
                - bench["refractive_index_error_pct"],
                "T_sl_abs_error_pct": bench["T_sl_error_pct"],
            }
        )

    feature_keys = [
        "intermolecular_contacts",
        "contact_xi",
        "curvature_density_fraction",
        "phase_curvature_density_fraction",
        "neighbor_lapse_overlap_factor",
        "halogen_strong_hbond_leg_factor",
        "linear_chain_zigzag_lattice_open_factor",
        "B_hom",
    ]
    residual_keys = [
        "density_abs_error_pct",
        "refractive_index_abs_error_pct",
        "refractive_index_one_way_abs_error_pct",
        "T_sl_abs_error_pct",
    ]
    correlations: dict[str, Any] = {}
    for residual in residual_keys:
        correlations[residual] = {}
        ys = [row[residual] for row in rows]
        for feature in feature_keys:
            xs = [row[feature] for row in rows]
            correlations[residual][feature] = pearson(xs, ys)

    return {
        "n": len(rows),
        "small_n_note": "Condensed panel is intentionally small; correlations are target selectors, not statistical claims.",
        "rows": rows,
        "group_means_by_motif": _group_means(rows, "motif", residual_keys),
        "group_means_by_optical_coupling_level": _group_means(
            rows, "optical_coupling_level", residual_keys
        ),
        "correlations": correlations,
        "largest_residuals": {
            residual: sorted(
                (
                    {"molecule": row["molecule"], "value_pct": row[residual]}
                    for row in rows
                ),
                key=lambda item: item["value_pct"],
                reverse=True,
            )
            for residual in residual_keys
        },
        "optical_coupled_relaxation_improvements": [
            {
                "molecule": row["molecule"],
                "coupling_level": row["optical_coupling_level"],
                "one_way_abs_error_pct": row["refractive_index_one_way_abs_error_pct"],
                "coupled_abs_error_pct": row["refractive_index_abs_error_pct"],
                "improvement_abs_pct": row["refractive_index_coupled_improvement_abs_pct"],
            }
            for row in rows
            if row["missing_optical_coupled_relaxation_flag"]
        ],
    }


def spectroscopy_panel(spec: dict[str, Any]) -> dict[str, Any]:
    row_by_name = {row["name"]: row for row in spec["rows"]}
    rows: list[dict[str, Any]] = []
    for name, comp in spec["comparison"].items():
        if not comp.get("available") or name not in row_by_name:
            continue
        row = row_by_name[name]
        err = comp["error_pct"]
        bracket = comp["concentration_bracket"]
        lower = bracket["omega_e_lower_diffuse_cm1"]
        upper = bracket["omega_e_upper_concentrated_cm1"]
        ref_omega = comp["reference"]["omega_e"]
        one_way_omega = row.get("omega_e_one_way_cm1", row["omega_e_cm1"])
        one_way_err = (one_way_omega - ref_omega) / ref_omega * 100.0
        width = upper - lower
        bracket_position = (ref_omega - lower) / width if width > 0.0 else None
        rows.append(
            {
                "molecule": name,
                "class": (
                    "homonuclear"
                    if row["label_i"] == row["label_j"]
                    else "polar_or_ionic"
                    if row["bond_ionic_character"] >= 0.05
                    else "weakly_polar"
                ),
                "geometry_reliable": bool(row["geometry_reliable"]),
                "geometry_reliable_numeric": 1.0 if row["geometry_reliable"] else 0.0,
                "geometry_route": row.get("geometry_route", "covalent_nested_wf"),
                "r_e_outside_contact_target_angstrom": row.get(
                    "r_e_outside_contact_target_angstrom"
                ),
                "geometry_outside_candidate_clears_floor": bool(
                    row.get("geometry_outside_candidate_clears_floor", False)
                ),
                "bond_ionic_character": row["bond_ionic_character"],
                "xi_contact": row["xi_contact"],
                "curvature_integral": row["curvature_integral"],
                "monogamy_channel_defect": row["monogamy_channel_defect"],
                "concentration_weight": row["concentration_weight"],
                "omega_e_cross_check_spread_pct": row["omega_e_cross_check_spread_pct"],
                "bracket_contains_reference": bool(bracket["nist_within_bracket"]),
                "bracket_contains_reference_numeric": 1.0
                if bracket["nist_within_bracket"]
                else 0.0,
                "omega_e_bracket_position": bracket_position,
                "omega_e_bracket_width_cm1": width,
                "coupling_level": row.get("coupling_level", "feed_forward"),
                "missing_coupled_relaxation_flag": row.get(
                    "missing_coupled_relaxation_flag", 0
                ),
                "coupled_relaxation_weight": row.get("coupled_relaxation_weight", 0.0),
                "omega_e_one_way_signed_error_pct": one_way_err,
                "omega_e_one_way_abs_error_pct": abs(one_way_err),
                "omega_e_coupled_improvement_abs_pct": abs(one_way_err)
                - abs(err["omega_e"]),
                "omega_e_signed_error_pct": err["omega_e"],
                "omega_e_abs_error_pct": abs(err["omega_e"]),
                "r_e_signed_error_pct": err["r_e"],
                "r_e_abs_error_pct": abs(err["r_e"]),
                "B_e_abs_error_pct": abs(err["B_e"]),
                "omega_e_xe_abs_error_pct": abs(err["omega_e_xe"]),
            }
        )

    feature_keys = [
        "geometry_reliable_numeric",
        "bond_ionic_character",
        "xi_contact",
        "curvature_integral",
        "monogamy_channel_defect",
        "concentration_weight",
        "omega_e_cross_check_spread_pct",
        "bracket_contains_reference_numeric",
        "omega_e_bracket_position",
        "omega_e_bracket_width_cm1",
    ]
    residual_keys = [
        "omega_e_abs_error_pct",
        "omega_e_one_way_abs_error_pct",
        "omega_e_signed_error_pct",
        "r_e_abs_error_pct",
        "B_e_abs_error_pct",
        "omega_e_xe_abs_error_pct",
    ]
    correlations: dict[str, Any] = {}
    for residual in residual_keys:
        correlations[residual] = {}
        ys = [row[residual] for row in rows]
        for feature in feature_keys:
            xs = [row[feature] for row in rows]
            correlations[residual][feature] = pearson(xs, ys)

    reliable = [row for row in rows if row["geometry_reliable"]]
    reliable_correlations: dict[str, Any] = {}
    for residual in residual_keys:
        reliable_correlations[residual] = {}
        ys = [row[residual] for row in reliable]
        for feature in feature_keys:
            xs = [row[feature] for row in reliable]
            reliable_correlations[residual][feature] = pearson(xs, ys)
    return {
        "n": len(rows),
        "n_reliable_geometry": len(reliable),
        "rows": rows,
        "group_means_by_class": _group_means(rows, "class", residual_keys),
        "group_means_reliable_geometry_by_class": _group_means(
            reliable, "class", residual_keys
        ),
        "group_means_by_geometry_reliability": _group_means(
            rows, "geometry_reliable", residual_keys
        ),
        "group_means_by_coupling_level": _group_means(rows, "coupling_level", residual_keys),
        "correlations": correlations,
        "correlations_reliable_geometry": reliable_correlations,
        "largest_residuals": {
            residual: sorted(
                (
                    {"molecule": row["molecule"], "value_pct": row[residual]}
                    for row in rows
                ),
                key=lambda item: abs(item["value_pct"]),
                reverse=True,
            )
            for residual in residual_keys
        },
        "in_bracket_flow_targets": [
            {
                "molecule": row["molecule"],
                "bracket_position": row["omega_e_bracket_position"],
                "omega_e_signed_error_pct": row["omega_e_signed_error_pct"],
            }
            for row in reliable
            if row["bracket_contains_reference"] and row["omega_e_bracket_position"] is not None
        ],
        "coupled_relaxation_improvements": [
            {
                "molecule": row["molecule"],
                "coupling_level": row["coupling_level"],
                "one_way_abs_error_pct": row["omega_e_one_way_abs_error_pct"],
                "coupled_abs_error_pct": row["omega_e_abs_error_pct"],
                "improvement_abs_pct": row["omega_e_coupled_improvement_abs_pct"],
            }
            for row in rows
            if row["missing_coupled_relaxation_flag"]
        ],
    }


def comparison_confidence(phase: dict[str, Any]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for key in ("water_llpt_observations", "water_hoh_angle_observations"):
        for obs in phase.get(key, []):
            source = obs.get("source", "")
            lower = source.lower()
            if "md" in lower or "mb-pol" in lower or "tip4p" in lower:
                confidence_class = "simulation_comparison"
            elif "experimental claim" in obs.get("label", "").lower():
                confidence_class = "debated_experimental_comparison"
            elif "nist" in lower or "j. mol." in lower or "science" in lower:
                confidence_class = "laboratory_or_database_comparison"
            else:
                confidence_class = "comparison_only"
            rows.append(
                {
                    "source": source,
                    "label": obs.get("label"),
                    "confidence_class": confidence_class,
                    "role": obs.get("role", "comparison_only"),
                }
            )
    return {"rows": rows}


def forward_prediction_candidates(phase: dict[str, Any], allotrope: dict[str, Any]) -> dict[str, Any]:
    water_grid = phase["species"]["H2O"]["grid"]
    selected_grid = []
    for target_t, target_p in ((80.0, 1.0), (80.0, 1250.0), (200.0, 1250.0), (300.0, 1.0)):
        row = min(
            water_grid,
            key=lambda item: abs(item["temperature_K"] - target_t)
            + abs(item["pressure_atm"] - target_p) / 1000.0,
        )
        selected_grid.append(
            {
                "molecule": "H2O",
                "temperature_K": row["temperature_K"],
                "pressure_atm": row["pressure_atm"],
                "derived_phase": row["derived_phase"],
                "liquid_subphase": row.get("liquid_subphase"),
                "f_low_density": row.get("f_low_density"),
                "rho_curv": row["rho_curv"],
                "coordination_fraction": row["coordination_fraction"],
                "benchmark_status": "forward_prediction_or_unscored_grid_row",
            }
        )

    cooling = allotrope["species"]["H2O"]["temperature_sweep"]
    selected_cooling = []
    for target_t in (50.0, 205.0, 325.0):
        row = min(cooling, key=lambda item: abs(item["temperature_K"] - target_t))
        selected_cooling.append(
            {
                "molecule": "H2O",
                "temperature_K": row["temperature_K"],
                "derived_phase": row["derived_phase"],
                "preferred_allotrope": row.get("preferred_allotrope"),
                "T_melt_K": row["T_melt_K"],
                "T_boil_K": row["T_boil_K"],
                "benchmark_status": "forward_prediction_or_unscored_sweep_row",
            }
        )
    return {"phase_grid_rows": selected_grid, "cooling_sweep_rows": selected_cooling}


def build_payload() -> dict[str, Any]:
    lab = _load_json(DATA / "hqiv_lab_witnesses.json")
    spec = _load_json(DATA / "molecular_spectroscopy_witnesses.json")
    phase = _load_json(DATA / "phase_diagram_audit.json")
    allotrope = _load_json(DATA / "allotrope_phase_cooling_audit.json")
    return {
        "source": "scripts/hqiv_chemistry_residual_correlation_audit.py",
        "comparison_policy": (
            "Residuals use quarantined comparison fields already present in witness JSON; "
            "no comparison value is used to tune or correct a readout."
        ),
        "anchor_policy": {
            "alpha": "fixed by Lean as alphaRat transverseDim = 3/5",
            "gamma": "fixed by Lean as gammaRat 3 = 2/5",
            "referenceM": "fixed by Lean lock-in at referenceM = 4",
            "counterfactual_anchor_variation": "not performed; varying these would be a falsification/sensitivity diagnostic, not an allowed fit knob",
        },
        "second_order_target_policy": (
            "Targets are residual correlations against existing derived slots: curvature density, "
            "ionic character, monogamy defect, concentration bracket/weight, and contact topology."
        ),
        "dynamics_treatment_policy": {
            "geometry_binding": (
                "OutsideContactGeometry exposes ionicOutsideContactLengthTarget and "
                "period3HalogenBondLengthTarget as upstream candidates; headline "
                "geometry_reliable quarantines ionic/period-3 routes until theorem promotion"
            ),
            "outside_environment": (
                "outsideEnvironmentModulator = outsideCurvatureBindingModulatorChart * "
                "outsideGravityGeffModulator (Lean/Python aligned)"
            ),
            "spectroscopy": "coupledRelaxationStep feeds concentration-flow target into structurally flagged one-way omega_e rows",
            "material": "linear-chain optical relaxation plus cage-limited thermal conductivity and network curvature propagation fields",
            "phase": "bounded branchFractionCoupledStep activates only on LDL/HDL mixture rows",
            "transport": "cageLimitedTransport slot is mirrored in material thermal transport; diffusion benchmarks remain finite Fick/Nernst-Einstein",
            "activation": "activationRateSlot is available as a finite reaction-gate multiplier; no transition-state benchmark is promoted yet",
            "network": "networkPropagationStep exposes local-to-neighbour finite register propagation fields",
        },
        "condensed_phase": condensed_phase_panel(lab),
        "spectroscopy": spectroscopy_panel(spec),
        "comparison_confidence": comparison_confidence(phase),
        "forward_prediction_candidates": forward_prediction_candidates(phase, allotrope),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Build residual-correlation audit JSON.")
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload()
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("HQIV chemistry residual-correlation audit")
    print("=" * 60)
    print(f"condensed rows: {payload['condensed_phase']['n']}")
    print(f"spectroscopy rows: {payload['spectroscopy']['n']}")
    print(f"wrote {args.json}")


if __name__ == "__main__":
    main()
