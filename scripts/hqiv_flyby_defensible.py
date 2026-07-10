#!/usr/bin/env python3
"""Faithful / audit-minimal Earth flyby scorecard.

Runs the load-bearing coupling from ``paper_defensible_coupling`` against
Anderson-scored flybys, compares head-to-head with the cluttered nominal
preset, and verifies each dropped flag is inert at NEAR (|Δ| ≲ 0.05 mm/s).

Usage:
  PYTHONPATH=scripts python3 scripts/hqiv_flyby_defensible.py
  PYTHONPATH=scripts python3 scripts/hqiv_flyby_defensible.py --json papers/orbital_flyby/artifacts/flyby_defensible_v1.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import hqiv_orbital_flyby_omaxwell as orb

# Anderson-scored Earth encounters (literature Δv∞ targets in catalog).
SCORED_KEYS = ("near_1998", "galileo_1990", "cassini_1999", "rosetta_2005")

# Null / quiet checks: Cassini is already small; keep catalog geometry probes.
NULLISH_KEYS = ("equator_to_equator",)

# Catalog-inert clutter: each alone restored onto the defensible base.
INERT_RESTORES: dict[str, dict[str, Any]] = {
    "galactic_disk_lapse_phi": {"galactic_disk_lapse_phi": True},
    "velocity_screen": {"velocity_screen": True},
    "phase_geometry_source": {"phase_geometry_source": True},
}

# Dropping a load-bearing channel from defensible should move NEAR by ≳ this.
LOAD_BEARING_DROPS: dict[str, dict[str, Any]] = {
    "no_lapse_drag": {"lapse_drag_phi": False},
    "no_horizon_metric": {"horizon_metric_channel": False},
    "no_lense_thirring": {"lapse_drag_lense_thirring": False},
    "no_angular_momentum_screen": {"angular_momentum_screen": False},
    "no_paper_inertia_screen": {"paper_inertia_screen": False, "modified_inertia_geodesic": False},
    # Angular Rindler is NEAR-inert but load-bearing on Rosetta; scored on Rosetta.
    "no_orbital_angular_rindler": {"orbital_angular_rindler": False},
}

# Identity-kept but flyby-inert when ⟨f⟩≈1 (documented separately).
IDENTITY_KEPT_INERT: dict[str, dict[str, Any]] = {
    "no_modified_geodesic": {"modified_inertia_geodesic": False},
}

INERT_TOL_MM_S = 0.05
LOAD_BEARING_MIN_MM_S = 0.05
RINDLER_PROBE_KEY = "rosetta_2005"


def _excess(row: dict[str, object]) -> float:
    return float(row["hqiv_minus_classical_mm_s"])


def _run_case(
    key: str,
    coupling: orb.HQIVOrbitCoupling,
) -> dict[str, Any]:
    case = orb.FLYBY_CATALOG[key]
    settings = orb.propagation_settings_for(orb.EARTH, case)
    row = orb.compare_classical_vs_hqiv(case, orb.EARTH, coupling, settings)
    lit = case.reported_anomaly_mm_s
    excess = _excess(row)
    classical = row["classical"]
    hqiv = row["hqiv"]
    assert isinstance(classical, dict) and isinstance(hqiv, dict)
    return {
        "case_id": key,
        "label": case.label,
        "lit_mm_s": lit,
        "hqiv_minus_classical_mm_s": excess,
        "pct_of_lit": (100.0 * excess / lit) if lit else None,
        "residual_mm_s": (lit - excess) if lit is not None else None,
        "r_ca_km": float(classical["r_ca_km"]),
        "lat_in_deg": float(classical["asymptote_lat_in_deg"]),
        "lat_out_deg": float(classical["asymptote_lat_out_deg"]),
        "lat_exchange_deg": float(classical["latitude_exchange_deg"]),
        "mean_f_blend": float(hqiv["mean_f_blend"]),
        "mean_one_minus_f_out": float(hqiv["mean_one_minus_f_out"]),
        "phi_source": orb.PHI_SOURCE,
        "phi_hom_m_s2": orb.phi_acceleration_homogeneous_si(),
    }


def _scorecard(coupling: orb.HQIVOrbitCoupling, keys: tuple[str, ...]) -> list[dict[str, Any]]:
    return [_run_case(k, coupling) for k in keys]


def _print_scorecard(title: str, rows: list[dict[str, Any]]) -> None:
    print(f"\n{title}")
    print(
        f"{'case':<16} {'lit':>8} {'HQIV−cls':>10} {'% lit':>8} "
        f"{'resid':>9} {'Δλ°':>7} {'⟨f⟩':>11}"
    )
    print("-" * 78)
    for r in rows:
        lit = r["lit_mm_s"]
        lit_s = f"{lit:8.2f}" if lit is not None else "     n/a"
        pct = r["pct_of_lit"]
        pct_s = f"{pct:8.1f}" if pct is not None else "     n/a"
        resid = r["residual_mm_s"]
        resid_s = f"{resid:9.2f}" if resid is not None else "      n/a"
        print(
            f"{r['case_id']:<16} {lit_s} {r['hqiv_minus_classical_mm_s']:10.4f} "
            f"{pct_s} {resid_s} {r['lat_exchange_deg']:7.2f} "
            f"{r['mean_f_blend']:11.9f}"
        )


def _ablation_near(
    base: orb.HQIVOrbitCoupling,
    *,
    scored_base: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    scored = scored_base or _scorecard(base, SCORED_KEYS)
    base_by_case = {r["case_id"]: r["hqiv_minus_classical_mm_s"] for r in scored}
    base_excess = base_by_case["near_1998"]
    probe_base = base_by_case[RINDLER_PROBE_KEY]
    inert_rows: list[dict[str, Any]] = []
    for name, kwargs in INERT_RESTORES.items():
        coup = replace(base, **kwargs)
        deltas = []
        for key in SCORED_KEYS:
            excess = _run_case(key, coup)["hqiv_minus_classical_mm_s"]
            deltas.append(excess - base_by_case[key])
        worst = max(deltas, key=abs)
        inert_rows.append(
            {
                "restore": name,
                "worst_delta_vs_defensible_mm_s": worst,
                "deltas_by_case_mm_s": dict(zip(SCORED_KEYS, deltas)),
                "inert_pass": abs(worst) <= INERT_TOL_MM_S,
            }
        )
    load_rows: list[dict[str, Any]] = []
    for name, kwargs in LOAD_BEARING_DROPS.items():
        probe_key = RINDLER_PROBE_KEY if name == "no_orbital_angular_rindler" else "near_1998"
        base_probe = probe_base if probe_key == RINDLER_PROBE_KEY else base_excess
        excess = _run_case(probe_key, replace(base, **kwargs))["hqiv_minus_classical_mm_s"]
        delta = excess - base_probe
        load_rows.append(
            {
                "drop": name,
                "probe_case": probe_key,
                "hqiv_minus_classical_mm_s": excess,
                "delta_vs_defensible_mm_s": delta,
                "load_bearing_pass": abs(delta) >= LOAD_BEARING_MIN_MM_S,
            }
        )
    identity_rows: list[dict[str, Any]] = []
    for name, kwargs in IDENTITY_KEPT_INERT.items():
        excess = _run_case("near_1998", replace(base, **kwargs))["hqiv_minus_classical_mm_s"]
        delta = excess - base_excess
        identity_rows.append(
            {
                "drop": name,
                "hqiv_minus_classical_mm_s": excess,
                "delta_vs_defensible_mm_s": delta,
                "inert_as_expected": abs(delta) <= INERT_TOL_MM_S,
            }
        )
    return {
        "near_defensible_mm_s": base_excess,
        "inert_tolerance_mm_s": INERT_TOL_MM_S,
        "load_bearing_min_mm_s": LOAD_BEARING_MIN_MM_S,
        "inert_restores": inert_rows,
        "load_bearing_drops": load_rows,
        "identity_kept_inert": identity_rows,
        "all_inert_pass": all(r["inert_pass"] for r in inert_rows),
        "all_load_bearing_pass": all(r["load_bearing_pass"] for r in load_rows),
    }


def _print_ablation(abl: dict[str, Any]) -> None:
    print(
        "\nCatalog-inert restore onto defensible "
        f"(expect |worst Δ| ≤ {abl['inert_tolerance_mm_s']} mm/s)"
    )
    print(f"{'restore':<28} {'worst Δ':>10} {'pass':>6}")
    print("-" * 48)
    for r in abl["inert_restores"]:
        print(
            f"{r['restore']:<28} {r['worst_delta_vs_defensible_mm_s']:10.4f} "
            f"{'OK' if r['inert_pass'] else 'FAIL':>6}"
        )
    print(
        "\nLoad-bearing drop from defensible "
        f"(expect |Δ| ≥ {abl['load_bearing_min_mm_s']} mm/s)"
    )
    print(f"{'drop':<28} {'probe':>12} {'Δ':>10} {'pass':>6}")
    print("-" * 62)
    for r in abl["load_bearing_drops"]:
        print(
            f"{r['drop']:<28} {r['probe_case']:>12} "
            f"{r['delta_vs_defensible_mm_s']:10.4f} "
            f"{'OK' if r['load_bearing_pass'] else 'FAIL':>6}"
        )
    if abl.get("identity_kept_inert"):
        print("\nIdentity-kept / flyby-inert when ⟨f⟩≈1 (expect |Δ| ≤ tol)")
        print(f"{'drop':<28} {'Δ':>10} {'as expected':>12}")
        print("-" * 54)
        for r in abl["identity_kept_inert"]:
            print(
                f"{r['drop']:<28} {r['delta_vs_defensible_mm_s']:10.4f} "
                f"{'yes' if r['inert_as_expected'] else 'no':>12}"
            )


def _kept_flags(coupling: orb.HQIVOrbitCoupling) -> dict[str, Any]:
    raw = asdict(coupling)
    kept = {
        "lapse_drag_phi": raw["lapse_drag_phi"],
        "horizon_repartition": raw["horizon_repartition"],
        "horizon_metric_channel": raw["horizon_metric_channel"],
        "suppress_vacuum_spin_coupling": raw["suppress_vacuum_spin_coupling"],
        "lapse_drag_colatitude": raw["lapse_drag_colatitude"],
        "lapse_drag_lense_thirring": raw["lapse_drag_lense_thirring"],
        "angular_momentum_screen": raw["angular_momentum_screen"],
        "orbital_angular_rindler": raw["orbital_angular_rindler"],
        "paper_inertia_screen": raw["paper_inertia_screen"],
        "modified_inertia_geodesic": raw["modified_inertia_geodesic"],
        "geff_on_newton": raw["geff_on_newton"],
        "geff_as_time_factor": raw["geff_as_time_factor"],
        "galactic_disk_lapse_phi": raw["galactic_disk_lapse_phi"],
        "velocity_screen": raw["velocity_screen"],
        "phase_geometry_source": raw["phase_geometry_source"],
        "annual_lapse_phi": raw["annual_lapse_phi"],
        "chord_source_gate": raw["chord_source_gate"],
        "lapse_drag_coherence_gate": raw["lapse_drag_coherence_gate"],
        "kappa_l": raw["kappa_l"],
    }
    return kept


def build_payload() -> dict[str, Any]:
    nominal = orb.paper_nominal_coupling()
    defensible = orb.paper_defensible_coupling()
    scored_def = _scorecard(defensible, SCORED_KEYS)
    scored_nom = _scorecard(nominal, SCORED_KEYS)
    null_def = _scorecard(defensible, NULLISH_KEYS)
    ablation = _ablation_near(defensible, scored_base=scored_def)

    head_to_head = []
    for d, n in zip(scored_def, scored_nom):
        head_to_head.append(
            {
                "case_id": d["case_id"],
                "defensible_mm_s": d["hqiv_minus_classical_mm_s"],
                "nominal_mm_s": n["hqiv_minus_classical_mm_s"],
                "delta_mm_s": d["hqiv_minus_classical_mm_s"] - n["hqiv_minus_classical_mm_s"],
                "lit_mm_s": d["lit_mm_s"],
            }
        )

    rms_resid = math.sqrt(
        sum((r["residual_mm_s"] or 0.0) ** 2 for r in scored_def) / max(len(scored_def), 1)
    )
    flags_def = _kept_flags(defensible)
    flags_nom = _kept_flags(nominal)
    return {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "phi_source": orb.PHI_SOURCE,
        "phi_hom_m_s2": orb.phi_acceleration_homogeneous_si(),
        "coupling_defensible": flags_def,
        "coupling_nominal_diff": {
            k: {"defensible": flags_def[k], "nominal": flags_nom[k]}
            for k in flags_def
            if flags_def[k] != flags_nom[k]
        },
        "scored_defensible": scored_def,
        "scored_nominal": scored_nom,
        "head_to_head_mm_s": head_to_head,
        "nullish_defensible": null_def,
        "near_ablation": ablation,
        "landing": {
            "rms_residual_vs_lit_mm_s": rms_resid,
            "near_pct_of_lit": scored_def[0]["pct_of_lit"],
            "max_abs_nominal_delta_mm_s": max(abs(h["delta_mm_s"]) for h in head_to_head),
            "inert_restores_ok": ablation["all_inert_pass"],
            "load_bearing_drops_ok": ablation["all_load_bearing_pass"],
            "verdict": (
                "defensible ≡ nominal on scored catalog; dropped flags inert; "
                "load-bearing drops move NEAR/Rosetta"
                if ablation["all_inert_pass"]
                and ablation["all_load_bearing_pass"]
                and max(abs(h["delta_mm_s"]) for h in head_to_head) <= INERT_TOL_MM_S
                else "review ablation / nominal delta"
            ),
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        type=str,
        default="",
        help="write full payload JSON (default: papers/orbital_flyby/artifacts/flyby_defensible_v1.json)",
    )
    parser.add_argument(
        "--phi-source",
        choices=("derived", "legacy"),
        default="derived",
        help="homogeneous φ source (default: derived Route-A age)",
    )
    args = parser.parse_args(argv)
    orb.PHI_SOURCE = args.phi_source

    payload = build_payload()
    _print_scorecard(
        f"Defensible coupling (φ_source={payload['phi_source']}, "
        f"φ_hom={payload['phi_hom_m_s2']:.3e} m/s²)",
        payload["scored_defensible"],
    )
    print("\nHead-to-head vs nominal (mm/s excess)")
    print(f"{'case':<16} {'defensible':>12} {'nominal':>12} {'Δ':>10}")
    print("-" * 54)
    for h in payload["head_to_head_mm_s"]:
        print(
            f"{h['case_id']:<16} {h['defensible_mm_s']:12.4f} "
            f"{h['nominal_mm_s']:12.4f} {h['delta_mm_s']:10.4f}"
        )
    _print_ablation(payload["near_ablation"])
    land = payload["landing"]
    print("\nLanding")
    print(f"  NEAR fraction of lit     : {land['near_pct_of_lit']:.1f}%")
    print(f"  RMS residual vs lit      : {land['rms_residual_vs_lit_mm_s']:.2f} mm/s")
    print(f"  max |def − nominal|      : {land['max_abs_nominal_delta_mm_s']:.4f} mm/s")
    print(f"  inert restores           : {'PASS' if land['inert_restores_ok'] else 'FAIL'}")
    print(f"  load-bearing drops       : {'PASS' if land['load_bearing_drops_ok'] else 'FAIL'}")
    print(f"  verdict                  : {land['verdict']}")

    out = Path(args.json) if args.json else (
        Path(__file__).resolve().parent.parent
        / "papers"
        / "orbital_flyby"
        / "artifacts"
        / "flyby_defensible_v1.json"
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"\nWrote {out}")
    return 0 if land["inert_restores_ok"] and land["load_bearing_drops_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
