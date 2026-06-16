#!/usr/bin/env python3
"""
Lean-aligned baryogenesis witness export.

Writes ``data/baryogenesis_witnesses.json`` for paper tables and CI audit.

Run:
  python3 scripts/hqiv_baryogenesis_witness.py
  python3 scripts/hqiv_baryogenesis_witness.py --json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import hqiv_dynamic_bulk_bbn as bulk
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "baryogenesis_witnesses.json"

QCD_SHELL = 3
REFERENCE_M = lean.REFERENCE_M


def _approx(a: float, b: float, rel: float = 1e-9, abs_tol: float = 1e-12) -> bool:
    if math.isfinite(a) and math.isfinite(b):
        return math.isclose(a, b, rel_tol=rel, abs_tol=abs_tol)
    return a == b


def lean_symbol_audit() -> dict:
    contrast = lean.cluster_binding_contrast_relative()
    dimless = lean.baryogenesis_binding_curvature_correction_dimless()
    mev = lean.baryogenesis_binding_curvature_correction()
    bind_lock = __import__("hqiv_bbn_abundances", fromlist=["cluster_binding_mev"]).cluster_binding_mev(
        lean.REFERENCE_M, 4
    )
    eta_dyn = lean.eta_at_horizon_dynamic(lean.REFERENCE_M, lean.REFERENCE_M)
    eta_base = lean.eta_at_horizon(lean.REFERENCE_M, lean.REFERENCE_M)
    return {
        "lean_modules": [
            "Hqiv.Physics.BaryogenesisDynamicBulk",
            "Hqiv.Physics.DynamicBBNBaryogenesis",
            "Hqiv.Physics.BaryogenesisWitness",
            "Hqiv.Physics.HomogeneousCurvatureSecondOrder",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
        ],
        "color_singlet_fraction": lean.color_singlet_fraction(),
        "baryon_strong_color_fraction": lean.baryon_strong_color_fraction(),
        "cluster_binding_contrast_relative": contrast,
        "binding_curvature_correction_dimless": dimless,
        "binding_curvature_correction_mev": mev,
        "mev_factorization_check": _approx(mev, dimless * bind_lock),
        "eta_at_horizon_lockin": eta_base,
        "eta_at_horizon_dynamic_lockin": eta_dyn,
        "eta10_dynamic_lockin": eta_dyn * 1e10,
        "dynamic_correction_factor": 1.0 + dimless,
        "omega_b_from_omega_m_at_lockin": lean.omega_b_from_omega_m(0.2993966731537347),
        "curvature_budget_at_xi_lockin": lean.curvature_budget_at_xi(lean.XI_LOCKIN),
        "curvature_budget_local_global_at_xi_lockin": lean.curvature_budget_local_global_at_xi(
            lean.XI_LOCKIN, lean.XI_LOCKIN
        ),
        "curvature_seed_excess_unity": lean.curvature_seed_excess(1.0),
    }


def shell_budget_audit() -> dict:
    """Per-shell curvature budget vs Lean defs (bulk integrator spine)."""
    m_lock, xi_lock, _ = bulk.find_hadronic_lockin_shell()
    rows = []
    cumulative_baryon = 0.0
    cumulative_seed = 0.0
    radiation_floor = 1.0
    for m in range(QCD_SHELL, m_lock + 1):
        xi = float(m + 1)
        omega_m_prev = (
            lean.GAMMA * cumulative_baryon
            / max(cumulative_baryon + cumulative_seed + radiation_floor, 1e-30)
            if rows
            else 0.0
        )
        shell_budget = lean.curvature_budget_at_shell(
            m,
            m_lock=m_lock,
            m_start=QCD_SHELL,
            xi=xi,
            omega_m_fraction=omega_m_prev,
        )
        b_local_global = lean.curvature_budget_local_global_at_xi(xi, xi_lock)
        combined = shell_budget * b_local_global
        seed_excess = lean.curvature_seed_excess(combined)
        rows.append(
            {
                "m": m,
                "xi": xi,
                "omega_m_fraction_prev": omega_m_prev,
                "shell_seed_budget": shell_budget,
                "B_local_global": b_local_global,
                "combined_curvature_budget": combined,
                "curvature_seed_excess": seed_excess,
                "shell_budget_lockin_is_one": _approx(shell_budget, 1.0) if m == m_lock else None,
            }
        )
        cumulative_baryon += 0.1
        cumulative_seed += 0.01
    lock_row = rows[-1]
    return {
        "shell_rows": rows,
        "lockin_shell_budget_one": _approx(lock_row["shell_seed_budget"], 1.0),
        "lockin_B_local_global_one": _approx(lock_row["B_local_global"], 1.0),
        "lockin_combined_one": _approx(lock_row["combined_curvature_budget"], 1.0),
    }


def bulk_integrator_audit() -> dict:
    result = bulk.evolve_shell_integrator()
    eta_row = bulk.eta_from_omega_b(result.baryon_matter_fraction, bulk.DEFAULT_H0_KM_S_MPC)
    omega_m = result.total_matter_fraction
    return {
        "omega_m_lockin": omega_m,
        "omega_b_lockin": result.baryon_matter_fraction,
        "omega_b_from_omega_m_check": lean.omega_b_from_omega_m(omega_m),
        "omega_b_check_pass": _approx(
            result.baryon_matter_fraction,
            lean.omega_b_from_omega_m(omega_m),
            rel=1e-12,
        ),
        "dynamic_shell_omega_m_formula_check": _approx(
            omega_m,
            lean.GAMMA
            * (result.final_cumulative_source)
            / max(result.final_cumulative_source + bulk.RADIATION_FLOOR, 1e-30),
            rel=1e-9,
        ),
        "eta_from_dynamic_bulk": eta_row,
    }


def vital_bundle_holds() -> dict:
    sym = lean_symbol_audit()
    bulk_row = bulk_integrator_audit()
    shell_row = shell_budget_audit()
    checks = {
        "color_singlet_one_third": _approx(sym["color_singlet_fraction"], 1 / 3),
        "baryon_channel_one_sixth": _approx(sym["baryon_strong_color_fraction"], 1 / 6),
        "mev_dimless_factorization": sym["mev_factorization_check"],
        "omega_b_readout": bulk_row["omega_b_check_pass"],
        "dynamic_eta_uses_dimless_not_mev": sym["dynamic_correction_factor"] < 2.0,
        "curvature_budget_unity_at_lockin": _approx(sym["curvature_budget_at_xi_lockin"], 1.0),
        "B_local_global_unity_at_lockin": _approx(sym["curvature_budget_local_global_at_xi_lockin"], 1.0),
        "curvature_seed_excess_zero_at_unity": _approx(sym["curvature_seed_excess_unity"], 0.0),
        "shell_budget_lockin_one": shell_row["lockin_shell_budget_one"],
        "lockin_combined_budget_one": shell_row["lockin_combined_one"],
    }
    return {"checks": checks, "all_pass": all(checks.values())}


def main() -> None:
    parser = argparse.ArgumentParser(description="Export baryogenesis Lean witness JSON")
    parser.add_argument("--json", action="store_true", help="Print JSON to stdout")
    parser.add_argument("-o", "--output", type=Path, default=OUT)
    args = parser.parse_args()

    payload = {
        "source": "HQIV baryogenesis Lean witness audit",
        "python_script": "scripts/hqiv_baryogenesis_witness.py",
        "lean_symbol_audit": lean_symbol_audit(),
        "shell_curvature_budget_audit": shell_budget_audit(),
        "dynamic_bulk_integrator": bulk_integrator_audit(),
        "vital_bundle": vital_bundle_holds(),
        "native_spine_modules": [
            "Hqiv.Physics.BaryogenesisDynamicBulk.baryogenesis_native_spine_vital_holds_any",
            "Hqiv.Physics.BaryogenesisDynamicBulk.curvatureBudgetLocalGlobalAtXi",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics.outsideCurvatureBindingModulatorChart",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    vital = payload["vital_bundle"]
    print(f"Wrote {args.output}")
    print(f"  vital_bundle all_pass = {vital['all_pass']}")
    for name, ok in vital["checks"].items():
        print(f"    {name}: {'OK' if ok else 'FAIL'}")
    sym = payload["lean_symbol_audit"]
    print(f"  eta10 dynamic lock-in = {sym['eta10_dynamic_lockin']:.6f}")
    print(f"  eta10 bulk comparison  = {payload['dynamic_bulk_integrator']['eta_from_dynamic_bulk']['eta10']:.6f}")

    if args.json:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
