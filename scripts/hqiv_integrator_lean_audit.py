#!/usr/bin/env python3
"""
Audit HQIV Python integrators against Lean-named witnesses.

Writes ``data/integrator_lean_audit.json`` for paper tables and CI.

Run:
  python3 scripts/hqiv_integrator_lean_audit.py
  python3 scripts/hqiv_integrator_lean_audit.py --json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import hqiv_dynamic_bulk_bbn as bulk
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "integrator_lean_audit.json"

OBS = {
    "eta10": 6.10,
    "eta10_sigma": 0.06,
    "Yp": 0.244,
    "Yp_sigma": 0.004,
    "D_over_H": 2.53e-5,
    "D_over_H_sigma": 0.04e-5,
    "Omega_b": 0.049,
}


def z_score(model: float, obs: float, sigma: float) -> float:
    if sigma <= 0:
        return 0.0
    return (model - obs) / sigma


def lean_constants_audit() -> dict:
    c2_lock = lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN)
    return {
        "lean_alignment": [
            "Hqiv.Physics.HopfShellBeltramiMassBridge.tuftHopfKappa6AtXi",
            "Hqiv.Physics.HopfShellBeltramiMassBridge.tuftLapseConcentrationAtXi",
            "Hqiv.Physics.DynamicBBNBaryogenesis.bbnDynamicC2OpportunitySuppression",
            "Hqiv.Physics.DynamicBBNBaryogenesis.bbnShellReactionOpportunity_dynamic_integrator",
        ],
        "constants": {
            "alpha": lean.ALPHA,
            "gamma": lean.GAMMA,
            "eta_paper": lean.ETA_PAPER,
            "xi_lockin": lean.XI_LOCKIN,
            "referenceM": lean.REFERENCE_M,
            "C2_at_xi_lockin": c2_lock,
            "C2_at_xi_lockin_expected": 56.0 / 45.0,
            "C2_lockin_match": abs(c2_lock - 56.0 / 45.0) < 1e-9,
        },
        "bbn_dynamic_C2_at_eta10_6p2": {
            "eta": 6.2e-10,
            "T_freeze_MeV": lean.bbn_dynamic_c2_freezeout_t_mev(6.2e-10),
            "T_bottleneck_MeV": lean.bbn_dynamic_c2_bottleneck_t_mev(6.2e-10),
            "lapse_exponent_at_0p1_MeV": lean.bbn_dynamic_c2_lapse_exponent(
                6.2e-10, T_MeV=0.1
            ),
            "lapse_exponent_at_freeze": lean.bbn_dynamic_c2_lapse_exponent(
                6.2e-10, T_MeV=lean.bbn_dynamic_c2_freezeout_t_mev(6.2e-10)
            ),
        },
        "bbn_dynamic_C2_ladder": [
            lean.bbn_dynamic_c2_readout_at_T(T, eta=6.2e-10, m_nucleon=938.272)
            for T in (10.0, 1.0, 0.15, 0.1, 0.01)
        ],
    }


def dynamic_bulk_audit(network_steps: int = 400) -> dict:
    integrator = bulk.evolve_shell_integrator()
    eta_layer = bulk.eta_from_omega_b(integrator.baryon_matter_fraction, bulk.DEFAULT_H0_KM_S_MPC)
    dynamic_bbn = bulk.run_dynamic_bbn_suite(
        eta_layer["eta"],
        integrator,
        network_steps=network_steps,
        use_dynamic_providers=True,
    )
    net = dynamic_bbn["cooling_network"]
    obs_cmp = bulk.observation_comparison_layer(eta_layer, integrator, dynamic_bbn)
    return {
        "integrator": "hqiv_dynamic_bulk_bbn.py",
        "payload_path": "data/dynamic_bulk_bbn_v2.json",
        "eta10": eta_layer["eta10"],
        "Omega_b": integrator.baryon_matter_fraction,
        "Yp": net["Yp"],
        "D_over_H": net["D_over_H"],
        "opportunity_mode": "shell_curvature_casimir_dynamic_C2",
        "observation_comparison": obs_cmp,
        "z_scores": {
            "eta10": z_score(eta_layer["eta10"], OBS["eta10"], OBS["eta10_sigma"]),
            "Yp": z_score(net["Yp"], OBS["Yp"], OBS["Yp_sigma"]),
            "D_over_H": z_score(net["D_over_H"], OBS["D_over_H"], OBS["D_over_H_sigma"]),
        },
        "lockin": dynamic_bbn["inputs_at_lockin"],
    }


def build_payload(network_steps: int) -> dict:
    const = lean_constants_audit()
    bulk_row = dynamic_bulk_audit(network_steps)
    return {
        "source": "HQIV integrator ↔ Lean witness audit",
        "python_script": "scripts/hqiv_integrator_lean_audit.py",
        "policy": (
            "Comparison targets (Coc et al. band) are not integrator inputs. "
            "B_curv sets eta/Omega_b; dynamic C2 sets D/H in the MeV bottleneck."
        ),
        **const,
        "dynamic_bulk_bbn": bulk_row,
        "paper_record": {
            "recommended_citation_row": {
                "eta10": bulk_row["eta10"],
                "Omega_b": bulk_row["Omega_b"],
                "Yp": bulk_row["Yp"],
                "D_over_H": bulk_row["D_over_H"],
                "driver": "bbnShellReactionOpportunity_dynamic_integrator (Python mirror)",
            },
            "formulas": {
                "kappa6": "eta_paper * B_curv(xi) * gamma * C2(xi)",
                "T_bottleneck": "gamma * (4/8) * T_freeze(eta)",
                "T_ref": "T_freeze(eta)",
                "w(T)": "gamma * (4/8) * Q_D_eff(T) / Q_np",
                "c2_suppression": "(kappa6_ref/kappa6)^w for T <= T_bottleneck(eta)",
                "integrator_opportunity": "base_shell * (1 + delta_bind/4) * c2_suppression",
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Integrator ↔ Lean audit")
    parser.add_argument("--json", action="store_true", help="Print JSON to stdout")
    parser.add_argument("--network-steps", type=int, default=400)
    parser.add_argument("--out", type=Path, default=OUT)
    args = parser.parse_args()

    payload = build_payload(args.network_steps)
    if args.json:
        print(json.dumps(payload, indent=2))
        return

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n")
    row = payload["paper_record"]["recommended_citation_row"]
    print(f"Wrote {args.out}")
    print("Dynamic bulk + dynamic C₂ (observation comparison):")
    print(f"  eta10   = {row['eta10']:.4f}  (obs {OBS['eta10']})")
    print(f"  Omega_b = {row['Omega_b']:.5f}  (obs {OBS['Omega_b']})")
    print(f"  Y_p     = {row['Yp']:.4f}  (obs {OBS['Yp']})")
    print(f"  D/H     = {row['D_over_H']:.3e}  (obs {OBS['D_over_H']:.2e})")
    zs = payload["dynamic_bulk_bbn"]["z_scores"]
    print(f"  z(D/H)  = {zs['D_over_H']:+.2f}")


if __name__ == "__main__":
    main()
