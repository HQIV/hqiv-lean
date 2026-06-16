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

import hqiv_bbn_condition_decay as decay
import hqiv_bbn_integrator as faithful
import hqiv_dynamic_bulk_bbn as bulk
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "integrator_lean_audit.json"
FAITHFUL_JSON = ROOT / "data" / "bbn_integrator.json"

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


def stoichiometric_spine_audit() -> dict:
    """Python ↔ Lean name map for ``BBNStoichiometricIntegrator.lean``."""
    eta = lean.ETA_PAPER
    Q_np = lean.bbn_neutron_proton_gap_mev()
    T = 0.2
    return {
        "lean_module": "Hqiv.Physics.BBNStoichiometricIntegrator",
        "python_module": "scripts/hqiv_bbn_condition_decay.py",
        "constants": {
            "bbnSynthesisDWindowHighMeV": 1.0,
            "bbnHe3SynthesisLowMeV": decay.HE3_SYNTH_LOW_MEV,
            "bbnHe3SynthesisMidMeV": decay.HE3_SYNTH_MID_MEV,
            "bbnHe3SynthesisHighMeV": decay.HE3_SYNTH_HIGH_MEV,
            "bbnHe3Be7FeedMidMeV": 0.15,
            "bbnHe3Be7FeedHighMeV": 0.35,
            "bbnAlphaSynthesisGateLowMeV": 0.035,
            "bbnAlphaSynthesisGateWidthMeV": 0.06,
        },
        "gate_samples_at_T_0p2_MeV": {
            "bbnHe3SynthesisGate": decay.he3_synthesis_gate(T),
            "bbnHe3Be7FeedGate": decay.he3_be7_feed_gate(T),
            "bbnAlphaSynthesisGate": decay.alpha_synthesis_gate(T),
            "bbnNpToDeuteriumSynthesisGate": decay.np_to_deuterium_synthesis_gate(T, eta, Q_np),
            "bbnSynthesisDWindowTailGate": decay.synthesis_d_window_tail_gate(T, eta, Q_np),
            "bbnDynamicC2OpportunitySuppression": lean.bbn_dynamic_c2_opportunity_suppression(
                T, eta=eta, m_nucleon=938.272
            ),
        },
        "strong_deposition_boost": {
            "bbnSynthesisStrongDepositionBoost": decay.synthesis_strong_deposition_boost(
                decay.np_to_deuterium_synthesis_gate(T, eta, Q_np),
                lean.bbn_dynamic_c2_opportunity_suppression(T, eta=eta, m_nucleon=938.272),
            ),
        },
        "window_bounds": {
            "bbnSynthesisDWindowLowMeV": decay.synthesis_window_end_mev(eta, Q_np),
            "bbnSynthesisDWindowPeakMeV": decay.synthesis_d_window_peak_mev(),
            "bbnHe3SynthesisWindowHighMeV": decay.he3_synthesis_window_bounds_mev()[0],
            "bbnHe3SynthesisWindowLowMeV": decay.he3_synthesis_window_bounds_mev()[1],
        },
        "python_to_lean": [
            ["HE3_SYNTH_LOW_MEV", "bbnHe3SynthesisLowMeV"],
            ["HE3_SYNTH_MID_MEV", "bbnHe3SynthesisMidMeV"],
            ["HE3_SYNTH_HIGH_MEV", "bbnHe3SynthesisHighMeV"],
            ["he3_synthesis_gate", "bbnHe3SynthesisGate"],
            ["he3_be7_feed_gate", "bbnHe3Be7FeedGate"],
            ["alpha_synthesis_gate", "bbnAlphaSynthesisGate"],
            ["np_to_deuterium_synthesis_gate", "bbnNpToDeuteriumSynthesisGate"],
            ["synthesis_d_window_tail_gate", "bbnSynthesisDWindowTailGate"],
            ["synthesis_strong_deposition_boost", "bbnSynthesisStrongDepositionBoost"],
            ["trimer_width_suppress_at_T", "bbnTrimerWidthStrongSuppressAtT"],
            ["synthesis_window_end_mev", "bbnSynthesisWindowEndMeV"],
            ["bbn_binding_release_factor", "bbnBindingReleaseFactor"],
            ["bbn_dynamic_c2_opportunity_suppression", "bbnDynamicC2OpportunitySuppression"],
        ],
    }


def faithful_bbn_audit() -> dict:
    payload = faithful.run_bbn_integrator()
    r = payload["abundance_readout"]
    obs = payload.get("observation_comparison", {})
    return {
        "integrator": "hqiv_bbn_integrator.py",
        "payload_path": "data/bbn_integrator.json",
        "eta": payload["hqiv_inputs"]["eta"],
        "eta10": payload["hqiv_inputs"]["eta"] * 1e10,
        "Yp": r["Y_p"],
        "D_over_H": r["D_over_H"],
        "He3_over_H": r["He3_over_H"],
        "Li7_over_H": r["Li7_over_H"],
        "opportunity_mode": "synthesis_window_stoichiometric_inventory",
        "synthesis_d_window": payload.get("synthesis_d_window"),
        "he3_synthesis_window": payload.get("he3_synthesis_window"),
        "free_neutron_curvature_channel": payload.get("free_neutron_curvature_channel"),
        "observation_comparison": obs,
        "z_scores": {
            "Yp": obs.get("Y_p", {}).get("z_score"),
            "D_over_H": obs.get("D_over_H", {}).get("z_score"),
            "He3_over_H": obs.get("He3_over_H", {}).get("z_score"),
            "Li7_over_H": obs.get("Li7_over_H", {}).get("z_score"),
        },
        "lean_modules": payload.get("lean_modules"),
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
    faithful_row = faithful_bbn_audit()
    bulk_row = dynamic_bulk_audit(network_steps)
    return {
        "source": "HQIV integrator ↔ Lean witness audit",
        "python_script": "scripts/hqiv_integrator_lean_audit.py",
        "policy": (
            "Comparison targets (Coc et al. band) are not integrator inputs. "
            "Faithful BBN integrator: synthesis-window D/H, coupled neutron inventory, "
            "post-synthesis Y_p. Dynamic bulk row retained for C₂ decomposition scaffold."
        ),
        **const,
        "stoichiometric_spine": stoichiometric_spine_audit(),
        "faithful_bbn_integrator": faithful_row,
        "dynamic_bulk_bbn": bulk_row,
        "paper_record": {
            "recommended_citation_row": {
                "eta10": faithful_row["eta10"],
                "Yp": faithful_row["Yp"],
                "D_over_H": faithful_row["D_over_H"],
                "He3_over_H": faithful_row["He3_over_H"],
                "Li7_over_H": faithful_row["Li7_over_H"],
                "driver": "hqiv_bbn_integrator (BBNStoichiometricIntegrator mirror)",
                "payload": "data/bbn_integrator.json",
            },
            "legacy_dynamic_bulk_row": {
                "eta10": bulk_row["eta10"],
                "Omega_b": bulk_row["Omega_b"],
                "Yp": bulk_row["Yp"],
                "D_over_H": bulk_row["D_over_H"],
                "driver": "bbnShellReactionOpportunity_dynamic_integrator (scaffold)",
                "notes": "Pre-synthesis-window bulk integrator; D/H understates faithful readout.",
            },
            "formulas": {
                "kappa6": "eta_paper * B_curv(xi) * gamma * C2(xi)",
                "T_bottleneck": "gamma * (4/8) * T_freeze(eta)",
                "T_ref": "T_freeze(eta)",
                "w(T)": "gamma * (4/8) * Q_D_eff(T) / Q_np",
                "c2_suppression": "(kappa6_ref/kappa6)^w for T <= T_bottleneck(eta)",
                "integrator_opportunity": "base_shell * (1 + delta_bind/4) * c2_suppression",
                "synthesis_d_window": (
                    "log-weight D/H over 1.0→T_bn with tail_gate(T_bn→T_peak) below ³He mid"
                ),
                "Y_p_readout": "2 x_n/(1+x_n) at post-synthesis T_low (coupled inventory march)",
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
    print("Faithful BBN integrator (recommended citation row):")
    print(f"  eta10   = {row['eta10']:.4f}  (obs {OBS['eta10']})")
    print(f"  Y_p     = {row['Yp']:.5f}  (obs {OBS['Yp']})")
    print(f"  D/H     = {row['D_over_H']:.4e}  (obs {OBS['D_over_H']:.2e})")
    print(f"  ³He/H   = {row['He3_over_H']:.4e}")
    print(f"  ⁷Li/H  = {row['Li7_over_H']:.4e}")
    zs = payload["faithful_bbn_integrator"]["z_scores"]
    print(f"  z(D/H)  = {zs['D_over_H']:+.2f}")
    legacy = payload["paper_record"]["legacy_dynamic_bulk_row"]
    print("Legacy dynamic bulk (scaffold only):")
    print(f"  D/H     = {legacy['D_over_H']:.3e}")


if __name__ == "__main__":
    main()
