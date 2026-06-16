#!/usr/bin/env python3
"""
Export BBN paper tables: provider decomposition, η sweep, sensitivity.

Writes ``data/bbn_paper_tables.json`` for ``papers/bbn/``.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_bbn_paper_tables.py
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_bbn_condition_decay as decay
import hqiv_bbn_integrator as integrator

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "bbn_paper_tables.json"
ETA_PAPER = bbn.ETA_PAPER


def _readout(cfg: integrator.BBNIntegratorConfig) -> dict[str, float]:
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    Q_np = float(w["derivedDeltaM_MeV"])
    lockin = decay.LockinNetworkQ.from_proton_mass(m_p, cfg.m_shell)
    r = integrator.integrate_window_stratified(cfg.eta, m_p, Q_np, lockin, cfg)
    return {
        "Y_p": r.Y_p,
        "D_over_H": r.D_over_H,
        "He3_over_H": r.He3_over_H,
        "Li7_over_H": r.Li7_over_H,
    }


def provider_decomposition() -> list[dict[str, Any]]:
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    Q_np = float(w["derivedDeltaM_MeV"])
    lockin = decay.LockinNetworkQ.from_proton_mass(m_p)
    T_f = 0.715
    part = bbn.abundances_at_epoch(
        ETA_PAPER,
        T_f,
        m_p,
        Q_np,
        lockin.Q_D,
        lockin.Q_4,
        lockin.Q_3,
        Q_7=lockin.Q_7_be,
        Q_be=lockin.Q_be,
        Q_li=lockin.Q_li,
    )
    rows: list[dict[str, Any]] = [
        {
            "layer": "lockin_Q_at_freeze",
            "label": "Lock-in $Q$ at $T_\\mathrm{freeze}$",
            "D_over_H": part["D_over_H"],
            "notes": "Static partition; no window integral",
        },
        {
            "layer": "hybrid_Q_T_partition",
            "label": "Hybrid $Q(T)$ release, partition window",
            **_readout(
                integrator.BBNIntegratorConfig(
                    use_binding_release=True,
                    stoichiometric_d_budget=False,
                )
            ),
        },
        {
            "layer": "stoichiometric_C2_full_window",
            "label": "Stoichiometric + $C_2$, full $1\\to 0.01$ MeV",
            **_readout(
                integrator.BBNIntegratorConfig(
                    use_binding_release=True,
                    stoichiometric_d_budget=True,
                    use_synthesis_d_window=False,
                    use_free_neutron_curvature=False,
                    use_coupled_neutron_inventory=False,
                )
            ),
        },
        {
            "layer": "synthesis_window_uncoupled",
            "label": "Synthesis window + $C_2$, uncoupled inventory",
            **_readout(
                integrator.BBNIntegratorConfig(
                    use_binding_release=True,
                    stoichiometric_d_budget=True,
                    use_synthesis_d_window=True,
                    use_free_neutron_curvature=False,
                    use_coupled_neutron_inventory=False,
                )
            ),
        },
        {
            "layer": "faithful_full",
            "label": "Faithful integrator (coupled inventory + curvature)",
            **_readout(integrator.BBNIntegratorConfig()),
        },
    ]
    return rows


def eta_sweep() -> list[dict[str, float]]:
    out: list[dict[str, float]] = []
    for eta10 in (5.8, 5.9, 6.0, 6.1, 6.2, 6.3, 6.4):
        eta = eta10 * 1e-10
        row = _readout(integrator.BBNIntegratorConfig(eta=eta))
        row["eta10"] = eta10
        out.append(row)
    return out


def sensitivity() -> dict[str, list[dict[str, float]]]:
    import hqiv_bbn_condition_decay as dmod
    import hqiv_lean_physics_primitives as lean

    base_gamma = lean.GAMMA
    base_strong = lean.STRONG_CHANNEL_FRACTION

    def run_with(*, gamma: float | None = None, strong: float | None = None) -> dict[str, float]:
        if gamma is not None:
            lean.GAMMA = gamma
            dmod.GAMMA = gamma
        if strong is not None:
            lean.STRONG_CHANNEL_FRACTION = strong
            dmod.STRONG = strong
        try:
            return _readout(integrator.BBNIntegratorConfig())
        finally:
            lean.GAMMA = base_gamma
            lean.STRONG_CHANNEL_FRACTION = base_strong
            dmod.GAMMA = base_gamma
            dmod.STRONG = base_strong

    gamma_rows = [
        {"gamma": g, **run_with(gamma=g)} for g in (0.36, 0.40, 0.44)
    ]
    strong_rows = [
        {"w_strong": s, **run_with(strong=s)} for s in (0.45, 0.50, 0.55)
    ]
    li7_gate_rows = []
    for strat, win in ((False, False), (False, True), (True, False), (True, True)):
        r = _readout(
            integrator.BBNIntegratorConfig(
                he3_stratified=strat,
                use_he3_synthesis_window=win,
            )
        )
        li7_gate_rows.append(
            {
                "he3_stratified": strat,
                "he3_synthesis_window": win,
                **r,
            }
        )
    return {
        "gamma": gamma_rows,
        "w_strong": strong_rows,
        "he3_gates": li7_gate_rows,
    }


def build_payload() -> dict[str, Any]:
    env = decay.free_neutron_weak_environment_at_T(0.715)
    return {
        "source": "BBN paper tables (faithful integrator)",
        "python_script": "scripts/hqiv_bbn_paper_tables.py",
        "eta_paper": ETA_PAPER,
        "eta10_paper": ETA_PAPER * 1e10,
        "tau_n_reference_s": decay.TAU_N_REFERENCE_S,
        "tau_ratio_at_freeze_witness": env.tau_ratio_vs_lockin,
        "weak_width_factor_at_freeze": env.weak_width_factor,
        "provider_decomposition": provider_decomposition(),
        "eta_sweep": eta_sweep(),
        "sensitivity": sensitivity(),
        "observation_anchors": {
            "Y_p_center": 0.244,
            "Y_p_sigma": 0.004,
            "D_over_H": 2.53e-5,
            "D_over_H_sigma": 0.04e-5,
            "Li7_band": [1.6e-10, 4.5e-10],
        },
    }


def main() -> None:
    payload = build_payload()
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    full = payload["provider_decomposition"][-1]
    print(f"Wrote {OUT}")
    print(f"Faithful D/H = {full['D_over_H']:.4e}  Y_p = {full['Y_p']:.5f}")


if __name__ == "__main__":
    main()
