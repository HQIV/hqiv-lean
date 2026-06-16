#!/usr/bin/env python3
"""
HQIV faithful BBN integrator.

Single entry point for paper-grade BBN statements in the HQIV model:

  1. **Lock-in network Q** — curvature binding spine (D, ³He, ⁴He, ⁷Be, ⁷Li)
  2. **Condition-dependent decay** — ``hqiv_bbn_condition_decay`` per-temperature
     release, resonance width, C₂ suppression, synthesis gates
  3. **Partition integration** — log-weighted T window with ``bbnBindingReleaseFactor``
  4. **Stratified channels** — ³He (synthesis gate), ⁷Li/⁷Be (MeV tail window)
  5. **Trimer width + stoichiometric D** — ³He Γ(T) broadening and D burn competition
     (D + p → ³He vs D + D → ⁴He vs photodissociation)

Primary abundance readout is the stoichiometric partition integrator (not the legacy
kinetic epoch network, which still over-produces ⁴He).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_bbn_integrator.py
  PYTHONPATH=scripts python3 scripts/hqiv_bbn_integrator.py --json data/bbn_integrator.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_bbn_condition_decay as decay
import hqiv_lean_physics_primitives as lean

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "bbn_integrator.json"

# Observation comparison layer (not integrator inputs)
OBS_Y_P = 0.244
OBS_Y_P_SIGMA = 0.004
OBS_DH = 2.53e-5
OBS_DH_SIGMA = 0.04e-5
OBS_HE3H = 1.0e-5
OBS_LI7H = 4.6e-10
OBS_LI7H_BAND = (1.6e-10, 4.5e-10)


@dataclass(frozen=True)
class BBNAbundanceReadout:
    Y_p: float
    D_over_H: float
    He3_over_H: float
    Be7_over_H: float
    Li7_over_H: float
    T_freeze_MeV: float
    T_freeze_effective_MeV: float
    Li7_tail_T_high_MeV: float
    Li7_tail_T_low_MeV: float
    synthesis_d_T_high_MeV: float = 0.0
    synthesis_d_T_low_MeV: float = 0.0
    synthesis_d_T_peak_MeV: float = 0.0
    stoichiometric_d_budget: bool = True
    free_neutron_curvature: bool = True
    coupled_neutron_inventory: bool = True
    tau_ratio_at_freeze: float = 1.0
    Y_p_bare_equilibrium: float = 0.0
    delta_Y_p_curvature: float = 0.0
    x_n_at_freeze: float = 0.0
    x_n_at_T_low: float = 0.0
    D_over_H_bare_uncoupled: float = 0.0
    delta_D_over_H_curvature: float = 0.0


@dataclass(frozen=True)
class BBNIntegratorConfig:
    eta: float = bbn.ETA_PAPER
    m_shell: int = decay.REFERENCE_M
    n_window_steps: int = 48
    n_tail_steps: int = 28
    n_he3_steps: int = 32
    use_binding_release: bool = True
    he3_stratified: bool = True
    use_he3_synthesis_window: bool = True
    stoichiometric_d_budget: bool = True
    T_high_MeV: float = bbn.BBN_T_HIGH_MEV
    T_low_MeV: float = bbn.BBN_T_LOW_MEV
    li7_tail_high_MeV: float = bbn.BBN_LI7_TAIL_T_HIGH_MEV
    li7_tail_low_MeV: float = bbn.BBN_LI7_TAIL_T_LOW_MEV
    use_free_neutron_curvature: bool = True
    use_coupled_neutron_inventory: bool = True
    use_synthesis_d_window: bool = True
    neutron_post_freeze_survival: bool = False


def _log_weights(temps: list[float]) -> list[float]:
    n = len(temps)
    weights: list[float] = []
    for i in range(n):
        if i == 0:
            weights.append(abs(math.log(temps[1] / temps[0])))
        elif i == n - 1:
            weights.append(abs(math.log(temps[-1] / temps[-2])))
        else:
            weights.append(abs(math.log(temps[i + 1] / temps[i - 1]) / 2.0))
    return weights


def integrate_window_stratified(
    eta: float,
    m_nucleon: float,
    Q_np: float,
    lockin: decay.LockinNetworkQ,
    cfg: BBNIntegratorConfig,
) -> BBNAbundanceReadout:
    """
    Log-weighted BBN window with trimer-width stoichiometric D and ⁷Li MeV-tail ladder.
    """
    if cfg.use_synthesis_d_window and cfg.stoichiometric_d_budget:
        temps = decay.build_synthesis_d_temperature_ladder(
            eta,
            Q_np,
            cfg.n_window_steps,
            T_high_MeV=cfg.T_high_MeV,
        )
        synth_hi, synth_lo = decay.synthesis_d_window_bounds_mev(
            eta, Q_np, T_high_MeV=cfg.T_high_MeV
        )
        synth_peak = decay.synthesis_d_window_peak_mev()
    else:
        temps = [
            cfg.T_high_MeV
            * (cfg.T_low_MeV / cfg.T_high_MeV) ** (i / (cfg.n_window_steps - 1))
            for i in range(cfg.n_window_steps)
        ]
        synth_hi, synth_lo = cfg.T_high_MeV, cfg.T_low_MeV
        synth_peak = 0.0
    weights = _log_weights(temps)
    if cfg.use_synthesis_d_window and cfg.stoichiometric_d_budget:
        d_weights = [
            w * decay.synthesis_d_window_tail_gate(T, eta, Q_np)
            for T, w in zip(temps, weights)
        ]
    else:
        d_weights = weights
    T_freeze = bbn.freezeout_temperature_mev(Q_np, eta)
    coupled_readout: decay.CoupledBBNReadout | None = None
    sto_rows: list[decay.StoichiometricAbundancesAtT] = []

    if (
        cfg.stoichiometric_d_budget
        and cfg.use_binding_release
        and cfg.use_coupled_neutron_inventory
    ):
        sto_rows, coupled_readout = decay.integrate_coupled_stoichiometric_window(
            eta,
            m_nucleon,
            Q_np,
            temps,
            weights,
            m_shell=cfg.m_shell,
            apply_he3_gate=cfg.he3_stratified,
            use_curvature=cfg.use_free_neutron_curvature,
        )
        Y_p = coupled_readout.Y_p
        T_freeze_eff = coupled_readout.T_freeze_effective_MeV
        yp_readout = decay.FreeNeutronCurvatureYpReadout(
            T_freeze_bare_MeV=coupled_readout.T_freeze_bare_MeV,
            T_freeze_effective_MeV=coupled_readout.T_freeze_effective_MeV,
            tau_ratio_at_freeze=coupled_readout.tau_ratio_at_freeze,
            outside_lifetime_ratio=decay.free_neutron_weak_environment_at_T(
                coupled_readout.T_freeze_effective_MeV
            ).outside_lifetime_ratio,
            weak_width_factor=decay.free_neutron_weak_environment_at_T(
                coupled_readout.T_freeze_effective_MeV
            ).weak_width_factor,
            x_n_equilibrium=coupled_readout.x_n_at_freeze,
            neutron_survival=coupled_readout.inventory_by_T[-1].cumulative_survival,
            x_n_after_capture=coupled_readout.x_n_at_T_low,
            Y_p=coupled_readout.Y_p,
            Y_p_bare_equilibrium=coupled_readout.Y_p_bare_equilibrium,
            delta_Y_p=coupled_readout.delta_Y_p,
            capture_time_s=decay.neutron_synthesis_capture_time_s(
                coupled_readout.T_freeze_effective_MeV, Q_np, lockin.Q_D
            ),
            tau_n_effective_s=decay.TAU_N_REFERENCE_S * coupled_readout.tau_ratio_at_freeze,
        )
    else:
        yp_readout = decay.y_p_with_free_neutron_curvature(
            eta,
            Q_np,
            lockin.Q_D,
            use_curvature=cfg.use_free_neutron_curvature,
            include_post_freeze_survival=cfg.neutron_post_freeze_survival,
        )
        Y_p = yp_readout.Y_p
        T_freeze_eff = yp_readout.T_freeze_effective_MeV

    d_vals: list[float] = []
    he3_vals: list[float] = []
    he3_li_vals: list[float] = []
    he3_w: list[float] = []
    for i, (T, w) in enumerate(zip(temps, weights)):
        cond = decay.BBNCondition(
            T_MeV=T,
            eta=eta,
            m_nucleon=m_nucleon,
            Q_np=Q_np,
            m_shell=cfg.m_shell,
        )
        if cfg.stoichiometric_d_budget and cfg.use_binding_release:
            if sto_rows:
                sto = sto_rows[i]
            else:
                inv = None
                if cfg.use_free_neutron_curvature:
                    inv_row = decay.build_coupled_inventory_march(
                        temps, eta, Q_np, use_curvature=True
                    ).inventory_by_T[i]
                    inv = inv_row
                sto = decay.deuterium_stoichiometric_abundances_at_T(
                    cond,
                    apply_he3_gate=cfg.he3_stratified,
                    apply_c2_suppression=True,
                    inventory=inv,
                )
            d_vals.append(sto.D_over_H)
            he3_vals.append(sto.He3_over_H)
            he3_li_vals.append(sto.He3_inventory_for_be7)
            he3_w.append(w)
        else:
            if cfg.use_binding_release:
                Q_D, Q_4, Q_3 = bbn.light_binding_q_at_temperature(T, m_shell=cfg.m_shell)
            else:
                Q_D, Q_4, Q_3 = lockin.Q_D, lockin.Q_4, lockin.Q_3
            row = bbn.abundances_at_epoch(
                eta,
                T,
                m_nucleon,
                Q_np,
                Q_D,
                Q_4,
                Q_3,
                Q_7=lockin.Q_7_be,
                Q_be=lockin.Q_be,
                Q_li=lockin.Q_li,
                T_freeze_mev=T_freeze_eff,
            )
            d_vals.append(row["D_over_H"])
            he3_val = row["He3_over_H"]
            gate = decay.he3_synthesis_gate(T) if cfg.he3_stratified else 1.0
            he3_vals.append(he3_val)
            he3_w.append(w * gate)

    total_w = sum(weights)
    d_total_w = sum(d_weights)
    D_over_H = sum(v * w for v, w in zip(d_vals, d_weights)) / d_total_w

    D_bare_uncoupled = D_over_H
    delta_d = 0.0
    if coupled_readout is not None:
        bare_sto, _bare = decay.integrate_coupled_stoichiometric_window(
            eta,
            m_nucleon,
            Q_np,
            temps,
            weights,
            m_shell=cfg.m_shell,
            apply_he3_gate=cfg.he3_stratified,
            use_curvature=False,
        )
        D_bare_uncoupled = sum(s.D_over_H * w for s, w in zip(bare_sto, d_weights)) / d_total_w
        delta_d = D_over_H - D_bare_uncoupled
    if (
        cfg.stoichiometric_d_budget
        and cfg.use_he3_synthesis_window
        and cfg.use_binding_release
    ):
        he3_temps = decay.build_he3_synthesis_temperature_ladder(cfg.n_he3_steps)
        he3_weights = _log_weights(he3_temps)
        he3_march = decay.build_coupled_inventory_march(
            he3_temps,
            eta,
            Q_np,
            Q_D=lockin.Q_D,
            use_curvature=cfg.use_free_neutron_curvature,
        )
        he3_inv_vals: list[float] = []
        he3_act_vals: list[float] = []
        he3_li_vals = []
        for T, inv in zip(he3_temps, he3_march.inventory_by_T):
            cond = decay.BBNCondition(
                T_MeV=T,
                eta=eta,
                m_nucleon=m_nucleon,
                Q_np=Q_np,
                m_shell=cfg.m_shell,
            )
            sto_he3 = decay.deuterium_stoichiometric_abundances_at_T(
                cond,
                apply_he3_gate=cfg.he3_stratified,
                apply_c2_suppression=True,
                inventory=inv,
            )
            wide = decay.he3_synthesis_gate(T)
            narrow = decay.he3_be7_feed_gate(T)
            be7_scale = narrow / max(wide, 1e-30) if wide > 0.0 else 0.0
            he3_inv_vals.append(sto_he3.He3_inventory_for_be7)
            he3_act_vals.append(sto_he3.He3_over_H)
            he3_li_vals.append(sto_he3.He3_inventory_for_be7 * be7_scale)
        he3_total_w = sum(he3_weights)
        He3_over_H = sum(v * w for v, w in zip(he3_inv_vals, he3_weights)) / he3_total_w
        He3_for_be7 = sum(v * w for v, w in zip(he3_li_vals, he3_weights)) / he3_total_w
    else:
        he3_denom = sum(he3_w)
        if he3_denom > 0.0:
            He3_over_H = sum(v * w for v, w in zip(he3_vals, he3_w)) / he3_denom
        else:
            He3_over_H = sum(v * w for v, w in zip(he3_vals, weights)) / total_w

        if cfg.stoichiometric_d_budget and he3_li_vals:
            he3_li_denom = sum(he3_w)
            He3_for_be7 = (
                sum(v * w for v, w in zip(he3_li_vals, he3_w)) / he3_li_denom
                if he3_li_denom > 0.0
                else He3_over_H
            )
        else:
            He3_for_be7 = He3_over_H

    li_tail = bbn.integrate_be7_li7_tail_window(
        eta,
        m_nucleon,
        Q_np,
        lockin.Q_D,
        lockin.Q_4,
        lockin.Q_3,
        lockin.Q_7_be,
        lockin.Q_be,
        lockin.Q_li,
        n_steps=cfg.n_tail_steps,
        T_high=cfg.li7_tail_high_MeV,
        T_low=cfg.li7_tail_low_MeV,
        use_binding_release=cfg.use_binding_release,
        m_shell=cfg.m_shell,
        he3_over_h=He3_for_be7,
    )
    return BBNAbundanceReadout(
        Y_p=Y_p,
        D_over_H=D_over_H,
        He3_over_H=He3_over_H,
        Be7_over_H=li_tail["Be7_over_H"],
        Li7_over_H=li_tail["Li7_over_H"],
        T_freeze_MeV=T_freeze,
        T_freeze_effective_MeV=T_freeze_eff,
        Li7_tail_T_high_MeV=cfg.li7_tail_high_MeV,
        Li7_tail_T_low_MeV=cfg.li7_tail_low_MeV,
        synthesis_d_T_high_MeV=synth_hi,
        synthesis_d_T_low_MeV=synth_lo,
        synthesis_d_T_peak_MeV=synth_peak,
        stoichiometric_d_budget=cfg.stoichiometric_d_budget,
        free_neutron_curvature=cfg.use_free_neutron_curvature,
        coupled_neutron_inventory=cfg.use_coupled_neutron_inventory,
        tau_ratio_at_freeze=yp_readout.tau_ratio_at_freeze,
        Y_p_bare_equilibrium=yp_readout.Y_p_bare_equilibrium,
        delta_Y_p_curvature=yp_readout.delta_Y_p,
        x_n_at_freeze=coupled_readout.x_n_at_freeze if coupled_readout else 0.0,
        x_n_at_T_low=coupled_readout.x_n_at_T_low if coupled_readout else 0.0,
        D_over_H_bare_uncoupled=D_bare_uncoupled,
        delta_D_over_H_curvature=delta_d,
    )


def z_score(model: float, obs: float, sigma: float) -> float | None:
    if sigma <= 0.0 or not math.isfinite(model):
        return None
    return (model - obs) / sigma


def observation_comparison(readout: BBNAbundanceReadout) -> dict[str, Any]:
    coc = bbn.coc2015_abundances(bbn.ETA_PAPER)
    return {
        "policy": "observation targets are not integrator inputs",
        "Y_p": {
            "model": readout.Y_p,
            "observed": OBS_Y_P,
            "sigma": OBS_Y_P_SIGMA,
            "z_score": z_score(readout.Y_p, OBS_Y_P, OBS_Y_P_SIGMA),
        },
        "D_over_H": {
            "model": readout.D_over_H,
            "observed": OBS_DH,
            "sigma": OBS_DH_SIGMA,
            "z_score": z_score(readout.D_over_H, OBS_DH, OBS_DH_SIGMA),
            "coc2015": coc["D_over_H"],
        },
        "He3_over_H": {
            "model": readout.He3_over_H,
            "observed_order": OBS_HE3H,
            "coc2015": coc["He3_over_H"],
            "notes": (
                "³He from stoichiometric D burn with trimer width Γ(T); "
                "synthesis gate when he3_stratified=True"
            ),
        },
        "Li7_over_H": {
            "model": readout.Li7_over_H,
            "observed_band": list(OBS_LI7H_BAND),
            "coc2015": coc["Li7_over_H"],
            "notes": "pre-astrophysical-depletion; network ³He+⁴He→⁷Be→⁷Li ladder",
        },
        "Be7_over_H": {
            "model": readout.Be7_over_H,
            "notes": "relic ⁷Be after partial capture; should be ≪ ⁷Li/H",
        },
    }


def run_bbn_integrator(cfg: BBNIntegratorConfig | None = None) -> dict[str, Any]:
    cfg = cfg or BBNIntegratorConfig()
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    Q_np = float(w["derivedDeltaM_MeV"])
    lockin = decay.LockinNetworkQ.from_proton_mass(m_p, cfg.m_shell)

    readout = integrate_window_stratified(cfg.eta, m_p, Q_np, lockin, cfg)
    decay_table = decay.build_condition_decay_table(
        cfg.eta, m_p, Q_np, m_shell=cfg.m_shell
    )
    key_temps = [1.0, 0.3, 0.1, 0.05, 0.01]
    key_rows = [
        decay.condition_decay_row(
            decay.BBNCondition(
                T_MeV=T, eta=cfg.eta, m_nucleon=m_p, Q_np=Q_np, m_shell=cfg.m_shell
            ),
            lockin,
        )
        for T in key_temps
    ]

    return {
        "source": "HQIV faithful BBN integrator (partition + condition-dependent decay)",
        "lean_modules": [
            "Hqiv.Physics.BBNNetworkFromWeights",
            "Hqiv.Physics.DynamicBBNBaryogenesis",
            "Hqiv.Physics.BBNEpochEvolution",
            "Hqiv.Physics.BBNEpochNetwork",
            "Hqiv.Physics.NuclearCurvatureBinding",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.BBNStoichiometricIntegrator",
        ],
        "python_scripts": [
            "scripts/hqiv_bbn_integrator.py",
            "scripts/hqiv_bbn_condition_decay.py",
            "scripts/hqiv_bbn_abundances.py",
            "scripts/hqiv_curvature_binding_core.py",
        ],
        "integrator_config": asdict(cfg),
        "hqiv_inputs": {
            "eta": cfg.eta,
            "referenceM": cfg.m_shell,
            "derivedProtonMass_MeV": m_p,
            "derivedDeltaM_MeV": Q_np,
            "lockin_network_Q_MeV": asdict(lockin),
            "T_freeze_MeV": readout.T_freeze_MeV,
            "T_freeze_effective_MeV": readout.T_freeze_effective_MeV,
            "T_bottleneck_MeV": lean.bbn_dynamic_c2_bottleneck_t_mev(cfg.eta, Q_np),
        },
        "synthesis_d_window": {
            "enabled": cfg.use_synthesis_d_window and cfg.stoichiometric_d_budget,
            "T_high_MeV": readout.synthesis_d_T_high_MeV,
            "T_peak_MeV": readout.synthesis_d_T_peak_MeV,
            "T_low_MeV": readout.synthesis_d_T_low_MeV,
            "tail_gate": "synthesis_d_window_tail_gate (unity ≥ T_peak; linear fade T_bn→T_peak)",
            "notes": (
                "D/H log-weighted over MeV synthesis through T_bn; below ³He mid-gate "
                "T_peak weights taper (thermal crush tail). n+p→D capture + strong deposition "
                "boost γ·strong·(1+g_np+c₂); Y_p from post-synthesis neutron inventory."
            ),
        },
        "he3_synthesis_window": {
            "enabled": cfg.use_he3_synthesis_window and cfg.stoichiometric_d_budget,
            "T_high_MeV": decay.he3_synthesis_window_bounds_mev()[0],
            "T_low_MeV": decay.he3_synthesis_window_bounds_mev()[1],
            "notes": "³He/H integrated on 0.45→0.05 MeV ladder (extended synthesis gate).",
        },
        "free_neutron_curvature_channel": {
            "enabled": cfg.use_free_neutron_curvature,
            "coupled_inventory": cfg.use_coupled_neutron_inventory,
            "post_freeze_survival": cfg.neutron_post_freeze_survival,
            "tau_ratio_at_freeze": readout.tau_ratio_at_freeze,
            "x_n_at_freeze": readout.x_n_at_freeze,
            "x_n_at_T_low": readout.x_n_at_T_low,
            "Y_p_bare_equilibrium": readout.Y_p_bare_equilibrium,
            "delta_Y_p": readout.delta_Y_p_curvature,
            "D_over_H_bare_uncoupled": readout.D_over_H_bare_uncoupled,
            "delta_D_over_H": readout.delta_D_over_H_curvature,
            "lean_modules": [
                "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
                "Hqiv.Physics.BBNStoichiometricIntegrator",
            ],
            "notes": (
                "Unified march: outside modulator + ν-width set τ_n(T); inventory scales "
                "n+p→D and D+D→⁴He; Y_p and D/H from the same x_n ladder."
            ),
        },
        "abundance_readout": asdict(readout),
        "observation_comparison": observation_comparison(readout),
        "condition_decay_key_epochs": [decay.row_to_dict(r) for r in key_rows],
        "condition_decay_ladder_summary": {
            "n_steps": len(decay_table),
            "T_high_MeV": decay_table[0].condition.T_MeV,
            "T_low_MeV": decay_table[-1].condition.T_MeV,
            "release_at_T_high": decay_table[0].effective_q.release_factor,
            "release_at_T_low": decay_table[-1].effective_q.release_factor,
            "width_8be_erosion_lockin_MeV": decay_table[0].widths.resonance_8be_erosion_mev,
            "width_8be_erosion_at_T_low_MeV": decay_table[-1].widths.resonance_8be_erosion_at_T_mev,
            "trimer_3he_width_lockin_MeV": decay_table[0].widths.trimer_3he_width_lockin_mev,
            "trimer_3he_width_at_T_high_MeV": decay_table[0].widths.trimer_3he_width_at_T_mev,
        },
        "paper_statements": {
            "primary_abundance_method": (
                "Log-weighted stoichiometric D budget over synthesis window "
                "(T=1→T_C₂) with coupled inventory and n+p→D capture; "
                "⁷Li/⁷Be MeV-tail ladder separate."
            ),
            "decay_spine": (
                "bbnBindingReleaseFactor(T) modulates lock-in Q; trimer_resonance_width_mev "
                "broadens ³He at epoch T; multi-α width on ⁸Be; ⁷Be→⁷Li from |Q_Be−Q_Li|; "
                "free-neutron outside curvature shifts weak freeze-out (τ_ratio^(1/5))."
            ),
            "honesty": (
                "⁷Li/H is pre-astrophysical-depletion. Kinetic epoch network remains diagnostic. "
                "Observation comparison is a readout layer, not a fit target."
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV faithful BBN integrator")
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON, help="Witness JSON path")
    parser.add_argument("--no-he3-stratified", action="store_true")
    parser.add_argument("--no-release", action="store_true")
    parser.add_argument(
        "--partition-only",
        action="store_true",
        help="Disable stoichiometric D budget (legacy uncoupled partition)",
    )
    parser.add_argument(
        "--no-neutron-curvature",
        action="store_true",
        help="Disable free-neutron outside-curvature freeze-out shift on Y_p",
    )
    parser.add_argument(
        "--neutron-survival",
        action="store_true",
        help="Include second-order post-freeze β decay (strong-channel shielded)",
    )
    args = parser.parse_args()

    cfg = BBNIntegratorConfig(
        he3_stratified=not args.no_he3_stratified,
        use_binding_release=not args.no_release,
        stoichiometric_d_budget=not args.partition_only,
        use_free_neutron_curvature=not args.no_neutron_curvature,
        neutron_post_freeze_survival=args.neutron_survival,
    )
    payload = run_bbn_integrator(cfg)

    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")

    r = payload["abundance_readout"]
    cmp_ = payload["observation_comparison"]
    print(f"Wrote {args.json}")
    print("\nHQIV faithful BBN integrator")
    print(f"  η = {cfg.eta:.3e}  T_freeze = {r['T_freeze_MeV']:.4f} MeV")
    if r.get("free_neutron_curvature"):
        print(
            f"  T_freeze(eff) = {r['T_freeze_effective_MeV']:.4f} MeV  "
            f"τ_ratio = {r['tau_ratio_at_freeze']:.4f}  ΔY_p = {r['delta_Y_p_curvature']:+.5f}"
        )
    print(f"  Y_p     = {r['Y_p']:.5f}  (obs {OBS_Y_P})")
    print(f"  D/H     = {r['D_over_H']:.4e}  (obs {OBS_DH:.2e})")
    print(f"  ³He/H   = {r['He3_over_H']:.4e}  (obs ~{OBS_HE3H:.1e})")
    print(f"  ⁷Be/H  = {r['Be7_over_H']:.4e}")
    print(f"  ⁷Li/H  = {r['Li7_over_H']:.4e}  (obs band {OBS_LI7H_BAND[0]:.1e}–{OBS_LI7H_BAND[1]:.1e})")
    z = cmp_["D_over_H"].get("z_score")
    if z is not None:
        print(f"  D/H z-score = {z:.2f}")


if __name__ == "__main__":
    main()
