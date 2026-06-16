#!/usr/bin/env python3
"""
HQIV BBN condition-dependent decay widths, thermal rates, and epoch readouts.

Faithful Python mirror of the Lean BBN + nuclear-outside spine:

  • ``Hqiv.Physics.DynamicBBNBaryogenesis`` — release, C₂, shell opportunity
  • ``Hqiv.Physics.BBNNetworkFromWeights`` — formation / capture Q
  • ``Hqiv.Physics.NuclearCurvatureBinding`` — multi-α resonance width
  • ``Hqiv.Physics.NuclearOutsideTemperatureDynamics`` — outside release, weak width
  • ``Hqiv.Physics.SpinStatistics`` — ``resonance_half_life`` from width scale

Used by ``hqiv_bbn_integrator.py``.  Comparison targets (Coc2015 / observations) are
never fit inputs.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_bbn_condition_decay.py
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_bbn_epoch_network as epoch_net
import hqiv_curvature_binding_core as cbc
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as notd

REFERENCE_M = hes.REFERENCE_M
HBAR_MEV_S = 6.582119569e-22
GAMMA = lean.GAMMA
STRONG = lean.STRONG_CHANNEL_FRACTION
# Laboratory neutron lifetime (comparison anchor; not an integrator fit knob).
TAU_N_REFERENCE_S = 879.4
# ``weak_relax_rate ∝ T^5`` in ``hqiv_bbn_epoch_network`` — freeze-out shifts as τ_ratio^(1/5).
WEAK_FREEZEOUT_TEMP_EXPONENT = 1.0 / 5.0


@dataclass(frozen=True)
class BBNCondition:
    """Cosmological synthesis condition (one row on the cooling ladder)."""

    T_MeV: float
    eta: float
    m_nucleon: float
    Q_np: float
    m_shell: int = REFERENCE_M

    @property
    def xi(self) -> float:
        return lean.xi_from_T_MeV(self.T_MeV)

    @property
    def shell_index(self) -> float:
        return bbn.shell_index_from_mev(self.T_MeV)


@dataclass(frozen=True)
class LockinNetworkQ:
    """Network curvature binding Q at hadronic lock-in (m = referenceM)."""

    Q_D: float
    Q_4: float
    Q_3: float
    Q_7_be: float
    Q_be: float
    Q_li: float
    Q_form_be7: float
    Q_capture_be7_li7: float

    @classmethod
    def from_proton_mass(cls, m_nucleon: float, m_shell: int = REFERENCE_M) -> LockinNetworkQ:
        Q_D, Q_4, Q_3, Q_7 = bbn.lockin_binding_q_network(m_nucleon, m_shell)
        Q_be, Q_li = bbn.lockin_li7_be7_q_network(m_nucleon, m_shell)
        return cls(
            Q_D=Q_D,
            Q_4=Q_4,
            Q_3=Q_3,
            Q_7_be=Q_7,
            Q_be=Q_be,
            Q_li=Q_li,
            Q_form_be7=bbn.be7_formation_q(Q_7, Q_3, Q_4),
            Q_capture_be7_li7=bbn.be7_to_li7_capture_q(Q_be, Q_li),
        )


@dataclass(frozen=True)
class EffectiveQAtCondition:
    """Binding Q and release diagnostics at epoch ``T``."""

    Q_D: float
    Q_4: float
    Q_3: float
    Q_7_be: float
    Q_be: float
    Q_li: float
    release_factor: float
    bounded_slope: float
    Q_form_be7: float
    Q_capture_be7_li7: float


@dataclass(frozen=True)
class DecayWidthsAtCondition:
    """Width scales (MeV) and derived lifetimes at ``T``."""

    resonance_8be_erosion_mev: float
    resonance_8be_erosion_at_T_mev: float
    trimer_3he_width_lockin_mev: float
    trimer_3he_width_at_T_mev: float
    Q_3_eff_after_trimer_width_mev: float
    be7_capture_width_mev: float
    be7_capture_half_life_s: float
    deuteron_destroy_width_mev: float


@dataclass(frozen=True)
class ThermalRatesAtCondition:
    """Boltzmann-weighted synthesis / destruction factors (dimensionless)."""

    formation_D: float
    formation_He3: float
    formation_He4_dd: float
    formation_be7: float
    capture_be7_li7: float
    destroy_D: float
    thermal_sink_D: float
    thermal_sink_He3: float
    photodissociation_boost: float


@dataclass(frozen=True)
class ConditionDecayRow:
    """Full per-temperature BBN decay + thermal readout."""

    condition: BBNCondition
    effective_q: EffectiveQAtCondition
    widths: DecayWidthsAtCondition
    thermal: ThermalRatesAtCondition
    weak_x_n: float
    Y_p_freezeout: float
    c2_suppression: float
    shell_opportunity_per_step: float
    he3_synthesis_gate: float
    alpha_synthesis_gate: float
    be7_tail_gate: float


def binding_release_factor(T_MeV: float) -> float:
    return lean.bbn_binding_release_factor(T_MeV)


def effective_q_at_condition(
    cond: BBNCondition,
    lockin: LockinNetworkQ,
) -> EffectiveQAtCondition:
    """Network lock-in Q uniformly modulated by ``bbnBindingReleaseFactor(T)``."""
    rel = binding_release_factor(cond.T_MeV)
    slope = lean.bbn_bounded_curvature_temperature_slope(cond.T_MeV)
    Q_7 = lockin.Q_7_be * rel
    Q_be = lockin.Q_be * rel
    Q_li = lockin.Q_li * rel
    Q_D_t, Q_4_t, Q_3_t = bbn.light_binding_q_at_temperature(
        cond.T_MeV, m_shell=cond.m_shell
    )
    return EffectiveQAtCondition(
        Q_D=Q_D_t,
        Q_4=Q_4_t,
        Q_3=Q_3_t,
        Q_7_be=Q_7,
        Q_be=Q_be,
        Q_li=Q_li,
        release_factor=rel,
        bounded_slope=slope,
        Q_form_be7=bbn.be7_formation_q(Q_7, Q_3_t, Q_4_t),
        Q_capture_be7_li7=bbn.be7_to_li7_capture_q(Q_be, Q_li),
    )


def trimer_resonance_width_at_T(
    T_MeV: float,
    m: int,
    A: int,
    Z: int,
    cluster_total_mev: float,
) -> float:
    """³He/³H trimer width at epoch ``T`` (lock-in width × ``bbnBindingReleaseFactor``)."""
    width_lock = cbc.trimer_resonance_width_mev(m, A, Z, cluster_total_mev)
    return width_lock * binding_release_factor(T_MeV)


def effective_q3_with_trimer_width(
    T_MeV: float,
    Q_3_trace_mev: float,
    m_shell: int,
    *,
    Z: int = 2,
) -> tuple[float, float]:
    """
    Effective ³He binding Q after trimer width erosion at ``T``.

    Width is computed from network lock-in cluster binding; erosion is applied
    proportionally to the trace-released ``Q_3`` at this epoch.
    """
    total_net = bbn.cluster_binding_network_mev(m_shell, 3, Z=Z)
    width = trimer_resonance_width_at_T(T_MeV, m_shell, 3, Z, total_net)
    if total_net <= 0.0:
        return Q_3_trace_mev, width
    frac = min(1.0, width / total_net)
    return max(0.01, Q_3_trace_mev * (1.0 - frac)), width


def resonance_width_erosion_at_T(
    T_MeV: float,
    m: int,
    n_alpha: int,
    cluster_total_mev: float,
) -> float:
    """
    Multi-α resonance erosion at epoch ``T``.

    Lock-in width from ``multi_alpha_resonance_width_mev`` scales with
    ``bbnBindingReleaseFactor(T)``: hotter epochs release more curvature,
    softening the effective resonance width contribution.
    """
    width_lock = cbc.multi_alpha_resonance_width_mev(m, n_alpha, cluster_total_mev)
    return width_lock * binding_release_factor(T_MeV)


def resonance_half_life_from_width_mev(width_mev: float) -> float:
    """Lean ``resonance_half_life``: t½ = (ln 2) ħ / Γ."""
    if width_mev <= 0.0:
        return math.inf
    return math.log(2.0) * HBAR_MEV_S / width_mev


# Shared ³He / D synthesis geometry (mid-MeV gate + thermal-crush tail below mid).
HE3_SYNTH_LOW_MEV = 0.05
HE3_SYNTH_MID_MEV = 0.18
HE3_SYNTH_HIGH_MEV = 0.45


def he3_synthesis_gate(T_mev: float) -> float:
    """³He synthesis window: after D bottleneck, through mid-MeV before ⁷Be tail."""
    low, mid, high = HE3_SYNTH_LOW_MEV, HE3_SYNTH_MID_MEV, HE3_SYNTH_HIGH_MEV
    if T_mev <= low or T_mev >= high:
        return 0.0
    if T_mev >= mid:
        return (high - T_mev) / (high - mid)
    return (T_mev - low) / (mid - low)


def he3_be7_feed_gate(T_mev: float) -> float:
    """Narrower ³He bath for the ⁷Be→⁷Li ladder (limits Li from extended He3 window)."""
    low, mid, high = 0.05, 0.15, 0.35
    if T_mev <= low or T_mev >= high:
        return 0.0
    if T_mev >= mid:
        return (high - T_mev) / (high - mid)
    return (T_mev - low) / (mid - low)


def he3_synthesis_window_bounds_mev() -> tuple[float, float]:
    """Dedicated ³He integration band (matches ``he3_synthesis_gate`` support)."""
    return 0.45, 0.05


def build_he3_synthesis_temperature_ladder(n_steps: int) -> list[float]:
    """Log-spaced ladder for relic ³He/H (separate from the D synthesis window)."""
    T_hi, T_lo = he3_synthesis_window_bounds_mev()
    if n_steps < 2:
        raise ValueError("n_steps must be >= 2")
    return [T_hi * (T_lo / T_hi) ** (i / (n_steps - 1)) for i in range(n_steps)]


def trimer_width_suppress_at_T(width_mev: float, T_mev: float) -> float:
    """Strong-channel erosion only (``exp(−Γ·γ·strong/T)``); weak sector returns to D/H."""
    return math.exp(-width_mev * STRONG * GAMMA / max(T_mev, 0.02))


def synthesis_strong_deposition_boost(
    gate_np: float,
    c2: float,
) -> float:
    """C₂ strong-channel deposition boost on the D budget (``1 + ½·γ·strong·(1+g_np+c₂)``)."""
    return 1.0 + 0.5 * STRONG * GAMMA * (1.0 + gate_np + c2)


def alpha_synthesis_gate(T_mev: float) -> float:
    """⁴He lock-in gate (mirrors ``dd_fusion_gate`` in epoch network)."""
    return epoch_net.dd_fusion_gate(T_mev)


def be7_tail_gate(T_mev: float) -> float:
    """⁷Be formation + capture gate (epoch network ``be7_fusion_gate``)."""
    return epoch_net.be7_fusion_gate(T_mev)


def thermal_rates_at_condition(
    cond: BBNCondition,
    eff: EffectiveQAtCondition,
) -> ThermalRatesAtCondition:
    T = cond.T_MeV
    Q_dd = max(0.01, eff.Q_4 - 2.0 * eff.Q_D)
    Q_he3 = max(0.01, eff.Q_3 - eff.Q_D)
    return ThermalRatesAtCondition(
        formation_D=epoch_net.formation_weight(eff.Q_D, T),
        formation_He3=epoch_net.formation_weight(Q_he3, T),
        formation_He4_dd=epoch_net.formation_weight(Q_dd, T),
        formation_be7=epoch_net.formation_weight(eff.Q_form_be7, T),
        capture_be7_li7=epoch_net.formation_weight(eff.Q_capture_be7_li7, T),
        destroy_D=epoch_net.formation_weight(-eff.Q_D, T),
        thermal_sink_D=bbn.thermal_sink(eff.Q_D, eff.Q_4, T),
        thermal_sink_He3=bbn.thermal_sink(eff.Q_3, eff.Q_4, T),
        photodissociation_boost=epoch_net.photodissociation_boost(T),
    )


def decay_widths_at_condition(
    cond: BBNCondition,
    eff: EffectiveQAtCondition,
    lockin: LockinNetworkQ,
) -> DecayWidthsAtCondition:
    """Width scales for ⁸Be / ³He erosion, ⁷Be capture, and D photodissociation."""
    del lockin
    total_8be = bbn.cluster_binding_network_mev(cond.m_shell, 8, Z=4)
    width_lock = cbc.multi_alpha_resonance_width_mev(cond.m_shell, 2, total_8be)
    width_at_T = resonance_width_erosion_at_T(cond.T_MeV, cond.m_shell, 2, total_8be)
    total_3he = bbn.cluster_binding_network_mev(cond.m_shell, 3, Z=2)
    trimer_lock = cbc.trimer_resonance_width_mev(cond.m_shell, 3, 2, total_3he)
    trimer_at_T = trimer_resonance_width_at_T(cond.T_MeV, cond.m_shell, 3, 2, total_3he)
    Q_3_eff, _ = effective_q3_with_trimer_width(
        cond.T_MeV, eff.Q_3, cond.m_shell, Z=2
    )
    cap_mev = eff.Q_capture_be7_li7
    return DecayWidthsAtCondition(
        resonance_8be_erosion_mev=width_lock,
        resonance_8be_erosion_at_T_mev=width_at_T,
        trimer_3he_width_lockin_mev=trimer_lock,
        trimer_3he_width_at_T_mev=trimer_at_T,
        Q_3_eff_after_trimer_width_mev=Q_3_eff,
        be7_capture_width_mev=cap_mev,
        be7_capture_half_life_s=resonance_half_life_from_width_mev(cap_mev),
        deuteron_destroy_width_mev=eff.Q_D * eff.release_factor,
    )


@dataclass(frozen=True)
class StoichiometricAbundancesAtT:
    """D / ³He abundances per H with deuterium burn competition at ``T``."""

    T_MeV: float
    D_over_H: float
    He3_over_H: float
    He3_inventory_for_be7: float
    D_seed_uncoupled: float
    burn_denominator: float
    branch_dd: float
    branch_he3: float
    branch_photo: float
    branch_np_to_d: float
    D_np_capture: float
    trimer_width_mev: float
    Q_3_eff_mev: float
    np_pair_factor: float = 1.0
    neutron_budget: float = 1.0


@dataclass(frozen=True)
class CoupledInventoryRow:
    """Free-neutron inventory at epoch ``T`` on the cooling march."""

    T_MeV: float
    x_n: float
    np_pair_factor: float
    neutron_budget: float
    below_freezeout: bool
    tau_ratio: float
    cumulative_survival: float


@dataclass(frozen=True)
class CoupledBBNReadout:
    """Unified Y_p + D/H from the same neutron inventory march."""

    T_freeze_bare_MeV: float
    T_freeze_effective_MeV: float
    x_n_at_freeze: float
    x_n_at_T_low: float
    tau_ratio_at_freeze: float
    Y_p: float
    Y_p_bare_equilibrium: float
    delta_Y_p: float
    he_capture_integral: float
    inventory_by_T: tuple[CoupledInventoryRow, ...]


def np_pair_factor(x_n: float) -> float:
    """Dimensionless n_n · n_p proxy in n/p units (n_p normalized to 1): ``x/(1+x)²``."""
    if x_n <= 0.0:
        return 0.0
    return x_n / (1.0 + x_n) ** 2


def cosmological_dt_seconds(T_hi_MeV: float, T_lo_MeV: float) -> float:
    """Elapsed time cooling from ``T_hi`` to ``T_lo`` (RD ``dt = |dT| / (T H)``)."""
    if T_hi_MeV <= T_lo_MeV:
        return 0.0
    T_mid = math.sqrt(T_hi_MeV * T_lo_MeV)
    H = epoch_net.hubble_rate_s(T_mid)
    return (T_hi_MeV - T_lo_MeV) / max(T_mid * H, 1e-30)


def synthesis_window_end_mev(eta: float, Q_np: float) -> float:
    """Physical end of active n+p / D synthesis (C₂ bottleneck ``T_bn``)."""
    return lean.bbn_dynamic_c2_bottleneck_t_mev(eta, Q_np)


def synthesis_d_window_peak_mev() -> float:
    """Mid-MeV gate peak (``he3_synthesis_gate`` apex); unity on the D/H tail gate."""
    return HE3_SYNTH_MID_MEV


def synthesis_d_window_tail_gate(T_mev: float, eta: float, Q_np: float) -> float:
    """
    Log-weight taper on D/H integration below the ³He synthesis mid-gate.

    Unity at and above ``HE3_SYNTH_MID_MEV``; linear fade from mid → ``T_bn`` as the
    thermal-crush tail (not a hard shut-off at mid-MeV).  Mirrors the ascending branch
    geometry of ``he3_synthesis_gate`` anchored at the C₂ bottleneck.
    """
    T_bn = synthesis_window_end_mev(eta, Q_np)
    mid = synthesis_d_window_peak_mev()
    if T_mev >= mid:
        return 1.0
    if T_mev <= T_bn:
        return 0.0
    return (T_mev - T_bn) / (mid - T_bn)


def synthesis_d_window_bounds_mev(
    eta: float,
    Q_np: float,
    *,
    T_high_MeV: float = bbn.BBN_T_HIGH_MEV,
) -> tuple[float, float]:
    """
    D/H integration ladder: MeV synthesis band through ``T_bn``.

    Log weights below ``HE3_SYNTH_MID_MEV`` are tapered by
    ``synthesis_d_window_tail_gate`` (thermal crush tail — not a hard cutoff at mid).
    """
    T_low = synthesis_window_end_mev(eta, Q_np)
    return max(T_high_MeV, T_low + 1e-6), T_low


def build_synthesis_d_temperature_ladder(
    eta: float,
    Q_np: float,
    n_steps: int,
    *,
    T_high_MeV: float = bbn.BBN_T_HIGH_MEV,
) -> list[float]:
    """Log-spaced cooling ladder for the D/H synthesis window."""
    T_hi, T_lo = synthesis_d_window_bounds_mev(eta, Q_np, T_high_MeV=T_high_MeV)
    if n_steps < 2:
        raise ValueError("n_steps must be >= 2")
    return [T_hi * (T_lo / T_hi) ** (i / (n_steps - 1)) for i in range(n_steps)]


def np_to_deuterium_synthesis_gate(T_mev: float, eta: float, Q_np: float) -> float:
    """
    n+p→D formation gate (strong channel before α lock-in dominates).

    Unity from weak freeze through the C₂ bottleneck; tapers only below ``T_bn``.
    Distinct from ``alpha_synthesis_gate`` (D+D→⁴He), which ramps up at lower T.
    """
    T_bn = lean.bbn_dynamic_c2_bottleneck_t_mev(eta, Q_np)
    if T_mev >= T_bn:
        return 1.0
    return max(0.0, T_mev / max(T_bn, 1e-6))


def x_n_after_synthesis_decay(
    x_n_freeze: float,
    T_freeze_MeV: float,
    T_end_MeV: float,
    Q_np: float,
    Q_D: float,
    *,
    use_curvature: bool = True,
) -> tuple[float, float]:
    """
    β decay from freeze-out through the synthesis band only (not the full BBN tail).

    Returns ``(x_n_after, cumulative_survival)`` with strong-channel shield on decay.
    """
    if T_end_MeV >= T_freeze_MeV:
        return x_n_freeze, 1.0
    dt = cosmological_dt_seconds(T_freeze_MeV, T_end_MeV)
    T_mid = math.sqrt(T_freeze_MeV * T_end_MeV)
    tr = (
        free_neutron_weak_environment_at_T(T_mid).tau_ratio_vs_lockin
        if use_curvature
        else 1.0
    )
    t_cap = neutron_synthesis_capture_time_s(T_freeze_MeV, Q_np, Q_D)
    tau = TAU_N_REFERENCE_S * tr
    synth_surv = math.exp(-min(dt, t_cap) / max(tau, 1e-30))
    synth_surv = 1.0 - (1.0 - synth_surv) * (GAMMA * STRONG)
    return neutron_fraction_after_freeze(x_n_freeze, synth_surv), synth_surv


def build_coupled_inventory_march(
    temps: list[float],
    eta: float,
    Q_np: float,
    *,
    Q_D: float = 2.2,
    use_curvature: bool = True,
) -> CoupledBBNReadout:
    """
    March free-neutron inventory down the BBN cooling ladder.

    Above ``T_freeze_eff``: weak equilibrium ``x_n(T)``.  Below freeze through the
    synthesis window: one β-decay step; inventory held below ``T_synth_end``.
    """
    T_bare, T_eff = effective_freezeout_temperature_mev(Q_np, eta, use_curvature=use_curvature)
    T_synth_end = synthesis_window_end_mev(eta, Q_np)
    x_n_bare_freeze = bbn.neutron_proton_ratio(T_bare, Q_np)
    x_n_freeze = bbn.neutron_proton_ratio(T_eff, Q_np)
    x_n_synth, cum_surv = x_n_after_synthesis_decay(
        x_n_freeze,
        T_eff,
        T_synth_end,
        Q_np,
        Q_D,
        use_curvature=use_curvature,
    )
    ref_np_bare = max(np_pair_factor(x_n_bare_freeze), 1e-30)
    np_at_freeze = np_pair_factor(x_n_freeze) / ref_np_bare
    n_budget_at_freeze = x_n_freeze / max(x_n_bare_freeze, 1e-30)
    rows: list[CoupledInventoryRow] = []

    for T in temps:
        if T > T_eff:
            x_n = bbn.neutron_proton_ratio(T, Q_np)
            np_scale = np_pair_factor(x_n) / ref_np_bare
            n_budget = x_n / max(x_n_bare_freeze, 1e-30)
            surv = 1.0
        else:
            x_n = x_n_synth
            np_scale = np_at_freeze
            n_budget = n_budget_at_freeze
            surv = cum_surv

        env = free_neutron_weak_environment_at_T(T)
        rows.append(
            CoupledInventoryRow(
                T_MeV=T,
                x_n=x_n,
                np_pair_factor=np_scale,
                neutron_budget=n_budget,
                below_freezeout=T <= T_eff,
                tau_ratio=env.tau_ratio_vs_lockin,
                cumulative_survival=surv,
            )
        )

    x_n_low = x_n_synth
    env_f = free_neutron_weak_environment_at_T(T_eff)
    return CoupledBBNReadout(
        T_freeze_bare_MeV=T_bare,
        T_freeze_effective_MeV=T_eff,
        x_n_at_freeze=x_n_freeze,
        x_n_at_T_low=x_n_low,
        tau_ratio_at_freeze=env_f.tau_ratio_vs_lockin,
        Y_p=0.0,
        Y_p_bare_equilibrium=bbn.y_p_from_neutron_fraction(
            bbn.neutron_proton_ratio(T_bare, Q_np)
        ),
        delta_Y_p=0.0,
        he_capture_integral=0.0,
        inventory_by_T=tuple(rows),
    )


def deuterium_stoichiometric_abundances_at_T(
    cond: BBNCondition,
    *,
    apply_he3_gate: bool = True,
    apply_c2_suppression: bool = True,
    inventory: CoupledInventoryRow | None = None,
) -> StoichiometricAbundancesAtT:
    """
    Coupled D + p → ³He vs D + D → ⁴He vs D photodissociation at epoch ``T``.

    Starts from the uncoupled partition seeds, then applies **dimensionless** drain
    couplings (γ·strong × gates × thermal ratios) — not raw ``exp(Q/T)`` rates, which
    would over-burn D in the MeV tail.  Trimer width Γ(T) suppresses the ³He branch via
    ``exp(−Γ/T)`` and lowers ``Q_3_eff`` for the ³He partition exponent.
    """
    T = cond.T_MeV
    Q_D, Q_4, Q_3 = bbn.light_binding_q_at_temperature(T, m_shell=cond.m_shell)
    Q_3_eff, w_trimer = effective_q3_with_trimer_width(T, Q_3, cond.m_shell, Z=2)

    np_scale = inventory.np_pair_factor if inventory is not None else 1.0
    n_scale = inventory.neutron_budget if inventory is not None else 1.0

    e10 = bbn.eta10(cond.eta)
    D_seed = (
        e10 ** bbn.eta_exponent_dh(Q_D, Q_4, cond.Q_np)
        * bbn.thermal_sink(Q_D, Q_4, T)
        * np_scale
    )
    He3_seed = (
        e10 ** bbn.eta_exponent_he3(Q_3_eff, Q_D, cond.Q_np)
        * bbn.thermal_sink(Q_3_eff, Q_4, T)
        * np_scale
    )

    gate_a = alpha_synthesis_gate(T)
    gate_h = he3_synthesis_gate(T) if apply_he3_gate else 1.0
    c2 = (
        lean.bbn_dynamic_c2_opportunity_suppression(
            T, eta=cond.eta, m_nucleon=cond.m_nucleon, m_shell=cond.m_shell
        )
        if apply_c2_suppression
        else 1.0
    )

    width_suppress = trimer_width_suppress_at_T(w_trimer, T)
    He3_full = He3_seed * gate_h
    He3_actual = He3_full * width_suppress
    # Trimer width blocks D + p → ³He; unburned deuterium returns to the D/H pool.
    D_returned = max(0.0, He3_full - He3_actual)

    # Dimensionless drain on D from D + D → ⁴He and photodissociation (α + photo only).
    q_gap_alpha = max(0.0, Q_4 - 2.0 * Q_D) / max(Q_4 - Q_D, 0.01)
    branch_dd = STRONG * GAMMA * gate_a * c2 * q_gap_alpha * n_scale
    branch_he3 = STRONG * GAMMA * gate_h * (1.0 - width_suppress) * np_scale
    branch_photo = (
        STRONG * GAMMA * min(epoch_net.photodissociation_boost(T) * 1.0e-4, 1.0)
    )
    # n + p → D: C₂ strong channel with coupled n·p inventory (``γ·(4/8)·Q_D/Q_np`` spine).
    gate_np = np_to_deuterium_synthesis_gate(T, cond.eta, cond.Q_np)
    branch_np_to_d = STRONG * GAMMA * gate_np * c2 * np_scale * n_scale
    D_np_capture = branch_np_to_d * (Q_D / max(cond.Q_np, 1e-30)) * D_seed
    strong_boost = synthesis_strong_deposition_boost(gate_np, c2)

    # Photodissociation only on the denominator (α burn is in Y_p / D+D channel).
    denom = 1.0 + branch_photo
    D_over_H = (D_seed + D_returned + D_np_capture) * strong_boost / denom
    He3_over_H = min(He3_actual, D_over_H) / denom
    # ⁷Be ladder uses the synthesis-bath ³He inventory (before width capture freeze-out).
    He3_inventory_for_be7 = He3_full / denom

    return StoichiometricAbundancesAtT(
        T_MeV=T,
        D_over_H=D_over_H,
        He3_over_H=He3_over_H,
        He3_inventory_for_be7=He3_inventory_for_be7,
        D_seed_uncoupled=D_seed,
        burn_denominator=denom,
        branch_dd=branch_dd,
        branch_he3=branch_he3,
        branch_photo=branch_photo,
        branch_np_to_d=branch_np_to_d,
        D_np_capture=D_np_capture,
        trimer_width_mev=w_trimer,
        Q_3_eff_mev=Q_3_eff,
        np_pair_factor=np_scale,
        neutron_budget=n_scale,
    )


def condition_decay_row(
    cond: BBNCondition,
    lockin: LockinNetworkQ,
    *,
    T_next_MeV: float | None = None,
) -> ConditionDecayRow:
    """Single rung on the BBN cooling ladder with full decay readout."""
    eff = effective_q_at_condition(cond, lockin)
    widths = decay_widths_at_condition(cond, eff, lockin)
    thermal = thermal_rates_at_condition(cond, eff)
    T_f = bbn.freezeout_temperature_mev(cond.Q_np, cond.eta)
    x_n = bbn.neutron_proton_ratio(T_f, cond.Q_np)
    T_next = T_next_MeV if T_next_MeV is not None else cond.T_MeV * 0.99
    return ConditionDecayRow(
        condition=cond,
        effective_q=eff,
        widths=widths,
        thermal=thermal,
        weak_x_n=bbn.neutron_proton_ratio(cond.T_MeV, cond.Q_np),
        Y_p_freezeout=bbn.y_p_from_neutron_fraction(x_n),
        c2_suppression=lean.bbn_dynamic_c2_opportunity_suppression(
            cond.T_MeV, eta=cond.eta, m_nucleon=cond.m_nucleon, m_shell=cond.m_shell
        ),
        shell_opportunity_per_step=lean.bbn_shell_reaction_opportunity(
            cond.T_MeV, T_next, lean.XI_LOCKIN
        ),
        he3_synthesis_gate=he3_synthesis_gate(cond.T_MeV),
        alpha_synthesis_gate=alpha_synthesis_gate(cond.T_MeV),
        be7_tail_gate=be7_tail_gate(cond.T_MeV),
    )


def default_temperature_ladder(
    T_high: float = bbn.BBN_T_HIGH_MEV,
    T_low: float = bbn.BBN_T_LOW_MEV,
    n_steps: int = 32,
) -> list[float]:
    if n_steps < 2:
        raise ValueError("n_steps must be >= 2")
    return [T_high * (T_low / T_high) ** (i / (n_steps - 1)) for i in range(n_steps)]


def build_condition_decay_table(
    eta: float,
    m_nucleon: float,
    Q_np: float,
    *,
    temperatures_mev: list[float] | None = None,
    m_shell: int = REFERENCE_M,
) -> list[ConditionDecayRow]:
    lockin = LockinNetworkQ.from_proton_mass(m_nucleon, m_shell)
    temps = temperatures_mev or default_temperature_ladder()
    rows: list[ConditionDecayRow] = []
    for i, T in enumerate(temps):
        T_next = temps[i + 1] if i + 1 < len(temps) else T * 0.99
        rows.append(
            condition_decay_row(
                BBNCondition(T_MeV=T, eta=eta, m_nucleon=m_nucleon, Q_np=Q_np, m_shell=m_shell),
                lockin,
                T_next_MeV=T_next,
            )
        )
    return rows


def weak_width_factor_at_condition(cond: BBNCondition, *, bonded: bool = False) -> float:
    """Free-branch weak-width catalysis from local curvature neutrino bath."""
    low, central, _high = notd.local_curvature_weak_width_factor_band(
        cond.xi, bonded=bonded, A=1
    )
    del low
    return central


@dataclass(frozen=True)
class FreeNeutronWeakEnvironment:
    """Outside curvature + relic-ν bath slots on the free-neutron β branch."""

    T_MeV: float
    xi: float
    outside_modulator_free: float
    weak_width_factor: float
    outside_lifetime_ratio: float
    tau_ratio_vs_lockin: float
    weak_rate_scale: float


@dataclass(frozen=True)
class FreeNeutronCurvatureYpReadout:
    """⁴He mass fraction from curvature-modulated weak freeze-out (+ optional survival)."""

    T_freeze_bare_MeV: float
    T_freeze_effective_MeV: float
    tau_ratio_at_freeze: float
    outside_lifetime_ratio: float
    weak_width_factor: float
    x_n_equilibrium: float
    neutron_survival: float
    x_n_after_capture: float
    Y_p: float
    Y_p_bare_equilibrium: float
    delta_Y_p: float
    capture_time_s: float
    tau_n_effective_s: float


def free_neutron_weak_environment_at_T(T_MeV: float) -> FreeNeutronWeakEnvironment:
    """
    Combined τ_n environment at epoch ``T`` (Python mirror of outside + ν-opacity spine).

    ``τ ∝ (mod_lock / mod_free) / weak_width_factor`` — outside support lengthens,
    relic-ν catalysis shortens.  Same stack as ``hqiv_isotope_stability_halflife``.
    """
    xi = lean.xi_from_T_MeV(T_MeV)
    mod = notd.outside_curvature_binding_modulator(xi, bonded=False)
    mod_lock = notd.outside_curvature_binding_modulator(notd.XI_LOCKIN, bonded=False)
    width_f = notd.local_curvature_weak_width_factor(xi, 0.0)
    outside_lifetime_ratio = mod_lock / max(mod, 1e-30)
    tau_ratio = outside_lifetime_ratio / max(width_f, 1e-30)
    return FreeNeutronWeakEnvironment(
        T_MeV=T_MeV,
        xi=xi,
        outside_modulator_free=mod,
        weak_width_factor=width_f,
        outside_lifetime_ratio=outside_lifetime_ratio,
        tau_ratio_vs_lockin=tau_ratio,
        weak_rate_scale=1.0 / max(tau_ratio, 1e-30),
    )


def effective_freezeout_temperature_mev(
    Q_np: float,
    eta: float,
    *,
    use_curvature: bool = True,
) -> tuple[float, float]:
    """
    Weak freeze-out temperature with optional curvature slowdown.

    Slower β at BBN ξ (longer τ_n) decouples n↔p at higher ``T`` than the bare
    ``Q_np / log(η₁₀)`` slot — ``weak_relax_rate ∝ T^5`` gives ``T_eff ∝ τ_ratio^(1/5)``.
    """
    T_bare = bbn.freezeout_temperature_mev(Q_np, eta)
    if not use_curvature:
        return T_bare, T_bare
    tr = free_neutron_weak_environment_at_T(T_bare).tau_ratio_vs_lockin
    T_eff = T_bare * tr**WEAK_FREEZEOUT_TEMP_EXPONENT
    return T_bare, T_eff


def neutron_synthesis_capture_time_s(
    T_freeze_MeV: float,
    Q_np: float,
    Q_D: float,
) -> float:
    """Strong-channel capture window ``γ·(4/8)·Q_D/Q_np / H(T_f)`` (C₂ / Hubble spine)."""
    import hqiv_bbn_epoch_network as epoch_net

    H = epoch_net.hubble_rate_s(T_freeze_MeV)
    return GAMMA * STRONG * Q_D / max(Q_np, 1e-30) / max(H, 1e-30)


def neutron_survival_after_freeze(
    T_freeze_MeV: float,
    Q_np: float,
    Q_D: float,
    *,
    tau_ratio: float,
    apply_strong_shield: bool = True,
) -> float:
    """
    Post-freeze neutron survival through the D/α synthesis window.

    Most neutrons are captured during the γ·(4/8) strong synthesis band; only the
    complement outside that window is subject to raw ``exp(−t/τ)`` decay.
    """
    t_cap = neutron_synthesis_capture_time_s(T_freeze_MeV, Q_np, Q_D)
    tau = TAU_N_REFERENCE_S * max(tau_ratio, 1e-30)
    raw_decay = 1.0 - math.exp(-t_cap / tau)
    if apply_strong_shield:
        raw_decay *= GAMMA * STRONG
    return 1.0 - raw_decay


def neutron_fraction_after_freeze(x_n_freeze: float, survival: float) -> float:
    """n/p after partial β decay between freeze-out and ⁴He lock-in."""
    return x_n_freeze * survival / (1.0 + x_n_freeze * (1.0 - survival))


def y_p_from_coupled_march(
    march: CoupledBBNReadout,
    *,
    sto_rows: list[StoichiometricAbundancesAtT],
    weights: list[float],
) -> CoupledBBNReadout:
    """
    ⁴He mass fraction from the same inventory that feeds D/H.

    Neutrons locked through α synthesis (``branch_dd``) plus surviving inventory
    at freeze-out set ``Y_p``; decay reduces the pool below freeze-out.
    """
    x_f = march.x_n_at_freeze
    he_integral = 0.0
    w_below = 0.0
    for sto, w, row in zip(sto_rows, weights, march.inventory_by_T):
        if not row.below_freezeout:
            continue
        he_integral += w * sto.branch_dd
        w_below += w
    if w_below > 0.0:
        he_integral /= w_below

    # ⁴He from neutrons surviving the synthesis band (β-decay shielded; shared with D march).
    x_n_he = march.x_n_at_T_low
    Y_p = bbn.y_p_from_neutron_fraction(x_n_he)
    return CoupledBBNReadout(
        T_freeze_bare_MeV=march.T_freeze_bare_MeV,
        T_freeze_effective_MeV=march.T_freeze_effective_MeV,
        x_n_at_freeze=x_f,
        x_n_at_T_low=march.x_n_at_T_low,
        tau_ratio_at_freeze=march.tau_ratio_at_freeze,
        Y_p=Y_p,
        Y_p_bare_equilibrium=march.Y_p_bare_equilibrium,
        delta_Y_p=Y_p - march.Y_p_bare_equilibrium,
        he_capture_integral=he_integral,
        inventory_by_T=march.inventory_by_T,
    )


def integrate_coupled_stoichiometric_window(
    eta: float,
    m_nucleon: float,
    Q_np: float,
    temps: list[float],
    weights: list[float],
    *,
    m_shell: int = REFERENCE_M,
    apply_he3_gate: bool = True,
    use_curvature: bool = True,
) -> tuple[list[StoichiometricAbundancesAtT], CoupledBBNReadout]:
    """Log-weighted stoichiometric D/³He with shared neutron inventory at each ``T``."""
    cond0 = BBNCondition(T_MeV=temps[0], eta=eta, m_nucleon=m_nucleon, Q_np=Q_np, m_shell=m_shell)
    Q_D0, _, _ = bbn.light_binding_q_at_temperature(temps[0], m_shell=m_shell)
    march = build_coupled_inventory_march(
        temps, eta, Q_np, Q_D=Q_D0, use_curvature=use_curvature
    )
    sto_rows: list[StoichiometricAbundancesAtT] = []
    for T, inv in zip(temps, march.inventory_by_T):
        cond = BBNCondition(
            T_MeV=T,
            eta=eta,
            m_nucleon=m_nucleon,
            Q_np=Q_np,
            m_shell=m_shell,
        )
        sto_rows.append(
            deuterium_stoichiometric_abundances_at_T(
                cond,
                apply_he3_gate=apply_he3_gate,
                apply_c2_suppression=True,
                inventory=inv,
            )
        )
    coupled = y_p_from_coupled_march(march, sto_rows=sto_rows, weights=weights)
    return sto_rows, coupled


def y_p_with_free_neutron_curvature(
    eta: float,
    Q_np: float,
    Q_D: float,
    *,
    use_curvature: bool = True,
    include_post_freeze_survival: bool = False,
) -> FreeNeutronCurvatureYpReadout:
    """
    ⁴He mass fraction from the free-neutron outside-curvature channel.

    Default (``include_post_freeze_survival=False``): instant capture at modified
    freeze-out — matches the partition integrator's He-lock-in assumption while
    booking the > ppm weak-rate shift from BBN ξ.

    Optional survival: second-order ``exp(−t/τ)`` with strong-channel shield.
    """
    T_bare, T_eff = effective_freezeout_temperature_mev(Q_np, eta, use_curvature=use_curvature)
    env = free_neutron_weak_environment_at_T(T_eff if use_curvature else T_bare)
    x_n0 = bbn.neutron_proton_ratio(T_eff, Q_np)
    if include_post_freeze_survival:
        T_bn = lean.bbn_dynamic_c2_bottleneck_t_mev(eta, Q_np)
        tr_mid = free_neutron_weak_environment_at_T(math.sqrt(T_eff * T_bn)).tau_ratio_vs_lockin
        surv = neutron_survival_after_freeze(
            T_eff,
            Q_np,
            Q_D,
            tau_ratio=tr_mid if use_curvature else 1.0,
        )
    else:
        surv = 1.0
    x_n = neutron_fraction_after_freeze(x_n0, surv)
    Y_p = bbn.y_p_from_neutron_fraction(x_n)
    Y_p_bare = bbn.y_p_from_neutron_fraction(bbn.neutron_proton_ratio(T_bare, Q_np))
    t_cap = neutron_synthesis_capture_time_s(T_eff, Q_np, Q_D)
    tau_eff = TAU_N_REFERENCE_S * (
        free_neutron_weak_environment_at_T(math.sqrt(T_eff * lean.bbn_dynamic_c2_bottleneck_t_mev(eta, Q_np))).tau_ratio_vs_lockin
        if use_curvature
        else 1.0
    )
    return FreeNeutronCurvatureYpReadout(
        T_freeze_bare_MeV=T_bare,
        T_freeze_effective_MeV=T_eff,
        tau_ratio_at_freeze=env.tau_ratio_vs_lockin,
        outside_lifetime_ratio=env.outside_lifetime_ratio,
        weak_width_factor=env.weak_width_factor,
        x_n_equilibrium=x_n0,
        neutron_survival=surv,
        x_n_after_capture=x_n,
        Y_p=Y_p,
        Y_p_bare_equilibrium=Y_p_bare,
        delta_Y_p=Y_p - Y_p_bare,
        capture_time_s=t_cap,
        tau_n_effective_s=tau_eff,
    )


def row_to_dict(row: ConditionDecayRow) -> dict[str, Any]:
    """JSON-serializable witness row."""
    d = asdict(row)
    d["condition"] = asdict(row.condition)
    d["effective_q"] = asdict(row.effective_q)
    d["widths"] = asdict(row.widths)
    d["thermal"] = asdict(row.thermal)
    d["weak_width_factor_free"] = weak_width_factor_at_condition(row.condition, bonded=False)
    d["outside_release_factor"] = notd.outside_curvature_release_factor(row.condition.xi)
    return d


def main() -> None:
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    dm = float(w["derivedDeltaM_MeV"])
    eta = bbn.ETA_PAPER
    lockin = LockinNetworkQ.from_proton_mass(m_p)
    rows = build_condition_decay_table(eta, m_p, dm, temperatures_mev=[1.0, 0.3, 0.1, 0.05, 0.01])

    print("HQIV BBN condition-dependent decay (network lock-in spine)")
    print(f"  η = {eta:.3e}  Q_np = {dm:.4f} MeV")
    print(f"  Q_D={lockin.Q_D:.3f}  Q_4={lockin.Q_4:.3f}  Q_3={lockin.Q_3:.3f} MeV")
    print(f"  Q_form(⁷Be)={lockin.Q_form_be7:.3f}  Q_cap(⁷Be→⁷Li)={lockin.Q_capture_be7_li7:.4f} MeV")
    print()
    print(
        f"{'T_MeV':>8} {'release':>8} {'Γ_3He@T':>10} {'Q3_eff':>8} "
        f"{'D/H_sto':>10} {'He3_sto':>10}"
    )
    for row in rows:
        sto = deuterium_stoichiometric_abundances_at_T(row.condition)
        print(
            f"{row.condition.T_MeV:8.3f} "
            f"{row.effective_q.release_factor:8.5f} "
            f"{row.widths.trimer_3he_width_at_T_mev:10.5f} "
            f"{row.widths.Q_3_eff_after_trimer_width_mev:8.3f} "
            f"{sto.D_over_H:10.4e} "
            f"{sto.He3_over_H:10.4e}"
        )


if __name__ == "__main__":
    main()
