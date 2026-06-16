#!/usr/bin/env python3
"""
Lean-aligned HQIV physics primitives (Python mirror of key definitions).

Single source for scripts that must match:
  - Hqiv.Physics.ContinuousXiCoupling / ContinuousXiPath
  - Hqiv.Physics.HopfShellBeltramiMassBridge
  - Hqiv.Physics.BaryogenesisWitness
  - Hqiv.Physics.DynamicBBNBaryogenesis
  - Hqiv.Physics.BBNEpochNetwork
"""

from __future__ import annotations

import math

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes

# Lattice-forced rationals (OctonionicLightCone)
ALPHA = 3.0 / 5.0
GAMMA = 2.0 / 5.0
ALPHA_HEAVY = 3.0 / 5.0  # t12_heavy_shell curvatureImprintAlpha
PHASE_LIFT_3 = 4.0 / 3.0  # phaseLiftCoeff 3 = phi(3)/6

REFERENCE_M = hes.REFERENCE_M
QCD_SHELL = 1  # BaryogenesisCore.m_QCD
XI_LOCKIN = float(REFERENCE_M + 1)  # xiLockin = 5 at referenceM = 4
T13_OUTER_MODE_COUNT = 140.0
STRONG_CHANNEL_FRACTION = 4.0 / 8.0  # bbnStrongChannelFraction
# Lean `constructiveValleyCap` (= pairwiseNucleonContactCount 4 = 6).
CONSTRUCTIVE_VALLEY_CAP = 6.0
ETA_PAPER = 6.10e-10
# Binding curvature feedback and baryogenesis correction are now fully derived
# (gamma_HQIV * strongChannelFraction * bounded_slope, no free κ).
# See Lean DynamicBBNBaryogenesis for the expressions.
C_RINDLER_SHARED = GAMMA / 2.0  # Lean `c_rindler_shared`


def curvature_density(x: float) -> float:
    if x <= 0.0:
        raise ValueError("curvature coordinate must be positive")
    return (1.0 / x) * (1.0 + ALPHA * math.log(x))


def shell_shape(m: int) -> float:
    return curvature_density(float(m + 1))


def curvature_integral(n: int) -> float:
    """Lean `curvature_integral n` = sum_{m < n} shell_shape m."""
    if n <= 0:
        return 0.0
    return sum(shell_shape(m) for m in range(n))


def curvature_primitive(xi: float) -> float:
    """Lean `continuousCurvaturePrimitive`."""
    if xi <= 0.0:
        return 0.0
    lx = math.log(xi)
    return lx + (ALPHA / 2.0) * lx * lx


def omega_k_xi(xi: float, xi_lock: float = XI_LOCKIN) -> float:
    """Lean `omegaK_xi` = omegaKContinuous ξ ξLock (epoch vs lock-in cumulative ratio)."""
    k0 = curvature_primitive(xi_lock)
    if k0 <= 0.0:
        return 1.0
    return curvature_primitive(xi) / k0


def curvature_budget_at_shell(
    m: int,
    *,
    m_lock: int,
    m_start: int,
    xi: float,
    omega_m_fraction: float,
) -> float:
    """Per-shell curvature budget: early asymmetry/radiation seed, relaxes to 1 at lock-in.

    Same-epoch local ≈ global at observation (budget → 1). Early shells carry extra
    curvature imprint while net matter fraction is still opening (Ω_m small): either
    matter–antimatter pair stress (``1/ω_K(chart) - 1``) or radiation-dominated excess
    ``α·(1 - ω_K(chart)`` on the path toward lock-in. The excess is routed outside the
    baryon accumulation track in the bulk integrator so η drifts down slightly by lock-in.
    """
    chart = max(omega_k_xi(xi), 1e-6)
    span = max(m_lock - m_start, 1)
    progress_to_lock = (m_lock - m) / span
    matter_opening = max(0.0, 1.0 - omega_m_fraction / max(GAMMA, 1e-6))
    pair_seed = max(0.0, 1.0 / chart - 1.0)
    rad_seed = ALPHA * max(0.0, 1.0 - chart)
    seed_strength = GAMMA * matter_opening * progress_to_lock * max(pair_seed, rad_seed)
    return 1.0 + seed_strength


def effective_inside_temperature(xi: float) -> float:
    """Inner trapped contact temperature on the ξ ladder."""
    t_bg = 1.0 / max(xi, 1e-30)
    trap = trapping_selection_heavy(ALPHA_HEAVY, omega_k_xi(xi))
    return t_bg / max(trap, 1e-30)


def effective_outside_temperature(xi: float) -> float:
    """Outer T13-suppressed temperature on the ξ ladder."""
    return (1.0 / max(xi, 1e-30)) * t13_outer_suppression_at_xi(xi)


def casimir_gap_at_xi(xi: float) -> float:
    """Leading separation proxy d ∝ 1/ξ for inner/outer Casimir on the ladder."""
    return 1.0 / max(xi, 1e-30)


def curvature_budget_local_global_at_xi(
    xi: float,
    xi_lock: float = XI_LOCKIN,
    *,
    casimir_power: float = 1.0,
) -> float:
    """
    Same-epoch local/global budget B_curv(ξ) for κ₆ and integrator witnesses.

    • At ξ_lock: B_curv = 1 (inside/outside Casimir balance calibrated).
    • On the shell ladder (ξ ≤ ξ_lock): Casimir gap law ~(d_lock/d)^casimir_power with
      d ∝ 1/ξ (parallel-plate intuition in 3D).
    • BBN / hot epochs (ξ ≫ ξ_lock): bonded outside modulator from nucleon-binding
      outside-curvature dynamics (~0.78 at T ≈ 0.1 MeV).
    """
    if abs(xi - xi_lock) < 1e-12:
        return 1.0

    if xi > xi_lock * 100.0:
        import hqiv_nuclear_outside_temperature_dynamics as notd

        return max(notd.outside_curvature_binding_modulator(xi, bonded=True), 1e-12)

    gap = casimir_gap_at_xi(xi)
    gap0 = casimir_gap_at_xi(xi_lock)
    # Unity when gap matches lock-in; softens toward small ξ on the discrete ladder.
    gap_ratio = (2.0 * math.sqrt(gap * gap0)) / max(gap + gap0, 1e-30)
    return max(min(gap_ratio**casimir_power, 4.0), 1e-6)


def curvature_budget_at_xi(xi: float, xi_lock: float = XI_LOCKIN) -> float:
    """κ₆ matter-slot B_curv(ξ): local/global Casimir readout (not ω_K chart ratio)."""
    return curvature_budget_local_global_at_xi(xi, xi_lock)


def curvature_seed_excess(budget: float) -> float:
    """Non-baryonic imprint strength above unit budget."""
    return max(0.0, budget - 1.0)


def trapping_selection_heavy(alpha: float, c: float) -> float:
    """Lean `trappingSelectionFromHeavyHopfShellWithAlpha a c`."""
    return 1.0 + c * alpha * math.log(1.0 + PHASE_LIFT_3 * alpha)


def t13_outer_suppression_at_xi(xi: float) -> float:
    """Lean `t13_outer_suppression_at_xi`: ωK(ξ) / modeCount."""
    return omega_k_xi(xi) / T13_OUTER_MODE_COUNT


def effective_casimir_scale_at_xi(xi: float) -> float:
    """Lean `effective_casimir_scale_at_xi`."""
    inner = trapping_selection_heavy(ALPHA_HEAVY, omega_k_xi(xi))
    return inner / t13_outer_suppression_at_xi(xi)


def heavy_lepton_gap_at_xi(xi: float) -> float:
    """Lean `heavy_lepton_gap_at_xi`."""
    scale0 = effective_casimir_scale_at_xi(XI_LOCKIN)
    return (4.0 / 5.0) * (xi / XI_LOCKIN) * (
        effective_casimir_scale_at_xi(xi) / max(scale0, 1e-30)
    )


def tuft_vev_factor_at_xi(xi: float) -> float:
    """Ratio heavy_lepton_gap_at_xi / heavy_lepton_gap_at_xi(5)."""
    g0 = heavy_lepton_gap_at_xi(XI_LOCKIN)
    return heavy_lepton_gap_at_xi(xi) / max(g0, 1e-30)


def xi_from_T_MeV(T_MeV: float) -> float:
    """Lean `bbnXiFromT_MeV` / `bbnShellXiFromT_MeV`."""
    return bbn.T_PL_MEV / T_MeV


def eta_at_horizon(n: int, N: int, eta_paper: float = ETA_PAPER) -> float:
    """Lean `eta_at_horizon n N` (positive curvature_integral branch)."""
    den = curvature_integral(N)
    if den <= 0.0:
        return eta_paper
    return eta_paper * curvature_integral(n) / den


COLOR_SINGLET_FRACTION = 1 / 3  # Lean: Hqiv.Physics.colorSingletFraction


def color_singlet_fraction() -> float:
    """Lean ``colorSingletFraction``."""
    return COLOR_SINGLET_FRACTION


def baryon_strong_color_fraction() -> float:
    """Lean ``baryonStrongColorFraction`` = (4/8)·(1/3) = 1/6."""
    return STRONG_CHANNEL_FRACTION * COLOR_SINGLET_FRACTION


def omega_b_from_omega_m(omega_m: float) -> float:
    """Lean ``omegaBFromOmegaM``."""
    return omega_m * baryon_strong_color_fraction()


def cluster_binding_contrast_relative() -> float:
    """Lean ``clusterBindingContrastRelative``."""
    bind_lock = bbn.cluster_binding_mev(REFERENCE_M, 4)
    bind_qcd = bbn.cluster_binding_mev(QCD_SHELL, 4)
    return (bind_lock - bind_qcd) / max(bind_lock, 1e-30)


def _cluster_binding_contrast_relative() -> float:
    """Deprecated alias for ``cluster_binding_contrast_relative``."""
    return cluster_binding_contrast_relative()


def baryogenesis_binding_curvature_correction_dimless() -> float:
    """Lean ``baryogenesis_binding_curvature_correction_dimless``."""
    return GAMMA * STRONG_CHANNEL_FRACTION * cluster_binding_contrast_relative()


def dynamic_binding_curvature_coupling_at_xi(xi: float, xi_lock: float = XI_LOCKIN) -> float:
    """
    Dynamic replacement for fixed κ_bind:

      κ(ξ) = γ · (4/8) · B_curv(ξ)

    Lean spine: `baryogenesis_binding_curvature_correction` + `curvature_budget_at_xi`.
    """
    return GAMMA * STRONG_CHANNEL_FRACTION * curvature_budget_at_xi(xi, xi_lock)


def dynamic_binding_curvature_correction_at_xi(
    xi: float,
    xi_lock: float = XI_LOCKIN,
) -> float:
    """κ(ξ) · (B_lock − B_qcd) / B_lock — dimensionless chemistry/BBN feedback."""
    return dynamic_binding_curvature_coupling_at_xi(xi, xi_lock) * _cluster_binding_contrast_relative()


def dynamic_binding_curvature_feedback_at_xi(
    xi: float,
    xi_lock: float = XI_LOCKIN,
) -> float:
    """1 + dynamic_binding_curvature_correction_at_xi."""
    return 1.0 + dynamic_binding_curvature_correction_at_xi(xi, xi_lock)


def dynamic_binding_curvature_feedback_second_order_at_xi(
    xi: float,
    xi_lock: float = XI_LOCKIN,
) -> float:
    """
    Second-order binding feedback: (1 + κ(ξ)·C_rel) · C₂(ξ)/C₂(ξ_lock).

    Lean: ``dynamicBindingCurvatureFeedbackSecondOrderAtXi`` (Hopf κ₆ lapse slot).
    """
    fb = dynamic_binding_curvature_feedback_at_xi(xi, xi_lock)
    c2 = tuft_lapse_concentration_at_xi(xi)
    c2_lock = tuft_lapse_concentration_at_xi(xi_lock)
    return fb * (c2 / max(c2_lock, 1e-30))


# Ice Ih tetrahedral H-bond coordination — reference bulk water density scale.
ICE_TETRAHEDRAL_CONTACT_REFERENCE = 4


def intermolecular_density_fraction(
    intermolecular_contacts: int,
    *,
    reference_contacts: int = ICE_TETRAHEDRAL_CONTACT_REFERENCE,
) -> float:
    """
    HQIV medium-density proxy ρ ∈ [0, 1]: intermolecular contact count vs ice reference.

    Dilute/GMTKN55 clusters → small ρ; bulk ice (4 contacts) → ρ = 1.
    """
    if reference_contacts <= 0:
        return 0.0
    return min(1.0, max(0.0, float(intermolecular_contacts) / float(reference_contacts)))


def curvature_second_order_scaled_for_medium_density(
    xi: float,
    medium_density_fraction: float,
    *,
    xi_lock: float = XI_LOCKIN,
) -> float:
    """
    Medium-specific κ₆ closure: full second-order curvature only at bulk density.

      f = 1 + (f₂(ξ) − 1) · ρ

    ρ = 0 recovers first-order/dilute limit; ρ = 1 is full ``dynamicBindingCurvatureFeedbackSecondOrderAtXi``.
    """
    fb2 = dynamic_binding_curvature_feedback_second_order_at_xi(xi, xi_lock)
    rho = min(1.0, max(0.0, medium_density_fraction))
    return 1.0 + (fb2 - 1.0) * rho


def compton_p_shell_active(triplet: tuple[int, int, int]) -> bool:
    """Lean ``dynamicComptonPShellActive``: middle p slot on (4,3,1)-type triplets."""
    m0, m1, m2 = triplet
    return m1 > 1 and m0 != m1


def dynamic_compton_eta_second_order(
    eta_p: float,
    triplet: tuple[int, int, int],
) -> float:
    """
    Second-order IR participation: η + (4/8)·η² when p shell active.

    Lean: ``dynamicComptonEtaSecondOrder``; mines LiH ``η_p · 3 · E_p`` valence trace.
    """
    if not compton_p_shell_active(triplet):
        return eta_p
    return eta_p + STRONG_CHANNEL_FRACTION * (eta_p**2)


def xi_from_compton_triplet(triplet: tuple[int, int, int]) -> float:
    """Mean contact ξ = m+1 over the Compton triplet shells."""
    return sum(float(m + 1) for m in triplet) / float(len(triplet))


def baryogenesis_binding_curvature_correction() -> float:
    """MeV-scale product (Lean ``baryogenesis_binding_curvature_correction``)."""
    bind_lock = bbn.cluster_binding_mev(REFERENCE_M, 4)
    return baryogenesis_binding_curvature_correction_dimless() * bind_lock


def lih_binding_curvature_correction(kappa_bind: float | None = None) -> float:
    """Deprecated alias: dynamic correction at ξ_lock (no free κ)."""
    _ = kappa_bind
    return dynamic_binding_curvature_correction_at_xi(XI_LOCKIN)


def lih_binding_curvature_feedback_factor(kappa_bind: float | None = None) -> float:
    """Deprecated alias: dynamic feedback at ξ_lock."""
    _ = kappa_bind
    return dynamic_binding_curvature_feedback_at_xi(XI_LOCKIN)


def eta_at_horizon_dynamic(
    n: int,
    N: int,
    eta_paper: float = ETA_PAPER,
) -> float:
    """Lean ``eta_at_horizon_dynamic``: dimensionless binding feedback at lock-in."""
    return eta_at_horizon(n, N, eta_paper) * (
        1.0 + baryogenesis_binding_curvature_correction_dimless()
    )


def bbn_curvature_temperature_slope(T_MeV: float, xi_lock: float = XI_LOCKIN) -> float:
    """Lean `bbnCurvatureTemperatureSlope`."""
    xi = xi_from_T_MeV(T_MeV)
    log_gap = max(math.log(max(xi / xi_lock, 1.0)), 1e-30)
    return max(0.0, omega_k_xi(xi) - omega_k_xi(xi_lock)) / log_gap


def bbn_bounded_curvature_temperature_slope(T_MeV: float, xi_lock: float = XI_LOCKIN) -> float:
    """Lean `bbnBoundedCurvatureTemperatureSlope`."""
    s = bbn_curvature_temperature_slope(T_MeV, xi_lock)
    return s / (1.0 + s)


def bbn_binding_release_factor(T_MeV: float, xi_lock: float = XI_LOCKIN) -> float:
    """Lean `bbnBindingReleaseFactor`."""
    bounded = bbn_bounded_curvature_temperature_slope(T_MeV, xi_lock)
    return math.exp(-(GAMMA * STRONG_CHANNEL_FRACTION * bounded))


def bbn_curvature_opportunity_factor(T_MeV: float, xi_lock: float = XI_LOCKIN) -> float:
    """BBN opportunity weight: bonded outside B_curv at epoch ξ(T)."""
    return curvature_budget_local_global_at_xi(xi_from_T_MeV(T_MeV), xi_lock)


def tuft_lapse_detuning_obs_at_xi(xi: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Lean `tuftLapseDetuningObsAtXi`: Θ_local(ξ)·(1+γ) + (N−1) at HQVM lapse (Φ, φ(ξ), t)."""
    hqvm_lapse = 1.0 + phi * t
    return xi * (1.0 + GAMMA) + (hqvm_lapse - 1.0)


def tuft_lapse_concentration_at_xi(xi: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Lean `tuftLapseConcentrationAtXi` (C₂): Rindler-dressed lapse concentration on referenceM."""
    obs = tuft_lapse_detuning_obs_at_xi(xi, phi, t)
    delta = C_RINDLER_SHARED * obs
    num = 1.0 + C_RINDLER_SHARED * REFERENCE_M + delta
    den = 1.0 + C_RINDLER_SHARED * REFERENCE_M
    return (1.0 + GAMMA) / 2.0 * num / den


def tuft_hopf_kappa6_at_xi(xi: float, phi: float = 0.0, t: float = 0.0) -> float:
    """Lean `tuftHopfKappa6AtXi`: η_paper · B_curv(ξ) · γ · C₂(ξ,Φ,t)."""
    return (
        ETA_PAPER
        * curvature_budget_at_xi(xi)
        * GAMMA
        * tuft_lapse_concentration_at_xi(xi, phi, t)
    )


def tuft_hopf_kappa6_at_lockin(phi: float = 0.0, t: float = 0.0) -> float:
    return tuft_hopf_kappa6_at_xi(XI_LOCKIN, phi, t)


def bbn_neutron_proton_gap_mev() -> float:
    """Lean `bbnNeutronProtonGap` (= derivedDeltaM at lock-in)."""
    return float(bbn.load_witness()["derivedDeltaM_MeV"])


def bbn_dynamic_c2_freezeout_t_mev(eta: float, Q_np: float | None = None) -> float:
    """Lean `bbnFreezeoutTemperatureMeV`: Q_np / log(η₁₀)."""
    return bbn.freezeout_temperature_mev(Q_np or bbn_neutron_proton_gap_mev(), eta)


def bbn_dynamic_c2_bottleneck_t_mev(eta: float, Q_np: float | None = None) -> float:
    """Lean `bbnDynamicC2BottleneckT_MeV`: γ · (4/8) · T_freeze(η)."""
    return GAMMA * STRONG_CHANNEL_FRACTION * bbn_dynamic_c2_freezeout_t_mev(eta, Q_np)


def bbn_dynamic_c2_reference_t_mev(eta: float, Q_np: float | None = None) -> float:
    """Lean `bbnDynamicC2ReferenceT_MeV`: κ₆ anchor at freeze-out temperature."""
    return bbn_dynamic_c2_freezeout_t_mev(eta, Q_np)


def bbn_nucleon_trace_binding_effective_at_t(
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> float:
    """Lean `bbnNucleonTraceBinding_effectiveAtT`."""
    return hes.e_bind_from_nucleon_trace_mev(m_shell, c) * bbn_binding_release_factor(T_MeV)


def bbn_deuteron_binding_q_effective_at_t(
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> float:
    """Lean `bbnDeuteronBindingQ_effectiveAtT`."""
    return 2.0 * bbn_nucleon_trace_binding_effective_at_t(T_MeV, m_shell, c) * bbn.valley_binding_factor(2)


def bbn_helium4_binding_q_effective_at_t(
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> float:
    """Lean `bbnHelium4BindingQ_effectiveAtT`."""
    return 4.0 * bbn_nucleon_trace_binding_effective_at_t(T_MeV, m_shell, c) * bbn.valley_binding_factor(4)


def bbn_he3_binding_q_effective_at_t(
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> float:
    """³He effective Q at BBN temperature (valley trace × release factor)."""
    return 3.0 * bbn_nucleon_trace_binding_effective_at_t(T_MeV, m_shell, c) * bbn.valley_binding_factor(3)


def bbn_light_binding_q_effective_at_t(
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """
    D, ⁴He, ³He binding Q at epoch ``T`` via ``bbnBindingReleaseFactor``.

    Mirrors ``dynamicBBNReadoutAtT`` thermal/exponent inputs (curvature-temperature
    release on the valley composite trace — not raw lock-in network Q).
    """
    return (
        bbn_deuteron_binding_q_effective_at_t(T_MeV, m_shell, c),
        bbn_helium4_binding_q_effective_at_t(T_MeV, m_shell, c),
        bbn_he3_binding_q_effective_at_t(T_MeV, m_shell, c),
    )


def bbn_dynamic_c2_lapse_exponent(
    eta: float,
    *,
    T_MeV: float,
    m_shell: int = REFERENCE_M,
    c: float = 1.0,
) -> float:
    """Lean `bbnDynamicC2LapseExponent`: γ · (4/8) · Q_D_eff(T) / Q_np."""
    Q_D_eff = bbn_deuteron_binding_q_effective_at_t(T_MeV, m_shell, c)
    return GAMMA * STRONG_CHANNEL_FRACTION * (Q_D_eff / bbn_neutron_proton_gap_mev())


def bbn_dynamic_c2_opportunity_suppression(
    T_MeV: float,
    *,
    eta: float,
    m_nucleon: float,
    m_shell: int = REFERENCE_M,
    Q_np: float | None = None,
) -> float:
    """
    Deuterium-bottleneck lapse clock from dynamic κ₆ (no fitted MeV slots).

    Bottleneck: T ≤ γ·(4/8)·T_freeze(η).  Anchor: T_ref = T_freeze(η).
    Exponent: γ·(4/8)·Q_D_eff(T)/Q_np via `bbnBindingReleaseFactor`.
    """
    if T_MeV > bbn_dynamic_c2_bottleneck_t_mev(eta, Q_np):
        return 1.0
    xi = xi_from_T_MeV(T_MeV)
    xi_ref = xi_from_T_MeV(bbn_dynamic_c2_reference_t_mev(eta, Q_np))
    k6 = tuft_hopf_kappa6_at_xi(xi)
    k6_ref = tuft_hopf_kappa6_at_xi(xi_ref)
    w = bbn_dynamic_c2_lapse_exponent(eta, T_MeV=T_MeV, m_shell=m_shell)
    return (k6_ref / max(k6, 1e-300)) ** w


def bbn_dynamic_c2_readout_at_T(
    T_MeV: float,
    *,
    eta: float,
    m_nucleon: float,
    m_shell: int = REFERENCE_M,
) -> dict[str, float]:
    """Diagnostics for dynamic C₂ / κ₆ on the BBN temperature ladder."""
    xi = xi_from_T_MeV(T_MeV)
    xi_ref = xi_from_T_MeV(bbn_dynamic_c2_reference_t_mev(eta))
    c2 = tuft_lapse_concentration_at_xi(xi)
    c2_ref = tuft_lapse_concentration_at_xi(xi_ref)
    k6 = tuft_hopf_kappa6_at_xi(xi)
    k6_ref = tuft_hopf_kappa6_at_xi(xi_ref)
    return {
        "T_MeV": T_MeV,
        "eta": eta,
        "xi": xi,
        "T_freeze_MeV": bbn_dynamic_c2_freezeout_t_mev(eta),
        "T_bottleneck_MeV": bbn_dynamic_c2_bottleneck_t_mev(eta),
        "Q_D_eff_MeV": bbn_deuteron_binding_q_effective_at_t(T_MeV, m_shell),
        "lapse_exponent": bbn_dynamic_c2_lapse_exponent(eta, T_MeV=T_MeV, m_shell=m_shell),
        "B_curv": curvature_budget_at_xi(xi),
        "C2": c2,
        "C2_over_C2_ref": c2 / max(c2_ref, 1e-300),
        "kappa6": k6,
        "kappa6_over_kappa6_ref": k6 / max(k6_ref, 1e-300),
        "c2_opportunity_suppression": bbn_dynamic_c2_opportunity_suppression(
            T_MeV, eta=eta, m_nucleon=m_nucleon, m_shell=m_shell
        ),
    }


UCN_TRAP_REFERENCE_FIELD_TESLA = 1.0
REPRESENTATIVE_BOTTLE_TRAP_FIELD_TESLA = 2.5
REPRESENTATIVE_BEAM_TRAP_FIELD_TESLA = 0.0
DEFAULT_BETA_WEAK_BRIDGE_SHAPE = 1.0 / 18.0  # Lean `defaultBetaWeakBridge_shape_eq_one_div_eighteen`


def trap_magnetic_curvature_fraction(
    B_tesla: float,
    B_ref_tesla: float = UCN_TRAP_REFERENCE_FIELD_TESLA,
) -> float:
    """Lean `trapMagneticCurvatureFraction`: B maps to ρ_mag ∈ [0,1] (curvature, not Zeeman)."""
    if B_ref_tesla <= 0.0:
        return 0.0
    return max(0.0, min(1.0, B_tesla / B_ref_tesla))


def trap_weak_width_factor_from_magnetic(
    B_tesla: float,
    B_ref_tesla: float = UCN_TRAP_REFERENCE_FIELD_TESLA,
) -> float:
    """Lean `trapWeakWidthFactorFromMagnetic`: Γ_eff = f(B) · Γ₀ on the weak Fano/Hopf bridge."""
    rho = trap_magnetic_curvature_fraction(B_tesla, B_ref_tesla)
    return 1.0 + GAMMA * rho * DEFAULT_BETA_WEAK_BRIDGE_SHAPE


def saturated_beam_over_bottle_lifetime_ratio() -> float:
    """Lean `saturatedBeamOverBottleLifetimeRatio` = 46/45."""
    f_bottle = trap_weak_width_factor_from_magnetic(REPRESENTATIVE_BOTTLE_TRAP_FIELD_TESLA)
    f_beam = trap_weak_width_factor_from_magnetic(REPRESENTATIVE_BEAM_TRAP_FIELD_TESLA)
    return f_bottle / f_beam


def apparent_beta_half_life_from_method(
    central_half_life_s: float,
    local_width_factor: float,
    outside_support_factor: float = 1.0,
) -> float:
    """Lean `apparentBetaHalfLifeFromMethod`: τ_app = τ0 * support / width."""
    if local_width_factor <= 0.0:
        return math.inf
    return central_half_life_s * outside_support_factor / local_width_factor


def method_shift_ppm(local_width_factor: float, outside_support_factor: float = 1.0) -> float:
    """Fractional apparent half-life shift in ppm relative to the central slot."""
    tau_ratio = apparent_beta_half_life_from_method(1.0, local_width_factor, outside_support_factor)
    return 1.0e6 * (tau_ratio - 1.0)


def collider_beta_method_width_factor(
    B_tesla: float,
    reference_tesla: float = 4.0,
    stream_fraction: float = 0.0,
) -> float:
    """Lean `colliderCurvatureWidthFactor` specialized to β-lifetime method comparisons."""
    if reference_tesla <= 0.0:
        field_density = 0.0
    else:
        field_density = (max(B_tesla, 0.0) / reference_tesla) ** 2
    stream_density = max(stream_fraction, 0.0) ** 2
    return 1.0 + GAMMA * DEFAULT_BETA_WEAK_BRIDGE_SHAPE * (field_density + stream_density)


def bbn_shell_reaction_opportunity(
    T_MeV: float,
    T_next_MeV: float,
    xi_lock: float = XI_LOCKIN,
) -> float:
    """Lean `bbnShellReactionOpportunity` / `dynamicBBNShellReactionOpportunity`."""
    xi = xi_from_T_MeV(T_MeV)
    xi_next = xi_from_T_MeV(T_next_MeV)
    log_shell = max(math.log(max(xi_next / xi, 1.0)), 0.0)
    log_lock = max(math.log(max(xi / xi_lock, 1.0)), 0.0)
    return log_shell * log_lock**3 * bbn_curvature_opportunity_factor(T_MeV)
