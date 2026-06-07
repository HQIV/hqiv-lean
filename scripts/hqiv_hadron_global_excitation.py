#!/usr/bin/env python3
"""
Global excitation correction on the TUFT vev-pinned hadron tower.

Mirrors `Hqiv/Physics/HadronGlobalExcitationCorrection.lean`.

Increment-only factorization (vev ground unchanged):

  m(ξ, n, ℓ) = g(ξ) + (g(ξ)/g₀) · Δ_lockin(n, ℓ) · G(ξ, n, ℓ)

  G = channel_twist × (w_S7 / w_S7|_{1,0}) / ijk_factor
"""

from __future__ import annotations

import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_tuft_hadron_s7_confinement as s7

import hqiv_tuft_shell_chart as tsc

REFERENCE_M = tsc.REFERENCE_M
TUFT_HEAVY_CHART_SHELL = tsc.TUFT_HEAVY_CHART_SHELL
DERIVED_PROTON_MEV = s7.DERIVED_PROTON_MEV


def omaxwell_fano_detuning1_jet(m: int) -> float:
    """Lean `omaxwellFanoDetuning1Jet`: 1 + (γ/2) · m."""
    return 1.0 + (lean.GAMMA / 2.0) * float(m)


def meta_horizon_excited_channel_shell(n: int, ell: int) -> int:
    """Lean `tuftHadronExcitedChannelShell` = `tuftHadronModeShell` on heavy TUFT chart."""
    return tsc.tuft_hadron_mode_shell(n, ell)


def meta_horizon_excited_channel_xi(n: int, ell: int) -> float:
    """Lean `metaHorizonExcitedChannelXi` = `xiOfShell` on the excited channel."""
    return float(meta_horizon_excited_channel_shell(n, ell) + 1)


def meta_horizon_excited_detuning_twist(n: int, ell: int) -> float:
    """Lean `tuftHadronExcitedDetuningTwist`."""
    shell = meta_horizon_excited_channel_shell(n, ell)
    return omaxwell_fano_detuning1_jet(shell) / omaxwell_fano_detuning1_jet(TUFT_HEAVY_CHART_SHELL)


def meta_horizon_excited_channel_twist_at_epoch(xi: float, n: int, ell: int) -> float:
    """Lean `metaHorizonExcitedChannelTwistAtEpoch`."""
    xi_ch = meta_horizon_excited_channel_xi(n, ell)
    return (lean.omega_k_xi(xi_ch) / lean.omega_k_xi(xi)) * meta_horizon_excited_detuning_twist(n, ell)


def hadron_s7_whole_mode_weight_normalized(n: int, ell: int) -> float:
    """Lean `hadronS7WholeModeWeightNormalized` (anchor radial Δ at n=1, ℓ=0)."""
    w = s7.hadron_s7_whole_mode_weight(n, ell)
    w_ref = s7.hadron_s7_whole_mode_weight(1, 0)
    return w / w_ref


def tuft_hadron_global_channel_twist_ratio(xi: float, n: int, ell: int) -> float:
    """Lean `tuftHadronGlobalChannelTwistRatio`: unity at ξ_lock."""
    t = meta_horizon_excited_channel_twist_at_epoch(xi, n, ell)
    t0 = meta_horizon_excited_channel_twist_at_epoch(lean.XI_LOCKIN, n, ell)
    return t / t0


def tuft_hadron_confinement_increment_shape(n: int, ell: int) -> float:
    """Lean `tuftHadronConfinementIncrementShape` (Phase 2; constant in ξ today)."""
    w = hadron_s7_whole_mode_weight_normalized(n, ell)
    return w / s7.hadron_ijk_excitation_confinement_factor(n, ell)


def tuft_hadron_global_excitation_factor_at_epoch(xi: float, n: int, ell: int) -> float:
    """Lean `tuftHadronGlobalExcitationFactorAtEpoch`: lock-in-normalized channel twist."""
    return tuft_hadron_global_channel_twist_ratio(xi, n, ell)


def tuft_hadron_beltrami_increment_operational_mev(n: int, ell: int) -> float:
    """Lean `tuftHadronBeltramiIncrementOperational`."""
    rad = hes.delta_m_radial_operational_mev(n, derived_proton_mev=DERIVED_PROTON_MEV)
    orb = hes.delta_m_orbital_operational_mev(ell, derived_proton_mev=DERIVED_PROTON_MEV)
    return rad + orb


def tuft_hadron_excited_mass_with_global_correction_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """Lean `tuftHadronExcitedMassWithGlobalCorrectionAtXi_MeV`."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    g0 = tmse.tuft_hadron_ground_at_xi_mev(tmse.XI_LOCKIN)
    inc = tuft_hadron_beltrami_increment_operational_mev(n, ell)
    factor = tuft_hadron_global_excitation_factor_at_epoch(xi, n, ell)
    return g + (g / g0) * inc * factor


def tuft_hadron_trapped_inside_ratio(n: int, ell: int) -> float:
    """Lean `tuftHadronTrappedInsideRatio` on the heavy TUFT chart."""
    m = tsc.tuft_hadron_mode_shell(n, ell)
    return hes.meta_horizon_trapped_inside_ratio(m, TUFT_HEAVY_CHART_SHELL)


def tuft_hadron_excited_mass_unified_inside_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """Lean `tuftHadronExcitedMassUnifiedInsideAtXi_MeV` — global readout on heavy chart."""
    import hqiv_tuft_global_hadron_readout as tgh

    return tgh.tuft_excited_mass_global_at_xi_mev(xi, tgh.TuftExcitationChannel.baryon(n, ell))


def tuft_hadron_excited_mass_global_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """Alias for `tuftExcitedMassGlobalAtXi_MeV` on baryon channels."""
    import hqiv_tuft_global_hadron_readout as tgh

    return tgh.tuft_excited_mass_global_at_xi_mev(xi, tgh.TuftExcitationChannel.baryon(n, ell))


def tuft_hadron_excited_mass_unified_inside_at_xi_mev_legacy(xi: float, n: int, ell: int) -> float:
    """
    Lean `tuftHadronExcitedMassUnifiedInsideAtXi_MeV`:

      m(ξ,n,ℓ) = g(ξ) · [ 1 + (R_in(m) − 1) · G_twist(ξ,n,ℓ) ]

    At ξ_lock: equals vev ground × trapped inside ratio (= trapped readout when g = m_p).
    """
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    r = tuft_hadron_trapped_inside_ratio(n, ell)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    return g * (1.0 + (r - 1.0) * twist)


def tuft_hadron_excited_mass_unified_with_curvature_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """
    Phase 2b: inside surplus modulated by same-epoch Casimir balance at channel ξ_m.

    m = g · [ 1 + (R_in − 1) · G_twist · B_curv(ξ_m) / B_curv(ξ_lock) ]
    """
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    r = tuft_hadron_trapped_inside_ratio(n, ell)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    xi_m = meta_horizon_excited_channel_xi(n, ell)
    b_ratio = lean.curvature_budget_local_global_at_xi(xi_m) / lean.curvature_budget_local_global_at_xi(
        lean.XI_LOCKIN
    )
    return g * (1.0 + (r - 1.0) * twist * b_ratio)


def tuft_hadron_excited_mass_unified_ijk_channel_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """
    Phase 2c research: one sorted f^{ijk} channel carries the inside surplus (1/9 of closure).

    m = g · [ 1 + (R_in − 1) · G_twist / 9 ]
    """
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    r = tuft_hadron_trapped_inside_ratio(n, ell)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    budget = float(s7.HADRON_IJK_SORTED_TRIPLE_BUDGET)
    return g * (1.0 + (r - 1.0) * twist / budget)


def tuft_hadron_trapped_inside_ratio_phase(n: int, ell: int) -> float:
    """Lean `tuftHadronTrappedInsideRatioPhase`: Compton-deficit on heavy TUFT chart."""
    import hqiv_continuous_shell_mass as csm

    m_eff = csm.effective_m_phase(n, ell, chart_shell=TUFT_HEAVY_CHART_SHELL)
    return csm.inside_ratio_discrete(m_eff, m_ref=float(TUFT_HEAVY_CHART_SHELL))


def tuft_hadron_excited_mass_unified_phase_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """
    Lean `tuftHadronExcitedMassUnifiedPhaseAtXi_MeV`:

      m(ξ,n,ℓ) = g(ξ) · [ 1 + (R_in(m_eff) − 1) · G_twist(ξ,n,ℓ) ]

    `m_eff = totalModeShell − Σ 1/(4ξ_j)` (Compton quarter-leak on the null lattice).
    """
    import hqiv_continuous_shell_mass as csm
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    r = tuft_hadron_trapped_inside_ratio_phase(n, ell)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    return g * (1.0 + (r - 1.0) * twist)


def tuft_hadron_excited_mass_unified_split_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """
    Split-channel unified readout (Python research; Lean mirror pending inversion lemma):

      m(ξ,n,ℓ) = g(ξ) · [ 1 + (R_in(ξ_split(n,ℓ)) − 1) · G_twist(ξ,n,ℓ) ]

    Radial and orbital Beltrami increments invert separately on the trapped curve,
    breaking the n vs ℓ degeneracy at fixed n+ℓ.
    """
    import hqiv_continuous_shell_mass as csm
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    xi_ch = csm.effective_xi_split(n, ell)
    r = csm.inside_ratio_at_xi(xi_ch, mode=csm.ContinuousReadout.INTERP)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    return g * (1.0 + (r - 1.0) * twist)


def tuft_hadron_excited_mass_unified_ijk_weighted_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """
    f^{ijk} channel occupancy on the inside surplus (not 1/9 suppression):

      m = g · [ 1 + (R_in − 1) · G_twist · hadronIjkExcitationConfinementFactor(n,ℓ) ]
    """
    import hqiv_tuft_hadron_s7_confinement as s7
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    r = tuft_hadron_trapped_inside_ratio(n, ell)
    twist = tuft_hadron_global_channel_twist_ratio(xi, n, ell)
    chi = s7.hadron_ijk_excitation_confinement_factor(n, ell)
    return g * (1.0 + (r - 1.0) * twist * chi)


def build_unified_excitation_rows(xi: float | None = None) -> list:
    """Back-compat: one global row per baryon slot."""
    import hqiv_tuft_global_hadron_readout as tgh
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    if xi is None:
        xi = tmse.XI_LOCKIN
    return tgh.build_global_rows(xi, tgh.BARYON_EXCITED_CHANNELS, "baryon")


def build_global_excitation_rows(xi: float | None = None) -> list:
    """Back-compat alias — superseded by global readout."""
    return build_unified_excitation_rows(xi)
