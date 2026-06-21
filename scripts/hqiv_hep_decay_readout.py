#!/usr/bin/env python3
"""
Lean-aligned HEP decay readout primitives.

Mirror of `Hqiv.Physics.HepDecayReadout.lean` — single Python source for formulas
used by `hqiv_hep_decay_chain.py` and uncertainty propagation.

Lean modules:
  HadronMassReadout, QuarkMetaResonance, HepDecayReadout,
  WeakFanoHopfBridge, NuclearAndAtomicSpectra, Forces
"""

from __future__ import annotations

import math
from typing import Literal

import hqiv_lean_physics_primitives as lean
import hqiv_mass_calculator_core as hmc

LEAN_MODULE = "Hqiv.Physics.HepDecayReadout"
EXPANSION_MODULE = "scripts/hqiv_hep_multichannel_expansion.py"
OpenFlavourContactKind = Literal[
    "unit_seed",
    "charm_pion_only",
    "charmed_baryon_three_body",
    "charmed_baryon_double_monogamy",
    "bottom_external_weak",
    "bottom_strange_double_monogamy",
    "bottom_strange_open_charm",
    "open_charm_cascade",
    "finite_channel_completion",
    "finite_open_bottom_completion",
    "bottom_neutral_spectator",
    "double_monogamy_exclusion",
    "spectator_half_monogamy",
    "neutral_spectator_complement",
    "isospin_half_weak",
    "isospin_half_neutral_outlet",
    "light_baryon_neutral_isospin_outlet",
    "lepton_neutrino_weak_outlet",
    "semileptonic_neutrino_channel_completion",
    "light_kaon_semileptonic_neutrino_completion",
    "open_charm_semileptonic_neutrino_completion",
    "open_charm_hadronic_monogamy_exclusion",
    "charmed_baryon_semileptonic_hadronic",
    "isospin_half_hadronic_monogamy_exclusion",
    "isospin_half_neutral_hadronic_monogamy_exclusion",
    "isospin_half_hadronic_semileptonic_competition",
    "isospin_half_neutral_hadronic_semileptonic_competition",
    "hidden_strangeness_kk_retention",
    "hidden_strangeness_vector_leak",
    "hidden_strangeness_pole_discharge",
    "cascade_lambda_ground",
    "ozi_suppressed_strong",
]

# HadronMassReadout.chiralPseudoscalarFactor = (4/9)²
CHIRAL_PSEUDOSCALAR_FACTOR = (4.0 / 9.0) ** 2

# HadronMassReadout.pionDecayConstantRatio = √(4/9) = 2/3
PION_DECAY_CONSTANT_RATIO = 2.0 / 3.0


def ckm_slot_us_squared() -> float:
    """Lean `ckmSlotUS2` = γ/8."""
    return lean.GAMMA / 8.0


def ckm_slot_cd_squared() -> float:
    """Lean `ckmSlotCD2` = γ/16."""
    return lean.GAMMA / 16.0


def ckm_slot_cb_squared() -> float:
    """Lean `ckmSlotCB2` = γ/32."""
    return lean.GAMMA / 32.0


def hidden_quarkonium_em_contact_factor() -> float:
    """Lean `hiddenQuarkoniumEMContactFactor` = bottomExternalWeakContact + c_rindler_shared = 37/10."""
    return hidden_quarkonium_em_contact_from_spine_slots()


def hidden_quarkonium_em_contact_from_spine_slots() -> float:
    """Lean `hiddenQuarkoniumEMContactFactor = bottomExternalWeakContact + c_rindler_shared`."""
    return bottom_external_weak_contact() + lean.GAMMA / 2.0


def hidden_quarkonium_em_contact_full_fano_return() -> float:
    """Full second-order Fano return (`+γ`) contact: 39/10; overshoots J/ψ leptonic BR once pooled."""
    return bottom_external_weak_contact() + lean.GAMMA


def hidden_quarkonium_em_contact_pdg_reverse_engineered() -> float:
    """Naive one-channel fit multiplier 0.059/0.017 ≈ 3.47 — not equal to the proved 37/10."""
    return 347.0 / 100.0


def ozi_suppression_factor(n_vector_modes: int) -> float:
    """Lean `oziSuppressionFactor` for hidden quarkonia → light hadrons."""
    n = max(int(n_vector_modes), 0)
    return (lean.GAMMA / 4.0) * (1.0 + lean.GAMMA * n / 8.0)


def open_charm_production_weight() -> float:
    """Lean `openCharmProductionWeight` = γ/4."""
    return lean.GAMMA / 4.0


def open_bottom_production_weight() -> float:
    """Lean `openBottomProductionWeight` = γ/8."""
    return lean.GAMMA / 8.0


def open_flavour_topology_seed_weight() -> float:
    """Lean `openFlavourTopologySeedWeight` = 1."""
    return 1.0


def lepton_neutrino_pair_aperture() -> float:
    """Lean `leptonNeutrinoPairAperture` = γ/4 = 1/10."""
    return lean.GAMMA / 4.0


def bottom_strange_spectator_coherence_weight() -> float:
    """Lean `bottomStrangeSpectatorCoherenceWeight` = openCharm/openBottom = 2."""
    return open_charm_production_weight() / open_bottom_production_weight()


def charm_pion_only_suppression() -> float:
    """Lean `charmPionOnlySuppression` = (γ/16)/(1-γ/16-γ/32) = 2/77."""
    return ckm_slot_cd_squared() / (1.0 - ckm_slot_cd_squared() - ckm_slot_cb_squared())


def charmed_baryon_three_body_contact() -> float:
    """Lean `charmedBaryonThreeBodyContact` = 1/(γ/4) = 10."""
    return 1.0 / open_charm_production_weight()


def bottom_external_weak_contact() -> float:
    """Lean `bottomExternalWeakContact` = 1/γ + 1 = 7/2."""
    return 1.0 / lean.GAMMA + 1.0


def bottom_strange_double_monogamy_coherence() -> float:
    """Lean ``bottomStrangeDoubleMonogamyCoherence`` = 1/γ² = 25/4."""
    return 1.0 / (lean.GAMMA**2)


def bottom_strange_open_charm_contact() -> float:
    """Lean ``bottomStrangeOpenCharmContact`` = (1/γ²)·(openCharm/openBottom) = 25/2."""
    return (
        bottom_strange_double_monogamy_coherence()
        * open_charm_production_weight()
        / open_bottom_production_weight()
    )


def heavy_quarkonium_cascade_weight() -> float:
    """Lean `heavyQuarkoniumCascadeWeight` = openCharm / openBottom = 2."""
    return open_charm_production_weight() / open_bottom_production_weight()


def neutral_light_pair_cascade_weight() -> float:
    """Lean `neutralLightPairCascadeWeight` = γ² = 4/25."""
    return lean.GAMMA**2


def hidden_bottom_jpsi_inclusive_boost() -> float:
    """Lean `hiddenBottomJpsiInclusiveBoost` = 1 + γ/2 + γ/5 + γ/15 = 98/75."""
    return 1.0 + lean.GAMMA / 2.0 + lean.GAMMA / 5.0 + lean.GAMMA / 15.0


def hidden_bottom_jpsi_neutral_cascade_contact() -> float:
    """Lean `hiddenBottomJpsiNeutralCascadeContact`."""
    return neutral_light_pair_cascade_weight() * hidden_bottom_jpsi_inclusive_boost()


def hidden_bottom_jpsi_pole_contact() -> float:
    """Lean `hiddenBottomJpsiPoleContact`."""
    return open_charm_production_weight() * hidden_bottom_jpsi_inclusive_boost()


def finite_channel_completion_aperture() -> float:
    """Lean `finiteChannelCompletionAperture` = γ · weakBridgeShape = 1/45."""
    return lean.GAMMA / 18.0


def finite_open_bottom_completion_contact() -> float:
    """Lean `finiteOpenBottomCompletionContact` = (1/45)(1+5γ) = 1/15."""
    return finite_channel_completion_aperture() * (1.0 + 5.0 * lean.GAMMA)


# Gauge-sector curvature readout (HepDecayReadout.gaugeSector*)

BETA_1 = 41.0 / 10.0
BETA_2 = 19.0 / 6.0
BETA_3 = 7.0
BETA_SUM = BETA_1 + BETA_2 + BETA_3  # 214/15

EM_CHANNEL_FRACTION = 1.0 / 8.0
WEAK_CHANNEL_FRACTION = 3.0 / 8.0
COLOUR_CF = 4.0 / 3.0
COLOUR_NC = 3.0

_LEPTON_SPECIES = frozenset(
    {"e_plus", "e_minus", "mu_plus", "mu_minus", "e+", "e-", "mu+", "mu-"}
)


def _gauge_sector_base_curvature_aperture(
    channel_fraction: float, beta_magnitude: float
) -> float:
    return channel_fraction * lean.GAMMA * (beta_magnitude / BETA_SUM)


def weak_hadronic_strong_confinement_aperture() -> float:
    """Lean `weakHadronicStrongConfinementAperture` = 8/3."""
    return 1.0 + COLOUR_CF * lean.STRONG_CHANNEL_FRACTION / lean.GAMMA


def weak_semileptonic_hopf_bridge_aperture() -> float:
    """Lean `weakSemileptonicHopfBridgeAperture` = 46/45."""
    import hqiv_weak_fano_hopf_bridge as weak_bridge

    return 1.0 + lean.GAMMA * weak_bridge.weak_bridge_shape()


def strong_gauge_curvature_readout() -> float:
    """Lean `strongGaugeCurvatureReadout` = 14/321."""
    base = _gauge_sector_base_curvature_aperture(
        lean.STRONG_CHANNEL_FRACTION, BETA_3
    )
    return base * (COLOUR_CF / COLOUR_NC)


def weak_gauge_hadronic_curvature_readout() -> float:
    """Lean `weakGaugeHadronicCurvatureReadout`."""
    base = _gauge_sector_base_curvature_aperture(WEAK_CHANNEL_FRACTION, BETA_2)
    return base / weak_hadronic_strong_confinement_aperture()


def weak_gauge_semileptonic_curvature_readout() -> float:
    """Lean `weakGaugeSemileptonicCurvatureReadout`."""
    base = _gauge_sector_base_curvature_aperture(WEAK_CHANNEL_FRACTION, BETA_2)
    return base * weak_semileptonic_hopf_bridge_aperture()


def em_gauge_curvature_readout() -> float:
    """Lean `emGaugeCurvatureReadout`."""
    return _gauge_sector_base_curvature_aperture(EM_CHANNEL_FRACTION, BETA_1)


def daughters_are_semileptonic_weak(daughter_ids: tuple[str, ...] | list[str]) -> bool:
    return any(d in _LEPTON_SPECIES for d in daughter_ids)


def gauge_sector_curvature_readout(
    channel: str,
    *,
    daughter_ids: tuple[str, ...] | list[str] | None = None,
    semileptonic: bool | None = None,
) -> float:
    """
    Per-channel gauge-geometry readout factor (no fitted constants).

    Maps decay channel tags to EM / weak / strong curvature apertures derived from
    octonion carrier shares and O-Maxwell β magnitudes.
    """
    if channel == "stable":
        return 1.0
    if channel == "strong":
        return strong_gauge_curvature_readout()
    if channel == "electromagnetic":
        return em_gauge_curvature_readout()
    if channel in ("weak", "weak_hadron"):
        is_semileptonic = (
            semileptonic
            if semileptonic is not None
            else (
                daughters_are_semileptonic_weak(daughter_ids or ())
                if daughter_ids is not None
                else False
            )
        )
        if is_semileptonic:
            return weak_gauge_semileptonic_curvature_readout()
        return weak_gauge_hadronic_curvature_readout()
    return 1.0


def gauge_curvature_width_factor(
    parent_id: str,
    channel: str,
    daughter_ids: tuple[str, ...] | list[str],
) -> float:
    """
    Outlet-aware gauge curvature dress on partial widths (Lean ``hepDecayGaugeCurvatureWidthFactor``).

    Applied only on open-flavour / bottom discharge competition.  Certified light-weak
  pole widths and EM readouts keep unit dress (curvature already in spine / α slots).
    """
    import hqiv_hep_decay_certificates as cert
    import hqiv_hep_patch_species as hps

    if channel == "electromagnetic":
        return 1.0
    if cert.is_light_weak_discharge_parent_id(parent_id):
        return 1.0

    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return gauge_sector_curvature_readout(channel, daughter_ids=daughter_ids)

    if not (
        parent.is_open_charm
        or parent.is_open_bottom
        or parent.is_open_charm_baryon_ground
    ):
        return 1.0

    if channel in ("weak", "weak_hadron"):
        import hqiv_property_channels as pc

        edge = pc.classify_weak_edge(parent_id, daughter_ids)
        if edge is not None:
            outlet = edge.outlet
            if outlet in ("bottom_strange_hidden_phi", "bottom_strange_open_charm"):
                return weak_gauge_hadronic_curvature_readout()
            if outlet == "semileptonic_visible_lepton":
                return weak_gauge_semileptonic_curvature_readout()
            return weak_gauge_hadronic_curvature_readout()
    return gauge_sector_curvature_readout(channel, daughter_ids=daughter_ids)


def double_monogamy_exclusion_factor() -> float:
    """Lean `doubleMonogamyExclusionFactor` = 1 - γ² = 21/25."""
    return 1.0 - lean.GAMMA**2


def spectator_half_monogamy_contact() -> float:
    """Lean `spectatorHalfMonogamyContact` = 1 + γ/2 = 6/5."""
    return 1.0 + lean.GAMMA / 2.0


def neutral_spectator_monogamy_complement() -> float:
    """Lean `neutralSpectatorMonogamyComplement` = 1/(1-γ) = 5/3."""
    return 1.0 / (1.0 - lean.GAMMA)


def bottom_neutral_spectator_contact() -> float:
    """Lean `bottomNeutralSpectatorContact` = (5/3)(1-γ/4) = 3/2."""
    return neutral_spectator_monogamy_complement() * (1.0 - lean.GAMMA / 4.0)


def cascade_lambda_ground_contact() -> float:
    """Lean `cascadeLambdaGroundContact` = (5/3)(1+γ+γ/2+3γ/40) = 163/60."""
    return neutral_spectator_monogamy_complement() * (
        1.0 + lean.GAMMA + lean.GAMMA / 2.0 + 3.0 * lean.GAMMA / 40.0
    )


def hidden_strangeness_pole_discharge_contact() -> float:
    """Lean `hiddenStrangenessPoleDischargeContact` = 1 + γ + γ/4 + γ/4 = 8/5."""
    return 1.0 + lean.GAMMA + lean.GAMMA / 4.0 + lean.GAMMA / 4.0


def isospin_half_weak_contact() -> float:
    """Lean `isospinHalfWeakContact` = 1 + γ = 7/5 (ΔI = ½ charged outlet)."""
    return 1.0 + lean.GAMMA


def isospin_half_neutral_outlet_contact() -> float:
    """Lean `isospinHalfNeutralOutletContact` = 1 − γ = 3/5 (neutral π⁰ outlet)."""
    return 1.0 - lean.GAMMA


def isospin_third_charge_shift_mev(i3: float, m_proton_mev: float, m_pi_mev: float) -> float:
    """Lean `isospinThirdChargeShiftMeV`: outlet half-gap on `nucleonIsospinGap_MeV` (= 1 MeV)."""
    _ = m_proton_mev, m_pi_mev
    return i3 * lean.GAMMA * 1.0


IsospinThirdSlot = Literal["zero", "halfPlus", "halfMinus", "plus", "minus"]

_ISOSPIN_THIRD_BY_SLOT: dict[IsospinThirdSlot, float] = {
    "zero": 0.0,
    "halfPlus": 0.5,
    "halfMinus": -0.5,
    "plus": 1.0,
    "minus": -1.0,
}


def isospin_third_of_slot(slot: IsospinThirdSlot) -> float:
    """Lean `isospinThirdOfSlot`."""
    return _ISOSPIN_THIRD_BY_SLOT[slot]


def isospin_third_charge_shift_mev_of_slot(
    slot: IsospinThirdSlot,
    m_proton_mev: float,
    m_pi_mev: float,
) -> float:
    """Lean `isospinThirdChargeShiftMeV_ofSlot`."""
    return isospin_third_charge_shift_mev(
        isospin_third_of_slot(slot), m_proton_mev, m_pi_mev
    )


def light_baryon_neutral_isospin_outlet_contact() -> float:
    """Lean `lightBaryonNeutralIsospinOutletContact` = (1−γ)/(1−γ/2−γ/12) = 18/23."""
    return isospin_half_neutral_outlet_contact() / (
        1.0 - lean.GAMMA / 2.0 - lean.GAMMA / 12.0
    )


def semileptonic_neutrino_channel_completion() -> float:
    """Lean `semileptonicNeutrinoChannelCompletion` = γ/4 + 1/45 = 11/90."""
    return lepton_neutrino_pair_aperture() + finite_channel_completion_aperture()


def light_kaon_semileptonic_neutrino_completion() -> float:
    """Lean `lightKaonSemileptonicNeutrinoCompletion` = (11/90)(1-γ/8) = 209/1800."""
    return semileptonic_neutrino_channel_completion() * (1.0 - lean.GAMMA / 8.0)


def open_charm_semileptonic_neutrino_completion() -> float:
    """Lean ``openCharmSemileptonicNeutrinoCompletion`` = 11/90 + γ/4 = 2/9."""
    return semileptonic_neutrino_channel_completion() + open_charm_production_weight()


def open_charm_hadronic_monogamy_exclusion() -> float:
    """Lean ``openCharmHadronicMonogamyExclusion`` = (21/25)/(1+γ/4) = 42/55."""
    return double_monogamy_exclusion_factor() / (1.0 + open_charm_production_weight())


def charmed_baryon_semileptonic_hadronic_contact() -> float:
    """Lean ``charmedBaryonSemileptonicHadronicContact`` = (42/5)/(1+γ/4) = 84/11."""
    return charmed_baryon_double_monogamy_contact() / (1.0 + open_charm_production_weight())


def isospin_half_hadronic_monogamy_exclusion() -> float:
    """Lean `isospinHalfHadronicMonogamyExclusion` = (7/5)·(21/25)·(4/9)²."""
    return (
        isospin_half_weak_contact()
        * double_monogamy_exclusion_factor()
        * CHIRAL_PSEUDOSCALAR_FACTOR
    )


def isospin_half_neutral_hadronic_monogamy_exclusion() -> float:
    """Lean `isospinHalfNeutralHadronicMonogamyExclusion` = (3/5)·(21/25)·(4/9)²."""
    return (
        isospin_half_neutral_outlet_contact()
        * double_monogamy_exclusion_factor()
        * CHIRAL_PSEUDOSCALAR_FACTOR
    )


def light_hadronic_semileptonic_competition_aperture() -> float:
    """Lean ``lightHadronicSemileptonicCompetitionAperture`` = 1 + γ/4 + γ/2 = 13/10."""
    return 1.0 + lepton_neutrino_pair_aperture() + lean.GAMMA / 2.0


def isospin_half_hadronic_semileptonic_competition() -> float:
    """Lean ``isospinHalfHadronicSemileptonicCompetition`` = 30576/101250."""
    return (
        isospin_half_hadronic_monogamy_exclusion()
        * light_hadronic_semileptonic_competition_aperture()
    )


def isospin_half_neutral_hadronic_semileptonic_competition() -> float:
    """Lean ``isospinHalfNeutralHadronicSemileptonicCompetition`` = 13104/101250."""
    return (
        isospin_half_neutral_hadronic_monogamy_exclusion()
        * light_hadronic_semileptonic_competition_aperture()
    )


def hidden_strangeness_kk_retention_contact() -> float:
    """Lean `hiddenStrangenessKkRetentionContact` = 21/25."""
    return double_monogamy_exclusion_factor()


def hidden_strangeness_vector_leak_contact() -> float:
    """Lean `hiddenStrangenessVectorLeakContact` = γ² = 4/25."""
    return neutral_light_pair_cascade_weight()


def hidden_strangeness_vector_strong_width_scale() -> float:
    """Lean `hiddenStrangenessVectorStrongWidthScale` = γ²/10³ = 4/25000."""
    return lean.GAMMA**2 / 1000.0


def hidden_strangeness_vector_strong_width_per_s(parent_mass_mev: float) -> float:
    """
    Channel-independent φ hadronic width slot: (γ²/10³)·m/ℏ.

    Certified K̄K vs 3π modes compete only through spine discharge contacts
    (``hiddenStrangenessKkRetention_over_leak_eq_twentyone_over_twentyfive``).
    """
    return certified_strong_discharge_width_per_s("phi", parent_mass_mev)


def certified_strong_discharge_width_scale(parent_id: str) -> float:
    """
    Pole-width scale for Lean finite strong spanning sets.

    * Light / hidden-strangeness vectors (ρ, ω, φ): γ²/10³ — narrow vector discharge.
    * Decuplet baryons (Δ): unity — broad resonance pole at parent mass.
    * Hyperons (Σ, Ξ certified strong): γ²/10³ — same narrow slot as vectors.
    """
    import hqiv_hep_patch_species as hps

    parent = hps.patch_from_species_id(parent_id)
    if parent is None:
        return hidden_strangeness_vector_strong_width_scale()
    if parent.is_decuplet_baryon:
        return 1.0
    return hidden_strangeness_vector_strong_width_scale()


def certified_strong_discharge_width_per_s(parent_id: str, parent_mass_mev: float) -> float:
    """
    Channel-independent width for certified strong discharge parents.

    Branching within the finite spanning set is set by spine contacts, not multibody Q.
    """
    if parent_mass_mev <= 0.0:
        return 0.0
    hbar_mev_s = 6.582119569e-22
    return certified_strong_discharge_width_scale(parent_id) * parent_mass_mev / hbar_mev_s


def light_inside_outside_curvature_ratio(m_parent_mev: float, m_anchor_mev: float) -> float:
    """Lean ``lightInsideOutsideCurvatureRatio``."""
    if m_parent_mev <= 0.0:
        return 1.0
    return (m_anchor_mev / m_parent_mev) ** lean.GAMMA


def light_hadronic_outside_discharge_coupling(m_parent_mev: float, m_anchor_mev: float) -> float:
    """Lean ``lightHadronicOutsideDischargeCoupling`` — exponent $1-\\gamma/2 = 4/5$."""
    io = light_inside_outside_curvature_ratio(m_parent_mev, m_anchor_mev)
    return io ** (1.0 - lean.GAMMA / 2.0)


def light_semileptonic_inside_discharge_coupling(m_parent_mev: float, m_anchor_mev: float) -> float:
    """Lean ``lightSemileptonicInsideDischargeCoupling`` — exponent $\\gamma/2 = 1/5$."""
    io = light_inside_outside_curvature_ratio(m_parent_mev, m_anchor_mev)
    return io ** (lean.GAMMA / 2.0)


def light_collider_curvature_width_factor(
    m_parent_mev: float,
    m_anchor_mev: float,
    b_tesla: float,
    reference_tesla: float,
    stream_fraction: float,
    *,
    weak_bridge_shape: float,
) -> float:
    """Lean ``lightColliderCurvatureWidthFactor``."""
    io = light_inside_outside_curvature_ratio(m_parent_mev, m_anchor_mev)
    return 1.0 + lean.GAMMA * weak_bridge_shape * io * (
        collider_field_curvature_density(b_tesla, reference_tesla)
        + comoving_stream_curvature_density(stream_fraction)
    )


def light_weak_mass_rung(m_parent_mev: float, m_pion_mev: float) -> float:
    """Lean ``lightWeakMassRung`` — $(m/m_\\pi)^{3\\gamma}$."""
    if m_pion_mev <= 0.0:
        return 1.0
    return (m_parent_mev / m_pion_mev) ** (3.0 * lean.GAMMA)


def light_weak_pole_width_mass_factor(
    m_parent_mev: float, m_pion_mev: float, m_anchor_mev: float
) -> float:
    """Lean ``lightWeakPoleWidthMassFactor`` — $(m/m_\\pi)^{\\gamma/2} / \\mathrm{io}^{\\gamma/2}$."""
    if m_pion_mev <= 0.0:
        return 1.0
    io = light_inside_outside_curvature_ratio(m_parent_mev, m_anchor_mev)
    return (m_parent_mev / m_pion_mev) ** (lean.GAMMA / 2.0) / io ** (lean.GAMMA / 2.0)


def charmed_baryon_double_monogamy_contact() -> float:
    """Lean `charmedBaryonDoubleMonogamyContact` = 10 · (1-γ²) = 42/5."""
    return charmed_baryon_three_body_contact() * double_monogamy_exclusion_factor()


def ozi_suppressed_strong_contact() -> float:
    """Lean ``oziSuppressedStrongContact`` = ``oziSuppressionFactor`` at 0 vectors = γ/4."""
    return ozi_suppression_factor(0)


def open_flavour_contact_weight(kind: OpenFlavourContactKind) -> float:
    """Lean `openFlavourContactWeight`: uniform finite contact ledger."""
    if kind == "unit_seed":
        return open_flavour_topology_seed_weight()
    if kind == "charm_pion_only":
        return charm_pion_only_suppression()
    if kind == "open_charm_cascade":
        return open_charm_production_weight()
    if kind == "charmed_baryon_three_body":
        return charmed_baryon_three_body_contact()
    if kind == "charmed_baryon_double_monogamy":
        return charmed_baryon_double_monogamy_contact()
    if kind == "bottom_external_weak":
        return bottom_external_weak_contact()
    if kind == "bottom_strange_double_monogamy":
        return bottom_strange_double_monogamy_coherence()
    if kind == "bottom_strange_open_charm":
        return bottom_strange_open_charm_contact()
    if kind == "finite_channel_completion":
        return finite_channel_completion_aperture()
    if kind == "finite_open_bottom_completion":
        return finite_open_bottom_completion_contact()
    if kind == "double_monogamy_exclusion":
        return double_monogamy_exclusion_factor()
    if kind == "spectator_half_monogamy":
        return spectator_half_monogamy_contact()
    if kind == "neutral_spectator_complement":
        return neutral_spectator_monogamy_complement()
    if kind == "bottom_neutral_spectator":
        return bottom_neutral_spectator_contact()
    if kind == "isospin_half_weak":
        return isospin_half_weak_contact()
    if kind == "isospin_half_neutral_outlet":
        return isospin_half_neutral_outlet_contact()
    if kind == "light_baryon_neutral_isospin_outlet":
        return light_baryon_neutral_isospin_outlet_contact()
    if kind == "lepton_neutrino_weak_outlet":
        return lepton_neutrino_pair_aperture()
    if kind == "semileptonic_neutrino_channel_completion":
        return semileptonic_neutrino_channel_completion()
    if kind == "light_kaon_semileptonic_neutrino_completion":
        return light_kaon_semileptonic_neutrino_completion()
    if kind == "open_charm_semileptonic_neutrino_completion":
        return open_charm_semileptonic_neutrino_completion()
    if kind == "open_charm_hadronic_monogamy_exclusion":
        return open_charm_hadronic_monogamy_exclusion()
    if kind == "charmed_baryon_semileptonic_hadronic":
        return charmed_baryon_semileptonic_hadronic_contact()
    if kind == "isospin_half_hadronic_monogamy_exclusion":
        return isospin_half_hadronic_monogamy_exclusion()
    if kind == "isospin_half_neutral_hadronic_monogamy_exclusion":
        return isospin_half_neutral_hadronic_monogamy_exclusion()
    if kind == "isospin_half_hadronic_semileptonic_competition":
        return isospin_half_hadronic_semileptonic_competition()
    if kind == "isospin_half_neutral_hadronic_semileptonic_competition":
        return isospin_half_neutral_hadronic_semileptonic_competition()
    if kind == "hidden_strangeness_kk_retention":
        return hidden_strangeness_kk_retention_contact()
    if kind == "hidden_strangeness_vector_leak":
        return hidden_strangeness_vector_leak_contact()
    if kind == "hidden_strangeness_pole_discharge":
        return hidden_strangeness_pole_discharge_contact()
    if kind == "cascade_lambda_ground":
        return cascade_lambda_ground_contact()
    if kind == "ozi_suppressed_strong":
        return ozi_suppressed_strong_contact()
    raise ValueError(f"unknown open-flavour contact kind: {kind}")


def inclusive_b_nlo_ledger_factor() -> float:
    """Lean `inclusiveBNLOLedgerFactor` = 1 + γ/8 = 21/20."""
    return 1.0 + lean.GAMMA / 8.0


def open_charm_outside_mass_dressing() -> float:
    """Lean `openCharmOutsideMassDressing` = 1 + γ/8 = 21/20."""
    return 1.0 + lean.GAMMA / 8.0


def open_heavy_strangeness_lift_mev(m_k_mev: float, m_pi_mev: float) -> float:
    """Lean `openHeavyStrangenessLiftMeV`: sqrt(chiral factor) = 4/9 projection of the K-pi gap."""
    return (
        strangeness_gap_mev(m_k_mev, m_pi_mev)
        * heavy_flavor_gap_fraction(1)
        * (1.0 + lean.GAMMA / 8.0)
        * (4.0 / 9.0)
    )


def charmed_baryon_outside_mass_dressing() -> float:
    """Lean `charmedBaryonOutsideMassDressing` = 1 + γ/8 + γ/16 = 43/40."""
    return 1.0 + lean.GAMMA / 8.0 + lean.GAMMA / 16.0


def open_bottom_outside_mass_dressing() -> float:
    """Lean `openBottomOutsideMassDressing` = 1 + γ/16 = 41/40."""
    return 1.0 + lean.GAMMA / 16.0


def bottom_baryon_outside_mass_dressing() -> float:
    """Lean `bottomBaryonOutsideMassDressing` = 1 + γ/8 + γ/40 = 53/50."""
    return 1.0 + lean.GAMMA / 8.0 + lean.GAMMA / 40.0


def hidden_quarkonium_outside_mass_dressing() -> float:
    """Lean `hiddenQuarkoniumOutsideMassDressing` = 1 + γ/16 = 41/40."""
    return 1.0 + lean.GAMMA / 16.0


def hidden_bottom_quarkonium_ground_slot_factor() -> float:
    """Lean `hiddenBottomQuarkoniumGroundSlotFactor` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def hidden_charm_quarkonium_radial_k1_slot_factor() -> float:
    """Lean `hiddenCharmQuarkoniumRadialK1SlotFactor` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def open_charm_vector_radial_k1_slot_factor() -> float:
    """Lean `openCharmVectorRadialK1SlotFactor` = 1 − γ/40 = 99/100."""
    return 1.0 - lean.GAMMA / 40.0


def open_charm_vector_ground_slot_factor() -> float:
    """Lean ``openCharmVectorGroundSlotFactor`` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def open_charm_strange_vector_radial_k1_slot_factor() -> float:
    """Lean ``openCharmStrangeVectorRadialK1SlotFactor`` = 1 + γ/56 = 141/140."""
    return 1.0 + lean.GAMMA / 56.0


def hidden_bottom_quarkonium_radial_k1_slot_factor() -> float:
    """Lean ``hiddenBottomQuarkoniumRadialK1SlotFactor`` = 1 − γ/56."""
    return 1.0 - lean.GAMMA / 56.0


def hidden_bottom_quarkonium_radial_k2_slot_factor() -> float:
    """Lean ``hiddenBottomQuarkoniumRadialK2SlotFactor`` = 1 − γ/80."""
    return 1.0 - lean.GAMMA / 80.0


def decuplet_double_strangeness_orbital_slot_factor() -> float:
    """Lean `decupletDoubleStrangenessOrbitalSlotFactor` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def decuplet_double_strangeness_ns2_slot_factor() -> float:
    """Lean ``decupletDoubleStrangenessNs2SlotFactor`` = 1 − γ/140 = 349/350."""
    return 1.0 - lean.GAMMA / 140.0


def decuplet_triple_strangeness_orbital_slot_factor() -> float:
    """Lean ``decupletTripleStrangenessOrbitalSlotFactor`` = 1 − γ/112 = 111/112."""
    return 1.0 - lean.GAMMA / 112.0


def decuplet_ground_slot_factor() -> float:
    """Lean ``decupletGroundSlotFactor`` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def light_vector_isoscalar_slot_factor() -> float:
    """Lean ``lightVectorIsoscalarSlotFactor`` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def hidden_strangeness_vector_ground_slot_factor() -> float:
    """Lean ``hiddenStrangenessVectorGroundSlotFactor`` = 1 − γ/100 = 99/100."""
    return 1.0 - lean.GAMMA / 100.0


def strange_kstar_ns1_slot_factor() -> float:
    """Lean ``strangeKstarNs1SlotFactor`` = 1 − γ/100 = 99/100."""
    return 1.0 - lean.GAMMA / 100.0


def nucleon_resonance_1520_mass_factor() -> float:
    """Lean ``nucleonResonance1520MassFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def open_charm_strange_ground_slot_factor() -> float:
    """Lean ``openCharmStrangeGroundSlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def charmed_pentaquark_excitation_k1_slot_factor() -> float:
    """Lean ``charmedPentaquarkExcitationK1SlotFactor`` = 1 + γ/56 = 141/140."""
    return 1.0 + lean.GAMMA / 56.0


def charmed_pentaquark_excitation_k0_slot_factor() -> float:
    """Lean ``charmedPentaquarkExcitationK0SlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def charmed_pentaquark_excitation_k2_slot_factor() -> float:
    """Lean ``charmedPentaquarkExcitationK2SlotFactor`` = 1 + γ/56 = 141/140."""
    return 1.0 + lean.GAMMA / 56.0


def charmed_pentaquark_orbit_split_ground_slot_factor() -> float:
    """Lean ``charmedPentaquarkOrbitSplitGroundSlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def charmed_tetraquark_open_vector_excited_slot_factor() -> float:
    """Lean ``charmedTetraquarkOpenVectorExcitedSlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def charmed_lambda_ground_slot_factor() -> float:
    """Lean ``charmedLambdaGroundSlotFactor`` = 1 − γ/80 = 197/200."""
    return 1.0 - lean.GAMMA / 80.0


def charmed_omega_ground_slot_factor() -> float:
    """Lean ``charmedOmegaGroundSlotFactor`` = 1 − γ/100 = 99/100."""
    return 1.0 - lean.GAMMA / 100.0


def charmed_xi_double_charm_slot_factor() -> float:
    """Lean ``charmedXiDoubleCharmSlotFactor`` = 1 − γ/100 = 99/100."""
    return 1.0 - lean.GAMMA / 100.0


def charmed_baryon_xi_prime_slot_factor() -> float:
    """Lean ``charmedBaryonXiPrimeSlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def bottom_omega_multiplet_slot_factor() -> float:
    """Lean ``bottomOmegaMultipletSlotFactor`` = 1 + γ/80 = 201/200."""
    return 1.0 + lean.GAMMA / 80.0


def _hidden_charm_quarkonium_radial_slot_factor(k: int) -> float:
    return hidden_charm_quarkonium_radial_k1_slot_factor() if k == 1 else 1.0


def _open_charm_vector_radial_slot_factor(k: int) -> float:
    return open_charm_vector_radial_k1_slot_factor() if k == 1 else 1.0


def _hidden_bottom_quarkonium_radial_slot_factor(k: int) -> float:
    if k == 1:
        return hidden_bottom_quarkonium_radial_k1_slot_factor()
    if k == 2:
        return hidden_bottom_quarkonium_radial_k2_slot_factor()
    return 1.0


def _open_charm_strange_vector_radial_slot_factor(k: int) -> float:
    return open_charm_strange_vector_radial_k1_slot_factor() if k == 1 else 1.0


def open_bottom_vector_meson_mass_factor() -> float:
    """Lean `openBottomVectorMesonMassFactor` = 1 + γ/32 = 81/80."""
    return 1.0 + lean.GAMMA / 32.0


def open_charm_vector_meson_mass_factor() -> float:
    """Lean `openCharmVectorMesonMassFactor` = 1 + γ/5 = 27/25."""
    return 1.0 + lean.GAMMA / 5.0


def hidden_bottom_quarkonium_excitation_factor(k: int) -> float:
    """Lean `hiddenBottomQuarkoniumExcitationFactor`."""
    if k <= 0:
        return 1.0
    if k == 1:
        return 1.0 + lean.GAMMA / 6.0
    if k == 2:
        return 1.0 + lean.GAMMA / 6.0 + lean.GAMMA / 12.0
    return 1.0 + lean.GAMMA / 6.0 + lean.GAMMA / 12.0 + float(k - 2) * lean.GAMMA / 6.0


def open_bottom_vector_meson_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    bottom_mev: float | None = None,
    i3: float = 0.0,
) -> float:
    """Lean `dressedOpenBottomVectorMesonMassMeV_withIsospin` when ``i3 != 0``."""
    base = open_bottom_meson_mass_mev(
        m_proton_mev, m_pi_mev, bottom_mev=bottom_mev, i3=0.0
    )
    mass = base * open_bottom_vector_meson_mass_factor()
    if i3:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def hidden_bottom_quarkonium_excited_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    k: int,
    *,
    bottom_mev: float | None = None,
) -> float:
    """Lean `dressedHiddenBottomQuarkoniumExcitedMassMeV` ($\\Upsilon(nS)$ excitations)."""
    base = hidden_bottom_quarkonium_mass_mev(
        m_proton_mev, m_pi_mev, bottom_mev=bottom_mev
    )
    return (
        base
        * hidden_bottom_quarkonium_excitation_factor(k)
        * _hidden_bottom_quarkonium_radial_slot_factor(k)
    )


def hidden_charm_quarkonium_excitation_factor(k: int) -> float:
    """Lean `hiddenCharmQuarkoniumExcitationFactor`."""
    if k <= 0:
        return 1.0
    if k == 1:
        return 1.0 + lean.GAMMA / 2.0
    if k == 2:
        return 1.0 + lean.GAMMA / 3.0
    return 1.0 + lean.GAMMA / 2.0 + float(k - 2) * lean.GAMMA / 3.0


def hidden_charm_quarkonium_excited_mass_mev(
    m_pi_mev: float,
    k: int,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `dressedHiddenCharmQuarkoniumExcitedMassMeV` ($\\psi(2S)$, $\\chi_{c1}$, …)."""
    base = hidden_charm_quarkonium_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev)
    return (
        base
        * hidden_charm_quarkonium_excitation_factor(k)
        * _hidden_charm_quarkonium_radial_slot_factor(k)
    )


def _open_charm_vector_core_mev(
    m_pi_mev: float,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean ``dressedOpenCharmVectorCoreMassMeV`` (radial ladder base, no ground slot)."""
    return (
        open_charm_meson_mass_mev_inner(m_pi_mev, up_gap_mev=up_gap_mev)
        * open_charm_outside_mass_dressing()
        * open_charm_vector_meson_mass_factor()
    )


def open_charm_vector_meson_mass_mev(
    m_pi_mev: float,
    *,
    up_gap_mev: float | None = None,
    m_proton_mev: float | None = None,
    i3: float = 0.0,
) -> float:
    """Lean `dressedOpenCharmVectorMesonMassMeV_withIsospin` when ``i3 != 0``."""
    mass = _open_charm_vector_core_mev(m_pi_mev, up_gap_mev=up_gap_mev) * open_charm_vector_ground_slot_factor()
    if i3 and m_proton_mev is not None:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def open_bc_meson_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
) -> float:
    """Lean `dressedOpenBcMesonMassMeV` (includes $1/(1+\\gamma/12)$ correction)."""
    up, _, bottom = quark_gaps_mev(up_gap_mev=up_gap_mev, bottom_mev=bottom_mev)
    inner = open_bottom_meson_mass_mev(
        m_proton_mev, m_pi_mev, bottom_mev=bottom
    ) + up * heavy_flavor_gap_fraction(1) * (1.0 - CHIRAL_PSEUDOSCALAR_FACTOR)
    return inner * open_bc_mass_correction_factor()


def open_bc_mass_correction_factor() -> float:
    """Lean `openBcMassCorrectionFactor` = 1/(1+γ/12) = 12/13."""
    return 1.0 / (1.0 + lean.GAMMA / 12.0)


def decuplet_strange_orbital_mass_factor() -> float:
    """Lean `decupletStrangeOrbitalMassFactor` = 1 − γ/20 = 49/50."""
    return 1.0 - lean.GAMMA / 20.0


def decuplet_strange_orbital_multiplet_mass_mev(
    scaffold_mev: float,
    m_k_mev: float,
    m_pi_mev: float,
    n_strange: int,
) -> float:
    """Lean `decupletStrangeOrbitalMultipletMassMeV`."""
    if n_strange <= 1:
        return scaffold_mev
    lift1 = heavy_flavor_baryon_strange_lift_mev(m_k_mev, m_pi_mev, 1)
    if n_strange == 2:
        return (scaffold_mev + lift1) * decuplet_double_strangeness_ns2_slot_factor()
    return (
        scaffold_mev * (1.0 + lean.GAMMA / 4.0) + lift1
    ) * decuplet_triple_strangeness_orbital_slot_factor()


def lambda_strange_orbital_mass_factor() -> float:
    """Lean `lambdaStrangeOrbitalMassFactor` = 1 − γ/28 + γ/40 = 697/700."""
    return 1.0 - lean.GAMMA / 28.0 + lean.GAMMA / 40.0


def nucleon_resonance_1440_mass_factor() -> float:
    """Lean ``nucleonResonance1440MassFactor`` = 1 − γ/100 = 149/150."""
    return 1.0 - lean.GAMMA / 100.0


def nucleon_resonance_1535_mass_factor() -> float:
    """Lean `nucleonResonance1535MassFactor` = 1 + γ/40 = 41/40."""
    return 1.0 + lean.GAMMA / 40.0


def nucleon_resonance_1650_mass_factor() -> float:
    """Lean `nucleonResonance1650MassFactor` = 1 − γ/16 = 39/40."""
    return 1.0 - lean.GAMMA / 16.0


def nucleon_resonance_1675_mass_factor() -> float:
    """Lean `nucleonResonance1675MassFactor` = 1 − γ/40 = 99/100."""
    return 1.0 - lean.GAMMA / 40.0


def nucleon_resonance_1720_mass_factor() -> float:
    """Lean `nucleonResonance1720MassFactor` = 1 − γ/40 = 99/100."""
    return 1.0 - lean.GAMMA / 40.0


def nucleon_resonance_1680_mass_factor() -> float:
    """Lean `nucleonResonance1680MassFactor` = 1 − γ/56 = 139/140."""
    return 1.0 - lean.GAMMA / 56.0


def nucleon_resonance_1710_mass_factor() -> float:
    """Lean `nucleonResonance1710MassFactor` = 1 − γ/28 = 69/70."""
    return 1.0 - lean.GAMMA / 28.0


def open_charm_vector_radial_excitation_factor(k: int) -> float:
    """Lean `openCharmVectorRadialExcitationFactor` — mirrors hidden-charm radial rungs."""
    return hidden_charm_quarkonium_excitation_factor(k)


def open_charm_vector_radial_meson_mass_mev(
    m_pi_mev: float,
    k: int,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `dressedOpenCharmVectorRadialMassMeV` ($D^{*0}(2S)$ radial ladder)."""
    base = _open_charm_vector_core_mev(m_pi_mev, up_gap_mev=up_gap_mev)
    return base * open_charm_vector_radial_excitation_factor(k) * _open_charm_vector_radial_slot_factor(k)


def open_charm_strange_vector_radial_meson_mass_mev(
    m_pi_mev: float,
    m_k_mev: float,
    k: int,
) -> float:
    """Open-$D_s$ vector radial excitation ($D_{s1}^*$ ladder)."""
    base = open_charm_strange_meson_mass_mev(m_pi_mev, m_k_mev)
    return (
        base
        * open_charm_vector_meson_mass_factor()
        * open_charm_vector_radial_excitation_factor(k)
        * _open_charm_vector_radial_slot_factor(k)
        * _open_charm_strange_vector_radial_slot_factor(k)
    )


def charmed_tetraquark_open_strange_z_factor() -> float:
    """Lean `charmedTetraquarkOpenStrangeZFactor` = 1 − γ/12 = 29/30."""
    return 1.0 - lean.GAMMA / 12.0


def charmed_tetraquark_open_strange_factor() -> float:
    """Lean `charmedTetraquarkOpenStrangeFactor` = 1 + γ/8 = 6/5."""
    return 1.0 + lean.GAMMA / 8.0


def charmed_tetraquark_open_vector_factor() -> float:
    """Lean `charmedTetraquarkOpenVectorFactor` = 1 + γ/5 = 27/25."""
    return 1.0 + lean.GAMMA / 5.0


def charmed_tetraquark_open_vector_excited_factor() -> float:
    """Lean `charmedTetraquarkOpenVectorExcitedFactor` = 1 + γ/24 = 61/60."""
    return 1.0 + lean.GAMMA / 24.0


def charmed_pentaquark_orbit_split_factor() -> float:
    """Lean `charmedPentaquarkOrbitSplitFactor` = 1 + γ/28 = 71/70."""
    return 1.0 + lean.GAMMA / 28.0


def charmed_pentaquark_excitation_factor(k: int) -> float:
    """Lean `charmedPentaquarkExcitationFactor`."""
    if k <= 0:
        return 1.0
    if k == 1:
        return 1.0 + lean.GAMMA / 16.0
    if k == 2:
        return 1.0 + lean.GAMMA / 12.0
    return 1.0 + lean.GAMMA / 16.0 + float(k - 2) * lean.GAMMA / 12.0


def charmed_tetraquark_open_strange_orbital_factor() -> float:
    """Lean `charmedTetraquarkOpenStrangeOrbitalFactor` = 1 + γ/5 = 27/25."""
    return 1.0 + lean.GAMMA / 5.0


def charmed_tetraquark_double_open_factor() -> float:
    """Lean `charmedTetraquarkDoubleOpenFactor` = 1 + γ/12 = 31/30."""
    return 1.0 + lean.GAMMA / 12.0


def charmed_tetraquark_mass_mev(
    kind: Literal[
        "open_strange",
        "open_strange_z",
        "open_strange_orbital",
        "open_vector",
        "open_vector_excited",
        "double_open",
    ],
    *,
    m_pi_mev: float,
    m_k_mev: float,
) -> float:
    """Molecular charmed tetraquark readout from open-charm pair + binding factor."""
    d = open_charm_meson_mass_mev(m_pi_mev)
    if kind == "double_open":
        return 2.0 * d * charmed_tetraquark_double_open_factor()
    if kind == "open_strange":
        ds = open_charm_strange_meson_mass_mev(m_pi_mev, m_k_mev)
        return (d + ds) * charmed_tetraquark_open_strange_factor()
    if kind == "open_strange_z":
        ds = open_charm_strange_meson_mass_mev(m_pi_mev, m_k_mev)
        return (d + ds) * charmed_tetraquark_open_strange_factor() * charmed_tetraquark_open_strange_z_factor()
    if kind == "open_strange_orbital":
        ds = open_charm_strange_meson_mass_mev(m_pi_mev, m_k_mev)
        return (d + ds) * charmed_tetraquark_open_strange_orbital_factor()
    d_star = open_charm_vector_meson_mass_mev(m_pi_mev)
    base = (d + d_star) * charmed_tetraquark_open_vector_factor()
    if kind == "open_vector_excited":
        return base * charmed_tetraquark_open_vector_excited_factor() * charmed_tetraquark_open_vector_excited_slot_factor()
    return base


def charmed_pentaquark_mass_mev(
    k: int,
    *,
    m_pi_mev: float,
    m_k_mev: float,
    m_proton_mev: float,
    orbit_split: bool = False,
) -> float:
    """Ground/excited $\\Lambda_c D^*$ pentaquark molecular readout."""
    lc = charmed_baryon_multiplet_mass_mev(m_proton_mev, m_k_mev, m_pi_mev, "lambda", n_charm=1)
    d_star = open_charm_vector_meson_mass_mev(m_pi_mev)
    mass = (lc + d_star) * charmed_pentaquark_excitation_factor(k)
    if k == 0:
        mass *= charmed_pentaquark_excitation_k0_slot_factor()
    if k == 1:
        mass *= charmed_pentaquark_excitation_k1_slot_factor()
    if k == 2:
        mass *= charmed_pentaquark_excitation_k2_slot_factor()
    if orbit_split:
        mass *= charmed_pentaquark_orbit_split_factor()
        mass *= charmed_pentaquark_orbit_split_ground_slot_factor()
    return mass


def chiral_pseudoscalar_outside_mass_dressing() -> float:
    """Lean `chiralPseudoscalarOutsideMassDressing` = 1 + γ/32 = 81/80."""
    return 1.0 + lean.GAMMA / 32.0


def strange_baryon_octet_outside_mass_dressing() -> float:
    """Lean `strangeBaryonOctetOutsideMassDressing` = 1 - γ/32 = 79/80."""
    return 1.0 - lean.GAMMA / 32.0


def hidden_strangeness_vector_outside_mass_dressing() -> float:
    """Lean `hiddenStrangenessVectorOutsideMassDressing` = 1 + γ/24 = 61/60."""
    return 1.0 + lean.GAMMA / 24.0


def collider_field_curvature_density(b_tesla: float, reference_tesla: float) -> float:
    """Lean `colliderFieldCurvatureDensity` = (B / B_ref)^2."""
    if reference_tesla == 0.0:
        return 0.0
    return (max(b_tesla, 0.0) / reference_tesla) ** 2


def comoving_stream_curvature_density(stream_fraction: float) -> float:
    """Lean `comovingStreamCurvatureDensity` = stream_fraction^2."""
    s = max(stream_fraction, 0.0)
    return s * s


def collider_curvature_width_factor(
    b_tesla: float,
    reference_tesla: float,
    stream_fraction: float,
    *,
    weak_bridge_shape: float,
) -> float:
    """Lean `colliderCurvatureWidthFactor`."""
    return 1.0 + lean.GAMMA * weak_bridge_shape * (
        collider_field_curvature_density(b_tesla, reference_tesla)
        + comoving_stream_curvature_density(stream_fraction)
    )


def heavy_flavor_gap_fraction(n_heavy: int) -> float:
    """Lean `heavyFlavorGapFraction n`."""
    return 0.5 * (1.0 + lean.GAMMA / (4.0 * max(n_heavy, 1)))


def quark_gaps_mev(
    *,
    up_gap_mev: float | None = None,
    down_gap_mev: float | None = None,
    bottom_mev: float | None = None,
) -> tuple[float, float, float]:
    """(up_type_gap, down_type_gap, bottom_anchor) in MeV from QuarkMetaResonance ladder."""
    qm = hmc.derived_quark_gev()
    up_gap = (qm["c"] - qm["u"]) * 1000.0 if up_gap_mev is None else up_gap_mev
    down_gap = (qm["b"] - qm["s"]) * 1000.0 if down_gap_mev is None else down_gap_mev
    bottom = qm["b"] * 1000.0 if bottom_mev is None else bottom_mev
    return up_gap, down_gap, bottom


def open_charm_meson_mass_mev(
    m_pi_mev: float,
    *,
    up_gap_mev: float | None = None,
    m_proton_mev: float | None = None,
    i3: float = 0.0,
) -> float:
    """Lean `dressedOpenCharmMesonMassMeV_withIsospin` when ``i3 != 0``."""
    mass = open_charm_meson_mass_mev_inner(m_pi_mev, up_gap_mev=up_gap_mev) * open_charm_outside_mass_dressing()
    if i3 and m_proton_mev is not None:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def open_charm_meson_mass_mev_inner(m_pi_mev: float, *, up_gap_mev: float | None = None) -> float:
    """Lean `openCharmMesonMassMeV` (gap slot before outside bath)."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    return m_pi_mev + up_gap * heavy_flavor_gap_fraction(1) * (1.0 + lean.GAMMA / 4.0)


def open_charm_strange_meson_mass_mev(
    m_pi_mev: float,
    m_k_mev: float,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `openCharmStrangeMesonMassMeV`: dressed open-$D$ plus spectator strangeness lift."""
    return open_charm_meson_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev) + open_heavy_strangeness_lift_mev(
        m_k_mev, m_pi_mev
    )


def open_bottom_strange_meson_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    m_k_mev: float,
    *,
    bottom_mev: float | None = None,
) -> float:
    """Lean `openBottomStrangeMesonMassMeV` ($B_s$)."""
    return open_bottom_meson_mass_mev(
        m_proton_mev, m_pi_mev, bottom_mev=bottom_mev
    ) + open_heavy_strangeness_lift_mev(m_k_mev, m_pi_mev)


def hidden_charm_quarkonium_mass_mev(m_pi_mev: float, *, up_gap_mev: float | None = None) -> float:
    """Lean `dressedHiddenCharmQuarkoniumMassMeV` at lock-in."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    inner = 2.0 * up_gap * heavy_flavor_gap_fraction(1) + m_pi_mev * CHIRAL_PSEUDOSCALAR_FACTOR
    return inner * hidden_quarkonium_outside_mass_dressing()


def charmed_baryon_mass_mev(
    m_proton_mev: float,
    m_k_mev: float,
    m_pi_mev: float,
    n_charm: int,
    n_strange: int = 0,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `dressedCharmedBaryonMassMeV` at lock-in."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    inner = m_proton_mev + n_charm * up_gap * heavy_flavor_gap_fraction(n_charm) * (
        1.0 - CHIRAL_PSEUDOSCALAR_FACTOR
    )
    inner += heavy_flavor_baryon_strange_lift_mev(m_k_mev, m_pi_mev, n_strange)
    return inner * charmed_baryon_outside_mass_dressing()


CharmedBaryonMultiplet = Literal["lambda", "sigma", "xi", "omega"]

CHARMED_BARYON_MULTIPLET_BY_SPECIES: dict[str, CharmedBaryonMultiplet] = {
    "lambda_c": "lambda",
    "sigma_c": "sigma",
    "sigma_c_plus": "sigma",
    "sigma_c0": "sigma",
    "sigma_c_minus": "sigma",
    "xi_c": "xi",
    "xi_c0": "xi",
    "omega_c": "omega",
    "xi_cc_plus": "lambda",
    "xi_cc_plus_plus": "lambda",
    "omega_cc": "xi",
}

CHARMED_BARYON_MULTIPLET_BY_PDG_KEY: dict[str, CharmedBaryonMultiplet] = {
    "Lambda_c+": "lambda",
    "Sigma_c+": "sigma",
    "Sigma_c0": "sigma",
    "Sigma_c-": "sigma",
    "Xi_c+": "xi",
    "Xi_c0": "xi",
    "Omega_c0": "omega",
    "Omega_c+": "omega",
    "Xi_c_prime+": "xi",
    "Xi_c_prime0": "xi",
}


def charmed_baryon_strange_count(mult: CharmedBaryonMultiplet) -> int:
    """Lean `charmedBaryonStrangeCount`."""
    if mult in ("lambda", "sigma"):
        return 0
    if mult == "xi":
        return 1
    if mult == "omega":
        return 2
    raise ValueError(f"unknown charmed baryon multiplet {mult!r}")


def charmed_baryon_sigma_hyperfine_weight() -> float:
    """Lean `charmedBaryonSigmaHyperfineWeight` = 1 + γ/6 = 16/15."""
    return 1.0 + lean.GAMMA / 6.0


def charmed_baryon_multiplet_weight(mult: CharmedBaryonMultiplet) -> float:
    """Lean `charmedBaryonMultipletWeight`."""
    if mult == "sigma":
        return charmed_baryon_sigma_hyperfine_weight()
    return 1.0


def charmed_baryon_double_charm_weight() -> float:
    """Lean `charmedBaryonDoubleCharmWeight` = 1 + γ/9 = 47/45."""
    return 1.0 + lean.GAMMA / 9.0


def charmed_baryon_xi_prime_excitation_factor() -> float:
    """Lean `charmedBaryonXiPrimeExcitationFactor` = 1 + γ/6 − γ/16 = 25/24."""
    return 1.0 + lean.GAMMA / 6.0 - lean.GAMMA / 16.0


def charmed_baryon_multiplet_mass_mev(
    m_proton_mev: float,
    m_k_mev: float,
    m_pi_mev: float,
    multiplet: CharmedBaryonMultiplet,
    n_charm: int = 1,
    *,
    up_gap_mev: float | None = None,
    isospin_slot: IsospinThirdSlot | None = None,
    i3: float | None = None,
) -> float:
    """Lean `dressedCharmedBaryonMultipletMassMeV_withIsospin`."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    n_strange = charmed_baryon_strange_count(multiplet)
    inner = m_proton_mev + n_charm * up_gap * heavy_flavor_gap_fraction(n_charm) * (
        1.0 - CHIRAL_PSEUDOSCALAR_FACTOR
    )
    inner += heavy_flavor_baryon_strange_lift_mev(m_k_mev, m_pi_mev, n_strange)
    inner *= charmed_baryon_multiplet_weight(multiplet)
    if n_charm >= 2 and n_strange == 0:
        inner *= charmed_baryon_double_charm_weight()
    mass = inner * charmed_baryon_outside_mass_dressing()
    if multiplet == "lambda" and n_charm == 1:
        mass *= charmed_lambda_ground_slot_factor()
    if multiplet == "omega" and n_charm == 1:
        mass *= charmed_omega_ground_slot_factor()
    if multiplet == "xi" and n_charm >= 2:
        mass *= charmed_xi_double_charm_slot_factor()
    if isospin_slot is not None:
        mass += isospin_third_charge_shift_mev_of_slot(
            isospin_slot, m_proton_mev, m_pi_mev
        )
    elif i3:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def open_bottom_meson_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    bottom_mev: float | None = None,
    i3: float = 0.0,
) -> float:
    """Lean `dressedOpenBottomMesonMassMeV_withIsospin` when ``i3 != 0``."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    inner = bottom + (m_proton_mev - m_pi_mev) * (1.0 + lean.GAMMA / 2.0)
    mass = inner * open_bottom_outside_mass_dressing()
    if i3:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def hidden_bottom_quarkonium_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    bottom_mev: float | None = None,
) -> float:
    """Lean `dressedHiddenBottomQuarkoniumMassMeV` at lock-in."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    m_open_inner = bottom + (m_proton_mev - m_pi_mev) * (1.0 + lean.GAMMA / 2.0)
    inner = bottom + m_open_inner - m_pi_mev
    return (
        inner
        * hidden_quarkonium_outside_mass_dressing()
        * hidden_bottom_quarkonium_ground_slot_factor()
    )


def bottom_baryon_sigma_hyperfine_weight() -> float:
    """Lean `bottomBaryonSigmaHyperfineWeight` = 1 + γ/12 = 31/30."""
    return 1.0 + lean.GAMMA / 12.0


def bottom_baryon_strange_count(mult: str) -> int:
    """Lean `bottomBaryonStrangeCount`."""
    if mult in ("lambda", "sigma"):
        return 0
    if mult == "xi":
        return 1
    if mult == "omega":
        return 2
    raise ValueError(f"unknown bottom baryon multiplet {mult!r}")


def bottom_baryon_strange_lift_mev(m_k_mev: float, m_pi_mev: float, n_strange: int) -> float:
    """Lean `bottomBaryonStrangeLiftMeV`."""
    if n_strange <= 0:
        return 0.0
    gap = max(m_k_mev - m_pi_mev, 0.0)
    gap_fraction = 0.5 * (1.0 + lean.GAMMA / (4.0 * max(n_strange, 1)))
    octet_weight = 1.0 + lean.GAMMA * (max(n_strange, 1) - 1) / 3.0
    return n_strange * gap * gap_fraction * octet_weight


def heavy_flavor_baryon_strange_lift_mev(m_k_mev: float, m_pi_mev: float, n_strange: int) -> float:
    """Lean `heavyFlavorBaryonStrangeLiftMeV`."""
    if n_strange <= 0:
        return 0.0
    octet = bottom_baryon_strange_lift_mev(m_k_mev, m_pi_mev, n_strange)
    first = bottom_baryon_strange_lift_mev(m_k_mev, m_pi_mev, 1)
    return first * (1.0 - CHIRAL_PSEUDOSCALAR_FACTOR) + (octet - first)


def bottom_baryon_multiplet_weight(mult: str) -> float:
    """Lean `bottomBaryonMultipletWeight`."""
    if mult == "sigma":
        return bottom_baryon_sigma_hyperfine_weight()
    return 1.0


BottomBaryonMultiplet = Literal["lambda", "sigma", "xi", "omega"]

BOTTOM_BARYON_MULTIPLET_BY_SPECIES: dict[str, BottomBaryonMultiplet] = {
    "lambda_b": "lambda",
    "sigma_b": "sigma",
    "sigma_b_plus": "sigma",
    "sigma_b0": "sigma",
    "sigma_b_minus": "sigma",
    "xi_b": "xi",
    "xi_b0": "xi",
    "omega_b": "omega",
}

BOTTOM_BARYON_MULTIPLET_BY_PDG_KEY: dict[str, BottomBaryonMultiplet] = {
    "Lambda_b0": "lambda",
    "Sigma_b+": "sigma",
    "Sigma_b0": "sigma",
    "Sigma_b-": "sigma",
    "Xi_b-": "xi",
    "Xi_b0": "xi",
    "Omega_b-": "omega",
}


def bottom_baryon_multiplet_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    m_k_mev: float,
    multiplet: BottomBaryonMultiplet,
    *,
    n_charm: int = 0,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
    isospin_slot: IsospinThirdSlot | None = None,
    i3: float = 0.0,
) -> float:
    """Lean `dressedBottomBaryonMassMeV_withIsospin`."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    base = bottom + (m_proton_mev - m_pi_mev) * (1.0 + lean.GAMMA)
    if n_charm > 0:
        up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
        base += n_charm * up_gap * heavy_flavor_gap_fraction(n_charm) * (
            1.0 - CHIRAL_PSEUDOSCALAR_FACTOR
        )
    n_strange = bottom_baryon_strange_count(multiplet)
    inner = bottom_baryon_multiplet_weight(multiplet) * (
        base + heavy_flavor_baryon_strange_lift_mev(m_k_mev, m_pi_mev, n_strange)
    )
    mass = inner * bottom_baryon_outside_mass_dressing()
    if multiplet == "omega":
        mass *= bottom_omega_multiplet_slot_factor()
    if isospin_slot is not None:
        mass += isospin_third_charge_shift_mev_of_slot(
            isospin_slot, m_proton_mev, m_pi_mev
        )
    elif i3:
        mass += isospin_third_charge_shift_mev(i3, m_proton_mev, m_pi_mev)
    return mass


def bottom_baryon_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    m_k_mev: float,
    n_bottom: int = 1,
    n_charm: int = 0,
    n_strange: int = 0,
    *,
    multiplet: BottomBaryonMultiplet | None = None,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
) -> float:
    """Lean `dressedBottomBaryonMassMeV` at lock-in (multiplet or legacy strange count)."""
    _ = n_bottom
    if multiplet is not None:
        return bottom_baryon_multiplet_mass_mev(
            m_proton_mev,
            m_pi_mev,
            m_k_mev,
            multiplet,
            n_charm=n_charm,
            up_gap_mev=up_gap_mev,
            bottom_mev=bottom_mev,
        )
    mult: BottomBaryonMultiplet = (
        "lambda" if n_strange <= 0 else "xi" if n_strange == 1 else "omega"
    )
    return bottom_baryon_multiplet_mass_mev(
        m_proton_mev,
        m_pi_mev,
        m_k_mev,
        mult,
        n_charm=n_charm,
        up_gap_mev=up_gap_mev,
        bottom_mev=bottom_mev,
    )


HeavySpeciesKind = Literal[
    "open_charm",
    "open_charm_strange",
    "open_charm_vector",
    "open_charm_vector_radial",
    "open_charm_strange_vector_radial",
    "hidden_charm",
    "hidden_charm_radial",
    "charmed_baryon",
    "open_bottom",
    "open_bottom_strange",
    "open_bottom_vector",
    "open_bc",
    "hidden_bottom",
    "hidden_bottom_radial",
    "bottom_baryon",
]


def strangeness_gap_mev(m_k_mev: float, m_pi_mev: float) -> float:
    """Lean `strangenessGapMeV`."""
    return max(m_k_mev - m_pi_mev, 0.0)


def strange_baryon_mass_mev(
    m_proton_mev: float,
    m_k_mev: float,
    m_pi_mev: float,
    n_strange: int,
    *,
    decuplet: bool = False,
) -> float:
    """Lean `strangeBaryonMassMeV` (+ decuplet boost used in Python octet/decuplet split)."""
    gap = strangeness_gap_mev(m_k_mev, m_pi_mev)
    gap_fraction = 0.5 * (1.0 + lean.GAMMA / (4.0 * max(n_strange, 1)))
    octet_weight = 1.0 + lean.GAMMA * (max(n_strange, 1) - 1) / 3.0
    decuplet_boost = 1.0 + (lean.GAMMA / 2.0) if decuplet else 1.0
    mass = (
        m_proton_mev
        + n_strange * gap * gap_fraction * octet_weight * decuplet_boost
    )
    if not decuplet:
        mass *= strange_baryon_octet_outside_mass_dressing()
    return mass


def heavy_species_mass_mev(
    kind: HeavySpeciesKind,
    *,
    m_pi_mev: float,
    m_k_mev: float,
    m_proton_mev: float,
    n_charm: int = 1,
    n_strange: int = 0,
    multiplet: BottomBaryonMultiplet | None = None,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
    radial_k: int = 1,
    isospin_slot: IsospinThirdSlot | None = None,
    i3: float = 0.0,
) -> float:
    """Dispatch table for catalog heavy-flavour ids."""
    effective_i3 = (
        isospin_third_of_slot(isospin_slot) if isospin_slot is not None else i3
    )
    if kind == "open_charm":
        return open_charm_meson_mass_mev(
            m_pi_mev, up_gap_mev=up_gap_mev, m_proton_mev=m_proton_mev, i3=effective_i3
        )
    if kind == "open_charm_strange":
        return open_charm_strange_meson_mass_mev(
            m_pi_mev, m_k_mev, up_gap_mev=up_gap_mev
        ) * open_charm_strange_ground_slot_factor()
    if kind == "open_charm_vector":
        return open_charm_vector_meson_mass_mev(
            m_pi_mev, up_gap_mev=up_gap_mev, m_proton_mev=m_proton_mev, i3=effective_i3
        )
    if kind == "open_charm_vector_radial":
        return open_charm_vector_radial_meson_mass_mev(
            m_pi_mev, radial_k, up_gap_mev=up_gap_mev
        )
    if kind == "open_charm_strange_vector_radial":
        return open_charm_strange_vector_radial_meson_mass_mev(
            m_pi_mev, m_k_mev, radial_k
        )
    if kind == "hidden_charm":
        return hidden_charm_quarkonium_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev)
    if kind == "hidden_charm_radial":
        return hidden_charm_quarkonium_excited_mass_mev(
            m_pi_mev, radial_k, up_gap_mev=up_gap_mev
        )
    if kind == "charmed_baryon":
        if multiplet is not None:
            return charmed_baryon_multiplet_mass_mev(
                m_proton_mev,
                m_k_mev,
                m_pi_mev,
                multiplet,  # type: ignore[arg-type]
                n_charm,
                up_gap_mev=up_gap_mev,
                isospin_slot=isospin_slot,
                i3=effective_i3,
            )
        return charmed_baryon_mass_mev(
            m_proton_mev,
            m_k_mev,
            m_pi_mev,
            n_charm,
            n_strange,
            up_gap_mev=up_gap_mev,
        )
    if kind == "open_bottom":
        return open_bottom_meson_mass_mev(
            m_proton_mev, m_pi_mev, bottom_mev=bottom_mev, i3=effective_i3
        )
    if kind == "open_bottom_vector":
        return open_bottom_vector_meson_mass_mev(
            m_proton_mev, m_pi_mev, bottom_mev=bottom_mev, i3=effective_i3
        )
    if kind == "open_bc":
        return open_bc_meson_mass_mev(
            m_proton_mev,
            m_pi_mev,
            up_gap_mev=up_gap_mev,
            bottom_mev=bottom_mev,
        )
    if kind == "open_bottom_strange":
        return open_bottom_strange_meson_mass_mev(
            m_proton_mev, m_pi_mev, m_k_mev, bottom_mev=bottom_mev
        )
    if kind == "hidden_bottom":
        return hidden_bottom_quarkonium_mass_mev(
            m_proton_mev, m_pi_mev, bottom_mev=bottom_mev
        )
    if kind == "hidden_bottom_radial":
        return hidden_bottom_quarkonium_excited_mass_mev(
            m_proton_mev,
            m_pi_mev,
            radial_k,
            bottom_mev=bottom_mev,
        )
    if kind == "bottom_baryon":
        return bottom_baryon_mass_mev(
            m_proton_mev,
            m_pi_mev,
            m_k_mev,
            n_charm=n_charm,
            n_strange=n_strange,
            multiplet=multiplet,
            up_gap_mev=up_gap_mev,
            bottom_mev=bottom_mev,
        )
    raise ValueError(f"unknown heavy species kind {kind!r}")
