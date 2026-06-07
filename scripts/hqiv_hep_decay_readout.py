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
    "bottom_external_weak",
    "bottom_strange_double_monogamy",
    "finite_channel_completion",
    "spectator_half_monogamy",
    "neutral_spectator_complement",
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
    """Lean `hiddenQuarkoniumEMContactFactor` = 1/γ + 1 + γ = 39/10."""
    return 1.0 / lean.GAMMA + 1.0 + lean.GAMMA


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
    """Lean `bottomStrangeDoubleMonogamyCoherence` = 1/γ² = 25/4."""
    return 1.0 / (lean.GAMMA**2)


def heavy_quarkonium_cascade_weight() -> float:
    """Lean `heavyQuarkoniumCascadeWeight` = openCharm / openBottom = 2."""
    return open_charm_production_weight() / open_bottom_production_weight()


def neutral_light_pair_cascade_weight() -> float:
    """Lean `neutralLightPairCascadeWeight` = γ² = 4/25."""
    return lean.GAMMA**2


def finite_channel_completion_aperture() -> float:
    """Lean `finiteChannelCompletionAperture` = γ · weakBridgeShape = 1/45."""
    return lean.GAMMA / 18.0


def double_monogamy_exclusion_factor() -> float:
    """Lean `doubleMonogamyExclusionFactor` = 1 - γ² = 21/25."""
    return 1.0 - lean.GAMMA**2


def spectator_half_monogamy_contact() -> float:
    """Lean `spectatorHalfMonogamyContact` = 1 + γ/2 = 6/5."""
    return 1.0 + lean.GAMMA / 2.0


def neutral_spectator_monogamy_complement() -> float:
    """Lean `neutralSpectatorMonogamyComplement` = 1/(1-γ) = 5/3."""
    return 1.0 / (1.0 - lean.GAMMA)


def open_flavour_contact_weight(kind: OpenFlavourContactKind) -> float:
    """Lean `openFlavourContactWeight`: uniform finite contact ledger."""
    if kind == "unit_seed":
        return open_flavour_topology_seed_weight()
    if kind == "charm_pion_only":
        return charm_pion_only_suppression()
    if kind == "charmed_baryon_three_body":
        return charmed_baryon_three_body_contact()
    if kind == "bottom_external_weak":
        return bottom_external_weak_contact()
    if kind == "bottom_strange_double_monogamy":
        return bottom_strange_double_monogamy_coherence()
    if kind == "finite_channel_completion":
        return finite_channel_completion_aperture()
    if kind == "spectator_half_monogamy":
        return spectator_half_monogamy_contact()
    if kind == "neutral_spectator_complement":
        return neutral_spectator_monogamy_complement()
    raise ValueError(f"unknown open-flavour contact kind: {kind}")


def inclusive_b_nlo_ledger_factor() -> float:
    """Lean `inclusiveBNLOLedgerFactor` = 1 + γ/8 = 21/20."""
    return 1.0 + lean.GAMMA / 8.0


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


def open_charm_meson_mass_mev(m_pi_mev: float, *, up_gap_mev: float | None = None) -> float:
    """Lean `openCharmMesonMassMeV`."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    return m_pi_mev + up_gap * heavy_flavor_gap_fraction(1) * (1.0 + lean.GAMMA / 4.0)


def open_charm_strange_meson_mass_mev(
    m_pi_mev: float,
    m_k_mev: float,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `openCharmStrangeMesonMassMeV`."""
    return open_charm_meson_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev) + strangeness_gap_mev(
        m_k_mev, m_pi_mev
    ) * heavy_flavor_gap_fraction(1) * (1.0 + lean.GAMMA / 8.0)


def hidden_charm_quarkonium_mass_mev(m_pi_mev: float, *, up_gap_mev: float | None = None) -> float:
    """Lean `hiddenCharmQuarkoniumMassMeV`."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    return 2.0 * up_gap * heavy_flavor_gap_fraction(1) + m_pi_mev * CHIRAL_PSEUDOSCALAR_FACTOR


def charmed_baryon_mass_mev(
    m_proton_mev: float,
    m_k_mev: float,
    m_pi_mev: float,
    n_charm: int,
    n_strange: int = 0,
    *,
    up_gap_mev: float | None = None,
) -> float:
    """Lean `charmedBaryonMassMeV`."""
    up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
    mass = m_proton_mev + n_charm * up_gap * heavy_flavor_gap_fraction(n_charm) * (
        1.0 - CHIRAL_PSEUDOSCALAR_FACTOR
    )
    if n_strange > 0:
        mass += (
            n_strange
            * strangeness_gap_mev(m_k_mev, m_pi_mev)
            * heavy_flavor_gap_fraction(n_strange)
            * (1.0 + lean.GAMMA / 8.0)
        )
    return mass


def open_bottom_meson_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    bottom_mev: float | None = None,
) -> float:
    """Lean `openBottomMesonMassMeV`."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    return bottom + (m_proton_mev - m_pi_mev) * (1.0 + lean.GAMMA / 2.0)


def hidden_bottom_quarkonium_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    *,
    bottom_mev: float | None = None,
) -> float:
    """Lean `hiddenBottomQuarkoniumMassMeV`."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    m_open = open_bottom_meson_mass_mev(m_proton_mev, m_pi_mev, bottom_mev=bottom)
    return bottom + m_open - m_pi_mev


def bottom_baryon_mass_mev(
    m_proton_mev: float,
    m_pi_mev: float,
    m_k_mev: float,
    n_bottom: int = 1,
    n_charm: int = 0,
    n_strange: int = 0,
    *,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
) -> float:
    """Lean `bottomBaryonMassMeV`."""
    _, _, bottom = quark_gaps_mev(bottom_mev=bottom_mev)
    mass = bottom + (m_proton_mev - m_pi_mev) * (1.0 + lean.GAMMA)
    if n_charm > 0:
        up_gap, _, _ = quark_gaps_mev(up_gap_mev=up_gap_mev)
        mass += n_charm * up_gap * heavy_flavor_gap_fraction(n_charm) * (
            1.0 - CHIRAL_PSEUDOSCALAR_FACTOR
        )
    if n_strange > 0:
        mass += (
            n_strange
            * strangeness_gap_mev(m_k_mev, m_pi_mev)
            * heavy_flavor_gap_fraction(n_strange)
            * (1.0 + lean.GAMMA / 8.0)
        )
    return mass


HeavySpeciesKind = Literal[
    "open_charm",
    "open_charm_strange",
    "hidden_charm",
    "charmed_baryon",
    "open_bottom",
    "open_bottom_strange",
    "hidden_bottom",
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
    return (
        m_proton_mev
        + n_strange * gap * gap_fraction * octet_weight * decuplet_boost
    )


def heavy_species_mass_mev(
    kind: HeavySpeciesKind,
    *,
    m_pi_mev: float,
    m_k_mev: float,
    m_proton_mev: float,
    n_charm: int = 1,
    n_strange: int = 0,
    up_gap_mev: float | None = None,
    bottom_mev: float | None = None,
) -> float:
    """Dispatch table for catalog heavy-flavour ids."""
    if kind == "open_charm":
        return open_charm_meson_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev)
    if kind == "open_charm_strange":
        return open_charm_strange_meson_mass_mev(
            m_pi_mev, m_k_mev, up_gap_mev=up_gap_mev
        )
    if kind == "hidden_charm":
        return hidden_charm_quarkonium_mass_mev(m_pi_mev, up_gap_mev=up_gap_mev)
    if kind == "charmed_baryon":
        return charmed_baryon_mass_mev(
            m_proton_mev,
            m_k_mev,
            m_pi_mev,
            n_charm,
            n_strange,
            up_gap_mev=up_gap_mev,
        )
    if kind == "open_bottom":
        return open_bottom_meson_mass_mev(m_proton_mev, m_pi_mev, bottom_mev=bottom_mev)
    if kind == "open_bottom_strange":
        base = open_bottom_meson_mass_mev(m_proton_mev, m_pi_mev, bottom_mev=bottom_mev)
        if n_strange >= 1:
            base += (
                strangeness_gap_mev(m_k_mev, m_pi_mev)
                * heavy_flavor_gap_fraction(1)
                * (1.0 + lean.GAMMA / 8.0)
            )
        return base
    if kind == "hidden_bottom":
        return hidden_bottom_quarkonium_mass_mev(
            m_proton_mev, m_pi_mev, bottom_mev=bottom_mev
        )
    if kind == "bottom_baryon":
        return bottom_baryon_mass_mev(
            m_proton_mev,
            m_pi_mev,
            m_k_mev,
            n_charm=n_charm,
            n_strange=n_strange,
            up_gap_mev=up_gap_mev,
            bottom_mev=bottom_mev,
        )
    raise ValueError(f"unknown heavy species kind {kind!r}")
