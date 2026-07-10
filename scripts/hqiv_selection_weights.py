#!/usr/bin/env python3
"""
Algebraic selection weights for chemistry routing (no molecule-type case statements).

Mirrors the preferred-axis spectral-gap pattern:
  g = (p_max − p_second) / Σp  → unique-channel projector on a finite spectrum.

This module supplies the continuous / spectrum-derived weights used to replace
alkali–halogen frozensets, homonuclear open/halogen bools, horizon name tables,
Compton branch trees, and period-3 geometry route enums.

Lean anchors:
  • ``HqivSpine.Chemistry.Spectroscopy.bondIonicCharacter``
  • ``HqivSpine.Physics.GeneratorDependentCoupling.preferredAxisSpectralGap``
  • ``Hqiv.QuantumChemistry.OutsideContactGeometry.ionicChargeAsymmetry``
"""

from __future__ import annotations

from typing import Sequence

import hqiv_lean_physics_primitives as lean
import hqiv_particle_shell_structure as pss

STRONG = lean.STRONG_CHANNEL_FRACTION


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, float(x)))


def spectral_gap(weights: Sequence[float]) -> float:
    """Unique-channel projector g = (w₍₁₎ − w₍₂₎) / Σw ∈ [0,1]."""
    ws = sorted((max(0.0, float(w)) for w in weights), reverse=True)
    total = sum(ws)
    if total <= 0.0:
        return 0.0
    w1 = ws[0]
    w2 = ws[1] if len(ws) > 1 else 0.0
    return clamp01((w1 - w2) / total)


def pull_asymmetry(p_i: float, p_j: float) -> float:
    """Lean ``pullAsymmetry``."""
    s = p_i + p_j
    if s <= 0.0:
        return 0.0
    return abs(p_i - p_j) / s


def bond_ionic_character(z_i: int, z_j: int) -> float:
    """Lean ``bondIonicCharacter`` via native valence electron pull (δ²)."""
    import hqiv_atom_construction as ac

    return pull_asymmetry(ac.valence_electron_pull(z_i), ac.valence_electron_pull(z_j)) ** 2


def donor_weight(z: int) -> float:
    """
    Alkali-like donor participation from bonding valence (Z>1).

    bonding V = 1 → 1; ≥2 → 0.  Replaces ``z in {3,11,19,…}`` frozenset.
    Uses ``bonding_valence_electron_count`` so post-d Ge/Ga are not misread
    from noble-gas residual counts.
    """
    if z <= 1:
        return 0.0
    v = float(pss.bonding_valence_electron_count(z))
    return clamp01(2.0 - v)


def acceptor_weight(z: int) -> float:
    """
    Halogen-like acceptor participation from bonding valence.

    bonding V = 7 → 1; ≤6 → 0.  Replaces ``z in {9,17,35,…}`` frozenset.
    """
    if z <= 1:
        return 0.0
    v = float(pss.bonding_valence_electron_count(z))
    return clamp01(v - 6.0)


def ionic_route_weight(z_i: int, z_j: int) -> float:
    """
    Continuous ionic-route selection (replaces alkali–halogen / metal–H bool).

    • donor×acceptor on either orientation (alkali halide)
    • donor×H on metal hydrides (LiH)
    On the current panel this recovers the old frozenset gate exactly.
    """
    d_a = donor_weight(z_i)
    d_b = donor_weight(z_j)
    a_a = acceptor_weight(z_i)
    a_b = acceptor_weight(z_j)
    halide = d_a * a_b + d_b * a_a
    hydride = d_a * (1.0 if z_j == 1 else 0.0) + d_b * (1.0 if z_i == 1 else 0.0)
    return clamp01(halide + hydride)


def hydrogen_1s_contact_weight(z: int) -> float:
    """Hydrogen 1s contact participation."""
    return 1.0 if z == 1 else 0.0


def metal_hydride_route_weight(z_i: int, z_j: int) -> float:
    """Donor × hydrogen-1s route participation."""
    return clamp01(
        donor_weight(z_i) * hydrogen_1s_contact_weight(z_j)
        + donor_weight(z_j) * hydrogen_1s_contact_weight(z_i)
    )


def alkali_halide_weight(z_i: int, z_j: int) -> float:
    """Donor×acceptor only (no metal–hydride)."""
    return clamp01(
        donor_weight(z_i) * acceptor_weight(z_j)
        + donor_weight(z_j) * acceptor_weight(z_i)
    )


def gas_phase_alkali_halide_weight(z_i: int, z_j: int) -> float:
    """Period-2 donor×acceptor gas contact, distinct from condensed outside route."""
    period = max(period_participation(z_i, threshold=3), period_participation(z_j, threshold=3))
    return clamp01(alkali_halide_weight(z_i, z_j) * (1.0 - period))


def hydrogen_acceptor_weight(z_i: int, z_j: int) -> float:
    """Hydrogen-1s contact against an acceptor p-shell."""
    return clamp01(
        hydrogen_1s_contact_weight(z_i) * acceptor_weight(z_j)
        + hydrogen_1s_contact_weight(z_j) * acceptor_weight(z_i)
    )


def halogen_open_channel_weight(z_i: int, z_j: int) -> float:
    """Homonuclear halogen open-channel participation (F₂/Cl₂-class)."""
    if z_i != z_j:
        return 0.0
    return clamp01(halogenicity(z_i) * open_channel_fraction(z_i))


def open_channel_count(z: int) -> int:
    """Antibonding / unsaturated p-channel count (geometry + surplus)."""
    from hqiv_electronic_valence_shells import homonuclear_bond_order

    valence = pss.valence_electron_count(z)
    channel_cap = 3 if valence >= 3 else 1
    bo = homonuclear_bond_order(z) if z > 1 else 1
    return max(0, channel_cap - int(bo))


def open_channel_fraction(z: int) -> float:
    """k_open / channel_cap ∈ [0,1]."""
    valence = pss.valence_electron_count(z)
    channel_cap = 3 if valence >= 3 else 1
    return clamp01(open_channel_count(z) / float(max(channel_cap, 1)))


def halogenicity(z: int) -> float:
    """Continuous halogen weight = acceptor_weight (valence → 7)."""
    return acceptor_weight(z)


def open_shell_dimer_weight(z: int) -> float:
    """
    Continuous open-shell dimer weight (O₂-class).

    Peaks when bond order ≈ 2, valence even and ≥ 6, and channels are open.
    """
    if z <= 1:
        return 0.0
    from hqiv_electronic_valence_shells import homonuclear_bond_order

    valence = pss.valence_electron_count(z)
    bo = float(homonuclear_bond_order(z))
    even = 1.0 if valence % 2 == 0 else 0.0
    valence_gate = clamp01(float(valence) - 5.0)
    bo_peak = clamp01(1.0 - abs(bo - 2.0))
    return clamp01(even * valence_gate * bo_peak * open_channel_fraction(z) * 3.0)


def period_participation(z: int, *, threshold: int = 3) -> float:
    """0 at period ≤ threshold−1, 1 at period ≥ threshold."""
    from hqiv_electronic_valence_shells import chemical_period

    return clamp01(float(chemical_period(z)) - float(threshold - 1))


def p_shell_activation(triplet: tuple[int, int, int]) -> float:
    """
    Continuous η² activation from Compton slot spectrum.

    Distinct middle p slot → 1; degenerate (1,1,1)/(4,4,4) → 0.
    Matches ``dynamicComptonPShellActive`` on current chart triplets.
    """
    m0, m1, _m2 = triplet
    if m1 <= 1 or m0 == m1:
        return 0.0
    return 1.0


def atomization_horizon_partition(
    fragments: Sequence[object],
) -> tuple[int, int, int] | None:
    """
    Derive ``(n_total, n_heavy, n_light)`` from fragment Z spectrum — no name table.

    Heavy = Σ electrons on Z>1; light = Σ electrons on Z=1.
    """
    if not fragments:
        return None
    heavy = sum(
        int(getattr(f, "electrons")) for f in fragments if int(getattr(f, "z_nuclear")) > 1
    )
    light = sum(
        int(getattr(f, "electrons")) for f in fragments if int(getattr(f, "z_nuclear")) == 1
    )
    total = heavy + light
    if heavy <= 0 or light <= 0:
        return None
    return total, heavy, light


def use_horizon_atomization_weight(
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> float:
    """
    Continuous gate for horizon-split atomization.

    Was ``period ≥ 3 ∧ n_bonds ≥ 3`` bool.  PH₃ → 1; period-2 hydrides → 0;
    bent dihydrides (2 bonds) → 0.
    """
    from hqiv_electronic_valence_shells import has_heavy_heavy_bond, heavy_centre_z

    if atomization_horizon_partition(fragments) is None:
        return 0.0
    if has_heavy_heavy_bond(tuple(fragments), tuple(bonds)):
        return 0.0
    z_h = heavy_centre_z(tuple(fragments))
    n_bonds = len(bonds)
    return clamp01(period_participation(z_h, threshold=3) * clamp01(float(n_bonds - 2)))


def geometry_route_weights(z_i: int, z_j: int) -> dict[str, float]:
    """
    Continuous blend weights for outside-contact geometry routes.

    Ionic outside-contact requires **both** partners period ≥ 3 (Lean
    ``period3IonicOutsideRoute``), matching the proved route predicate.
    """
    both_period = min(
        period_participation(z_i, threshold=3),
        period_participation(z_j, threshold=3),
    )
    w_ion = ionic_route_weight(z_i, z_j) * both_period
    w_hal = 0.0
    if z_i == z_j:
        w_hal = halogenicity(z_i) * period_participation(z_i, threshold=3)
    rem = max(0.0, 1.0 - w_ion - w_hal)
    return {
        "ionic_outside_contact": w_ion,
        "period3_halogen_open_channel": w_hal,
        "covalent_nested_wf": rem,
    }


def spectroscopy_geometry_route_weights(z_i: int, z_j: int) -> dict[str, float]:
    """
    Gas/vapor spectroscopy contact-route weights.

    Metal hydrides stay on the covalent nested-WF route.  Alkali–halide ionic
    outside contact requires both partners period ≥ 3 (Lean
    ``period3IonicOutsideRoute``), so mixed period-2/3 pairs (LiCl, NaF) stay
    on covalent nested-WF until a dedicated mixed-period theorem lands.
    """
    both_period = min(
        period_participation(z_i, threshold=3),
        period_participation(z_j, threshold=3),
    )
    w_ion = alkali_halide_weight(z_i, z_j) * both_period
    w_hal = (
        halogenicity(z_i) * period_participation(z_i, threshold=3)
        if z_i == z_j
        else 0.0
    )
    rem = max(0.0, 1.0 - w_ion - w_hal)
    return {
        "ionic_outside_contact": w_ion,
        "period3_halogen_open_channel": w_hal,
        "covalent_nested_wf": rem,
    }
