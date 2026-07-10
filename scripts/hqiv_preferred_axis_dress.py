#!/usr/bin/env python3
"""
Preferred-axis plane-local colour dress (quantum selection, no molecule-type case).

Lean: `HqivSpine.Physics.GeneratorDependentCoupling.preferredAxisPlaneLocalDress`

  factor = 1 + (1/2) · t · (C_A/C_F − 1) · g
  t = clamp01(η) · (4/8)
  g = preferred-axis spectral gap of bond polarities
      g = (p₍₁₎ − p₍₂₎) / Σ p   ∈ [0,1]

Quantum reading: the polarity measure on bonds is a finite spectrum.  The dress
opens only when a unique preferred channel is selected (spectral gap).  Degenerate
equal polar bonds (H₂O, NH₃, CH₄, …) have g = 0 — no unique axis — so the
abelian identity is recovered without a diatomic/polyatomic case statement.
A single polar bond has g = 1 and recovers the half-channel plane-local dress
(the old boolean heteronuclear gate is exactly this {0,1} limit).

No fitted coefficients; n-body ready.
"""

from __future__ import annotations

from typing import Sequence

import hqiv_lean_physics_primitives as lean

COLOUR_FILTER = 9.0 / 4.0
COLOUR_EXCESS = COLOUR_FILTER - 1.0  # 5/4
STRONG_FRAC = lean.STRONG_CHANNEL_FRACTION  # 4/8


def clamp01(x: float) -> float:
    return max(0.0, min(1.0, x))


def bond_polarity(z1: int, z2: int) -> float:
    """|Z₁ − Z₂| / (Z₁ + Z₂) on a covalent contact."""
    return abs(z1 - z2) / max(z1 + z2, 1)


def preferred_axis_purity(bond_polarities: Sequence[float]) -> float:
    """
    Herfindahl purity H = Σ (p_b / Σ p)² (diagnostic / classical collision weight).

    Not the live selection weight — see `preferred_axis_spectral_gap`.
    """
    pols = [max(0.0, float(p)) for p in bond_polarities]
    total = sum(pols)
    if total <= 0.0:
        return 0.0
    return sum((p / total) ** 2 for p in pols)


def preferred_axis_spectral_gap(bond_polarities: Sequence[float]) -> float:
    """
    Quantum preferred-axis selection weight:

        g = (p_max − p_second) / Σ p  ∈ [0,1]

    Empty / all-zero → 0.
    Unique polar support → 1.
    Degenerate equal polar bonds → 0 (no unique preferred channel).
    Partial uniqueness → continuous in (0,1) for n-body asymmetry.
    """
    pols = sorted((max(0.0, float(p)) for p in bond_polarities), reverse=True)
    total = sum(pols)
    if total <= 0.0:
        return 0.0
    p1 = pols[0]
    p2 = pols[1] if len(pols) > 1 else 0.0
    return clamp01((p1 - p2) / total)


def promotion_fraction(eta: float) -> float:
    """Lean `promotionFraction`."""
    return clamp01(eta) * STRONG_FRAC


def preferred_axis_selection_weight(bond_polarities: Sequence[float]) -> float:
    """Lean `preferredAxisSelectionWeight` — spectral gap of the polarity measure."""
    return preferred_axis_spectral_gap(bond_polarities)


def preferred_axis_plane_local_dress(eta: float, selection_weight: float) -> float:
    """Lean `preferredAxisPlaneLocalDress eta g` (linear in spectral gap)."""
    g = clamp01(selection_weight)
    return 1.0 + 0.5 * promotion_fraction(eta) * COLOUR_EXCESS * g


def bond_polarities_from_fragments_bonds(
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> list[float]:
    """Extract |ΔZ|/(Z_i+Z_j) for each bond using FragmentConfig / BondGeometry fields."""
    out: list[float] = []
    for b in bonds:
        i = getattr(b, "frag_i", None)
        j = getattr(b, "frag_j", None)
        if i is None or j is None:
            continue
        z1 = int(getattr(fragments[i], "z_nuclear"))
        z2 = int(getattr(fragments[j], "z_nuclear"))
        out.append(bond_polarity(z1, z2))
    return out


def preferred_axis_dress_for_molecule(
    eta: float,
    fragments: Sequence[object],
    bonds: Sequence[object],
) -> dict[str, float | list[float]]:
    """Full quantum preferred-axis dress readout for a molecule."""
    pols = bond_polarities_from_fragments_bonds(fragments, bonds)
    g = preferred_axis_spectral_gap(pols)
    H = preferred_axis_purity(pols)
    factor = preferred_axis_plane_local_dress(eta, g)
    return {
        "bond_polarities": pols,
        "preferred_axis_spectral_gap": g,
        "preferred_axis_selection_weight": g,
        "preferred_axis_purity": H,  # diagnostic Herfindahl
        "promotion_t": promotion_fraction(eta),
        "preferred_axis_plane_local_dress": factor,
        "colour_filter": COLOUR_FILTER,
        "colour_excess": COLOUR_EXCESS,
    }
