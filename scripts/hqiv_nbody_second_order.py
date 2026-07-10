#!/usr/bin/env python3
"""
N-body second-order chemistry envelope (Lean ``nBodySecondOrderEnvelope``).

General form (no molecule-type case):

  E = EV · η₂ · surplus · vev · geom · κ(ξ)
        · outside_geff(Σ_b G_eff, surplus)
        · preferred_axis_dress(η, g)
        · [optional: C₂ lapse · vev Taylor · graph hyperclosure]

where
  g = preferredAxisSpectralGap([|ΔZ|/(Z_i+Z_j)]_b)   # unique-channel projector
  outside_geff = 1 + (4/8)·(Σ_b G_eff(θ_b) / surplus)

The promoted live chart uses outside_geff × preferred_axis only; optional slots
are available for audit / promotion decisions.

Lean: ``Hqiv.QuantumChemistry.SecondOrderEffects``
"""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any, Sequence

import hqiv_lean_physics_primitives as lean
import hqiv_preferred_axis_dress as pad

STRONG = lean.STRONG_CHANNEL_FRACTION
ALPHA = lean.ALPHA


@dataclass(frozen=True)
class NBodySecondOrderFactors:
    """All second-order slots for one molecule (n-body ready)."""

    outside_geff: float
    preferred_axis_dress: float
    preferred_axis_spectral_gap: float
    c2_lapse: float
    vev_cluster_taylor: float
    graph_hyperclosure_weak: float
    promoted_factor: float
    full_envelope: float
    n_bonds: int
    outside_ledger: dict[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def outside_geff_surplus(geff_sum: float, surplus: float) -> float:
    """Lean ``outsideGeffSurplus``."""
    return 1.0 + STRONG * float(geff_sum) / max(abs(float(surplus)), 1e-12)


def c2_lapse_feedback(c2_xi: float, c2_lock: float) -> float:
    """Lean ``c2LapseFeedback``."""
    return float(c2_xi) / max(float(c2_lock), 1e-12)


def vev_cluster_taylor(vev: float, vev_bare: float) -> float:
    """Lean ``vevClusterTaylor``."""
    return (float(vev) / max(float(vev_bare), 1e-12)) ** ALPHA


def graph_hyperclosure_weak(n_bonds: int) -> float:
    """Lean ``graphHyperclosureWeak``."""
    if n_bonds < 2:
        return 1.0
    return 1.0 + STRONG * (1.0 - 1.0 / math.sqrt(float(n_bonds)))


def promoted_second_order_factor(
    geff_sum: float,
    surplus: float,
    eta: float,
    spectral_gap: float,
) -> float:
    """Lean ``nBodyPromotedSecondOrderFactor`` (live chart dress)."""
    return outside_geff_surplus(geff_sum, surplus) * pad.preferred_axis_plane_local_dress(
        eta, spectral_gap
    )


def n_body_second_order_envelope(
    *,
    c2_xi: float,
    c2_lock: float,
    geff_sum: float,
    surplus: float,
    vev: float,
    vev_bare: float,
    eta: float,
    spectral_gap: float,
    n_bonds: int,
) -> float:
    """Lean ``nBodySecondOrderEnvelope`` (full optional × promoted)."""
    optional = (
        c2_lapse_feedback(c2_xi, c2_lock)
        * outside_geff_surplus(geff_sum, surplus)
        * vev_cluster_taylor(vev, vev_bare)
        * graph_hyperclosure_weak(n_bonds)
    )
    return optional * pad.preferred_axis_plane_local_dress(eta, spectral_gap)


def factors_from_network(
    *,
    geff_thetas: Sequence[float],
    surplus: float,
    eta: float,
    fragments: Sequence[object],
    bonds: Sequence[object],
    contact_xi: float,
    vev: float,
    vev_bare: float,
    phi_epsilon: float = 0.0,
    rho_bulk: float = 0.0,
    coordination_excess: float = 0.0,
    dilute_gas_assay: bool = True,
) -> NBodySecondOrderFactors:
    """Build the full n-body second-order factor set for one molecule.

    Outside G_eff is bookkept as a multi-channel ledger (grav / em / bulk / local /
    contact).  Dilute-gas assay keeps environment channels at identity so the
    promoted factor matches the legacy ``outside_geff × preferred_axis`` dress.
    """
    import hqiv_outside_contact_ledger as ocl

    geoms = list(geff_thetas)
    n_bonds = len(geoms)
    axis = pad.preferred_axis_dress_for_molecule(eta, fragments, bonds)
    g = float(axis["preferred_axis_spectral_gap"])
    axis_dress = float(axis["preferred_axis_plane_local_dress"])
    ledger = ocl.ledger_for_molecule(
        geff_thetas=geoms,
        surplus=surplus,
        fragments=fragments,
        bonds=bonds,
        phi_epsilon=phi_epsilon,
        rho_bulk=rho_bulk,
        coordination_excess=coordination_excess,
        contact_xi=contact_xi,
        dilute_gas_assay=dilute_gas_assay,
    )
    outside = ledger.dress
    c2 = c2_lapse_feedback(
        lean.tuft_lapse_concentration_at_xi(contact_xi),
        lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN),
    )
    vev_t = vev_cluster_taylor(vev, vev_bare)
    hyper = graph_hyperclosure_weak(n_bonds)
    promoted = outside * axis_dress
    full = c2 * outside * vev_t * hyper * axis_dress
    return NBodySecondOrderFactors(
        outside_geff=outside,
        preferred_axis_dress=axis_dress,
        preferred_axis_spectral_gap=g,
        c2_lapse=c2,
        vev_cluster_taylor=vev_t,
        graph_hyperclosure_weak=hyper,
        promoted_factor=promoted,
        full_envelope=full,
        n_bonds=n_bonds,
        outside_ledger=ledger.to_dict(),
    )
