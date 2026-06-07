#!/usr/bin/env python3
"""
Inside / outside curvature primitives (shared; **primary use: nuclear binding**).

Binding lives in the same place as proton (or any hadron) mass:

  • **Inside:** trapped curvature volume × Planck budget (`metaHorizonTrappedInsideRatio`)
    times the composite-trace nucleon binding at the readout shell.
  • **Outside:** nucleon–nucleon contact bonding via `G_eff(θ) = (θ/θ₀)^α` on valley
    contact points (α = 3/5 from the lattice).

For nuclear readouts see `scripts/hqiv_nuclear_inside_outside_binding.py` and
`Hqiv.Physics.NuclearCurvatureBinding`.  Molecular bond-state charts are a separate
downstream projection layer.

Mirrors:
  `Hqiv.Physics.MetaHorizonTrappedPlanckMass`
  `Hqiv.Geometry.HQVMetric` (`G_eff`)
  `Hqiv.Physics.ComptonIRWindow` (`phaseTheta`, `phaseParticipationEta`)
  `Hqiv.Physics.HopfShellBeltramiMassBridge` (inner/outer Casimir split)
"""

from __future__ import annotations

import math

import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
from lih_derivation_scan import PHASE_THETA, compton_window_angles_from_shells

REFERENCE_M = hes.REFERENCE_M
ALPHA = lean.ALPHA  # 3/5 lattice imprint
EV_PER_LAMBDA = 13.6 / 7.0


def g_eff(phi: float) -> float:
    """Lean `G_eff φ = φ^α` for φ ≥ 0 (natural units G₀=H₀=1)."""
    if phi <= 0.0:
        return 0.0
    return phi**ALPHA


def phase_theta() -> float:
    return PHASE_THETA


def meta_horizon_inside_ratio(m_exc: int, m_ref: int = REFERENCE_M) -> float:
    return hes.meta_horizon_trapped_inside_ratio(m_exc, m_ref)


def inside_binding_mev(m: int, m_ref: int = REFERENCE_M) -> float:
    """Inside-curvature binding at shell m (same spine as hadron mass readout)."""
    return meta_horizon_inside_ratio(m, m_ref) * hes.e_bind_from_nucleon_trace_mev(m)


def inside_binding_dimless(m: int, m_ref: int = REFERENCE_M) -> float:
    """Dimensionless inside binding on the hydrogen λ ladder."""
    proton_mev = 938.272
    return inside_binding_mev(m, m_ref) / proton_mev


def inside_binding_ev_anchor(m: int, m_ref: int = REFERENCE_M) -> float:
    return inside_binding_dimless(m, m_ref) * EV_PER_LAMBDA


def outside_contact_coupling(theta_rad: float) -> float:
    """
    Contact-point outside curvature coupling: `G_eff(θ/θ₀)`.

    θ is the Compton IR-window phase at the contact; θ₀ = phaseTheta = π/2.
    With G₀ = H₀ = 1 this is `(θ/θ₀)^α` for α = 3/5 from the lattice.
    """
    theta0 = phase_theta()
    if theta_rad <= 0.0 or theta0 <= 0.0:
        return 0.0
    phi = min(theta_rad / theta0, 1.0)
    return g_eff(phi)


def scale_outside_coupling_for_medium_density(
    coupling: float,
    medium_density_fraction: float,
) -> float:
    """
    Medium-density scaling for outside ``G_eff`` (and surplus multipliers ≥ 1).

      f_ρ = 1 + (f − 1) · ρ

    ρ = 0: dilute / gas-phase assay (no outside closure boost above unity).
    ρ = 1: bulk condensed contact (full ``G_eff`` at the bond).
    """
    rho = min(1.0, max(0.0, medium_density_fraction))
    return 1.0 + (coupling - 1.0) * rho


def outside_contact_coupling_scaled(
    theta_rad: float,
    medium_density_fraction: float,
) -> float:
    """``G_eff(θ)`` with intermolecular density ρ (ice reference via network/thermo)."""
    return scale_outside_coupling_for_medium_density(
        outside_contact_coupling(theta_rad),
        medium_density_fraction,
    )


def outside_geff_surplus_factor(
    bond_geff_theta_sum: float,
    surplus_dimless: float,
    medium_density_fraction: float,
) -> float:
    """
    Surplus-level outside boost from summed bond ``G_eff(θ)`` (chart second-order).

      1 + (4/8) · Σ G_eff(θ) / surplus   then scaled by ρ on the increment above unity.
    """
    surplus = max(abs(surplus_dimless), 1e-12)
    raw = 1.0 + lean.STRONG_CHANNEL_FRACTION * bond_geff_theta_sum / surplus
    return scale_outside_coupling_for_medium_density(raw, medium_density_fraction)


def contact_phase_theta_rad(shell_triplet: tuple[int, int, int]) -> float:
    """Mean Compton phase angle on the contact shell triplet."""
    compton = compton_window_angles_from_shells(shell_triplet)
    return sum(compton.angles_rad) / len(compton.angles_rad)


def contact_shell_triplet(a_s: int, b_s: int) -> tuple[int, int, int]:
    return (max(a_s, 1), max(b_s, 1), abs(a_s - b_s) + 1)


def outer_suppression_at_shell(m: int) -> float:
    xi = float(m + 1)
    return lean.t13_outer_suppression_at_xi(xi)


def effective_casimir_at_shell(m: int) -> float:
    xi = float(m + 1)
    return lean.effective_casimir_scale_at_xi(xi)


def outside_contact_dimless(
    theta_rad: float,
    *,
    m_contact: int,
    geometry_weight: float = 1.0,
) -> float:
    """
    Outside bond contribution at one contact.

    Outside curvature meets at the contact point through `G_eff(θ)`; geometry
    weight carries distance/overlap.  The hadron-scale inner/outer Casimir ratio
    belongs to the inside binding spine, not this contact layer.
    """
    contact = outside_contact_coupling(theta_rad)
    return contact * geometry_weight


def outside_contact_ev(
    theta_rad: float,
    *,
    m_contact: int,
    geometry_weight: float = 1.0,
) -> float:
    return outside_contact_dimless(theta_rad, m_contact=m_contact, geometry_weight=geometry_weight) * EV_PER_LAMBDA


def joint_readout_shell(fragments_mass_numbers: tuple[int, ...]) -> int:
    a_tot = sum(fragments_mass_numbers)
    return ncb.nucleus_curvature_shell(max(a_tot, 1))


def inside_surplus_ev(
    fragment_shells: tuple[int, ...],
    joint_shell: int,
) -> float:
    """Closed inside curvature minus separated fragment inside curvatures."""
    separated = sum(inside_binding_ev_anchor(m) for m in fragment_shells)
    joint = inside_binding_ev_anchor(joint_shell)
    return joint - separated
