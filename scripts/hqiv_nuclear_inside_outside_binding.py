#!/usr/bin/env python3
"""
Nuclear inside / outside curvature binding primitives.

**Nuclear binding energy** lives in the same place as proton (or any hadron) mass:

  • **Inside:** trapped curvature volume × Planck budget (`metaHorizonTrappedInsideRatio`)
    times the composite-trace nucleon binding at the readout shell.
  • **Outside:** hierarchical Casimir caustics — spherical pair overlap, barbell
    torus, tetrahedral closure — all deepening the same well via `G_eff(θ)`.

This is the nuclear binding readout — not molecular / chemistry eV projection.

Mirrors:
  `Hqiv.Physics.NuclearCurvatureBinding`
  `Hqiv.Physics.MetaHorizonTrappedPlanckMass`
  `Hqiv.Geometry.HQVMetric` (`G_eff`)
  `Hqiv.Physics.ComptonIRWindow` (`phaseTheta`)
"""

from __future__ import annotations

import math

import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
from lih_derivation_scan import PHASE_THETA, compton_window_angles_from_shells

REFERENCE_M = hes.REFERENCE_M
ALPHA = lean.ALPHA
PROTON_MEV = 938.27208816

# Isotope valley contact count (Lean `bbnValleyCount` / `HQIVNuclei.valleyCount`).
VALLEY_CONTACT_COUNT: dict[int, int] = {1: 0, 2: 2, 3: 4, 4: 6}


def g_eff(phi: float) -> float:
    """Lean `G_eff φ = φ^α` for φ ≥ 0 (natural units G₀=H₀=1)."""
    if phi <= 0.0:
        return 0.0
    return phi**ALPHA


def meta_horizon_inside_ratio(m_exc: int, m_ref: int = REFERENCE_M) -> float:
    return hes.meta_horizon_trapped_inside_ratio(m_exc, m_ref)


def outside_contact_coupling(theta_rad: float) -> float:
    """`G_eff(θ/θ₀)` with θ₀ = phaseTheta = π/2."""
    if theta_rad <= 0.0:
        return 0.0
    phi = min(theta_rad / PHASE_THETA, 1.0)
    return g_eff(phi)


def contact_phase_theta_rad(shell_triplet: tuple[int, int, int]) -> float:
    compton = compton_window_angles_from_shells(shell_triplet)
    return sum(compton.angles_rad) / len(compton.angles_rad)


def nucleon_trace_binding_mev(m: int, c: float = 1.0) -> float:
    return hes.e_bind_from_nucleon_trace_mev(m, c)


def inside_nuclear_binding_mev(m: int, A: int, *, m_cluster: int, c: float = 1.0) -> float:
    """
    Inside-curvature cluster binding: A nucleons closing from separated shells
    onto the cluster readout shell (same trapped-inside spine as hadron mass).
    """
    if A <= 1:
        return 0.0
    trace = nucleon_trace_binding_mev(m, c)
    r_free = meta_horizon_inside_ratio(m, REFERENCE_M)
    r_clos = meta_horizon_inside_ratio(m_cluster, REFERENCE_M)
    return float(A) * trace * max(0.0, r_clos - r_free)


def outside_nuclear_binding_mev(
    m: int,
    A: int,
    *,
    m_cluster: int,
    c: float = 1.0,
) -> float:
    """
    Outside binding from hierarchical Casimir caustics (sphere pair, barbell torus,
    tetrahedral closure).  See `hqiv_nuclear_caustic_binding`.
    """
    from hqiv_nuclear_caustic_binding import cumulative_caustic_binding_mev

    total, _ = cumulative_caustic_binding_mev(m, A, m_cluster=m_cluster, c=c)
    return total


def nuclear_cluster_binding_mev(
    m: int,
    A: int,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
) -> tuple[float, float, float]:
    """
    Total nuclear cluster binding = inside + outside (MeV).

    Returns `(total, inside, outside)`.
    """
    from hqiv_nuclear_caustic_binding import nuclear_cluster_binding_mev as caustic_total

    total, inside, outside, _ = caustic_total(m, A, m_cluster=m_cluster, c=c)
    return total, inside, outside
