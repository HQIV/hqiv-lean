#!/usr/bin/env python3
"""
Hierarchical nuclear Casimir caustic binding.

Picture (matches `Hqiv.Physics.HQIVNuclei` + `NuclearAndAtomicSpectra`):

  1. **Spherical Fresnel caustic** — each nucleon wraps a Casimir surface; Fresnel
     envelope at meta-horizon radius `R_m = m+1` in all directions (~surface radius).
  2. **Pair overlap** — two nucleons fit together; `causticOverlap` / `valleyPotential`
     deepens the well (`deuteronBindingScale = γ · modes / R_m`).
  3. **Barbell torus** — dumbbell → ring: toroidal caustic one shell higher
     (`new_modes(m+1) = 8(m+2)`, `barbell_ring_caustic`).
  4. **Tetrahedral closure** — completing ⁴He adds the deepest cooperative caustic spot.

All active caustics **deepen the same binding well together** (additive stack on the
composite-trace MeV scale, modulated by `G_eff(θ)` at contact).

Lean: `Hqiv.Physics.NuclearCausticBinding`.
"""

from __future__ import annotations

from dataclasses import dataclass

import hqiv_curvature_information_ontology as cio
import hqiv_excited_states as hes
import hqiv_nuclear_inside_outside_binding as niob

REFERENCE_M = hes.REFERENCE_M
GAMMA = cio.GAMMA
ALPHA = cio.ALPHA


def R_m(m: int) -> float:
    return float(m + 1)


def available_modes(m: int) -> float:
    return cio.available_modes(m)


def new_modes_at_succ(m: int) -> float:
    """Lean `new_modes (m+1) = 8 * (m+2)` (`toroidal_ring_closure`)."""
    return 8.0 * float(m + 2)


def deuteron_binding_scale(m: int) -> float:
    """Lean `deuteronBindingScale m = γ · modes m / R_m m`."""
    return GAMMA * available_modes(m) / R_m(m)


def fresnel_curvature(m: int) -> float:
    """Lean `vacuumModeDensity` / `fresnelCaustic.curvature` = modes / R_m."""
    return available_modes(m) / R_m(m)


def pair_sphere_overlap_scale(m: int) -> float:
    """
    Two spherical Fresnel caustics overlap at ~R_m.

    `causticOverlap = R_m²`; valley deepening carries the horizon ratio scale.
    """
    _ = fresnel_curvature(m)
    return deuteron_binding_scale(m)


def barbell_torus_scale(m: int) -> float:
    """Toroidal ring caustic around the barbell at shell `m+1`."""
    return GAMMA * new_modes_at_succ(m) / R_m(m + 1)


def torus_deepening_scale(m: int, ring_offset: int) -> float:
    """Further bind steps deepen toroidal caustics on successively higher shells."""
    ms = m + ring_offset
    return GAMMA * cio.new_modes(ms) / R_m(ms)


def tetrahedral_closure_scale(m: int) -> float:
    """Deepest cooperative caustic spot completing the He tetrahedron."""
    ms = m + 2
    return GAMMA * available_modes(ms) / R_m(ms)


@dataclass(frozen=True)
class CausticLayer:
    name: str
    depth_mev: float


def caustic_layers(
    m: int,
    A: int,
    *,
    trace_mev: float,
    geff: float,
) -> tuple[CausticLayer, ...]:
    """Ordered caustic layers active for mass number A."""
    if A <= 1 or trace_mev <= 0.0:
        return ()

    scale = geff * trace_mev
    out: list[CausticLayer] = []

    out.append(
        CausticLayer(
            "sphere_pair_overlap",
            pair_sphere_overlap_scale(m) * scale,
        )
    )
    out.append(
        CausticLayer(
            "barbell_torus",
            barbell_torus_scale(m) * scale,
        )
    )

    for step in range(1, A - 1):
        out.append(
            CausticLayer(
                f"torus_deepen_step_{step}",
                torus_deepening_scale(m, step + 1) * scale,
            )
        )

    if A >= 4:
        out.append(
            CausticLayer(
                "tetrahedral_closure",
                tetrahedral_closure_scale(m) * scale,
            )
        )

    return tuple(out)


def cumulative_caustic_binding_mev(
    m: int,
    A: int,
    *,
    m_cluster: int,
    c: float = 1.0,
) -> tuple[float, tuple[CausticLayer, ...]]:
    """
    Outside caustic binding: all layers deepen the well together.

    Returns `(total_outside_mev, layers)`.
    """
    trace = niob.nucleon_trace_binding_mev(m, c)
    triplet = (max(m, 1), max(m_cluster, 1), abs(m - m_cluster) + 1)
    theta = niob.contact_phase_theta_rad(triplet)
    geff = niob.outside_contact_coupling(theta)
    layers = caustic_layers(m, A, trace_mev=trace, geff=geff)
    return sum(layer.depth_mev for layer in layers), layers


def nuclear_cluster_binding_mev(
    m: int,
    A: int,
    *,
    m_cluster: int | None = None,
    c: float = 1.0,
) -> tuple[float, float, float, tuple[CausticLayer, ...]]:
    """
    Total nuclear binding = inside trapped curvature + cumulative caustic outside.

    Returns `(total, inside, outside, caustic_layers)`.
    """
    if m_cluster is None:
        m_cluster = m if A <= 1 else m
    inside = niob.inside_nuclear_binding_mev(m, A, m_cluster=m_cluster, c=c)
    outside, layers = cumulative_caustic_binding_mev(m, A, m_cluster=m_cluster, c=c)
    return inside + outside, inside, outside, layers
