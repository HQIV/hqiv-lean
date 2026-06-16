#!/usr/bin/env python3
"""
Derived chemistry scalars from the nuclear + condensed spine (no AMU / ρ tables).

  • Atomic mass [amu] from ``cluster_mass_mev`` on the curvature binding ladder
  • Melt reference density from solid geometry + network-derived melt opening
"""

from __future__ import annotations

import math

import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
from fragment_aware_bonded_horizon import FragmentConfig

# CODATA 2018 — unit conversion only (not a chemistry fit).
MEV_PER_AMU = 931.49410242


def derived_atomic_mass_amu(z: int, electrons: int | None = None) -> float:
    """Mass [amu] from nuclear cluster readout at stable A(Z)."""
    e = electrons if electrons is not None else z
    a = ncb.stable_mass_number(z, e)
    m_nuc = ncb.nucleus_curvature_shell(a)
    return ncb.cluster_mass_mev(m_nuc, a) / MEV_PER_AMU


def fragment_mass_amu(frag: FragmentConfig) -> float:
    return derived_atomic_mass_amu(frag.z_nuclear, frag.electrons)


def derived_liquid_density_scale_from_solid(
    rho_solid_g_cm3: float,
    *,
    motif: str,
    mono: object | None = None,
    salt: object | None = None,
    n_coord: int = 4,
    molecule: str | None = None,
) -> float:
    """
    Liquid ρ reference at melt from dynamic crystalline melt opening.

    Prefer ``mono`` (molecular) or ``salt`` (ionic) witnesses; motif-only fallback
    delegates to ``hqiv_phase_geometry_density.resolve_crystalline_melt_density_ratio``.
    """
    import hqiv_phase_geometry_density as pgd

    melt_ratio, solid_denser = pgd.resolve_crystalline_melt_density_ratio(
        motif=motif,
        n_coord=n_coord,
        molecule=molecule,
        mono=mono,
        salt=salt,
    )
    from hqiv_lab.packing import melt_density_g_cm3_from_solid

    return melt_density_g_cm3_from_solid(
        rho_solid_g_cm3,
        melt_ratio,
        solid_denser=solid_denser,
    )


def derived_liquid_reference_density_g_cm3(
    molecule: str,
    *,
    temperature_k: float = 273.15,
) -> float:
    """Primary solid template density → network-derived melt reference (no ρ table)."""
    from hqiv_lab.coordination import infer_monomer_geometry
    from hqiv_lab.spec import resolve_spec
    from hqiv_lab.unit_cell import density_g_cm3, unit_cell_for_allotrope

    spec = resolve_spec(molecule)
    mono = infer_monomer_geometry(spec)
    from hqiv_lab.packing import templates_for_motif
    from hqiv_lab.unit_cell import density_g_cm3, unit_cell_for_allotrope

    templates = templates_for_motif(mono.motif, spec=spec)
    if not templates:
        return 1.0
    cell = unit_cell_for_allotrope(spec, templates[0], mono, temperature_k=temperature_k)
    rho_s = density_g_cm3(cell)
    from hqiv_lab.polyol_geometry import (
        is_monomer_polyol_alcohol,
        is_triol_polyol,
        monomer_polyol_liquid_density_factor,
        polyol_triol_liquid_density_factor,
    )

    if is_triol_polyol(spec):
        # Liquid witness above T_melt: weak network densification (γ/6 slot).
        return rho_s * polyol_triol_liquid_density_factor()
    rho_liq = derived_liquid_density_scale_from_solid(
        rho_s,
        motif=mono.motif.value,
        mono=mono,
        n_coord=mono.intermolecular_contacts,
    )
    if is_monomer_polyol_alcohol(spec):
        return rho_liq * monomer_polyol_liquid_density_factor()
    return rho_liq


def chemistry_compton_triplet_from_z(z: int) -> tuple[int, int, int]:
    """Single-fragment Compton triplet for ion nodes."""
    frag = FragmentConfig("X", z, z)
    return evs.chemistry_compton_triplet((frag,))
