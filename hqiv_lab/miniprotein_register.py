"""
Ramachandran basin assignment — computed from spine readout (``miniprotein_basin``).

Named register profiles are removed.  Use ``dihedrals_from_spine``.
"""

from __future__ import annotations

from hqiv_lab.miniprotein_basin import (
    BasinKind,
    ResidueContext,
    SpineContactCoupling,
    basin_to_dihedral,
    blend_basin_dihedrals,
    build_residue_contexts,
    contact_coupling_from_basins,
    contact_flags_from_spine,
    dihedrals_from_spine,
    resolve_basins_for_sequence,
    resolve_strand_basin,
)

RegisterContactCoupling = SpineContactCoupling


def dihedrals_from_register(
    sequence: str,
    ss_map: dict,
    profile=None,
) -> tuple[tuple[float, float], ...]:
    """Spine-computed (φ, ψ); legacy ``profile`` argument is ignored."""
    _ = profile
    return dihedrals_from_spine(sequence, ss_map)


def register_contact_coupling_for_sequence(
    sequence: str,
    ss_map: dict,
) -> SpineContactCoupling:
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss = ss_per_residue(sequence, ss_map)
    basins = resolve_basins_for_sequence(sequence, ss)
    return contact_coupling_from_basins(basins, ss)


def contact_flags_for_sequence(sequence: str, ss_map: dict) -> dict[str, bool]:
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss = ss_per_residue(sequence, ss_map)
    basins = resolve_basins_for_sequence(sequence, ss)
    return contact_flags_from_spine(basins, ss)


def register_contact_coupling(profile) -> SpineContactCoupling:
    raise TypeError("register_contact_coupling(profile) removed — use register_contact_coupling_for_sequence")


def contact_flags_for_register(profile) -> dict[str, bool]:
    raise TypeError("contact_flags_for_register(profile) removed — use contact_flags_for_sequence")


def register_manifest(profile) -> dict[str, str]:
    return {"engine": "spine_matrix_readout", "named_profile": "deprecated"}
