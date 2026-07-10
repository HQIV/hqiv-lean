"""
Sparse atom-site contact graph for protein folding.

Lean mirrors: ``MiniproteinTertiaryContacts``, ``ProteinSolventPhaseGeometry``.

Contacts reference physical sites (``N``, ``CA``, ``C``, ``O``, sidechain centroid proxy)
rather than residue-indexed Cα pairs only.  Legacy ``TertiaryContact`` rows project to
``CA``/``CA`` atom contacts for audit compatibility.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from hqiv_lab.miniprotein_backbone import BackboneAtomState, Vec3
from hqiv_lab.miniprotein_contacts import TertiaryContact

SiteKind = Literal["N", "CA", "C", "O", "SC"]


@dataclass(frozen=True)
class AtomSiteRef:
    """Residue index (0-based) + backbone/sidechain site kind."""

    residue: int
    kind: SiteKind


@dataclass(frozen=True)
class AtomContact:
    """Distance target between two atom sites (sparse graph edge)."""

    i: AtomSiteRef
    j: AtomSiteRef
    target_angstrom: float
    kind: str


SITE_KINDS_PER_RESIDUE: tuple[SiteKind, ...] = ("N", "CA", "C", "O", "SC")


def site_coord(state: BackboneAtomState, ref: AtomSiteRef) -> Vec3:
    """Coordinate for a single atom site."""
    r = ref.residue
    if ref.kind == "N":
        return state.n_atoms[r]
    if ref.kind == "CA":
        return state.ca_atoms[r]
    if ref.kind == "C":
        return state.c_atoms[r]
    if ref.kind == "O":
        return state.o_atoms[r]
    return state.sc_centroids[r]


def flat_site_list(state: BackboneAtomState) -> list[tuple[AtomSiteRef, Vec3]]:
    """Enumerate all atom sites in residue-major order (sparse, not dense all-pairs)."""
    out: list[tuple[AtomSiteRef, Vec3]] = []
    for r in range(state.n_residues):
        for kind in SITE_KINDS_PER_RESIDUE:
            ref = AtomSiteRef(r, kind)
            out.append((ref, site_coord(state, ref)))
    return out


def site_flat_index(residue: int, kind: SiteKind, n_residues: int) -> int:
    """Linear index into ``flat_site_list`` order."""
    kind_idx = SITE_KINDS_PER_RESIDUE.index(kind)
    return residue * len(SITE_KINDS_PER_RESIDUE) + kind_idx


def residue_from_flat_index(flat_idx: int) -> int:
    return flat_idx // len(SITE_KINDS_PER_RESIDUE)


def tertiary_to_atom_contacts(
    contacts: tuple[TertiaryContact, ...],
    *,
    hydrophobic_use_sc: bool = True,
) -> tuple[AtomContact, ...]:
    """
    Project legacy residue Cα contacts to atom-site contacts.

    Structure register contacts stay at ``CA``/``CA``; hydrophobic pairs optionally use
    sidechain centroid proxies for burial geometry.
    """
    out: list[AtomContact] = []
    for c in contacts:
        if c.kind == "hydrophobic" and hydrophobic_use_sc:
            out.append(
                AtomContact(
                    AtomSiteRef(c.i, "SC"),
                    AtomSiteRef(c.j, "SC"),
                    c.target_angstrom,
                    c.kind,
                )
            )
        else:
            out.append(
                AtomContact(
                    AtomSiteRef(c.i, "CA"),
                    AtomSiteRef(c.j, "CA"),
                    c.target_angstrom,
                    c.kind,
                )
            )
    return tuple(out)


def expand_atom_contacts_with_backbone(
    contacts: tuple[AtomContact, ...],
    state: BackboneAtomState,
) -> tuple[AtomContact, ...]:
    """
    Add sparse intra-residue backbone bond constraints (N–CA, CA–C, C–O).

    Keeps the contact graph sparse: ``O(n)`` local bonds, not all-pairs.
    """
    from hqiv_lab.derived_bond_geometry import (
        peptide_bond_length_c_o,
        peptide_bond_length_n_ca,
        peptide_bond_length_ca_c,
    )

    n_ca = peptide_bond_length_n_ca()
    ca_c = peptide_bond_length_ca_c()
    c_o = peptide_bond_length_c_o()
    local: list[AtomContact] = []
    for r in range(state.n_residues):
        local.append(
            AtomContact(
                AtomSiteRef(r, "N"),
                AtomSiteRef(r, "CA"),
                n_ca,
                "backbone_n_ca",
            )
        )
        local.append(
            AtomContact(
                AtomSiteRef(r, "CA"),
                AtomSiteRef(r, "C"),
                ca_c,
                "backbone_ca_c",
            )
        )
        local.append(
            AtomContact(
                AtomSiteRef(r, "C"),
                AtomSiteRef(r, "O"),
                c_o,
                "backbone_c_o",
            )
        )
    return contacts + tuple(local)


def interface_exposure_from_atom_site(
    site_kind: SiteKind,
    contact_kind: str,
) -> str:
    """Map atom site + contact register to solvent interface exposure."""
    if contact_kind == "hydrophobic" or site_kind == "SC":
        return "hydrophobic"
    if site_kind in ("N", "O"):
        return "hydrophilic"
    if contact_kind in ("helix_sheet", "terminus", "helix_i3", "helix_i4", "sheet_i2"):
        return "hydrophilic"
    return "neutral"


def dress_atom_contact_targets(
    contacts: tuple[AtomContact, ...],
    *,
    temperature_k: float | None,
) -> tuple[AtomContact, ...]:
    """Apply aqueous H–O–H pivot dress per atom-site interface exposure."""
    if temperature_k is None:
        return contacts
    from hqiv_lab.protein_solvent_phase import aqueous_angle_pivot_dress_factor

    pivot_cache: dict[str, float] = {}
    dressed: list[AtomContact] = []
    for c in contacts:
        if c.kind.startswith("backbone_"):
            dressed.append(c)
            continue
        exp_i = interface_exposure_from_atom_site(c.i.kind, c.kind)
        exp_j = interface_exposure_from_atom_site(c.j.kind, c.kind)
        exp = exp_i if exp_i == "hydrophobic" or exp_j != "hydrophobic" else exp_j
        if exp not in pivot_cache:
            pivot_cache[exp] = aqueous_angle_pivot_dress_factor(temperature_k, exp)
        target = c.target_angstrom * pivot_cache[exp]
        dressed.append(AtomContact(c.i, c.j, target, c.kind))
    return tuple(dressed)
