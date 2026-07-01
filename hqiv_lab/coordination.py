"""Monomer geometry and intermolecular coordination — derived from bonds + VSEPR."""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

from hqiv_lab._scripts import ensure_scripts_on_path
from hqiv_lab.derived_bond_geometry import bond_length_angstrom, centre_bond_angle_rad
from hqiv_lab.spec import MoleculeSpec

ensure_scripts_on_path()
import hqiv_electronic_valence_shells as evs  # noqa: E402
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402

def element_amu(label: str, z: int) -> float:
    """Atomic mass from nuclear cluster readout (no periodic-table lookup)."""
    import hqiv_derived_chemistry as hdc

    _ = label
    return hdc.derived_atomic_mass_amu(z, z)


class IntermolecularMotif(str, Enum):
    """How the monomer participates in a condensed network."""

    TETRAHEDRAL_HBOND = "tetrahedral_hbond"  # H2O ice
    PYRAMIDAL_HBOND = "pyramidal_hbond"  # NH3
    APOLAR_CLOSE_PACK = "apolar_close_pack"  # CH4
    LINEAR_CHAIN = "linear_chain"  # HF, LiH
    DIATOMIC = "diatomic"  # H2
    IONIC_LATTICE = "ionic_lattice"  # rocksalt / ionic crystal
    METALLIC_LATTICE = "metallic_lattice"  # delocalized Fermi sea / close-packed metal
    POLYOL_HBOND = "polyol_hbond"  # alcohol / carbohydrate OH network
    PEPTIDE_LAYER = "peptide_layer"  # dipeptide / peptide crystal H-bond sheets
    GENERIC = "generic"


@dataclass(frozen=True)
class MonomerGeometry:
    z_heavy: int
    n_bonds_at_heavy: int
    mean_bond_length_angstrom: float
    bond_angle_rad: float
    lone_pair_count: int
    h_count: int
    motif: IntermolecularMotif
    intermolecular_contacts: int


def _heavy_centre_index(fragments: tuple[FragmentConfig, ...]) -> int:
    best = 0
    best_z = -1
    for i, f in enumerate(fragments):
        if f.z_nuclear > best_z:
            best_z = f.z_nuclear
            best = i
    return best


def _bonds_at_centre(
    centre: int,
    bonds: tuple[BondGeometry, ...],
) -> tuple[BondGeometry, ...]:
    return tuple(
        b
        for b in bonds
        if b.frag_i == centre or b.frag_j == centre
    )


def _mean_bond_angle(bonds: tuple[BondGeometry, ...], *, z_heavy: int, n_bonds: int) -> float:
    angles = [b.bond_angle_rad for b in bonds if b.bond_angle_rad is not None]
    if angles:
        return sum(angles) / len(angles)
    if n_bonds >= 1 and z_heavy > 1:
        return centre_bond_angle_rad(z_heavy, n_bonds)
    if len(bonds) == 1:
        return math.pi
    return centre_bond_angle_rad(z_heavy, max(n_bonds, 2))


def _count_oh_groups(
    fragments: tuple[FragmentConfig, ...],
    bonds: tuple[BondGeometry, ...],
) -> int:
    o_indices = {i for i, f in enumerate(fragments) if f.z_nuclear == 8}
    h_indices = {i for i, f in enumerate(fragments) if f.z_nuclear == 1}
    oh = 0
    for o in o_indices:
        has_h = False
        has_heavy = False
        for b in bonds:
            if b.frag_i == o and b.frag_j in h_indices:
                has_h = True
            if b.frag_j == o and b.frag_i in h_indices:
                has_h = True
            if b.frag_i == o and b.frag_j not in h_indices:
                has_heavy = True
            if b.frag_j == o and b.frag_i not in h_indices:
                has_heavy = True
        if has_h and has_heavy:
            oh += 1
    return oh


def _is_peptide_backbone(spec: MoleculeSpec) -> bool:
    labels = {f.label.upper() for f in spec.fragments}
    return any(l.startswith("N") for l in labels) and any(l.startswith("CA") for l in labels)


def infer_monomer_geometry(spec: MoleculeSpec) -> MonomerGeometry:
    """Derive coordination motif from fragment graph (no phase tables)."""
    frags = spec.fragments
    if len(frags) == 2 and all(f.z_nuclear == 1 for f in frags):
        b = spec.bonds[0] if spec.bonds else BondGeometry(0, 1, bond_length_angstrom("H", "H"))
        return MonomerGeometry(
            z_heavy=1,
            n_bonds_at_heavy=1,
            mean_bond_length_angstrom=b.distance_angstrom,
            bond_angle_rad=math.pi,
            lone_pair_count=0,
            h_count=2,
            motif=IntermolecularMotif.DIATOMIC,
            intermolecular_contacts=1,
        )

    centre = _heavy_centre_index(frags)
    z = frags[centre].z_nuclear
    centre_bonds = _bonds_at_centre(centre, spec.bonds)
    n_bonds = len(centre_bonds)
    mean_len = (
        sum(b.distance_angstrom for b in centre_bonds) / n_bonds
        if n_bonds
        else 1.0
    )
    angle = _mean_bond_angle(centre_bonds, z_heavy=z, n_bonds=n_bonds)
    from hqiv_lab.atomic_chart import lean_centre_lone_pair_count

    n_lp = lean_centre_lone_pair_count(z, n_bonds)
    h_count = sum(1 for f in frags if f.z_nuclear == 1)
    oh_count = _count_oh_groups(frags, spec.bonds)

    if _is_peptide_backbone(spec):
        r_pep = bond_length_angstrom("C", "N", coord_i=2, coord_j=2)
        return MonomerGeometry(
            z_heavy=7,
            n_bonds_at_heavy=2,
            mean_bond_length_angstrom=r_pep,
            bond_angle_rad=centre_bond_angle_rad(7, 2),
            lone_pair_count=1,
            h_count=h_count,
            motif=IntermolecularMotif.PEPTIDE_LAYER,
            intermolecular_contacts=4,
        )

    if oh_count >= 1 and any(f.z_nuclear == 6 for f in frags):
        oh_lens = [
            b.distance_angstrom
            for b in spec.bonds
            if any(
                frags[b.frag_i].z_nuclear == 8 and frags[b.frag_j].z_nuclear == 1
                or frags[b.frag_j].z_nuclear == 8 and frags[b.frag_i].z_nuclear == 1
                for _ in [0]
            )
        ]
        mean_oh = sum(oh_lens) / len(oh_lens) if oh_lens else bond_length_angstrom("O", "H", coord_i=1, coord_j=1)
        inter = min(6, 4 + max(0, oh_count - 2))
        return MonomerGeometry(
            z_heavy=8,
            n_bonds_at_heavy=2,
            mean_bond_length_angstrom=mean_oh,
            bond_angle_rad=centre_bond_angle_rad(8, 2),
            lone_pair_count=1,
            h_count=h_count,
            motif=IntermolecularMotif.POLYOL_HBOND,
            intermolecular_contacts=inter,
        )

    from hqiv_lab.atomic_chart import (
        intermolecular_contact_count,
        intermolecular_motif_from_chart,
    )

    motif = intermolecular_motif_from_chart(z, n_bonds, n_lp, h_count)
    inter = intermolecular_contact_count(motif, n_bonds=n_bonds, n_lp=n_lp)

    return MonomerGeometry(
        z_heavy=z,
        n_bonds_at_heavy=n_bonds,
        mean_bond_length_angstrom=mean_len,
        bond_angle_rad=angle,
        lone_pair_count=n_lp,
        h_count=h_count,
        motif=motif,
        intermolecular_contacts=inter,
    )


def melt_motif_relative_scale(
    motif: IntermolecularMotif,
    n_inter: int,
    *,
    z_heavy: int = 8,
) -> float:
    """
    Motif-specific melt ladder scale relative to tetrahedral ice (= 1).

    HQIV rationals only (α, γ); Python mirror of ``meltMotifRelativeScale`` in Lean.
    """
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_lean_physics_primitives as lean

    g = lean.GAMMA
    a = lean.ALPHA
    ref_n = 4
    n = max(n_inter, 1)

    if motif == IntermolecularMotif.TETRAHEDRAL_HBOND:
        return 1.0
    if motif == IntermolecularMotif.PYRAMIDAL_HBOND:
        return (3.0 / ref_n) * (1.0 - g / 8.0)
    if motif == IntermolecularMotif.APOLAR_CLOSE_PACK:
        return (g / a) / math.sqrt(float(n))
    if motif == IntermolecularMotif.LINEAR_CHAIN:
        hal = 1.0 + g * (z_heavy / 8.0)
        return (g / a) / float(n) * hal * (1.0 + g) * (1.0 + g / 16.0)
    if motif == IntermolecularMotif.IONIC_LATTICE:
        return (a / g) / float(max(n, 1))
    if motif == IntermolecularMotif.METALLIC_LATTICE:
        return (g / a) / float(max(n, 1))
    if motif == IntermolecularMotif.POLYOL_HBOND:
        n = max(n_inter, 1)
        return (3.0 / ref_n) * (1.0 + g / 8.0) * (float(ref_n) / float(n))
    if motif == IntermolecularMotif.PEPTIDE_LAYER:
        return (3.0 / ref_n) * (1.0 - g / 16.0)
    return g / float(n)
