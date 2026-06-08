"""Monomer geometry and intermolecular coordination — derived from bonds + VSEPR."""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

from hqiv_lab._scripts import ensure_scripts_on_path
from hqiv_lab.spec import MoleculeSpec

ensure_scripts_on_path()
import hqiv_electronic_valence_shells as evs  # noqa: E402
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig  # noqa: E402

_ELEMENT_AMU: dict[str, float] = {
    "H": 1.008,
    "Li": 6.94,
    "C": 12.011,
    "N": 14.007,
    "O": 15.999,
    "F": 18.998,
    "T": 3.016,
}


def element_amu(label: str, z: int) -> float:
    return _ELEMENT_AMU.get(label, float(z))


class IntermolecularMotif(str, Enum):
    """How the monomer participates in a condensed network."""

    TETRAHEDRAL_HBOND = "tetrahedral_hbond"  # H2O ice
    PYRAMIDAL_HBOND = "pyramidal_hbond"  # NH3
    APOLAR_CLOSE_PACK = "apolar_close_pack"  # CH4
    LINEAR_CHAIN = "linear_chain"  # HF, LiH
    DIATOMIC = "diatomic"  # H2
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


def _mean_bond_angle(bonds: tuple[BondGeometry, ...]) -> float:
    angles = [b.bond_angle_rad for b in bonds if b.bond_angle_rad is not None]
    if angles:
        return sum(angles) / len(angles)
    if len(bonds) == 2:
        return math.radians(104.5)
    if len(bonds) == 3:
        return math.radians(107.0)
    if len(bonds) == 4:
        return math.radians(109.47)
    return math.radians(109.47)


def infer_monomer_geometry(spec: MoleculeSpec) -> MonomerGeometry:
    """Derive coordination motif from fragment graph (no phase tables)."""
    frags = spec.fragments
    if len(frags) == 2 and all(f.z_nuclear == 1 for f in frags):
        b = spec.bonds[0] if spec.bonds else BondGeometry(0, 1, 0.74)
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
    angle = _mean_bond_angle(centre_bonds)
    n_lp = evs.centre_vsepr_lone_pair_count(z, n_bonds)
    h_count = sum(1 for f in frags if f.z_nuclear == 1)

    motif = IntermolecularMotif.GENERIC
    inter = max(2, n_bonds + n_lp)

    if z == 8 and n_bonds == 2 and h_count == 2:
        motif = IntermolecularMotif.TETRAHEDRAL_HBOND
        inter = 4
    elif z == 7 and n_bonds == 3 and h_count == 3:
        motif = IntermolecularMotif.PYRAMIDAL_HBOND
        inter = 4
    elif z == 6 and n_bonds == 4 and h_count == 4:
        motif = IntermolecularMotif.APOLAR_CLOSE_PACK
        inter = 4
    elif z == 9 and n_bonds == 1:
        motif = IntermolecularMotif.LINEAR_CHAIN
        inter = 2
    elif z <= 3 and n_bonds == 1:
        motif = IntermolecularMotif.LINEAR_CHAIN
        inter = 2

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
    return g / float(n)
