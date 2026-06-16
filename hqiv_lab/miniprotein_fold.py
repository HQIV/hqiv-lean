"""Miniprotein fold readout — secondary-structure dihedral spine + contact network."""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any

from hqiv_lab.miniprotein_backbone import (
    SecondaryStructure,
    Vec3,
    dihedrals_from_secondary_structure,
    hqiv_peptide_bond_geometry,
    kabsch_rmsd,
    place_ca_trace,
    ramachandran_extended_rad,
)
from hqiv_lab.miniprotein_closure import apply_staged_tertiary_contact_closure
from hqiv_lab.miniprotein_contacts import (
    HYDROPHOBIC_RESIDUES,
    TertiaryContact,
    build_tertiary_contact_graph,
)

TRP_CAGE_SEQUENCE = "NLYIQWLKDGGPSSGRPPPS"

# Literature secondary-structure map for Trp-cage (1L2Y / TC5b).
TRP_CAGE_SECONDARY_STRUCTURE: dict[SecondaryStructure, tuple[int, ...]] = {
    "E": (2, 3, 4),
    "H": tuple(range(7, 18)),
    "C": (1, 5, 6, 18, 19, 20),
}

_TRP_CAGE_DIHEDRALS = dihedrals_from_secondary_structure(
    TRP_CAGE_SEQUENCE,
    TRP_CAGE_SECONDARY_STRUCTURE,
)
_TRP_CAGE_CONTACTS = build_tertiary_contact_graph(
    TRP_CAGE_SEQUENCE,
    TRP_CAGE_SECONDARY_STRUCTURE,
)
_BOND_GEOMETRY = hqiv_peptide_bond_geometry()
_BOND_GEOMETRY_DICT = {
    "N_CA": _BOND_GEOMETRY.n_ca,
    "CA_C": _BOND_GEOMETRY.ca_c,
    "C_N": _BOND_GEOMETRY.c_n,
    "C_O": _BOND_GEOMETRY.c_o,
}


@dataclass(frozen=True)
class MiniproteinFoldResult:
    name: str
    sequence: str
    n_residues: int
    strategy: str
    ca_trace: tuple[Vec3, ...]
    bond_geometry: dict[str, float]
    network_contacts: int
    tertiary_contacts: int
    ca_rmsd_angstrom: float | None
    ca_rmsd_pass_angstrom: float | None
    passed: bool | None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def protein_scaffold_contact_count(n_residues: int) -> int:
    """
    O(1) contact count for linear ``build_protein_network`` scaffolds.

    Matches cluster_deficit (n) + covalent (n−1) + hyperclosure (1 for n≥3).
    """
    n = max(n_residues, 0)
    if n <= 1:
        return n
    if n == 2:
        return 3
    return 2 * n


def _build_protein_network(name: str, sequence: str, dihedrals: tuple[tuple[float, float], ...]):
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_curvature_contact_network as ccn
    import hqiv_s2_binding_geometry as s2g
    import hqiv_thermodynamic_phase_from_tp as tptp

    backbone = tuple(
        s2g.BackboneDihedral(i, phi, psi) for i, (phi, psi) in enumerate(dihedrals)
    )
    return ccn.build_protein_network(
        name,
        n_residues=len(sequence),
        environment=tptp.ThermodynamicEnvironment.protein_cytosol(),
        backbone_dihedrals=backbone,
    )


def _resolve_network_contacts(
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    name: str,
    include_network: bool,
) -> int:
    if include_network:
        return len(_build_protein_network(name, sequence, dihedrals).contacts)
    return protein_scaffold_contact_count(len(sequence))


def fold_from_dihedrals(
    name: str,
    sequence: str,
    dihedrals: tuple[tuple[float, float], ...],
    *,
    strategy: str,
    witness_ca: list[Vec3] | None = None,
    pass_threshold_angstrom: float | None = None,
    include_network: bool = False,
    tertiary_contacts: int = 0,
) -> MiniproteinFoldResult:
    ca = place_ca_trace(sequence, dihedrals)
    rmsd = kabsch_rmsd(ca, witness_ca) if witness_ca else None
    passed = None
    if rmsd is not None and pass_threshold_angstrom is not None:
        passed = rmsd <= pass_threshold_angstrom
    return MiniproteinFoldResult(
        name=name,
        sequence=sequence,
        n_residues=len(sequence),
        strategy=strategy,
        ca_trace=tuple(ca),
        bond_geometry=dict(_BOND_GEOMETRY_DICT),
        network_contacts=_resolve_network_contacts(
            sequence, dihedrals, name=name, include_network=include_network
        ),
        tertiary_contacts=tertiary_contacts,
        ca_rmsd_angstrom=rmsd,
        ca_rmsd_pass_angstrom=pass_threshold_angstrom,
        passed=passed,
    )


def fold_glycylglycine(
    *,
    witness_ca: list[Vec3] | None = None,
    pass_a: float = 2.0,
    include_network: bool = False,
) -> MiniproteinFoldResult:
    seq = "GG"
    dihedrals = dihedrals_from_secondary_structure(seq, {"E": (1, 2)})
    return fold_from_dihedrals(
        "GG",
        seq,
        dihedrals,
        strategy="beta_strand_dipeptide",
        witness_ca=witness_ca,
        pass_threshold_angstrom=pass_a,
        include_network=include_network,
    )


def fold_trp_cage(
    *,
    witness_ca: list[Vec3] | None = None,
    pass_a: float = 5.0,
    tertiary_closure: bool = True,
    include_network: bool = False,
) -> MiniproteinFoldResult:
    """Trp-cage (TC5b): cached SS φ/ψ + tertiary contact closure (fast default path)."""
    seq = TRP_CAGE_SEQUENCE
    dihedrals = _TRP_CAGE_DIHEDRALS
    contacts: tuple[TertiaryContact, ...] = _TRP_CAGE_CONTACTS
    ca = place_ca_trace(seq, dihedrals)
    strategy = "secondary_structure_spine"
    if tertiary_closure:
        ca = apply_staged_tertiary_contact_closure(ca, contacts)
        strategy = "secondary_structure_spine+staged_tertiary_contacts"
    rmsd = kabsch_rmsd(ca, witness_ca) if witness_ca else None
    passed = None
    if rmsd is not None and pass_a is not None:
        passed = rmsd <= pass_a
    return MiniproteinFoldResult(
        name="trp_cage",
        sequence=seq,
        n_residues=len(seq),
        strategy=strategy,
        ca_trace=tuple(ca),
        bond_geometry=dict(_BOND_GEOMETRY_DICT),
        network_contacts=_resolve_network_contacts(
            seq, dihedrals, name="trp_cage", include_network=include_network
        ),
        tertiary_contacts=len(contacts),
        ca_rmsd_angstrom=rmsd,
        ca_rmsd_pass_angstrom=pass_a,
        passed=passed,
    )


def fold_extended_control(
    sequence: str,
    name: str = "extended",
    *,
    include_network: bool = False,
) -> MiniproteinFoldResult:
    ext = ramachandran_extended_rad()
    dihedrals = tuple(ext for _ in sequence)
    return fold_from_dihedrals(
        name,
        sequence,
        dihedrals,
        strategy="extended_chain_control",
        include_network=include_network,
    )


def radius_of_gyration(ca: list[Vec3]) -> float:
    if not ca:
        return float("nan")
    cx = sum(p[0] for p in ca) / len(ca)
    cy = sum(p[1] for p in ca) / len(ca)
    cz = sum(p[2] for p in ca) / len(ca)
    return math.sqrt(sum((p[0] - cx) ** 2 + (p[1] - cy) ** 2 + (p[2] - cz) ** 2 for p in ca) / len(ca))


def hydrophobic_contact_pairs(
    sequence: str,
    *,
    min_sep: int = 4,
    max_sep: int | None = None,
) -> list[tuple[int, int]]:
    n = len(sequence)
    hi = max_sep if max_sep is not None else max(n // 2, min_sep + 1)
    pairs: list[tuple[int, int]] = []
    for i, aa in enumerate(sequence):
        if aa not in HYDROPHOBIC_RESIDUES:
            continue
        for j in range(i + min_sep, min(i + hi + 1, n)):
            if sequence[j] in HYDROPHOBIC_RESIDUES:
                pairs.append((i, j))
    return pairs


def count_tertiary_contacts(sequence: str, ss_map: dict[SecondaryStructure, tuple[int, ...]]) -> int:
    return len(build_tertiary_contact_graph(sequence, ss_map))
