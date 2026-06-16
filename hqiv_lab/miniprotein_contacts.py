"""Sequence-derived tertiary contact graph for miniprotein closure."""

from __future__ import annotations

from dataclasses import dataclass

from functools import lru_cache

from hqiv_lab.miniprotein_backbone import SecondaryStructure
from hqiv_lab.peptide_geometry import (
    compact_terminus_ca_distance_angstrom,
    helix_ca_i_i3_distance_angstrom,
    helix_ca_i_i4_distance_angstrom,
    helix_sheet_ca_packing_distance_angstrom,
    peptide_backbone_contact_distance_angstrom,
    sheet_ca_i_i2_distance_angstrom,
)

HYDROPHOBIC_RESIDUES = frozenset("WLIVFMY")

STRUCTURE_CONTACT_KINDS = frozenset({"helix_i3", "helix_i4", "sheet_i2", "helix_sheet"})
BURIAL_CONTACT_KINDS = frozenset({"hydrophobic", "terminus"})

# Lower rank wins duplicate Cα pairs (structure register beats burial).
TERTIARY_CONTACT_KIND_RANK: dict[str, int] = {
    "helix_i3": 0,
    "helix_i4": 1,
    "sheet_i2": 2,
    "helix_sheet": 3,
    "terminus": 4,
    "hydrophobic": 5,
}


@lru_cache(maxsize=1)
def _derived_tertiary_contact_angstrom() -> float:
    from hqiv_lab.coordination import infer_monomer_geometry
    from hqiv_lab.foundation_specs import foundation_spec

    spec = foundation_spec("GlyGly")
    mono = infer_monomer_geometry(spec)
    return peptide_backbone_contact_distance_angstrom(spec, n_inter=mono.intermolecular_contacts)


@dataclass(frozen=True)
class TertiaryContact:
    """Cα pair target distance from derived geometry (not witness coordinates)."""

    i: int
    j: int
    target_angstrom: float
    kind: str


def ss_per_residue(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
) -> list[SecondaryStructure]:
    ss_by_index: dict[int, SecondaryStructure] = {}
    for ss, indices in ss_map.items():
        for idx in indices:
            ss_by_index[idx] = ss
    return [ss_by_index.get(i + 1, "C") for i in range(len(sequence))]


def _kind_rank(kind: str) -> int:
    return TERTIARY_CONTACT_KIND_RANK.get(kind, 99)


def _add_pair(
    pairs: dict[tuple[int, int], TertiaryContact],
    i: int,
    j: int,
    target: float,
    kind: str,
) -> None:
    if i == j:
        return
    key = (min(i, j), max(i, j))
    cand = TertiaryContact(key[0], key[1], target, kind)
    prev = pairs.get(key)
    if prev is None or _kind_rank(cand.kind) < _kind_rank(prev.kind):
        pairs[key] = cand


def _add_helix_sheet_contacts(
    pairs: dict[tuple[int, int], TertiaryContact],
    ss: list[SecondaryStructure],
    *,
    target: float,
    min_sep: int = 3,
    max_sep: int = 5,
) -> None:
    """Register Cα pairs between trailing sheet and leading helix (N→C order)."""
    sheet_idxs = [i for i, s in enumerate(ss) if s == "E"]
    helix_idxs = [i for i, s in enumerate(ss) if s == "H"]
    if len(sheet_idxs) < 2 or len(helix_idxs) < 3:
        return
    for si in sheet_idxs[-2:]:
        for hi in helix_idxs[:3]:
            if hi <= si:
                continue
            sep = hi - si
            if min_sep <= sep <= max_sep:
                _add_pair(pairs, si, hi, target, "helix_sheet")


def partition_tertiary_contacts(
    contacts: tuple[TertiaryContact, ...],
) -> tuple[tuple[TertiaryContact, ...], tuple[TertiaryContact, ...]]:
    """Split SS packing vs hydrophobic/terminus burial (legacy two-pass)."""
    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    burial = hydrophobic + terminus
    return structure, burial


def partition_tertiary_contacts_staged(
    contacts: tuple[TertiaryContact, ...],
) -> tuple[tuple[TertiaryContact, ...], tuple[TertiaryContact, ...], tuple[TertiaryContact, ...]]:
    """Split structure register, hydrophobic core, and terminus cap (three-pass closure)."""
    structure: list[TertiaryContact] = []
    hydrophobic: list[TertiaryContact] = []
    terminus: list[TertiaryContact] = []
    for c in contacts:
        if c.kind in STRUCTURE_CONTACT_KINDS:
            structure.append(c)
        elif c.kind == "hydrophobic":
            hydrophobic.append(c)
        elif c.kind == "terminus":
            terminus.append(c)
    return tuple(structure), tuple(hydrophobic), tuple(terminus)


def build_tertiary_contact_graph(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    *,
    include_terminus: bool = True,
) -> tuple[TertiaryContact, ...]:
    """
    Derived tertiary Cα contacts from SS topology + hydrophobic sequence.

    Kinds partition closure passes only; all contacts share the same Jacobi step law.
    """
    n = len(sequence)
    ss = ss_per_residue(sequence, ss_map)
    pairs: dict[tuple[int, int], TertiaryContact] = {}

    i3 = helix_ca_i_i3_distance_angstrom()
    i4 = helix_ca_i_i4_distance_angstrom()
    i2 = sheet_ca_i_i2_distance_angstrom()
    hx = helix_sheet_ca_packing_distance_angstrom()
    hydro = _derived_tertiary_contact_angstrom()

    for i in range(n):
        if ss[i] == "H":
            for sep, target, kind in (
                (3, i3, "helix_i3"),
                (4, i4, "helix_i4"),
            ):
                j = i + sep
                if j < n and ss[j] == "H":
                    _add_pair(pairs, i, j, target, kind)
        if ss[i] == "E":
            j = i + 2
            if j < n and ss[j] == "E":
                _add_pair(pairs, i, j, i2, "sheet_i2")

    _add_helix_sheet_contacts(pairs, ss, target=hx)

    for i, aa in enumerate(sequence):
        if aa not in HYDROPHOBIC_RESIDUES:
            continue
        for j in range(i + 4, min(i + max(n // 2, 5), n)):
            if sequence[j] in HYDROPHOBIC_RESIDUES:
                _add_pair(pairs, i, j, hydro, "hydrophobic")

    if include_terminus and n >= 12:
        term = compact_terminus_ca_distance_angstrom(n, contact_angstrom=hydro)
        _add_pair(pairs, 0, n - 1, term, "terminus")

    return tuple(pairs.values())
