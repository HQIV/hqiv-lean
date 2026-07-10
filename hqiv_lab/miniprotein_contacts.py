"""Sequence-derived tertiary contact graph for miniprotein closure."""

from __future__ import annotations

import math
from dataclasses import dataclass

from functools import lru_cache

from hqiv_lab.miniprotein_backbone import SecondaryStructure
from hqiv_lab.miniprotein_basin import SpineContactCoupling
from hqiv_lab.protein_solvent_phase import PROTEIN_FOLDING_TEMPERATURE_K
from hqiv_lab.peptide_geometry import (
    compact_terminus_ca_distance_angstrom,
    helix_ca_i_i3_distance_angstrom,
    helix_ca_i_i3_distorted_distance_angstrom,
    helix_ca_i_i4_distance_angstrom,
    helix_ca_i_i4_distorted_distance_angstrom,
    helix_sheet_ca_packing_distance_angstrom,
    helix_sheet_hairpin_compact_distance_angstrom,
    helix_sheet_hairpin_distance_angstrom,
    peptide_backbone_contact_distance_angstrom,
    sheet_ca_i_i2_distance_angstrom,
    sheet_ca_i_i2_strap_distance_angstrom,
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

# Lean ``tertiaryContactPass`` — closure locality (register → burial → terminus).
TERTIARY_CONTACT_PASS: dict[str, int] = {
    "helix_i3": 0,
    "helix_i4": 0,
    "sheet_i2": 0,
    "helix_sheet": 0,
    "hydrophobic": 1,
    "terminus": 2,
}

TERTIARY_CONTACT_MAX_PASS: int = 2


def tertiary_contact_pass(kind: str) -> int:
    """Lean ``tertiaryContactPass`` witness."""
    return TERTIARY_CONTACT_PASS.get(kind, 0)


def closure_pass_weight(kind: str) -> float:
    """``(pass + 1) / (maxPass + 1)`` — terminus pass gets full closure weight."""
    return (tertiary_contact_pass(kind) + 1) / (TERTIARY_CONTACT_MAX_PASS + 1)


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


def max_helix_run_length(ss: list[SecondaryStructure]) -> int:
    """Longest contiguous helix run (residue count)."""
    best = 0
    i = 0
    while i < len(ss):
        if ss[i] != "H":
            i += 1
            continue
        j = i
        while j < len(ss) and ss[j] == "H":
            j += 1
        best = max(best, j - i)
        i = j
    return best


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
    hairpin_singleton: bool = False,
) -> None:
    """Register Cα pairs between trailing sheet and leading helix (N→C order)."""
    sheet_idxs = [i for i, s in enumerate(ss) if s == "E"]
    helix_idxs = [i for i, s in enumerate(ss) if s == "H"]
    if len(sheet_idxs) < 2 or len(helix_idxs) < 1:
        return
    short_helix = max_helix_run_length(ss) <= 2
    if short_helix and not hairpin_singleton:
        return
    if short_helix:
        si = sheet_idxs[-1]
        hi = helix_idxs[0]
        if hi > si:
            sep = hi - si
            if min_sep <= sep <= max_sep:
                _add_pair(pairs, si, hi, target, "helix_sheet")
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
    hairpin_strap: bool = False,
    strap_sheet_i2: bool = False,
    compact_helix: bool = False,
) -> tuple[TertiaryContact, ...]:
    """
    Derived tertiary Cα contacts from SS topology + hydrophobic sequence.

    ``strap_sheet_i2`` selects strap NeRF i+2 targets when the register uses strap
    strand (decoupled from ``hairpin_strap`` helix–sheet packing distances).
    """
    n = len(sequence)
    ss = ss_per_residue(sequence, ss_map)
    pairs: dict[tuple[int, int], TertiaryContact] = {}

    i3 = (
        helix_ca_i_i3_distorted_distance_angstrom()
        if compact_helix
        else helix_ca_i_i3_distance_angstrom()
    )
    i4 = (
        helix_ca_i_i4_distorted_distance_angstrom()
        if compact_helix
        else helix_ca_i_i4_distance_angstrom()
    )
    use_strap_i2 = strap_sheet_i2 or hairpin_strap
    i2 = sheet_ca_i_i2_strap_distance_angstrom() if use_strap_i2 else sheet_ca_i_i2_distance_angstrom()
    if hairpin_strap and compact_helix:
        hx = helix_sheet_hairpin_compact_distance_angstrom()
    elif hairpin_strap:
        hx = (
            helix_sheet_hairpin_compact_distance_angstrom()
            if max_helix_run_length(ss) <= 2
            else helix_sheet_hairpin_distance_angstrom()
        )
    else:
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

    _add_helix_sheet_contacts(
        pairs,
        ss,
        target=hx,
        hairpin_singleton=hairpin_strap and max_helix_run_length(ss) <= 2,
    )

    for i, aa in enumerate(sequence):
        if aa not in HYDROPHOBIC_RESIDUES:
            continue
        for j in range(i + 4, min(i + max(n // 2, 5), n)):
            if sequence[j] in HYDROPHOBIC_RESIDUES:
                if (ss[i] == "E" and ss[j] == "H") or (ss[i] == "H" and ss[j] == "E"):
                    continue
                _add_pair(pairs, i, j, hydro, "hydrophobic")

    if include_terminus and n >= 12:
        term = compact_terminus_ca_distance_angstrom(n, contact_angstrom=hydro)
        _add_pair(pairs, 0, n - 1, term, "terminus")

    return tuple(pairs.values())


def _helix_sheet_target_from_spine(
    coupling: SpineContactCoupling,
    seed: list,
    contact: TertiaryContact,
    ss: list[SecondaryStructure],
    *,
    include_terminus: bool,
) -> float:
    """Cross-register Cα target from bound-state rules + computed spine coupling."""
    if coupling.hairpin_helix_sheet_singleton and max_helix_run_length(ss) <= 2:
        return helix_sheet_hairpin_compact_distance_angstrom()
    if coupling.compact_helix_contacts and include_terminus:
        return helix_sheet_ca_packing_distance_angstrom()
    return math.dist(seed[contact.i], seed[contact.j])


SOLVENT_DRESSED_CONTACT_KINDS = frozenset(
    {"hydrophobic", "helix_sheet", "terminus", "helix_i3", "helix_i4", "sheet_i2"}
)


def dress_structure_contact_targets(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    contacts: tuple[TertiaryContact, ...],
    *,
    include_terminus: bool,
    temperature_k: float | None = PROTEIN_FOLDING_TEMPERATURE_K,
) -> tuple[TertiaryContact, ...]:
    """Assign structure Cα targets from bound-state geometry + aqueous outside dress."""
    from hqiv_lab.miniprotein_backbone import place_ca_trace
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine
    from hqiv_lab.miniprotein_register import register_contact_coupling_for_sequence
    from hqiv_lab.peptide_shell_dress import tertiary_contact_packing_scale
    from hqiv_lab.protein_solvent_phase import (
        aqueous_angle_pivot_dress_factor,
        aqueous_outside_geometry_scale,
        directional_local_network_rho,
        interface_exposure_from_contact_kind,
    )

    coupling = register_contact_coupling_for_sequence(sequence, ss_map)
    ss = ss_per_residue(sequence, ss_map)
    seed = place_ca_trace(sequence, dihedrals_from_spine(sequence, ss_map))
    pivot_dress: dict[str, float] = {}
    if temperature_k is not None:
        for exposure in ("hydrophobic", "hydrophilic", "neutral"):
            pivot_dress[exposure] = aqueous_angle_pivot_dress_factor(temperature_k, exposure)
    dressed: list[TertiaryContact] = []
    for contact in contacts:
        if contact.kind == "helix_i3":
            target = (
                helix_ca_i_i3_distorted_distance_angstrom()
                if coupling.compact_helix_contacts
                else helix_ca_i_i3_distance_angstrom()
            )
        elif contact.kind == "helix_i4":
            target = (
                helix_ca_i_i4_distorted_distance_angstrom()
                if coupling.compact_helix_contacts
                else helix_ca_i_i4_distance_angstrom()
            )
        elif contact.kind == "sheet_i2":
            target = (
                sheet_ca_i_i2_strap_distance_angstrom()
                if coupling.strap_sheet_i2_contacts
                else sheet_ca_i_i2_distance_angstrom()
            )
        elif contact.kind == "helix_sheet":
            target = _helix_sheet_target_from_spine(
                coupling, seed, contact, ss, include_terminus=include_terminus
            )
        else:
            target = contact.target_angstrom
        if temperature_k is not None and contact.kind in SOLVENT_DRESSED_CONTACT_KINDS:
            exposure = interface_exposure_from_contact_kind(contact.kind)
            target *= pivot_dress.get(exposure, 1.0)
        # Shell open-channel packing (aqueous phase_contact_weight from medium ρ).
        target *= tertiary_contact_packing_scale(
            contact.kind, aqueous=True, temperature_k=temperature_k
        )
        # Outside ledger: bulk(foldXi)×local×thermal — gas ρ=0 recovers identity.
        if temperature_k is not None:
            rho_local = directional_local_network_rho(seed, contact, ss)
            outside = aqueous_outside_geometry_scale(
                temperature_k=temperature_k,
                contact_kind=contact.kind,
                rho_local=rho_local,
            )
            target *= outside["scale"]
        dressed.append(TertiaryContact(contact.i, contact.j, target, contact.kind))
    return tuple(dressed)


def build_tertiary_contact_graph_for_spine(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    *,
    include_terminus: bool = True,
) -> tuple[TertiaryContact, ...]:
    """SS topology + spine-derived bound-state contact targets."""
    from hqiv_lab.miniprotein_register import register_contact_coupling_for_sequence

    coupling = register_contact_coupling_for_sequence(sequence, ss_map)
    topology = build_tertiary_contact_graph(
        sequence,
        ss_map,
        include_terminus=include_terminus,
        hairpin_strap=coupling.hairpin_helix_sheet_singleton,
        strap_sheet_i2=coupling.strap_sheet_i2_contacts,
        compact_helix=coupling.compact_helix_contacts,
    )
    return dress_structure_contact_targets(
        sequence, ss_map, topology, include_terminus=include_terminus
    )


def build_tertiary_contact_graph_for_register(
    sequence: str,
    ss_map: dict[SecondaryStructure, tuple[int, ...]],
    profile: str | None = None,
    *,
    include_terminus: bool = True,
) -> tuple[TertiaryContact, ...]:
    """Legacy name — ``profile`` ignored; uses spine readout."""
    _ = profile
    return build_tertiary_contact_graph_for_spine(sequence, ss_map, include_terminus=include_terminus)
