"""Miniprotein fold readout — secondary-structure dihedral spine + contact network."""

from __future__ import annotations

import math
from dataclasses import asdict, dataclass
from typing import Any

from hqiv_lab.miniprotein_backbone import (
    SecondaryStructure,
    Vec3,
    dihedrals_from_secondary_structure,
    dihedrals_from_secondary_structure_with_sheet_helix_turn,
    hqiv_peptide_bond_geometry,
    kabsch_rmsd,
    place_ca_trace,
    ramachandran_extended_rad,
)
from hqiv_lab.miniprotein_closure import apply_nerf_contact_refinement, apply_staged_nerf_contact_refinement
from hqiv_lab.miniprotein_contacts import (
    HYDROPHOBIC_RESIDUES,
    TertiaryContact,
    build_tertiary_contact_graph,
    build_tertiary_contact_graph_for_register,
    ss_per_residue,
)
from hqiv_lab.miniprotein_osh import apply_osh_contact_refinement, apply_staged_osh_contact_refinement
from hqiv_lab.miniprotein_basin import dihedrals_from_spine
from hqiv_lab.miniprotein_register import contact_flags_for_sequence

TRP_CAGE_SEQUENCE = "NLYIQWLKDGGPSSGRPPPS"
TRP_CAGE_STAGED_FINAL_ROUNDS = 20
TRP_CAGE_STAGED_TERMINUS_ROUNDS = 10
# Medium fragments (8–11 res) staged polish depth.
STAGED_MEDIUM_FINAL_ROUNDS = 16

# Competitive Cα RMSD gate for every fold length (AlphaFold-class bar).
# Pass requires strict RMSD < this threshold; length-dependent soft gates are retired.
COMPETITIVE_CA_RMSD_PASS_ANGSTROM = 2.0

# Ladder targets whose NeRF closure uses curvature-dressed tertiary weights.
CURVATURE_WEIGHTED_FOLD_TARGETS: tuple[str, ...] = (
    "trp_cage",
    "sheet_helix_10",
    "cage_core_14",
)


def fold_temperature_strategy_suffix(temperature_k: float) -> str:
    if abs(temperature_k - round(temperature_k)) < 1e-6:
        return f"+T{int(round(temperature_k))}K"
    return f"+T{temperature_k:.2f}K"

# Literature secondary-structure map for Trp-cage (1L2Y / TC5b).
TRP_CAGE_SECONDARY_STRUCTURE: dict[SecondaryStructure, tuple[int, ...]] = {
    "E": (2, 3, 4),
    "H": tuple(range(7, 18)),
    "C": (1, 5, 6, 18, 19, 20),
}

_TRP_CAGE_DIHEDRALS = dihedrals_from_spine(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
_TRP_CAGE_CONTACT_FLAGS = contact_flags_for_sequence(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
_TRP_CAGE_CONTACTS = build_tertiary_contact_graph_for_register(
    TRP_CAGE_SEQUENCE,
    TRP_CAGE_SECONDARY_STRUCTURE,
    include_terminus=True,
)
_BOND_GEOMETRY = hqiv_peptide_bond_geometry()
_BOND_GEOMETRY_DICT = {
    "N_CA": _BOND_GEOMETRY.n_ca,
    "CA_C": _BOND_GEOMETRY.ca_c,
    "C_N": _BOND_GEOMETRY.c_n,
    "C_O": _BOND_GEOMETRY.c_o,
}


def _bond_geometry_dict_for_sequence(sequence: str) -> dict[str, float]:
    """Full-bound dynamic bond geometry for ``sequence`` length."""
    from hqiv_lab.miniprotein_backbone import hqiv_peptide_bond_geometry_at_bound

    n = len(sequence)
    if n <= 0:
        return dict(_BOND_GEOMETRY_DICT)
    g = hqiv_peptide_bond_geometry_at_bound(n, n)
    return {"N_CA": g.n_ca, "CA_C": g.ca_c, "C_N": g.c_n, "C_O": g.c_o}


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
        passed = rmsd < pass_threshold_angstrom
    return MiniproteinFoldResult(
        name=name,
        sequence=sequence,
        n_residues=len(sequence),
        strategy=strategy,
        ca_trace=tuple(ca),
        bond_geometry=_bond_geometry_dict_for_sequence(sequence),
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
    dihedrals = dihedrals_from_secondary_structure(seq, {"C": (1, 2)})
    return fold_from_dihedrals(
        "GG",
        seq,
        dihedrals,
        strategy="extended_dipeptide",
        witness_ca=witness_ca,
        pass_threshold_angstrom=pass_a,
        include_network=include_network,
    )


def fold_trp_cage(
    *,
    witness_ca: list[Vec3] | None = None,
    pass_a: float = COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
    tertiary_closure: bool = True,
    include_network: bool = False,
    closure_engine: str = "nerf",
    temperature_k: float | None = None,
) -> MiniproteinFoldResult:
    """Trp-cage (TC5b): SS φ/ψ + sheet–helix turn + tertiary closure."""
    seq = TRP_CAGE_SEQUENCE
    dihedrals = _TRP_CAGE_DIHEDRALS
    contacts: tuple[TertiaryContact, ...] = _TRP_CAGE_CONTACTS
    ss = ss_per_residue(seq, TRP_CAGE_SECONDARY_STRUCTURE)
    strategy = "secondary_structure_spine+trp_cage_register"
    if tertiary_closure:
        from hqiv_lab.protein_solvent_phase import PROTEIN_FOLDING_TEMPERATURE_K

        fold_t_k = (
            temperature_k if temperature_k is not None else PROTEIN_FOLDING_TEMPERATURE_K
        )
        if closure_engine == "osh":
            ca, _ = apply_staged_osh_contact_refinement(
                seq,
                dihedrals,
                contacts,
                ss,
                terminus_rounds=TRP_CAGE_STAGED_TERMINUS_ROUNDS,
                final_rounds=TRP_CAGE_STAGED_FINAL_ROUNDS,
                strap_strand=_TRP_CAGE_CONTACT_FLAGS["strap_sheet_i2"],
                compact_helix=_TRP_CAGE_CONTACT_FLAGS["compact_helix"],
                macro_ricci_soft=True,
                atom_sites=True,
                temperature_k=fold_t_k,
            )
            strategy = (
                "secondary_structure_spine+trp_cage_register+osh_contact_refinement"
                "+macro_ricci_soft_closure+atom_sites"
            )
        else:
            ca, _ = apply_staged_nerf_contact_refinement(
                seq,
                dihedrals,
                contacts,
                terminus_rounds=TRP_CAGE_STAGED_TERMINUS_ROUNDS,
                final_rounds=TRP_CAGE_STAGED_FINAL_ROUNDS,
                ss=ss,
                curvature_weights=True,
                macro_ricci_soft=True,
                temperature_k=fold_t_k,
                atom_sites=True,
            )
            strategy = (
                "secondary_structure_spine+trp_cage_register+staged_nerf_contact_refinement"
                "+macro_ricci_soft_closure+atom_sites"
                + fold_temperature_strategy_suffix(fold_t_k)
            )
    else:
        ca = place_ca_trace(seq, dihedrals)
    rmsd = kabsch_rmsd(ca, witness_ca) if witness_ca else None
    passed = None
    if rmsd is not None and pass_a is not None:
        passed = rmsd < pass_a
    return MiniproteinFoldResult(
        name="trp_cage",
        sequence=seq,
        n_residues=len(seq),
        strategy=strategy,
        ca_trace=tuple(ca),
        bond_geometry=_bond_geometry_dict_for_sequence(seq),
        network_contacts=_resolve_network_contacts(
            seq, dihedrals, name="trp_cage", include_network=include_network
        ),
        tertiary_contacts=len(contacts),
        ca_rmsd_angstrom=rmsd,
        ca_rmsd_pass_angstrom=pass_a,
        passed=passed,
    )


@dataclass(frozen=True)
class MiniproteinFragmentSpec:
    """PDB fragment gate on the fold ladder (comparison witnesses only)."""

    name: str
    sequence: str
    ss_map: dict[SecondaryStructure, tuple[int, ...]]
    pass_a: float
    register_profile: str | None = None  # deprecated — ignored; spine readout only
    tertiary_closure: bool = False
    staged_closure: bool = False
    curvature_weights: bool = False
    sheet_helix_turn: bool = False
    strap_strand: bool = False
    pdb_residue_range: tuple[int, int] | None = None
    staged_final_rounds: int | None = None
    staged_terminus_rounds: int | None = None


# 1L2Y sub-traces — difficulty steps between GG and full Trp-cage.
FRAGMENT_FOLD_SPECS: tuple[MiniproteinFragmentSpec, ...] = (
    MiniproteinFragmentSpec(
        name="beta_strand_3",
        sequence="LYI",
        ss_map={"E": (1, 2, 3)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        strap_strand=True,
        pdb_residue_range=(2, 4),
    ),
    MiniproteinFragmentSpec(
        name="hairpin_turn_5",
        sequence="LYIQW",
        ss_map={"E": (1, 2, 3), "C": (4, 5)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        strap_strand=True,
        pdb_residue_range=(2, 6),
    ),
    MiniproteinFragmentSpec(
        name="alpha_helix_4",
        sequence="LKDG",
        ss_map={"H": (1, 2, 3, 4)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        pdb_residue_range=(7, 10),
    ),
    MiniproteinFragmentSpec(
        name="helix_6",
        sequence="LKDGGP",
        ss_map={"H": (1, 2, 3, 4, 5, 6)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        register_profile="trp_cage",
        pdb_residue_range=(7, 12),
    ),
    MiniproteinFragmentSpec(
        name="sheet_helix_6",
        sequence="LYIQWL",
        ss_map={"E": (1, 2, 3), "C": (4, 5), "H": (6,)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        register_profile="hairpin",
        tertiary_closure=True,
        pdb_residue_range=(2, 7),
    ),
    MiniproteinFragmentSpec(
        name="sheet_helix_8",
        sequence="LYIQWLKD",
        ss_map={"E": (1, 2, 3), "C": (4, 5), "H": (6, 7, 8)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        register_profile="hairpin",
        tertiary_closure=True,
        staged_closure=True,
        staged_final_rounds=STAGED_MEDIUM_FINAL_ROUNDS,
        pdb_residue_range=(2, 9),
    ),
    MiniproteinFragmentSpec(
        name="helix_8",
        sequence="LKDGGPSS",
        ss_map={"H": (1, 2, 3, 4, 5, 6, 7, 8)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        register_profile="compact",
        tertiary_closure=True,
        pdb_residue_range=(7, 14),
    ),
    MiniproteinFragmentSpec(
        name="sheet_helix_10",
        sequence="LYIQWLKDGGP",
        ss_map={"E": (1, 2, 3), "C": (4, 5), "H": (6, 7, 8, 9, 10, 11)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        register_profile="trp_cage",
        tertiary_closure=True,
        staged_closure=True,
        curvature_weights=True,
        staged_final_rounds=14,
        pdb_residue_range=(2, 12),
    ),
    MiniproteinFragmentSpec(
        name="cage_core_14",
        sequence="LYIQWLKDGGPSSG",
        ss_map={"E": (1, 2, 3), "C": (4, 5), "H": (6, 7, 8, 9, 10, 11, 12, 13, 14)},
        pass_a=COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        tertiary_closure=True,
        staged_closure=True,
        curvature_weights=True,
        staged_final_rounds=18,
        staged_terminus_rounds=TRP_CAGE_STAGED_TERMINUS_ROUNDS,
        pdb_residue_range=(2, 15),
    ),
)


def _dihedrals_for_fragment(spec: MiniproteinFragmentSpec) -> tuple[tuple[float, float], ...]:
    return dihedrals_from_spine(spec.sequence, spec.ss_map)


def fold_miniprotein_fragment(
    spec: MiniproteinFragmentSpec,
    *,
    witness_ca: list[Vec3] | None = None,
    pass_a: float | None = None,
    include_network: bool = False,
    closure_engine: str = "nerf",
    temperature_k: float | None = None,
) -> MiniproteinFoldResult:
    """Fold a PDB fragment target (SS spine ± tertiary closure)."""
    from hqiv_lab.miniprotein_contacts import build_tertiary_contact_graph_for_register

    dihedrals = _dihedrals_for_fragment(spec)
    ss = ss_per_residue(spec.sequence, spec.ss_map)
    hairpin_strap = contact_flags_for_sequence(spec.sequence, spec.ss_map).get("hairpin_strap", False)
    contacts: tuple[TertiaryContact, ...] = ()
    if spec.tertiary_closure:
        include_terminus = len(spec.sequence) >= 12 and spec.staged_closure
        contacts = build_tertiary_contact_graph_for_register(
            spec.sequence,
            spec.ss_map,
            include_terminus=include_terminus,
        )
    strategy = "secondary_structure_spine+spine_matrix_readout"
    if spec.tertiary_closure and contacts:
        staged_kw: dict[str, int | bool | list[str] | None] = {}
        if spec.staged_closure:
            n = len(spec.sequence)
            final_rounds = (
                spec.staged_final_rounds
                if spec.staged_final_rounds is not None
                else TRP_CAGE_STAGED_FINAL_ROUNDS
                if n >= 12
                else STAGED_MEDIUM_FINAL_ROUNDS
            )
            terminus_rounds = (
                spec.staged_terminus_rounds
                if spec.staged_terminus_rounds is not None
                else TRP_CAGE_STAGED_TERMINUS_ROUNDS
                if n >= 12
                else 0
            )
            staged_kw = {
                "terminus_rounds": terminus_rounds,
                "final_rounds": final_rounds,
                "ss": ss,
                "curvature_weights": spec.curvature_weights,
                "macro_ricci_soft": spec.tertiary_closure and spec.name != "cage_core_14",
            }
            from hqiv_lab.protein_solvent_phase import PROTEIN_FOLDING_TEMPERATURE_K

            fold_t_k = (
                temperature_k if temperature_k is not None else PROTEIN_FOLDING_TEMPERATURE_K
            )
            staged_kw["temperature_k"] = fold_t_k
            if spec.curvature_weights:
                staged_kw["atom_sites"] = len(spec.sequence) >= 8
        if closure_engine == "osh":
            flags = contact_flags_for_sequence(spec.sequence, spec.ss_map)
            if spec.staged_closure:
                ca, _ = apply_staged_osh_contact_refinement(
                    spec.sequence,
                    dihedrals,
                    contacts,
                    ss,
                    terminus_rounds=int(staged_kw.get("terminus_rounds") or 0),
                    final_rounds=int(staged_kw.get("final_rounds") or 10),
                    strap_strand=flags.get("strap_sheet_i2", hairpin_strap),
                    compact_helix=flags.get("compact_helix", False),
                    macro_ricci_soft=spec.name != "cage_core_14",
                    atom_sites=True,
                    temperature_k=staged_kw.get("temperature_k"),
                )
                strategy += "+staged_osh_contact_refinement"
            else:
                use_atom_sites = len(spec.sequence) >= 8
                ca, _ = apply_osh_contact_refinement(
                    spec.sequence,
                    dihedrals,
                    contacts,
                    ss,
                    strap_strand=hairpin_strap,
                    atom_sites=use_atom_sites,
                )
                strategy += "+osh_contact_refinement"
                if use_atom_sites:
                    strategy += "+atom_sites"
        elif spec.staged_closure:
            ca, _ = apply_staged_nerf_contact_refinement(
                spec.sequence,
                dihedrals,
                contacts,
                **staged_kw,
            )
            strategy += "+staged_nerf_contact_refinement"
            if staged_kw.get("macro_ricci_soft"):
                strategy += "+macro_ricci_soft_closure"
            if spec.curvature_weights:
                from hqiv_lab.protein_solvent_phase import PROTEIN_FOLDING_TEMPERATURE_K

                fold_t_k = (
                    temperature_k if temperature_k is not None else PROTEIN_FOLDING_TEMPERATURE_K
                )
                strategy += fold_temperature_strategy_suffix(fold_t_k)
        else:
            use_atom_sites = len(spec.sequence) >= 8
            ca, _ = apply_nerf_contact_refinement(
                spec.sequence,
                dihedrals,
                contacts,
                macro_ricci_soft=spec.name != "cage_core_14",
                atom_sites=use_atom_sites,
            )
            strategy += "+nerf_contact_refinement"
            if use_atom_sites:
                strategy += "+atom_sites"
            if spec.tertiary_closure and spec.name != "cage_core_14":
                strategy += "+macro_ricci_soft_closure"
    else:
        ca = place_ca_trace(spec.sequence, dihedrals)
    threshold = pass_a if pass_a is not None else spec.pass_a
    rmsd = kabsch_rmsd(ca, witness_ca) if witness_ca else None
    passed = None
    if rmsd is not None:
        passed = rmsd < threshold
    return MiniproteinFoldResult(
        name=spec.name,
        sequence=spec.sequence,
        n_residues=len(spec.sequence),
        strategy=strategy,
        ca_trace=tuple(ca),
        bond_geometry=_bond_geometry_dict_for_sequence(spec.sequence),
        network_contacts=_resolve_network_contacts(
            spec.sequence, dihedrals, name=spec.name, include_network=include_network
        ),
        tertiary_contacts=len(contacts),
        ca_rmsd_angstrom=rmsd,
        ca_rmsd_pass_angstrom=threshold,
        passed=passed,
    )


def fold_fragment_by_name(
    name: str,
    *,
    witness_ca: list[Vec3] | None = None,
    include_network: bool = False,
    closure_engine: str = "nerf",
    temperature_k: float | None = None,
) -> MiniproteinFoldResult:
    for spec in FRAGMENT_FOLD_SPECS:
        if spec.name == name:
            return fold_miniprotein_fragment(
                spec,
                witness_ca=witness_ca,
                include_network=include_network,
                closure_engine=closure_engine,
                temperature_k=temperature_k,
            )
    raise KeyError(f"unknown fragment fold target: {name}")


def run_ladder_with_engine(
    closure_engine: str,
    *,
    witnesses: dict[str, Any] | None = None,
    include_network: bool = False,
    temperature_k: float | None = None,
) -> dict[str, MiniproteinFoldResult]:
    """GG + fragments + Trp-cage using ``nerf`` or ``osh`` tertiary closure."""
    w = witnesses or {}
    out: dict[str, MiniproteinFoldResult] = {}

    def _witness(key: str) -> list[Vec3] | None:
        raw = w.get(key, {}).get("ca_angstrom")
        if raw is None:
            return None
        return [tuple(row) for row in raw]

    out["GG"] = fold_glycylglycine(witness_ca=_witness("GG"), include_network=include_network)
    out["trp_cage"] = fold_trp_cage(
        witness_ca=_witness("trp_cage"),
        closure_engine=closure_engine,
        include_network=include_network,
        temperature_k=temperature_k,
    )
    for spec in FRAGMENT_FOLD_SPECS:
        out[spec.name] = fold_miniprotein_fragment(
            spec,
            witness_ca=_witness(spec.name),
            include_network=include_network,
            closure_engine=closure_engine,
            temperature_k=temperature_k,
        )
    return out


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
