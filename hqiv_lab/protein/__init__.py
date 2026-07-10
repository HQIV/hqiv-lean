"""
HQIV protein folding readout package — miniprotein spine on derived geometry.

All bond lengths, Ramachandran basins, and tertiary contact targets flow from
``hqiv_spine_chemistry`` + TUFT dynamics (no PDB inputs to the fold).

Comparison: PDB/COD Cα witnesses grade predictions only (see ``data/miniprotein_witnesses.json``).
"""

from __future__ import annotations

from hqiv_lab.miniprotein_fold import (
    MiniproteinFoldResult,
    FRAGMENT_FOLD_SPECS,
    MiniproteinFragmentSpec,
    TRP_CAGE_SECONDARY_STRUCTURE,
    TRP_CAGE_SEQUENCE,
    fold_extended_control,
    fold_fragment_by_name,
    fold_from_dihedrals,
    fold_glycylglycine,
    fold_miniprotein_fragment,
    fold_trp_cage,
    hydrophobic_contact_pairs,
    protein_scaffold_contact_count,
    radius_of_gyration,
    run_ladder_with_engine,
)
from hqiv_lab.miniprotein_osh import (
    apply_osh_contact_refinement,
    build_contact_network_matrix,
    osh_refinement_manifest,
)
from hqiv_lab.miniprotein_backbone import (
    SecondaryStructure,
    hqiv_peptide_bond_geometry,
    ramachandran_alpha_rad,
    ramachandran_beta_rad,
)


def spine_chemistry_manifest() -> dict[str, object]:
    """Re-export spine constants used by the protein pipeline."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_spine_chemistry as sc

    return sc.spine_manifest()


def peptide_shell_dress_manifest() -> dict[str, object]:
    """Shell-equation dress on peptide bonds / tertiary registers / H-bond pivots."""
    from hqiv_lab.peptide_shell_dress import peptide_shell_dress_manifest as _manifest

    return _manifest()


def run_baseline_folds(*, include_network: bool = False) -> dict[str, MiniproteinFoldResult]:
    """GG + fragment ladder + Trp-cage default path (no witness alignment)."""
    out: dict[str, MiniproteinFoldResult] = {
        "GG": fold_glycylglycine(include_network=include_network),
        "trp_cage": fold_trp_cage(include_network=include_network),
    }
    for spec in FRAGMENT_FOLD_SPECS:
        out[spec.name] = fold_miniprotein_fragment(spec, include_network=include_network)
    return out


def run_baseline_folds_osh(*, include_network: bool = False) -> dict[str, MiniproteinFoldResult]:
    """Same ladder with OSH-oracle tertiary closure."""
    return run_ladder_with_engine("osh", include_network=include_network)


__all__ = [
    "MiniproteinFoldResult",
    "MiniproteinFragmentSpec",
    "FRAGMENT_FOLD_SPECS",
    "SecondaryStructure",
    "TRP_CAGE_SEQUENCE",
    "TRP_CAGE_SECONDARY_STRUCTURE",
    "fold_extended_control",
    "fold_fragment_by_name",
    "fold_from_dihedrals",
    "fold_glycylglycine",
    "fold_miniprotein_fragment",
    "fold_trp_cage",
    "hqiv_peptide_bond_geometry",
    "hydrophobic_contact_pairs",
    "protein_scaffold_contact_count",
    "radius_of_gyration",
    "ramachandran_alpha_rad",
    "ramachandran_beta_rad",
    "run_baseline_folds",
    "run_baseline_folds_osh",
    "run_ladder_with_engine",
    "apply_osh_contact_refinement",
    "build_contact_network_matrix",
    "osh_refinement_manifest",
    "spine_chemistry_manifest",
    "peptide_shell_dress_manifest",
]
