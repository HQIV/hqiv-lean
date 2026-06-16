#!/usr/bin/env python3
"""Miniprotein backbone + fold pipeline gates."""

from __future__ import annotations

import json
import math
from pathlib import Path

from hqiv_lab.miniprotein_backbone import (
    hqiv_peptide_bond_geometry,
    kabsch_rmsd,
    place_ca_trace,
    ramachandran_alpha_rad,
    ramachandran_beta_rad,
)
from hqiv_lab.miniprotein_fold import (
    TRP_CAGE_SECONDARY_STRUCTURE,
    TRP_CAGE_SEQUENCE,
    fold_glycylglycine,
    fold_trp_cage,
    radius_of_gyration,
)
from hqiv_lab.peptide_geometry import ca_ca_step_angstrom, helix_ca_i_i3_distance_angstrom


def test_peptide_bond_lengths_positive() -> None:
    bg = hqiv_peptide_bond_geometry()
    assert bg.n_ca > 1.0
    assert bg.ca_c > 1.0
    assert bg.c_n > 1.0


def test_ca_ca_spacing_in_reasonable_range() -> None:
    ca = place_ca_trace("GG", (ramachandran_beta_rad(), ramachandran_beta_rad()))
    d = math.sqrt(sum((ca[0][i] - ca[1][i]) ** 2 for i in range(3)))
    assert 2.8 < d < 4.5, f"CA-CA spacing {d:.3f} Å out of peptide range"


def test_alpha_vs_beta_traces_differ() -> None:
    ca_a = place_ca_trace("AAAA", (ramachandran_alpha_rad(),) * 4)
    ca_b = place_ca_trace("AAAA", (ramachandran_beta_rad(),) * 4)
    rmsd = kabsch_rmsd(ca_a, ca_b)
    assert rmsd > 0.5, f"alpha/beta traces too similar RMSD={rmsd:.3f}"


def test_protein_scaffold_contact_count() -> None:
    from hqiv_lab.miniprotein_fold import protein_scaffold_contact_count

    assert protein_scaffold_contact_count(20) == 40
    assert protein_scaffold_contact_count(2) == 3


def test_helix_i_i3_target_matches_alpha_spine() -> None:
    from hqiv_lab.miniprotein_backbone import place_ca_trace, ramachandran_alpha_rad

    ca = place_ca_trace("AAAA", (ramachandran_alpha_rad(),) * 4)
    dx = ca[0][0] - ca[3][0]
    dy = ca[0][1] - ca[3][1]
    dz = ca[0][2] - ca[3][2]
    measured = (dx * dx + dy * dy + dz * dz) ** 0.5
    assert abs(helix_ca_i_i3_distance_angstrom() - measured) < 1e-9


def test_helix_i_i3_above_ca_step() -> None:
    assert helix_ca_i_i3_distance_angstrom() > ca_ca_step_angstrom()


def test_trp_cage_fold_runs_and_reports_rmsd() -> None:
    result = fold_trp_cage(witness_ca=None, pass_a=999.0)
    assert result.n_residues == 20
    assert result.network_contacts == 40
    assert result.tertiary_contacts >= 20
    assert result.ca_rmsd_angstrom is None
    assert len(result.ca_trace) == 20
    assert "staged" in result.strategy


def test_gg_passes_cod_witness_when_present() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    gg = json.loads(path.read_text())["witnesses"].get("GG", {})
    ca_raw = gg.get("ca_angstrom")
    if ca_raw is None:
        return
    witness = [tuple(row) for row in ca_raw]
    result = fold_glycylglycine(witness_ca=list(witness), pass_a=2.0)
    assert result.passed is True, f"GG RMSD {result.ca_rmsd_angstrom:.2f} Å"


def test_trp_cage_two_pass_closure() -> None:
    from hqiv_lab.miniprotein_contacts import build_tertiary_contact_graph, partition_tertiary_contacts_staged
    from hqiv_lab.miniprotein_closure import hydrophobic_step_fraction, default_structure_step_fraction

    contacts = build_tertiary_contact_graph(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    assert any(c.kind == "helix_sheet" for c in structure)
    assert all(c.kind == "hydrophobic" for c in hydrophobic)
    assert all(c.kind == "terminus" for c in terminus)
    assert len(structure) + len(hydrophobic) + len(terminus) == len(contacts)
    assert abs(hydrophobic_step_fraction() - default_structure_step_fraction() * 0.8) < 1e-12


def test_helix_sheet_packing_distance() -> None:
    from hqiv_lab.peptide_geometry import (
        helix_ca_i_i3_distance_angstrom,
        helix_sheet_ca_packing_distance_angstrom,
        sheet_ca_i_i2_distance_angstrom,
    )
    import hqiv_lean_physics_primitives as lean

    h3 = helix_ca_i_i3_distance_angstrom()
    s2 = sheet_ca_i_i2_distance_angstrom()
    hx = helix_sheet_ca_packing_distance_angstrom()
    expected = (h3 + s2) / 2.0 * (1.0 + lean.GAMMA / 6.0)
    assert abs(hx - expected) < 1e-9
    assert 4.5 < hx < 6.0


def test_trp_cage_witness_radius_of_gyration() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    w = json.loads(path.read_text())["witnesses"]["trp_cage"]["ca_angstrom"]
    rg = radius_of_gyration([tuple(row) for row in w])
    assert 4.0 < rg < 8.0, f"Trp-cage witness Rg={rg:.2f} Å unexpected"


if __name__ == "__main__":
    for fn in (
        test_peptide_bond_lengths_positive,
        test_ca_ca_spacing_in_reasonable_range,
        test_alpha_vs_beta_traces_differ,
        test_protein_scaffold_contact_count,
        test_helix_i_i3_target_matches_alpha_spine,
        test_helix_i_i3_above_ca_step,
        test_trp_cage_fold_runs_and_reports_rmsd,
        test_gg_passes_cod_witness_when_present,
        test_trp_cage_two_pass_closure,
        test_helix_sheet_packing_distance,
        test_trp_cage_witness_radius_of_gyration,
    ):
        fn()
    print("test_hqiv_miniprotein_fold: OK")
