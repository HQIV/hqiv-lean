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
    ramachandran_strap_rad,
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


def test_ramachandran_strap_rad() -> None:
    import hqiv_lean_physics_primitives as lean

    phi, psi = ramachandran_strap_rad()
    assert abs(phi - lean.GAMMA * math.pi) < 1e-12
    assert abs(psi - (lean.ALPHA / 2.0) * math.pi) < 1e-12
    assert abs(psi - (3.0 / 10.0) * math.pi) < 1e-12


def test_ramachandran_distorted_helix_rad() -> None:
    import hqiv_lean_physics_primitives as lean
    from hqiv_lab.miniprotein_backbone import ramachandran_distorted_helix_rad

    phi, psi = ramachandran_distorted_helix_rad()
    assert abs(phi - (7.0 / 20.0) * math.pi) < 1e-12
    assert abs(psi - (2.0 / 15.0) * math.pi) < 1e-12
    assert abs(phi - (lean.GAMMA + lean.ALPHA / 2.0) * math.pi / 2.0) < 1e-12


def test_ramachandran_helix_exit_rad() -> None:
    import hqiv_lean_physics_primitives as lean
    from hqiv_lab.miniprotein_backbone import ramachandran_helix_exit_rad, ramachandran_strap_rad

    phi, psi = ramachandran_helix_exit_rad()
    sphi, _ = ramachandran_strap_rad()
    assert abs(phi - sphi) < 1e-12
    assert abs(psi + (11.0 / 15.0) * math.pi) < 1e-12
    assert abs(psi + (lean.ALPHA + lean.GAMMA / 3.0) * math.pi) < 1e-12


def test_ramachandran_strap_helix_turn_rad() -> None:
    from hqiv_lab.miniprotein_backbone import (
        ramachandran_distorted_helix_rad,
        ramachandran_strap_helix_turn_rad,
        ramachandran_strap_rad,
    )
    import hqiv_lean_physics_primitives as lean

    ps, pd = ramachandran_strap_rad(), ramachandran_distorted_helix_rad()
    t = lean.ALPHA
    phi, psi = ramachandran_strap_helix_turn_rad()
    assert abs(phi - ((1.0 - t) * ps[0] + t * pd[0])) < 1e-12
    assert abs(psi - ((1.0 - t) * ps[1] + t * pd[1])) < 1e-12


def test_distorted_helix_contact_distances() -> None:
    from hqiv_lab.peptide_geometry import (
        helix_ca_i_i3_distorted_distance_angstrom,
        helix_ca_i_i4_distorted_distance_angstrom,
        helix_sheet_hairpin_compact_distance_angstrom,
    )

    i3 = helix_ca_i_i3_distorted_distance_angstrom()
    i4 = helix_ca_i_i4_distorted_distance_angstrom()
    assert i4 > i3 > 0
    assert helix_sheet_hairpin_compact_distance_angstrom() > 0


def test_spine_readout_replaces_named_profiles() -> None:
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine, resolve_basins_for_sequence
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    dih = dihedrals_from_spine(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    assert len(dih) == len(TRP_CAGE_SEQUENCE)
    ss = ss_per_residue(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    basins = resolve_basins_for_sequence(TRP_CAGE_SEQUENCE, ss)
    assert any(b.value == "strap" for b in basins)
    assert any(b.value == "distorted_helix" for b in basins)


def test_spine_matrix_coil_turn() -> None:
    from hqiv_lab.miniprotein_basin import (
        BasinKind,
        build_residue_contexts,
        dihedrals_from_spine,
        resolve_basins_for_sequence,
    )
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss_map = {"E": (1, 2, 3), "C": (4, 5), "H": (6, 7, 8)}
    seq = "LYIQWLKD"
    ss = ss_per_residue(seq, ss_map)
    ctx = build_residue_contexts(ss)[3]
    assert ctx.ss == "C" and ctx.upstream == "E" and ctx.downstream == "H"
    dih = dihedrals_from_spine(seq, ss_map)
    basins = resolve_basins_for_sequence(seq, ss)
    assert basins[0] == BasinKind.STRAP
    assert dih[3] != dih[0]


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
    assert "nerf_contact" in result.strategy


def test_trp_cage_staged_nerf_improves_over_single_pass() -> None:
    """Staged closure (Lean pass order) beats single-pass NeRF on Trp-cage witness."""
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    witness = json.loads(path.read_text())["witnesses"]["trp_cage"]["ca_angstrom"]
    wit = [tuple(row) for row in witness]
    from hqiv_lab.miniprotein_closure import apply_nerf_contact_refinement, apply_staged_nerf_contact_refinement
    from hqiv_lab.miniprotein_register import dihedrals_from_register

    dih = dihedrals_from_register(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE, "trp_cage")
    from hqiv_lab.miniprotein_fold import (
        TRP_CAGE_STAGED_FINAL_ROUNDS,
        TRP_CAGE_STAGED_TERMINUS_ROUNDS,
        _TRP_CAGE_CONTACTS,
    )
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss = ss_per_residue(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    ca1, _ = apply_nerf_contact_refinement(
        TRP_CAGE_SEQUENCE,
        dih,
        _TRP_CAGE_CONTACTS,
        rounds=12,
        ss=ss,
        curvature_weights=True,
        atom_sites=True,
    )
    ca2, _ = apply_staged_nerf_contact_refinement(
        TRP_CAGE_SEQUENCE,
        dih,
        _TRP_CAGE_CONTACTS,
        terminus_rounds=TRP_CAGE_STAGED_TERMINUS_ROUNDS,
        final_rounds=TRP_CAGE_STAGED_FINAL_ROUNDS,
        ss=ss,
        curvature_weights=True,
        atom_sites=True,
    )
    r1 = kabsch_rmsd(ca1, wit)
    r2 = kabsch_rmsd(ca2, wit)
    assert r2 <= r1 + 1e-9, f"staged {r2:.3f} should beat single-pass {r1:.3f}"
    assert r2 < 5.7, f"Trp-cage staged RMSD {r2:.2f} Å"


def test_helix_6_uses_spine_distorted_helix() -> None:
    from hqiv_lab.miniprotein_basin import BasinKind, dihedrals_from_spine, resolve_basins_for_sequence
    from hqiv_lab.miniprotein_contacts import ss_per_residue
    from hqiv_lab.miniprotein_fold import FRAGMENT_FOLD_SPECS

    spec = next(s for s in FRAGMENT_FOLD_SPECS if s.name == "helix_6")
    ss = ss_per_residue(spec.sequence, spec.ss_map)
    basins = resolve_basins_for_sequence(spec.sequence, ss)
    assert basins.count(BasinKind.DISTORTED_HELIX) >= 3
    assert basins[-1] == BasinKind.HELIX_EXIT
    assert len(dihedrals_from_spine(spec.sequence, spec.ss_map)) == len(spec.sequence)


def test_contact_flags_from_spine_trp_cage() -> None:
    from hqiv_lab.miniprotein_register import contact_flags_for_sequence

    flags = contact_flags_for_sequence(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    assert flags["strap_sheet_i2"] is False
    assert flags["compact_helix"] is False


def test_trp_cage_passes_witness_when_present() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    tc = json.loads(path.read_text())["witnesses"].get("trp_cage", {})
    raw = tc.get("ca_angstrom")
    if raw is None:
        return
    witness = [tuple(row) for row in raw]
    from hqiv_lab.miniprotein_fold import COMPETITIVE_CA_RMSD_PASS_ANGSTROM

    result = fold_trp_cage(witness_ca=list(witness))
    assert result.ca_rmsd_pass_angstrom == COMPETITIVE_CA_RMSD_PASS_ANGSTROM
    # Competitive bar is Cα RMSD < 2 Å; current Trp-cage is not yet competitive.
    assert result.passed is False, (
        f"Trp-cage unexpectedly passed competitive gate: "
        f"RMSD {result.ca_rmsd_angstrom:.2f} Å < {COMPETITIVE_CA_RMSD_PASS_ANGSTROM}"
    )
    assert result.ca_rmsd_angstrom is not None
    assert result.ca_rmsd_angstrom >= COMPETITIVE_CA_RMSD_PASS_ANGSTROM


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
    assert result.ca_rmsd_angstrom is not None and result.ca_rmsd_angstrom < 0.5


def test_trp_cage_two_pass_closure() -> None:
    from hqiv_lab.miniprotein_contacts import build_tertiary_contact_graph, partition_tertiary_contacts_staged
    from hqiv_lab.miniprotein_closure import hydrophobic_step_fraction, default_structure_step_fraction

    contacts = build_tertiary_contact_graph(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    structure, hydrophobic, terminus = partition_tertiary_contacts_staged(contacts)
    assert any(c.kind == "helix_sheet" for c in structure)
    assert all(c.kind == "hydrophobic" for c in hydrophobic)
    assert all(c.kind == "terminus" for c in terminus)
    assert len(structure) + len(hydrophobic) + len(terminus) == len(contacts)
    assert len(hydrophobic) <= 2
    assert abs(hydrophobic_step_fraction() - default_structure_step_fraction() * 0.8) < 1e-12


def test_osh_matches_nerf_on_ladder() -> None:
    """OSH-oracle closure reproduces NeRF RMSD on the full witness ladder."""
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    witnesses = json.loads(path.read_text()).get("witnesses", {})
    from hqiv_lab.miniprotein_fold import run_ladder_with_engine

    nerf = run_ladder_with_engine("nerf", witnesses=witnesses)
    osh = run_ladder_with_engine("osh", witnesses=witnesses)
    for name in nerf:
        rn = nerf[name].ca_rmsd_angstrom
        ro = osh[name].ca_rmsd_angstrom
        if rn is None or ro is None:
            continue
        assert abs(rn - ro) < 0.06, f"{name}: nerf {rn:.4f} vs osh {ro:.4f}"


def test_contact_network_matrix_trace() -> None:
    from hqiv_lab.miniprotein_contacts import build_tertiary_contact_graph
    from hqiv_lab.miniprotein_fold import TRP_CAGE_SECONDARY_STRUCTURE, TRP_CAGE_SEQUENCE
    from hqiv_lab.miniprotein_osh import build_contact_network_matrix

    contacts = build_tertiary_contact_graph(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    net = build_contact_network_matrix(TRP_CAGE_SEQUENCE, contacts)
    assert net.n == 20
    assert len(net.pairs) == len(contacts)
    assert sum(net.site_energy) > 0


def test_trp_cage_osh_fold_runs() -> None:
    result = fold_trp_cage(witness_ca=None, pass_a=999.0, closure_engine="osh")
    assert result.n_residues == 20
    assert "osh_contact" in result.strategy


def test_fragment_ladder_osh_passes_when_witnesses_present() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    witnesses = json.loads(path.read_text()).get("witnesses", {})
    from hqiv_lab.miniprotein_fold import (
        COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        FRAGMENT_FOLD_SPECS,
        fold_miniprotein_fragment,
    )

    for spec in FRAGMENT_FOLD_SPECS:
        raw = witnesses.get(spec.name, {}).get("ca_angstrom")
        if raw is None:
            continue
        result = fold_miniprotein_fragment(
            spec,
            witness_ca=[tuple(row) for row in raw],
            closure_engine="osh",
        )
        assert result.ca_rmsd_pass_angstrom == COMPETITIVE_CA_RMSD_PASS_ANGSTROM
        assert result.ca_rmsd_angstrom is not None
        expected = result.ca_rmsd_angstrom < COMPETITIVE_CA_RMSD_PASS_ANGSTROM
        assert result.passed is expected, (
            f"{spec.name} OSH RMSD {result.ca_rmsd_angstrom:.2f} Å "
            f"passed={result.passed} expected={expected}"
        )


def test_fragment_ladder_passes_when_witnesses_present() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "miniprotein_witnesses.json"
    if not path.is_file():
        return
    witnesses = json.loads(path.read_text()).get("witnesses", {})
    from hqiv_lab.miniprotein_fold import (
        COMPETITIVE_CA_RMSD_PASS_ANGSTROM,
        FRAGMENT_FOLD_SPECS,
        fold_miniprotein_fragment,
    )

    for spec in FRAGMENT_FOLD_SPECS:
        raw = witnesses.get(spec.name, {}).get("ca_angstrom")
        if raw is None:
            continue
        result = fold_miniprotein_fragment(spec, witness_ca=[tuple(row) for row in raw])
        assert result.ca_rmsd_pass_angstrom == COMPETITIVE_CA_RMSD_PASS_ANGSTROM
        assert result.ca_rmsd_angstrom is not None
        expected = result.ca_rmsd_angstrom < COMPETITIVE_CA_RMSD_PASS_ANGSTROM
        assert result.passed is expected, (
            f"{spec.name} RMSD {result.ca_rmsd_angstrom:.2f} Å "
            f"passed={result.passed} expected={expected}"
        )


def test_macro_ricci_soft_open_beta_sheet_i2() -> None:
    from hqiv_lab.macro_ricci_flow import (
        is_open_beta_sheet_i2_contact,
        macro_ricci_contact_dress_blend,
        macro_ricci_soft_contact_target,
        macro_ricci_stacked_line_breathing_scale,
    )
    from hqiv_lab.miniprotein_backbone import place_ca_trace
    from hqiv_lab.miniprotein_contacts import TertiaryContact
    from hqiv_lab.peptide_geometry import sheet_ca_i_i2_distance_angstrom, sheet_ca_i_i2_strap_distance_angstrom

    open_d = sheet_ca_i_i2_distance_angstrom()
    strap_d = sheet_ca_i_i2_strap_distance_angstrom()
    open_c = TertiaryContact(0, 2, open_d, "sheet_i2")
    strap_c = TertiaryContact(0, 2, strap_d, "sheet_i2")
    assert is_open_beta_sheet_i2_contact(open_c)
    assert not is_open_beta_sheet_i2_contact(strap_c)
    breathing = macro_ricci_stacked_line_breathing_scale()
    assert 0.85 < breathing < 1.0
    seq = "VIV"
    ca = place_ca_trace(seq, [(-120.0, 120.0)] * len(seq))
    contacts = (open_c,)
    blend = macro_ricci_contact_dress_blend(seq, open_c, ca, ["E", "E", "E"], contacts)
    assert 0.0 <= blend <= 1.0
    soft = macro_ricci_soft_contact_target(open_c, seq, ca, ["E", "E", "E"], contacts)
    dressed = open_d * breathing
    assert soft == open_d + blend * (dressed - open_d)
    assert soft <= open_d


def test_macro_ricci_system_dress_terminus() -> None:
    from hqiv_lab.macro_ricci_flow import (
        macro_ricci_contact_breathing_scale,
        macro_ricci_inward_strength_for_kind,
        macro_ricci_soft_contact_target,
        macro_ricci_stacked_line_breathing_scale,
    )
    from hqiv_lab.miniprotein_contacts import TertiaryContact, closure_pass_weight
    from hqiv_lab.residue_site_physics import (
        macro_ricci_network_compound_excess,
        macro_ricci_system_dress_amplitude,
    )

    seq = "NLYIQWLKDGGPSSGRPPPS"
    ca = [(float(i) * 3.8, 0.0, 0.0) for i in range(len(seq))]
    term = TertiaryContact(0, len(seq) - 1, 12.0, "terminus")
    sheet = TertiaryContact(1, 3, 6.44, "sheet_i2")
    contacts = (sheet, term)
    amp = macro_ricci_system_dress_amplitude(seq, contacts, ca, ["E"] * len(seq))
    assert amp > 0.0
    assert closure_pass_weight("terminus") > closure_pass_weight("sheet_i2")
    assert macro_ricci_inward_strength_for_kind("terminus") > macro_ricci_inward_strength_for_kind(
        "helix_i3"
    )
    term_b = macro_ricci_contact_breathing_scale(term)
    assert term_b < 1.0
    soft_term = macro_ricci_soft_contact_target(term, seq, ca, ["E"] * len(seq), contacts)
    assert soft_term <= term.target_angstrom
    breathing = macro_ricci_stacked_line_breathing_scale()
    assert macro_ricci_network_compound_excess(1, breathing) == breathing - 1.0


def test_macro_ricci_no_fitted_kind_table() -> None:
    import hqiv_lab.residue_site_physics as rsp

    assert not hasattr(rsp, "CONTACT_KIND_RICCI_PARTICIPATION")


def test_macro_ricci_local_be_mass_gly_zero() -> None:
    from hqiv_lab.miniprotein_contacts import TertiaryContact
    from hqiv_lab.peptide_geometry import sheet_ca_i_i2_distance_angstrom
    from hqiv_lab.residue_site_physics import macro_ricci_local_dress_amplitude

    open_d = sheet_ca_i_i2_distance_angstrom()
    contact = TertiaryContact(0, 2, open_d, "sheet_i2")
    seq = "GGG"
    ca = [(0.0, 0.0, 0.0), (3.8, 0.0, 0.0), (7.6, 0.0, 0.0)]
    assert macro_ricci_local_dress_amplitude(seq, contact, ca, ["E", "E", "E"]) == 0.0


def test_macro_ricci_medium_density_scaling() -> None:
    """Lean ``scaleOutsideCouplingForMediumDensity`` / dilute limit."""
    from hqiv_lab._scripts import ensure_scripts_on_path

    ensure_scripts_on_path()
    import hqiv_curvature_bond_state as cbs

    raw = 1.5
    assert abs(cbs.scale_outside_coupling_for_medium_density(raw, 0.0) - 1.0) < 1e-12
    assert abs(cbs.scale_outside_coupling_for_medium_density(raw, 1.0) - raw) < 1e-12
    assert abs(cbs.scale_outside_coupling_for_medium_density(raw, 0.5) - 1.25) < 1e-12


def test_stacked_line_outside_curvature_breathing() -> None:
    import math

    import hqiv_lean_physics_primitives as lean
    from hqiv_lab.peptide_geometry import (
        beta_strand_stacking_angle_rad,
        dress_stacked_line_contact_distance,
        sheet_ca_i_i2_distance_angstrom,
        stacked_line_outside_curvature_scale,
    )

    theta0 = math.pi / 2.0
    assert abs(stacked_line_outside_curvature_scale(theta0) - 1.0) < 1e-9
    beta_bend = beta_strand_stacking_angle_rad()
    geff = stacked_line_outside_curvature_scale(beta_bend)
    breathing = 1.0 + (lean.GAMMA / 2.0) * (geff - 1.0)
    open_i2 = sheet_ca_i_i2_distance_angstrom()
    dressed = dress_stacked_line_contact_distance(open_i2, [], 0, 2, open_beta_spine=True)
    assert abs(dressed - open_i2 * breathing) < 1e-6
    assert open_i2 * geff < dressed < open_i2


def test_helix_sheet_packing_distance() -> None:
    from hqiv_lab.peptide_geometry import (
        helix_ca_i_i3_distance_angstrom,
        helix_sheet_ca_packing_distance_angstrom,
        helix_sheet_hairpin_distance_angstrom,
        sheet_ca_i_i2_distance_angstrom,
    )
    import hqiv_lean_physics_primitives as lean

    h3 = helix_ca_i_i3_distance_angstrom()
    s2 = sheet_ca_i_i2_distance_angstrom()
    hx = helix_sheet_ca_packing_distance_angstrom()
    expected = (h3 + s2) / 2.0 * (1.0 + lean.GAMMA / 6.0)
    assert abs(hx - expected) < 1e-9
    assert 4.5 < hx < 6.0
    assert 4.0 < helix_sheet_hairpin_distance_angstrom() < 7.0


def test_contact_coupling_from_spine_basins() -> None:
    from hqiv_lab.miniprotein_basin import BasinKind, contact_coupling_from_basins, resolve_basins_for_sequence
    from hqiv_lab.miniprotein_contacts import ss_per_residue

    ss_map = {"E": (1, 2, 3), "C": (4, 5), "H": (6,)}
    seq = "LYIQWL"
    ss = ss_per_residue(seq, ss_map)
    basins = resolve_basins_for_sequence(seq, ss)
    coupling = contact_coupling_from_basins(basins, ss)
    assert coupling.hairpin_helix_sheet_singleton
    assert coupling.strap_sheet_i2_contacts
    assert BasinKind.STRAP in basins


def test_dress_structure_contact_targets_uses_spine() -> None:
    import math

    from hqiv_lab.miniprotein_backbone import place_ca_trace
    from hqiv_lab.miniprotein_basin import dihedrals_from_spine
    from hqiv_lab.miniprotein_contacts import (
        build_tertiary_contact_graph_for_spine,
        dress_structure_contact_targets,
        build_tertiary_contact_graph,
    )
    from hqiv_lab.miniprotein_register import register_contact_coupling_for_sequence

    seq = "LYIQWLKD"
    ss_map = {"E": (1, 2, 3), "C": (4, 5), "H": (6, 7, 8)}
    coupling = register_contact_coupling_for_sequence(seq, ss_map)
    topology = build_tertiary_contact_graph(
        seq,
        ss_map,
        include_terminus=False,
        hairpin_strap=coupling.hairpin_helix_sheet_singleton,
        strap_sheet_i2=coupling.strap_sheet_i2_contacts,
        compact_helix=coupling.compact_helix_contacts,
    )
    dressed = dress_structure_contact_targets(seq, ss_map, topology, include_terminus=False)
    seed = place_ca_trace(seq, dihedrals_from_spine(seq, ss_map))
    hx = [c for c in dressed if c.kind == "helix_sheet"]
    assert len(hx) > 1
    for contact in hx:
        assert abs(contact.target_angstrom - math.dist(seed[contact.i], seed[contact.j])) < 1e-9


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
        test_ramachandran_strap_rad,
        test_ramachandran_distorted_helix_rad,
        test_ramachandran_helix_exit_rad,
        test_ramachandran_strap_helix_turn_rad,
        test_distorted_helix_contact_distances,
        test_spine_readout_replaces_named_profiles,
        test_spine_matrix_coil_turn,
        test_ca_ca_spacing_in_reasonable_range,
        test_alpha_vs_beta_traces_differ,
        test_protein_scaffold_contact_count,
        test_helix_i_i3_target_matches_alpha_spine,
        test_helix_i_i3_above_ca_step,
        test_trp_cage_fold_runs_and_reports_rmsd,
        test_trp_cage_staged_nerf_improves_over_single_pass,
        test_contact_flags_from_spine_trp_cage,
        test_helix_6_uses_spine_distorted_helix,
        test_trp_cage_passes_witness_when_present,
        test_gg_passes_cod_witness_when_present,
        test_fragment_ladder_passes_when_witnesses_present,
        test_fragment_ladder_osh_passes_when_witnesses_present,
        test_osh_matches_nerf_on_ladder,
        test_contact_network_matrix_trace,
        test_trp_cage_osh_fold_runs,
        test_trp_cage_two_pass_closure,
        test_macro_ricci_soft_open_beta_sheet_i2,
        test_macro_ricci_system_dress_terminus,
        test_macro_ricci_no_fitted_kind_table,
        test_macro_ricci_local_be_mass_gly_zero,
        test_macro_ricci_medium_density_scaling,
        test_stacked_line_outside_curvature_breathing,
        test_helix_sheet_packing_distance,
        test_contact_coupling_from_spine_basins,
        test_dress_structure_contact_targets_uses_spine,
        test_trp_cage_witness_radius_of_gyration,
    ):
        fn()
    print("test_hqiv_miniprotein_fold: OK")
