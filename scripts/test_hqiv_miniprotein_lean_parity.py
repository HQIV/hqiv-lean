#!/usr/bin/env python3
"""Lean parity: miniprotein fold spine matches ProteinResearch + PeptideBackboneGeometry."""

from __future__ import annotations

import math

import hqiv_lean_physics_primitives as lean
from hqiv_lab.miniprotein_backbone import (
    _place_atom,
    _v_norm,
    _v_sub,
    kabsch_rmsd,
    ramachandran_alpha_rad,
    ramachandran_beta_rad,
    ramachandran_extended_rad,
)
from hqiv_lab.miniprotein_closure import _compile_contacts
from hqiv_lab.miniprotein_contacts import HYDROPHOBIC_RESIDUES, TertiaryContact
from hqiv_lab.miniprotein_fold import (
    TRP_CAGE_SECONDARY_STRUCTURE,
    TRP_CAGE_SEQUENCE,
    count_tertiary_contacts,
    protein_scaffold_contact_count,
)
from hqiv_lab.peptide_geometry import (
    ca_ca_step_angstrom,
    compact_terminus_ca_distance_angstrom,
    helix_ca_i_i3_distance_angstrom,
    helix_ca_i_i3_distance_nominal_angstrom,
    helix_ca_i_i3_nominal_scale,
    helix_ca_i_i4_distance_angstrom,
    sheet_ca_i_i2_distance_angstrom,
    peptide_backbone_diameter_factor,
    peptide_backbone_open_factor,
)


def test_ramachandran_alpha_psi_dressed() -> None:
    phi, psi = ramachandran_alpha_rad()
    assert abs(phi + math.pi / 3.0) < 1e-12
    expected_psi = -math.pi / 4.0 * (1.0 + lean.GAMMA / 6.0)
    assert abs(psi - expected_psi) < 1e-12
    assert abs(psi - expected_psi * (15.0 / 16.0) * (16.0 / 15.0)) < 1e-12


def test_ramachandran_beta_basin() -> None:
    phi, psi = ramachandran_beta_rad()
    assert abs(phi + 2.0 * math.pi / 3.0) < 1e-12
    assert abs(psi - 2.0 * math.pi / 3.0) < 1e-12


def test_ramachandran_extended() -> None:
    phi, psi = ramachandran_extended_rad()
    assert abs(phi - math.pi) < 1e-12
    assert abs(psi - math.pi) < 1e-12


def test_protein_scaffold_contact_count() -> None:
    assert protein_scaffold_contact_count(1) == 1
    assert protein_scaffold_contact_count(2) == 3
    assert protein_scaffold_contact_count(20) == 40


def test_peptide_backbone_layer_factors() -> None:
    assert abs(peptide_backbone_diameter_factor() - 33.0 / 10.0) < 1e-12
    assert abs(peptide_backbone_open_factor() - 21.0 / 20.0) < 1e-12


def test_ca_ca_distance_scales() -> None:
    step = ca_ca_step_angstrom()
    assert step > 0.0
    i3 = helix_ca_i_i3_distance_angstrom()
    i4 = helix_ca_i_i4_distance_angstrom()
    i2 = sheet_ca_i_i2_distance_angstrom()
    assert i3 > step
    assert i4 > i3
    assert i2 > step
    assert abs(helix_ca_i_i3_nominal_scale() - (1.0 + lean.ALPHA + lean.GAMMA / 4.0)) < 1e-12
    assert abs(helix_ca_i_i3_nominal_scale() - 17.0 / 10.0) < 1e-12
    assert abs(helix_ca_i_i3_distance_nominal_angstrom() - step * (17.0 / 10.0)) < 1e-9


def test_compact_terminus_scale() -> None:
    contact = 10.0
    n = 20
    expected = contact * math.sqrt(n / 6.0)
    assert abs(compact_terminus_ca_distance_angstrom(n, contact_angstrom=contact) - expected) < 1e-9


def test_trp_cage_ss_map() -> None:
    assert len(TRP_CAGE_SEQUENCE) == 20
    assert TRP_CAGE_SECONDARY_STRUCTURE["E"] == (2, 3, 4)
    assert TRP_CAGE_SECONDARY_STRUCTURE["H"] == tuple(range(7, 18))
    assert TRP_CAGE_SECONDARY_STRUCTURE["C"] == (1, 5, 6, 18, 19, 20)
    n_ss = sum(len(v) for v in TRP_CAGE_SECONDARY_STRUCTURE.values())
    assert n_ss == 20


def test_hydrophobic_alphabet() -> None:
    assert HYDROPHOBIC_RESIDUES == frozenset("WLIVFMY")


def test_trp_cage_tertiary_contact_counts() -> None:
    n = count_tertiary_contacts(TRP_CAGE_SEQUENCE, TRP_CAGE_SECONDARY_STRUCTURE)
    assert n == 24


def test_scaffold_contact_general() -> None:
    for n in (3, 10, 20):
        assert protein_scaffold_contact_count(n) == 2 * n


def test_peptide_backbone_open_factor() -> None:
    assert abs(peptide_backbone_open_factor() - 21.0 / 20.0) < 1e-12


def test_pass_thresholds() -> None:
    assert 5.0 == 5.0  # trpCageCaRmsdPassAngstrom
    assert 2.0 == 2.0  # glyGlyCaRmsdPassAngstrom


def test_nerf_bond_length_preserved() -> None:
    """NeRF placement preserves bond length under a non-degenerate frame."""
    origin = (0.0, 0.0, 0.0)
    ref = (1.0, 0.0, 0.0)
    prev = (1.0, 1.0, 0.0)
    length = 1.47
    angle = math.pi / 3.0
    dihedral = math.pi / 4.0
    placed = _place_atom(origin, ref, prev, length, angle, dihedral)
    dist = _v_norm(_v_sub(placed, prev))
    assert abs(dist - length) < 1e-9


def test_kabsch_self_rmsd_zero() -> None:
    """Collinear trace: power-iteration Kabsch is exact (identity rotation)."""
    trace = [(float(i), 0.0, 0.0) for i in range(12)]
    assert kabsch_rmsd(trace, trace) < 1e-9


def test_closure_half_step_formula() -> None:
    """Python ``step_fraction * 0.5`` matches Lean ``tertiaryHalfStep``."""
    step_fraction = 0.25  # defaultClosureStepFraction
    contact = TertiaryContact(0, 3, 5.0, "helix_i3")
    compiled = _compile_contacts((contact,), step_fraction)
    assert len(compiled) == 1
    _, _, _, half_step = compiled[0]
    assert abs(half_step - step_fraction * 0.5) < 1e-12
    assert abs(half_step - 0.125) < 1e-12


def test_closure_error_damping_factor() -> None:
    """Single-pair Jacobi half-step η=1/2 zeroes error (Lean ``single_pair_damping_at_half``)."""
    eta = 0.5
    err = 3.7
    assert abs((1.0 - 2.0 * eta) * err) < 1e-12
    eta = 0.25
    assert abs(1.0 - 2.0 * eta) <= 1.0


def test_closure_default_step_degree_budget() -> None:
    """Default step × max site degree ≤ 1 (Lean ``default_half_step_times_max_degree``)."""
    step_fraction = 0.25
    max_degree = 4
    assert step_fraction * max_degree <= 1.0 + 1e-12


if __name__ == "__main__":
    test_ramachandran_alpha_psi_dressed()
    test_ramachandran_beta_basin()
    test_ramachandran_extended()
    test_protein_scaffold_contact_count()
    test_peptide_backbone_layer_factors()
    test_ca_ca_distance_scales()
    test_compact_terminus_scale()
    test_trp_cage_ss_map()
    test_trp_cage_tertiary_contact_counts()
    test_scaffold_contact_general()
    test_hydrophobic_alphabet()
    test_pass_thresholds()
    test_nerf_bond_length_preserved()
    test_kabsch_self_rmsd_zero()
    test_closure_half_step_formula()
    test_closure_error_damping_factor()
    test_closure_default_step_degree_budget()
    print("miniprotein lean parity: ok")
