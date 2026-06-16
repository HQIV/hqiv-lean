#!/usr/bin/env python3
"""Witness tests for nested-WF bond geometry (no diamond-node Θ)."""

from __future__ import annotations

import math

import hqiv_chemistry_tuft_dynamics as ctd


def test_h2_bond_length_matches_experiment() -> None:
    r = ctd.bond_equilibrium_from_atomic_numbers(1, 1)
    assert abs(r - 0.741) < 0.02


def test_oh_bond_length_within_few_percent() -> None:
    r = ctd.bond_equilibrium_from_atomic_numbers(8, 1)
    assert abs(r - 0.957) / 0.957 < 0.05


def test_carbonyl_bond_length() -> None:
    from hqiv_lab.derived_bond_geometry import bond_length_angstrom

    r = bond_length_angstrom("C", "O", coord_i=4, coord_j=1)
    assert 1.0 < r < 2.0


def test_hcl_period3_hydride_elongation() -> None:
    r = ctd.bond_equilibrium_from_atomic_numbers(17, 1)
    assert 1.15 < r < 1.35


def test_homonuclear_diatomic_lengths() -> None:
    import hqiv_nested_wf_bond_geometry as nwbg

    for name, ref in (("N2", 1.098), ("O2", 1.208)):
        bonds = nwbg.bonds_for_molecule_name(name)
        assert abs(bonds[0].distance_angstrom - ref) / ref < 0.05


def test_h2o_angle_not_tabulated() -> None:
    import hqiv_nested_wf_bond_geometry as nwbg

    bonds = nwbg.bonds_for_molecule_name("H2O")
    assert bonds[0].bond_angle_rad is not None
    assert abs(math.degrees(bonds[0].bond_angle_rad) - 104.5) > 0.5


def test_molecule_topology_count() -> None:
    import hqiv_nested_wf_bond_geometry as nwbg

    assert len(nwbg._BENCHMARK_TOPOLOGY) >= 18


def test_covalent_radius_is_rm_over_z() -> None:
    r = ctd.nested_wf_covalent_radius_bohr(4, 8)
    assert abs(r - 5.0 / 8.0) < 1e-9


def test_monogamy_factor_is_one_minus_alpha_half() -> None:
    assert abs(ctd.INFORMATIONAL_MONOGAMY_LENGTH_FACTOR - 0.7) < 1e-12


if __name__ == "__main__":
    test_h2_bond_length_matches_experiment()
    test_oh_bond_length_within_few_percent()
    test_carbonyl_bond_length()
    test_hcl_period3_hydride_elongation()
    test_homonuclear_diatomic_lengths()
    test_h2o_angle_not_tabulated()
    test_molecule_topology_count()
    test_covalent_radius_is_rm_over_z()
    test_monogamy_factor_is_one_minus_alpha_half()
    print("test_hqiv_nested_wf_bond_geometry: OK")
