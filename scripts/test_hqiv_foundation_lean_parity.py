#!/usr/bin/env python3
"""Lean parity: foundation melt ratios match PhaseAllotropeDerivation."""

from __future__ import annotations

import hqiv_lean_physics_primitives as lean
import hqiv_phase_geometry_density as pgd
from hqiv_lab.coordination import IntermolecularMotif, MonomerGeometry
from hqiv_lab.packing import molecular_melt_density_ratio


def test_polyol_melt_eq_tetrahedral_spine() -> None:
    mono = MonomerGeometry(
        z_heavy=8,
        n_bonds_at_heavy=2,
        mean_bond_length_angstrom=1.0,
        bond_angle_rad=1.0,
        lone_pair_count=1,
        h_count=4,
        motif=IntermolecularMotif.POLYOL_HBOND,
        intermolecular_contacts=6,
    )
    ratio, solid = molecular_melt_density_ratio(mono)
    expected = pgd.tetrahedral_melt_density_ratio(6)
    assert abs(ratio - expected) < 1e-12
    assert solid is True


def test_peptide_layer_melt_open_cell() -> None:
    mono = MonomerGeometry(
        z_heavy=7,
        n_bonds_at_heavy=2,
        mean_bond_length_angstrom=1.0,
        bond_angle_rad=1.0,
        lone_pair_count=1,
        h_count=4,
        motif=IntermolecularMotif.PEPTIDE_LAYER,
        intermolecular_contacts=4,
    )
    ratio, solid = molecular_melt_density_ratio(mono)
    open_cell = 1.0 + lean.GAMMA / 8.0
    assert abs(ratio - 1.0 / open_cell) < 1e-12
    assert solid is True


def test_tetrahedral_melt_h2o_contact() -> None:
    r4 = pgd.tetrahedral_melt_density_ratio(4)
    assert 0.75 < r4 < 0.85


def test_pyranose_chair_contact_factors() -> None:
    from hqiv_lab.pyranose_geometry import (
        pyranose_chair_diameter_factor,
        pyranose_chair_open_factor,
        pyranose_exocyclic_oh_dress_factor,
        pyranose_molecules_per_cell,
    )

    assert abs(pyranose_chair_diameter_factor() - 17.0 / 5.0) < 1e-12
    assert abs(pyranose_chair_open_factor() - 11.0 / 10.0) < 1e-12
    assert abs(pyranose_exocyclic_oh_dress_factor(6) - (1.5**0.5)) < 1e-12
    assert pyranose_molecules_per_cell() == 4


def test_polyol_liquid_local_field_divisor() -> None:
    import hqiv_phase_material_response as pmr

    div = pmr.clausius_mossotti_local_field_divisor("C3H8O3", "liquid")
    n_dom = pmr.coordination_domain_count("C3H8O3")
    eta = pmr.optical_phase_eta("C3H8O3")
    base = max(1.0 - lean.C_RINDLER_SHARED * eta, 1e-6)
    expected = base * n_dom * n_dom * (1.0 + lean.GAMMA) / (1.0 + lean.GAMMA / 4.0)
    assert abs(div - expected) < 1e-9


def test_monomer_alcohol_liquid_local_field_divisor() -> None:
    import hqiv_phase_material_response as pmr

    div = pmr.clausius_mossotti_local_field_divisor("CH3OH", "liquid")
    n_dom = pmr.coordination_domain_count("CH3OH")
    eta = pmr.optical_phase_eta("CH3OH")
    base = max(1.0 - lean.C_RINDLER_SHARED * eta, 1e-6)
    expected = base * n_dom * (1.0 + lean.ALPHA / 3.0) / (1.0 + lean.GAMMA / 4.0)
    assert abs(div - expected) < 1e-9


if __name__ == "__main__":
    for fn in (
        test_polyol_melt_eq_tetrahedral_spine,
        test_peptide_layer_melt_open_cell,
        test_tetrahedral_melt_h2o_contact,
        test_pyranose_chair_contact_factors,
        test_polyol_liquid_local_field_divisor,
        test_monomer_alcohol_liquid_local_field_divisor,
    ):
        fn()
    print("test_hqiv_foundation_lean_parity: OK")
