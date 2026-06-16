#!/usr/bin/env python3
"""Neighbor covalent lapse overlap on bulk H-bond wells."""

import unittest

from hqiv_lab import MaterialsLab
from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.packing import (
    intermolecular_contact_distance_angstrom,
    neighbor_covalent_lapse_overlap_factor,
)
from hqiv_lab.spec import MoleculeSpec

import hqiv_lean_physics_primitives as lean


class TestNeighborLapseOverlap(unittest.TestCase):
    def test_tetrahedral_shrink_factor(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("H2O"))
        f = neighbor_covalent_lapse_overlap_factor(mono)
        expected = 1.0 - lean.GAMMA * lean.STRONG_CHANNEL_FRACTION / 4.0
        self.assertAlmostEqual(f, expected)
        self.assertAlmostEqual(f, 0.95)

    def test_pyramidal_unchanged(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("NH3"))
        self.assertEqual(neighbor_covalent_lapse_overlap_factor(mono), 1.0)

    def test_apolar_unchanged(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("CH4"))
        self.assertEqual(neighbor_covalent_lapse_overlap_factor(mono), 1.0)

    def test_h2o_contact_shorter_than_isolated_dimer(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("H2O"))
        bulk = intermolecular_contact_distance_angstrom(mono)
        # Isolated: no neighbor overlap factor
        r = mono.mean_bond_length_angstrom
        sc = lean.STRONG_CHANNEL_FRACTION
        from hqiv_lab.packing import _bend_dress

        r_hbond = r * lean.ALPHA * (1.0 + sc) * (1.0 + lean.C_RINDLER_SHARED * _bend_dress(mono))
        isolated = 2.0 * r + r_hbond
        self.assertLess(bulk, isolated)
        self.assertAlmostEqual(bulk, 2.76, delta=0.02)

    def test_h2o_ice_density_near_nist(self) -> None:
        lab = MaterialsLab()
        spec = lab.spec_from_name("H2O")
        best = lab.preferred_allotrope(spec, temperature_k=273.15)
        self.assertEqual(best.label, "Ih")
        self.assertAlmostEqual(best.density_g_cm3, 0.917, delta=0.02)


if __name__ == "__main__":
    unittest.main()
