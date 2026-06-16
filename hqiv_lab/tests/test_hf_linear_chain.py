#!/usr/bin/env python3
"""HF zigzag chain: linear monomer + halogen H-bond + lattice open."""

import math
import unittest

from hqiv_lab import MaterialsLab
from hqiv_lab.coordination import infer_monomer_geometry
from hqiv_lab.packing import (
    halogen_strong_hbond_leg_factor,
    intermolecular_contact_distance_angstrom,
    linear_chain_zigzag_lattice_open_factor,
)
from hqiv_lab.spec import MoleculeSpec

import hqiv_lean_physics_primitives as lean


class TestHFLinearChain(unittest.TestCase):
    def test_monomer_is_linear_not_tetrahedral_default(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("HF"))
        self.assertAlmostEqual(mono.bond_angle_rad, math.pi)
        self.assertEqual(mono.n_bonds_at_heavy, 1)

    def test_halogen_leg_compression_factor(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("HF"))
        f = halogen_strong_hbond_leg_factor(mono)
        expected = 1.0 - lean.GAMMA * lean.STRONG_CHANNEL_FRACTION / 9.0
        self.assertAlmostEqual(f, expected)

    def test_zigzag_lattice_open(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("HF"))
        f = linear_chain_zigzag_lattice_open_factor(mono)
        self.assertAlmostEqual(f, 1.0 + lean.GAMMA / 12.0)

    def test_contact_shorter_than_spurious_bend_default(self) -> None:
        mono = infer_monomer_geometry(MoleculeSpec.from_chart_name("HF"))
        bulk = intermolecular_contact_distance_angstrom(mono)
        r = mono.mean_bond_length_angstrom
        sc = lean.STRONG_CHANNEL_FRACTION
        spurious_dress = 0.5 * (1.0 - math.cos(0.5 * math.radians(109.47)))
        r_hbond_old = r * lean.ALPHA * (1.0 + sc) * (1.0 + lean.C_RINDLER_SHARED * spurious_dress)
        isolated = 2.0 * r + r_hbond_old
        self.assertLess(bulk, isolated)

    def test_hf_solid_density_near_nist(self) -> None:
        lab = MaterialsLab()
        best = lab.preferred_allotrope(lab.spec_from_name("HF"), temperature_k=189.6)
        self.assertEqual(best.label, "chain")
        self.assertAlmostEqual(best.density_g_cm3, 1.15, delta=0.02)


if __name__ == "__main__":
    unittest.main()
