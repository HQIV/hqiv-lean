#!/usr/bin/env python3
"""Tests: allotropes derived from molecular inputs (not hardcoded tables)."""

import unittest

from hqiv_lab import MaterialsLab, MoleculeSpec
from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.packing import templates_for_motif


class TestAllotropeDerivation(unittest.TestCase):
    def setUp(self) -> None:
        self.lab = MaterialsLab()

    def test_h2o_motif_tetrahedral(self) -> None:
        spec = self.lab.spec_from_name("H2O")
        mono = infer_monomer_geometry(spec)
        self.assertEqual(mono.motif, IntermolecularMotif.TETRAHEDRAL_HBOND)
        self.assertEqual(mono.intermolecular_contacts, 4)

    def test_h2o_derives_ih_ic_amorphous(self) -> None:
        spec = self.lab.spec_from_name("H2O")
        labels = {c.label for c in self.lab.derive_allotropes(spec)}
        self.assertIn("Ih", labels)
        self.assertIn("Ic", labels)

    def test_h2o_preferred_is_ih_at_273k(self) -> None:
        spec = self.lab.spec_from_name("H2O")
        best = self.lab.preferred_allotrope(spec, temperature_k=273.15)
        self.assertEqual(best.label, "Ih")
        self.assertAlmostEqual(best.density_g_cm3, 0.92, delta=0.06)

    def test_nh3_fcc_density_near_nist(self) -> None:
        spec = self.lab.spec_from_name("NH3")
        best = self.lab.preferred_allotrope(spec, temperature_k=195.8)
        self.assertEqual(best.label, "solid")
        self.assertAlmostEqual(best.density_g_cm3, 0.82, delta=0.05)

    def test_hf_chain_z4_density(self) -> None:
        spec = self.lab.spec_from_name("HF")
        best = self.lab.preferred_allotrope(spec, temperature_k=189.6)
        self.assertEqual(best.label, "chain")
        self.assertEqual(best.unit_cell.molecules_per_cell, 4)
        self.assertAlmostEqual(best.density_g_cm3, 1.15, delta=0.08)

    def test_ch4_motif_apolar(self) -> None:
        spec = self.lab.spec_from_name("CH4")
        mono = infer_monomer_geometry(spec)
        self.assertEqual(mono.motif, IntermolecularMotif.APOLAR_CLOSE_PACK)

    def test_ch4_preferred_solid_i(self) -> None:
        spec = self.lab.spec_from_name("CH4")
        best = self.lab.preferred_allotrope(spec, temperature_k=90.0)
        self.assertEqual(best.label, "solid_I")
        self.assertAlmostEqual(best.density_g_cm3, 0.52, delta=0.04)

    def test_nh3_pyramidal_templates(self) -> None:
        spec = self.lab.spec_from_name("NH3")
        mono = infer_monomer_geometry(spec)
        self.assertEqual(mono.motif, IntermolecularMotif.PYRAMIDAL_HBOND)
        self.assertGreaterEqual(len(templates_for_motif(mono.motif)), 1)

    def test_unit_cell_from_derived_not_table(self) -> None:
        spec = MoleculeSpec.from_chart_name("H2O")
        mono = infer_monomer_geometry(spec)
        cell = self.lab.unit_cell(spec, "Ih")
        self.assertGreater(cell.a_angstrom, 3.5)
        self.assertGreater(cell.c_angstrom, 4.5)
        self.assertEqual(cell.molecules_per_cell, 4)

    def test_readout_includes_allotrope_list(self) -> None:
        out = self.lab.readout(self.lab.spec_from_name("H2O"), include_response=False)
        self.assertGreaterEqual(len(out["allotropes"]), 2)
        self.assertIsNotNone(out["preferred_allotrope"])

    def test_scores_sorted_descending(self) -> None:
        cands = self.lab.derive_allotropes(self.lab.spec_from_name("H2O"))
        scores = [c.score for c in cands]
        self.assertEqual(scores, sorted(scores, reverse=True))


if __name__ == "__main__":
    unittest.main()
