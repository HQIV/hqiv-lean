#!/usr/bin/env python3
"""Tests for the per-species alpha slice of the 7x7 Fano coupling matrix."""

from __future__ import annotations

import json
import unittest

import hqiv_alpha_species_slice as ss


class AlphaSpeciesSliceTests(unittest.TestCase):
    def test_zero_offset_recovers_canonical_sector(self) -> None:
        frame = ss.species_shell_frame(ss.REFERENCE_M)
        self.assertEqual(frame, list(ss._SECTOR_SHELLS))

    def test_frame_translates_rigidly(self) -> None:
        base = ss.species_shell_frame(ss.REFERENCE_M)
        up = ss.species_shell_frame(ss.REFERENCE_M + 2)
        self.assertEqual(up, [m + 2 for m in base])

    def test_frame_clamps_nonnegative(self) -> None:
        frame = ss.species_shell_frame(0)
        self.assertTrue(all(m >= 0 for m in frame))

    def test_solve_residual_small(self) -> None:
        s = ss.solve_species_alpha("C-12", "isotope", 8, "test")
        self.assertLess(s.residual, 1e-6)

    def test_heavier_isotope_has_larger_inv_alpha(self) -> None:
        he = ss.solve_species_alpha("He-4", "isotope", ss.isotope_anchor_shell(4), "t")
        fe = ss.solve_species_alpha("Fe-56", "isotope", ss.isotope_anchor_shell(56), "t")
        self.assertGreater(fe.inv_alpha_weighted, he.inv_alpha_weighted)

    def test_isotope_and_atom_frames_differ_for_carbon(self) -> None:
        iso = ss.solve_species_alpha("C-12", "isotope", ss.isotope_anchor_shell(12), "t")
        atom = ss.solve_species_alpha("C", "atom", ss.atom_anchor_shell(6), "t")
        self.assertNotAlmostEqual(iso.inv_alpha_weighted, atom.inv_alpha_weighted, places=3)

    def test_allotrope_diamond_vs_graphite_differ(self) -> None:
        dia = ss.solve_species_alpha("dia", "allotrope", ss.allotrope_anchor_shell(6, 4), "t")
        gra = ss.solve_species_alpha("gra", "allotrope", ss.allotrope_anchor_shell(6, 3), "t")
        self.assertNotAlmostEqual(dia.inv_alpha_weighted, gra.inv_alpha_weighted, places=3)

    def test_alpha_weighted_is_reciprocal(self) -> None:
        s = ss.solve_species_alpha("C-12", "isotope", 8, "t")
        self.assertAlmostEqual(s.alpha_weighted, 1.0 / s.inv_alpha_weighted, places=12)

    def test_report_json_roundtrip(self) -> None:
        report = ss.build_report()
        loaded = json.loads(json.dumps(report.to_dict()))
        self.assertIn("slices", loaded)
        self.assertGreaterEqual(len(loaded["slices"]), 12)
        kinds = {s["kind"] for s in loaded["slices"]}
        self.assertEqual(kinds, {"isotope", "atom", "molecule", "allotrope"})

    def test_carbon_isotope_brackets_codata(self) -> None:
        # the isotope frame should straddle CODATA between light and heavy nuclei
        c12 = ss.solve_species_alpha("C-12", "isotope", ss.isotope_anchor_shell(12), "t")
        fe = ss.solve_species_alpha("Fe-56", "isotope", ss.isotope_anchor_shell(56), "t")
        self.assertLess(c12.inv_alpha_weighted, ss.CODATA_INV_ALPHA)
        self.assertGreater(fe.inv_alpha_weighted, ss.CODATA_INV_ALPHA)


if __name__ == "__main__":
    unittest.main()
