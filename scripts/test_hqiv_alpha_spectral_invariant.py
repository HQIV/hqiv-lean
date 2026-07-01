#!/usr/bin/env python3
"""Tests for the octonion spectral-invariant per-species alpha."""

from __future__ import annotations

import json
import unittest

import numpy as np

import hqiv_alpha_spectral_invariant as si


class SpectralInvariantTests(unittest.TestCase):
    def test_single_unit_matrices_are_spectrally_identical(self) -> None:
        # every imaginary-unit left-mult L_v has eigenvalues +-i (4-fold) -> |eig|=1
        for v in range(1, 8):
            eigs = np.abs(np.linalg.eigvals(si._L[v]))
            self.assertTrue(np.allclose(eigs, 1.0, atol=1e-9))

    def test_structured_four_mode_spectrum(self) -> None:
        r = si.spectral_invariant("C-12", "isotope", si.ss.isotope_anchor_shell(12))
        # 4 distinct imaginary mode magnitudes (not degenerate at |g|)
        self.assertEqual(len(r.spectral_modes), 4)
        self.assertGreater(r.spectral_spread, 2.0)

    def test_quadratic_invariant_near_four_g_sq(self) -> None:
        # sum(mode^2) ~ 4|g|^2 up to the gate table's (small) normalization defect
        r = si.spectral_invariant("C-12", "isotope", si.ss.isotope_anchor_shell(12))
        rel = r.quad_consistency / (4.0 * r.g_norm**2)
        self.assertLess(rel, 1e-2)

    def test_inv_norm_monotone_with_isotope_mass(self) -> None:
        h = si.spectral_invariant("H-1", "isotope", si.ss.isotope_anchor_shell(1))
        fe = si.spectral_invariant("Fe-56", "isotope", si.ss.isotope_anchor_shell(56))
        self.assertGreater(fe.inv_alpha_spectral_norm, h.inv_alpha_spectral_norm)

    def test_inv_norm_near_gut_scale(self) -> None:
        # the basis-independent norm readout lives near INV_ALPHA_GUT, not 137
        report = si.build_report()
        for r in report.invariants:
            self.assertGreater(r.inv_alpha_spectral_norm, 25.0)
            self.assertLess(r.inv_alpha_spectral_norm, 60.0)

    def test_isotope_and_atom_frames_differ_for_carbon(self) -> None:
        iso = si.spectral_invariant("C-12", "isotope", si.ss.isotope_anchor_shell(12))
        atom = si.spectral_invariant("C", "atom", si.ss.atom_anchor_shell(6))
        self.assertNotAlmostEqual(iso.g_norm, atom.g_norm, places=4)

    def test_report_json_roundtrip(self) -> None:
        loaded = json.loads(json.dumps(si.build_report().to_dict()))
        self.assertIn("invariants", loaded)
        self.assertIn("findings", loaded)
        self.assertGreaterEqual(len(loaded["invariants"]), 12)


if __name__ == "__main__":
    unittest.main()
