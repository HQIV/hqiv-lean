#!/usr/bin/env python3
"""Tests for portable outside-curvature overlay calculator."""

from __future__ import annotations

import json
import unittest
from pathlib import Path

import hqiv_outside_curvature_calculator as occ

ROOT = Path(__file__).resolve().parents[1]


class TestOutsideCurvatureCalculator(unittest.TestCase):
    def test_earth_lab_unity_facility(self) -> None:
        ov = occ.preset_overlay("earth_lab")
        self.assertAlmostEqual(ov.k_facility(), 1.0)
        self.assertGreater(ov.k_mass_chart(), 1.0)

    def test_cms_preset_increases_k(self) -> None:
        ov = occ.preset_overlay("cms_lhc")
        self.assertGreater(ov.k_facility(), 1.0)

    def test_beam_velocity_adds_stream(self) -> None:
        base = occ.OutsideEnvironmentOverlay(comoving_stream_fraction=0.0)
        fast = occ.OutsideEnvironmentOverlay(
            comoving_stream_fraction=0.0,
            beam_velocity_m_s=0.5 * occ.C_LIGHT_M_S,
        )
        self.assertGreater(fast.effective_stream_fraction(), base.effective_stream_fraction())

    def test_compare_facility_frame_uses_apparent_mass(self) -> None:
        ov = occ.preset_overlay("cms_lhc")
        pole = 2000.0
        res = occ.compare_mass_readout(
            pole,
            pole * ov.k_total(),
            1.0,
            ov,
            comparison_frame="facility_apparent",
        )
        self.assertAlmostEqual(res.delta_mev, 0.0, places=3)

    def test_sigma_combined_includes_dressing(self) -> None:
        ov = occ.preset_overlay("cms_lhc")
        res = occ.compare_mass_readout(
            2286.0,
            2290.0,
            0.14,
            ov,
            comparison_frame="facility_apparent",
        )
        self.assertGreater(res.sigma_combined_mev, 0.14)

    def test_batch_example_runs(self) -> None:
        path = ROOT / "data" / "outside_curvature_calculator_example.json"
        payload = json.loads(path.read_text(encoding="utf-8"))
        out = occ.run_batch(payload)
        self.assertIn("dressing", out)
        self.assertIn("comparisons", out)
        self.assertIn("excited_panel_summary", out)


if __name__ == "__main__":
    unittest.main()
