"""Tests for HQIV stellar-collapse ε ceiling witness."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_stellar_collapse import (  # noqa: E402
    EPS_HORIZON,
    hqiv_geometry_ceilings,
    hqiv_remnant_at_uniform_nuclear,
    stellar_collapse_row,
    stellar_collapse_witness,
)


class StellarCollapseTests(unittest.TestCase):
    def test_ns_max_matches_compact_object(self) -> None:
        ceil = hqiv_geometry_ceilings()
        self.assertAlmostEqual(ceil["neutron_star_max_msun"], 1.98, delta=0.05)

    def test_direct_bh_uniform_sphere_near_eight_msun(self) -> None:
        ceil = hqiv_geometry_ceilings()
        self.assertAlmostEqual(ceil["direct_bh_uniform_sphere_msun"], 7.83, delta=0.1)

    def test_low_zams_neutron_star(self) -> None:
        row = stellar_collapse_row(12.0)
        self.assertEqual(row.outcome_uniform, "neutron_star")
        self.assertLess(row.epsilon_surface, EPS_HORIZON)

    def test_high_core_direct_bh(self) -> None:
        uni = hqiv_remnant_at_uniform_nuclear(20.0)
        self.assertEqual(uni["outcome"], "direct_black_hole")
        self.assertGreaterEqual(float(uni["epsilon_surface"]), EPS_HORIZON)

    def test_pair_instability_window(self) -> None:
        row = stellar_collapse_row(180.0)
        self.assertTrue(row.trad_pair_instability)
        self.assertEqual(row.outcome_uniform, "pair_instability_disrupted")

    def test_witness_bundle(self) -> None:
        data = stellar_collapse_witness(zams_grid=[15, 25, 40, 180])
        self.assertIn("direct_bh_ceiling_scan", data)
        self.assertEqual(len(data["rows"]), 4)


if __name__ == "__main__":
    unittest.main()
