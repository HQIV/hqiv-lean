#!/usr/bin/env python3
"""Tests for full multi-channel HEP decay expansion."""

from __future__ import annotations

import unittest

import hqiv_hep_decay_benchmark as bench
import hqiv_hep_decay_chain as hep
import hqiv_hep_multichannel_expansion as mc


class TestMultichannelExpansion(unittest.TestCase):
    def test_jpsi_many_open_channels(self) -> None:
        env = hep.ExperimentEnvironment()
        p = hep.build_particle("Jpsi")
        edges = hep.edges_from_particle(p, env=env)
        self.assertGreaterEqual(len(edges), 100)
        self.assertAlmostEqual(sum(e.branching_ratio for e in edges), 1.0, places=6)

    def test_quarkonium_ee_channel(self) -> None:
        env = hep.ExperimentEnvironment()
        edges = hep.edges_from_particle(hep.build_particle("Jpsi"), env=env)
        ee = [e for e in edges if e.mode.daughter_ids == ("e_plus", "e_minus")]
        self.assertEqual(len(ee), 1)
        self.assertGreater(ee[0].branching_ratio, 0.005)

    def test_d_plus_weak_expansion(self) -> None:
        env = hep.ExperimentEnvironment()
        edges = hep.edges_from_particle(hep.build_particle("D_plus"), env=env)
        self.assertGreaterEqual(len(edges), 5)
        self.assertAlmostEqual(sum(e.branching_ratio for e in edges), 1.0, places=6)
        self.assertTrue(any("K_minus" in e.mode.daughter_ids for e in edges))
        self.assertTrue(any(e.mode.daughter_ids == ("pi_plus", "pi_minus", "pi_zero") for e in edges))

    def test_ozi_suppression(self) -> None:
        self.assertLess(mc.ozi_suppression_factor("Jpsi", ("rho_zero",)), 1.0)
        self.assertEqual(mc.ozi_suppression_factor("Upsilon", ("Jpsi",)), 1.0)

    def test_heavy_cascade_weight_from_lean(self) -> None:
        import hqiv_hep_decay_readout as hdr

        self.assertAlmostEqual(hdr.heavy_quarkonium_cascade_weight(), 2.0)
        self.assertAlmostEqual(
            hdr.open_charm_production_weight() / hdr.open_bottom_production_weight(),
            hdr.heavy_quarkonium_cascade_weight(),
        )
        self.assertAlmostEqual(hdr.ozi_suppression_factor(0), hdr.open_charm_production_weight())
        self.assertAlmostEqual(hdr.neutral_light_pair_cascade_weight(), 0.16)

    def test_upsilon_jpsi_inclusive_neutral_aggregate(self) -> None:
        env = hep.ExperimentEnvironment()
        edges = hep.edges_from_particle(hep.build_particle("Upsilon"), env=env)
        selected = [
            e
            for e in edges
            if "Jpsi" in e.mode.daughter_ids and mc.strong_neutral_light_cascade(e.mode.daughter_ids)
        ]
        self.assertGreaterEqual(len(selected), 8)
        br = sum(e.branching_ratio for e in selected)
        self.assertGreater(br, 0.005)
        self.assertLess(br, 0.007)

    def test_benchmark_multichannel_panel(self) -> None:
        payload = bench.build_payload()
        mc_rows = [r for r in payload["rows"] if r["panel"] == "multichannel"]
        self.assertGreaterEqual(len(mc_rows), 4)
        self.assertTrue(all(r["status"] == "pass" for r in mc_rows))


if __name__ == "__main__":
    unittest.main()
