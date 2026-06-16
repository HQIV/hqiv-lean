#!/usr/bin/env python3
"""Tests for the unified binding energy program."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import hqiv_bbn_abundances as bbn
import hqiv_binding_energy_program as bep
import hqiv_post_alpha_binding_program as pap


class TestBindingEnergyProgram(unittest.TestCase):
    def test_constructive_ladder_matches_bbn_cluster(self) -> None:
        m = bep.M_SHELL
        for A, Z in ((2, 1), (3, 2), (4, 2)):
            self.assertAlmostEqual(
                bep.constructive_ladder_binding_mev(m, A, Z),
                bbn.cluster_binding_mev(m, A, Z=Z),
                places=6,
            )

    def test_ladder_equals_naive_times_amplification(self) -> None:
        m = bep.M_SHELL
        for A, Z in ((2, 1), (3, 1), (4, 2)):
            naive = bep.naive_valley_geometry_binding_mev(m, A, Z)
            amp = bep.constructive_ladder_amplification(A, Z)
            ladder = bep.constructive_ladder_binding_mev(m, A, Z)
            self.assertAlmostEqual(ladder, naive * amp, places=6)

    def test_lean_spine_matches_caustic_geometry_hook(self) -> None:
        m = bep.M_SHELL
        self.assertAlmostEqual(
            bep.cluster_binding_from_caustic_geometry(m, 4, 2),
            pap.post_alpha_cluster_binding_with_network_mev(m, 4, 2),
            places=6,
        )
        self.assertAlmostEqual(
            bep.cluster_binding_from_caustic_geometry(m, 7, 4),
            pap.post_alpha_cluster_binding_with_network_mev(m, 7, 4),
            places=6,
        )

    def test_he4_ladder_not_pdg_be_per_a_trap(self) -> None:
        row = bep.build_comparison_row(4, 2, "⁴He")
        self.assertIsNotNone(row.pdg_binding_total_mev)
        self.assertIsNotNone(row.pdg_be_per_a_mev)
        assert row.pdg_binding_total_mev is not None
        assert row.pdg_be_per_a_mev is not None
        # Legacy total B ≈ PDG BE/A numerically — must not be read as ~1% agreement.
        self.assertAlmostEqual(
            row.binding_constructive_ladder_mev, row.pdg_be_per_a_mev, delta=0.1
        )
        self.assertLess(row.binding_constructive_ladder_mev / row.pdg_binding_total_mev, 0.3)

    def test_be7_network_ordering(self) -> None:
        m = bep.M_SHELL
        b_be = bep.cluster_binding_from_caustic_geometry(m, 7, 4)
        b_li = bep.cluster_binding_from_caustic_geometry(m, 7, 3)
        self.assertGreater(b_be, b_li)

    def test_witness_json_roundtrip(self) -> None:
        rows = bep.build_panel([(4, 2, "⁴He"), (7, 4, "⁷Be")])
        payload = bep.export_witness(rows)
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "witness.json"
            path.write_text(json.dumps(payload) + "\n")
            loaded = json.loads(path.read_text())
        self.assertIn("summary", loaded)
        self.assertEqual(len(loaded["rows"]), 2)


if __name__ == "__main__":
    unittest.main()
