#!/usr/bin/env python3
"""Tests for post-α binding program witness."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

import hqiv_bbn_abundances as bbn
import hqiv_post_alpha_binding_program as prog
import hqiv_post_alpha_sphere_touching as touch


class TestPostAlphaBindingProgram(unittest.TestCase):
    def test_be7_effective_valleys_gt_li7(self) -> None:
        self.assertGreater(
            touch.post_alpha_outside_valley_count_effective(7, 4),
            touch.post_alpha_outside_valley_count_effective(7, 3),
        )

    def test_geometry_binding_ordering(self) -> None:
        m = 4
        q_be = prog.post_alpha_cluster_binding_geometry_mev(m, 7, 4)
        q_li = prog.post_alpha_cluster_binding_geometry_mev(m, 7, 3)
        self.assertGreater(q_be, q_li)

    def test_geometry_matches_effective_valleys(self) -> None:
        m = 4
        eff = touch.post_alpha_outside_valley_count_effective(7, 4)
        unit = prog.sphere_touch_contact_energy_unit_mev(m)
        coupling = prog.geometry_to_mev_coupling(m)
        geom = prog.post_alpha_geometric_touch_energy(m, 7, 4)
        self.assertAlmostEqual(geom, eff * unit, places=6)
        self.assertAlmostEqual(geom * coupling, prog.post_alpha_cluster_binding_geometry_mev(m, 7, 4), places=6)

    def test_witness_json_roundtrip(self) -> None:
        rows = prog.build_rows([(7, 4, "⁷Be"), (7, 3, "⁷Li")])
        payload = {"rows": [__import__("dataclasses").asdict(r) for r in rows]}
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "witness.json"
            path.write_text(json.dumps(payload) + "\n")
            loaded = json.loads(path.read_text())
        self.assertGreaterEqual(len(loaded["rows"]), 2)

    def test_capture_q_positive(self) -> None:
        m = 4
        q_be = prog.post_alpha_cluster_binding_geometry_mev(m, 7, 4)
        q_li = prog.post_alpha_cluster_binding_geometry_mev(m, 7, 3)
        self.assertGreater(bbn.be7_to_li7_capture_q(q_be, q_li), 0.0)

    def test_network_binding_ordering_be7_li7(self) -> None:
        m = 4
        b_be = prog.post_alpha_cluster_binding_with_network_mev(m, 7, 4)
        b_li = prog.post_alpha_cluster_binding_with_network_mev(m, 7, 3)
        self.assertGreater(b_be, b_li)

    def test_relaxation_lowers_be_per_A_vs_pre_relax(self) -> None:
        """Lighter extras relax the well: final BE/A ≤ deepened+network BE/A for ⁷Li."""
        m = 4
        pre = prog.binding_per_nucleon_mev(
            prog.post_alpha_cluster_binding_pre_relax_mev(m, 7, 3), 7
        )
        final = prog.binding_per_nucleon_mev(
            prog.post_alpha_cluster_binding_with_network_mev(m, 7, 3), 7
        )
        self.assertLessEqual(final, pre)
        self.assertGreater(prog.post_alpha_well_relaxation_mev(m, 7, 3), 0.0)
        # Deepening still raises total binding vs bare geometry-only.
        geom = prog.binding_per_nucleon_mev(
            prog.post_alpha_cluster_binding_geometry_mev(m, 7, 3), 7
        )
        self.assertGreater(final, geom)


if __name__ == "__main__":
    unittest.main()
