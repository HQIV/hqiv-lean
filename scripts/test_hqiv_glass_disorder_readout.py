#!/usr/bin/env python3
"""Tests for glass / amorphous disorder score."""

from __future__ import annotations

import unittest

import hqiv_glass_disorder_readout as gdr
import hqiv_lean_physics_primitives as lean
from hqiv_lab.allotrope import packing_disorder_score


class TestGlassDisorder(unittest.TestCase):
    def test_ordered_below_alpha(self) -> None:
        s = packing_disorder_score(
            periodic_weight=1.0,
            mean_coordination=4.0,
            coordination_variance=0.0,
            open_fraction=0.0,
        )
        self.assertLessEqual(s, lean.ALPHA)

    def test_disordered_above_alpha(self) -> None:
        s = packing_disorder_score(
            periodic_weight=0.0,
            mean_coordination=4.0,
            coordination_variance=4.0 * lean.STRONG_CHANNEL_FRACTION,
            open_fraction=lean.ALPHA + lean.GAMMA,
        )
        self.assertGreater(s, lean.ALPHA)

    def test_audit_identity(self) -> None:
        audit = gdr.build_glass_disorder_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        self.assertTrue(
            any(t["label"] == "amorphous" for t in audit["rows"][0]["templates"])
        )


if __name__ == "__main__":
    unittest.main()
