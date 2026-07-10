#!/usr/bin/env python3
"""Tests for contact-network allotrope ranking."""

from __future__ import annotations

import unittest

import hqiv_allotrope_contact_rank_readout as acr
import hqiv_lean_physics_primitives as lean


class TestAllotropeContactRank(unittest.TestCase):
    def test_score_scales_with_bond_order(self) -> None:
        a = acr.contact_network_allotrope_score(1.0, periodic_increment=1.0, contact_weight=1.0)
        b = acr.contact_network_allotrope_score(2.0, periodic_increment=1.0, contact_weight=1.0)
        self.assertAlmostEqual(b, 2.0 * a, places=12)

    def test_ionic_dress(self) -> None:
        base = acr.contact_network_allotrope_score(1.0, ionic_character=0.0)
        dressed = acr.contact_network_allotrope_score(1.0, ionic_character=1.0)
        self.assertAlmostEqual(
            dressed, base * (1.0 + lean.GAMMA * lean.STRONG_CHANNEL_FRACTION), places=12
        )

    def test_carbon_diamond_ranks_first(self) -> None:
        audit = acr.build_allotrope_contact_rank_audit()
        self.assertTrue(audit["all_identity_checks_pass"])
        self.assertEqual(audit["carbon_ranking"][0]["coordination"], 4)
        self.assertEqual(audit["carbon_ranking"][0]["rank"], 1)


if __name__ == "__main__":
    unittest.main()
