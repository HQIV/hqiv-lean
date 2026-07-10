#!/usr/bin/env python3
"""Unit tests for period-3/n outside-contact suite."""
from __future__ import annotations

import unittest

import hqiv_chemistry_tuft_dynamics as ctd
import hqiv_period_n_outside_contact_suite as suite
import hqiv_selection_weights as sw


class TestPeriodNOutsideContact(unittest.TestCase):
    def test_nacl_elongation_seven_halves(self) -> None:
        self.assertAlmostEqual(ctd.ionic_inert_core_length_elongation(11, 17), 3.5)

    def test_gas_dress_eight_fifths(self) -> None:
        self.assertAlmostEqual(ctd.ionic_gas_phase_em_dress(), 1.6)

    def test_nacl_route_ionic_licl_covalent(self) -> None:
        self.assertGreater(sw.spectroscopy_geometry_route_weights(11, 17)["ionic_outside_contact"], 0.5)
        self.assertGreater(sw.spectroscopy_geometry_route_weights(3, 17)["covalent_nested_wf"], 0.5)

    def test_nacl_gas_near_nist_quarantine(self) -> None:
        row = next(r for r in suite.build_payload()["ionic_period_n"] if r["name"] == "NaCl")
        self.assertTrue(row["hierarchy_core_lt_gas_lt_lattice"])
        self.assertLess(abs(row["gas_error_pct_quarantine"]), 2.0)

    def test_identity_checks(self) -> None:
        checks = suite.build_payload()["identity_checks"]
        self.assertTrue(all(checks.values()), checks)


if __name__ == "__main__":
    unittest.main()
