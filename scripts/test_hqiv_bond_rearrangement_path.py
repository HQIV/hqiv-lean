#!/usr/bin/env python3
"""Unit tests for bond rearrangement paths and GMTKN activation subset."""

from __future__ import annotations

import unittest

import hqiv_bond_rearrangement_path as brp
import hqiv_discrete_saddle_defect_readout as dsd


class TestBondRearrangementPath(unittest.TestCase):
    def test_break_coordination_excess(self) -> None:
        self.assertAlmostEqual(brp.break_coordination_excess(1.0), 1.0)
        self.assertAlmostEqual(brp.break_coordination_excess(2.0), 0.5)
        self.assertAlmostEqual(brp.break_coordination_excess(4.0), 0.25)

    def test_nil_path(self) -> None:
        path = brp.BondRearrangementPath("∅", ())
        self.assertEqual(path.barrier_ev, 0.0)
        self.assertAlmostEqual(path.activation_rate(2.5), 2.5)

    def test_single_break_gate(self) -> None:
        path = brp.single_bond_break_path(molecule="H2", binding_ev=4.0, delta=1.0)
        self.assertAlmostEqual(path.barrier_ev, dsd.contact_edge_gate_ev(4.0, 1.0))

    def test_gmtkn_audit(self) -> None:
        payload = brp.build_gmtkn_activation_audit()
        self.assertTrue(payload["all_identity_checks_pass"])
        names = {r["molecule"] for r in payload["rows"] if "error" not in r}
        for name in ("H2", "HF", "LiH", "N2", "H2O", "CH4"):
            self.assertIn(name, names)
        by_name = {r["molecule"]: r for r in payload["rows"] if "error" not in r}
        # Diatomic break: CN 1→0 ⇒ δ = 1
        self.assertAlmostEqual(by_name["H2"]["delta_coord"], 1.0)
        self.assertAlmostEqual(by_name["HF"]["delta_coord"], 1.0)
        # H2O: O CN2→1 (δ=0.5) vs H CN1→0 (δ=1) ⇒ max = 1
        self.assertAlmostEqual(by_name["H2O"]["delta_coord"], 1.0)
        # CH4: C CN4→3 (δ=0.25) vs H CN1→0 (δ=1) ⇒ max = 1
        self.assertAlmostEqual(by_name["CH4"]["delta_coord"], 1.0)
        # LiH should route ionic
        self.assertIn(by_name["LiH"]["contact_kind"], ("ionicBond", "ionic_bond"))
        # Barriers positive; transmission in (0,1]
        for row in by_name.values():
            self.assertGreater(row["path_barrier_ev"], 0.0)
            self.assertGreater(row["barrier_transmission"], 0.0)
            self.assertLessEqual(row["barrier_transmission"], 1.0)
        # H2O bonding CN: O=2, H=1 ⇒ first edge O–H has δ = max(1/2, 1/1) = 1
        # (edge 0 may be either O–H; both give δ=1 once steric is excluded)
        self.assertAlmostEqual(by_name["H2O"]["delta_coord"], 1.0)
        # Atomization ladders
        self.assertIsNotNone(by_name["H2O"].get("atomization_ladder"))
        self.assertEqual(by_name["H2O"]["atomization_ladder"]["n_steps"], 2)
        self.assertIsNotNone(by_name["CH4"].get("atomization_ladder"))
        self.assertEqual(by_name["CH4"]["atomization_ladder"]["n_steps"], 4)
        # Activated transport recovers activation rate at unit contact
        self.assertAlmostEqual(
            by_name["H2"]["activated_transport_unit_contact"],
            by_name["H2"]["activation_rate_unit_contact"],
        )

    def test_atomization_ladder_deltas(self) -> None:
        lad = brp.atomization_ladder_path(
            molecule="CH4", binding_ev_per_step=1.0, centre_cn0=4.0, n_steps=4
        )
        self.assertEqual(len(lad.steps), 4)
        # Every step has a terminal H (δ partner = 1) ⇒ edge δ = 1
        self.assertTrue(all(abs(s.delta_coord - 1.0) < 1e-12 for s in lad.steps))
        self.assertAlmostEqual(lad.barrier_ev, dsd.contact_edge_gate_ev(1.0, 1.0))

    def test_activated_transport_nil(self) -> None:
        self.assertAlmostEqual(
            brp.activated_transport_rate_slot(3.0, brp.BondRearrangementPath("∅", ())),
            3.0,
        )


if __name__ == "__main__":
    unittest.main()
