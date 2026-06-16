#!/usr/bin/env python3
"""Tests for the extended BBN cooling network (⁷Be → ⁷Li ladder)."""

from __future__ import annotations

import unittest

import hqiv_bbn_abundances as bbn
import hqiv_bbn_epoch_network as net
import hqiv_excited_states as hes


class TestBBNEpochNetworkLiBe(unittest.TestCase):
    ETA = 6.2e-10
    M_P = 938.272

    def setUp(self) -> None:
        self.Q_D, self.Q_4, self.Q_3, self.Q_7 = bbn.lockin_binding_q_network(
            self.M_P, hes.REFERENCE_M
        )
        self.dm = 1.293

    def test_lockin_be7_binding_positive(self) -> None:
        self.assertGreater(self.Q_7, self.Q_3)
        self.assertGreater(bbn.be7_formation_q(self.Q_7, self.Q_3, self.Q_4), 0.0)

    def test_geometry_li7_far_neutron_weaker_than_be7(self) -> None:
        Q_be, Q_li = bbn.lockin_li7_be7_q(self.M_P, hes.REFERENCE_M)
        self.assertGreater(Q_be, Q_li)
        from hqiv_post_alpha_sphere_touching import post_alpha_outside_valley_count_effective

        self.assertLess(
            post_alpha_outside_valley_count_effective(7, 3),
            post_alpha_outside_valley_count_effective(7, 4),
        )

    def test_network_li7_more_bound_than_be7(self) -> None:
        Q_be, Q_li = bbn.lockin_li7_be7_q_network(self.M_P, hes.REFERENCE_M)
        self.assertGreater(Q_li, Q_be)
        self.assertGreater(bbn.be7_to_li7_capture_q(Q_be, Q_li), 0.0)
        self.assertGreater(bbn.be7_formation_q(self.Q_7, self.Q_3, self.Q_4), 0.0)

    def test_li7_ladder_order_of_magnitude(self) -> None:
        Q_D, Q_4, Q_3, Q_7 = bbn.lockin_binding_q_network(self.M_P, hes.REFERENCE_M)
        Q_be, Q_li = bbn.lockin_li7_be7_q_network(self.M_P, hes.REFERENCE_M)
        tail = bbn.integrate_be7_li7_tail_window(
            self.ETA,
            self.M_P,
            self.dm,
            Q_D,
            Q_4,
            Q_3,
            Q_7,
            Q_be,
            Q_li,
        )
        li7 = tail["Li7_over_H"]
        self.assertGreater(li7, 1.0e-12)
        self.assertLess(li7, 1.0e-7)

    def test_integrated_li7_nonzero_with_be_ladder(self) -> None:
        final, _meta = net.integrate_cooling_network(
            self.ETA,
            self.dm,
            self.Q_D,
            self.Q_3,
            self.Q_4,
            n_steps=300,
        )
        readout = net.readout_from_state(final, self.ETA)
        self.assertGreater(readout["Li7_over_H"] + readout["Be7_over_H"], 0.0)

    def test_baryon_budget_preserved(self) -> None:
        final, meta = net.integrate_cooling_network(
            self.ETA,
            self.dm,
            self.Q_D,
            self.Q_3,
            self.Q_4,
            n_steps=200,
        )
        self.assertAlmostEqual(meta["final_baryon_sum"], self.ETA, delta=1e-14 * self.ETA)


if __name__ == "__main__":
    unittest.main()
