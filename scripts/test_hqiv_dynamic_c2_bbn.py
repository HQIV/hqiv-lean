#!/usr/bin/env python3
"""Dynamic C₂ / κ₆ BBN ladder mirrors Lean `DynamicBBNBaryogenesis`."""

from __future__ import annotations

import unittest

import hqiv_bbn_abundances as bbn
import hqiv_lean_physics_primitives as lean


class TestDynamicC2BBN(unittest.TestCase):
    ETA = 6.2e-10
    M_P = 938.272

    def test_C2_at_lockin_matches_lean(self) -> None:
        c2 = lean.tuft_lapse_concentration_at_xi(lean.XI_LOCKIN)
        self.assertAlmostEqual(c2, 56.0 / 45.0, places=9)

    def test_lapse_exponent_from_effective_deuteron_at_t(self) -> None:
        T = 0.1
        Q_eff = lean.bbn_deuteron_binding_q_effective_at_t(T, lean.REFERENCE_M)
        expected = lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * (
            Q_eff / lean.bbn_neutron_proton_gap_mev()
        )
        self.assertAlmostEqual(
            lean.bbn_dynamic_c2_lapse_exponent(self.ETA, T_MeV=T),
            expected,
            places=9,
        )
        self.assertLess(expected, lean.bbn_dynamic_c2_lapse_exponent(self.ETA, T_MeV=1.0))

    def test_bottleneck_from_freezeout(self) -> None:
        Tb = lean.bbn_dynamic_c2_bottleneck_t_mev(self.ETA)
        Tf = lean.bbn_dynamic_c2_freezeout_t_mev(self.ETA)
        self.assertAlmostEqual(Tb, lean.GAMMA * lean.STRONG_CHANNEL_FRACTION * Tf, places=9)
        self.assertGreater(Tb, 0.1)
        self.assertLess(Tb, 0.2)

    def test_suppression_unity_above_bottleneck(self) -> None:
        Tb = lean.bbn_dynamic_c2_bottleneck_t_mev(self.ETA)
        self.assertEqual(
            lean.bbn_dynamic_c2_opportunity_suppression(
                Tb + 0.05, eta=self.ETA, m_nucleon=self.M_P
            ),
            1.0,
        )

    def test_suppression_in_bottleneck_below_one(self) -> None:
        s = lean.bbn_dynamic_c2_opportunity_suppression(
            0.1, eta=self.ETA, m_nucleon=self.M_P
        )
        self.assertGreater(s, 0.0)
        self.assertLess(s, 1.0)

    def test_kappa6_ratio_tracks_temperature(self) -> None:
        r_hot = lean.bbn_dynamic_c2_readout_at_T(
            10.0, eta=self.ETA, m_nucleon=self.M_P
        )["kappa6_over_kappa6_ref"]
        r_cold = lean.bbn_dynamic_c2_readout_at_T(
            0.1, eta=self.ETA, m_nucleon=self.M_P
        )["kappa6_over_kappa6_ref"]
        self.assertGreater(r_cold, r_hot)


if __name__ == "__main__":
    unittest.main()
