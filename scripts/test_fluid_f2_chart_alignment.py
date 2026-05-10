"""Tests for scripts/fluid_f2_chart_alignment.py (F2 vacuum source mirror)."""

import unittest

from fluid_f2_chart_alignment import (
    OMaxwellFluidChartHypothesisData,
    chart_spatial_phi_gradient,
    vacuum_momentum_source3,
)


class TestFluidF2ChartAlignment(unittest.TestCase):
    def test_spatial_slice_of_grad(self) -> None:
        g4 = [0.0, 1.0, 2.0, 3.0]
        self.assertEqual(chart_spatial_phi_gradient(g4), (1.0, 2.0, 3.0))

    def test_vacuum_momentum_matches_linear_combo(self) -> None:
        gamma = 2.0 / 5.0
        phi = 2.0
        dot = 3.0
        gp = (0.1, 0.0, 0.0)
        gd = (0.0, 0.5, 0.0)
        out = vacuum_momentum_source3(gamma, phi, dot, gp, gd)
        expect0 = (-gamma / 6.0) * (phi * gd[0] + dot * gp[0])
        self.assertAlmostEqual(out[0], expect0)

    def test_hypothesis_data_holds(self) -> None:
        d = OMaxwellFluidChartHypothesisData(
            phi_f_at_c=1.0,
            phi_fluid=1.0,
            dot_theta=0.5,
            delta_theta_prime_e_prime=0.5,
            grad_phi3=(0.0, 0.0, 0.0),
            chart_grad_phi3=(0.0, 0.0, 0.0),
            grad_dot3=(0.0, 0.0, 0.0),
            chart_grad_dot3=(0.0, 0.0, 0.0),
        )
        self.assertTrue(d.holds_algebraically())


if __name__ == "__main__":
    unittest.main()
