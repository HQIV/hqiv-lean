"""Tests for scripts/fluid_f2_chart_alignment.py (F2 vacuum source mirror)."""

import unittest

from fluid_f2_chart_alignment import (
    ActionMinedForcePointData,
    OMaxwellFluidChartHypothesisData,
    SSTTransportPointData,
    action_mined_force3,
    add_action_mined_forces3,
    add_longitudinal_force3,
    chart_spatial_phi_gradient,
    dynamic_bradshaw_from_equilibrium,
    dynamic_bradshaw_from_stress,
    hqiv_inertia_factor,
    longitudinal_stress_force3,
    longitudinal_stress_tensor3,
    sst_k_residual,
    sst_omega_residual,
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

    def test_longitudinal_stress_tensor_is_directional_outer_product(self) -> None:
        tensor = longitudinal_stress_tensor3(
            kappa_l=0.5,
            density=2.0,
            coupling_log=3.0,
            grad_phi_along=4.0,
            direction=(1.0, 2.0, 0.0),
        )
        coeff = 0.5 * 2.0 * 3.0 * 4.0
        self.assertEqual(
            tensor,
            (
                (coeff, 2.0 * coeff, 0.0),
                (2.0 * coeff, 4.0 * coeff, 0.0),
                (0.0, 0.0, 0.0),
            ),
        )

    def test_longitudinal_force_adds_to_rhs(self) -> None:
        div_tau = longitudinal_stress_force3((0.1, -0.2, 0.0))
        self.assertEqual(div_tau, (0.1, -0.2, 0.0))
        self.assertEqual(add_longitudinal_force3((1.0, 2.0, 3.0), div_tau), (1.1, 1.8, 3.0))

    def test_action_mined_force_bundle_sums_slots(self) -> None:
        force = action_mined_force3(
            longitudinal_stress_divergence=(1.0, 0.0, 0.0),
            field_stress_divergence=(0.0, 2.0, 0.0),
            metric_phi_force=(0.0, 0.0, 3.0),
            plaquette_force=(0.5, 0.5, 0.5),
            current_coherence_force=(-0.5, 1.0, -1.0),
        )
        self.assertEqual(force, (1.0, 3.5, 2.5))

    def test_action_mined_force_adds_to_rhs(self) -> None:
        data = ActionMinedForcePointData(
            longitudinal_stress_divergence=(0.1, 0.0, 0.0),
            field_stress_divergence=(0.0, 0.2, 0.0),
            metric_phi_force=(0.0, 0.0, 0.3),
            plaquette_force=(0.0, 0.0, 0.0),
            current_coherence_force=(0.4, 0.0, -0.1),
        )
        self.assertEqual(data.force(), (0.5, 0.2, 0.19999999999999998))
        self.assertEqual(add_action_mined_forces3((1.0, 1.0, 1.0), data), (1.5, 1.2, 1.2))

    def test_sst_residuals_include_lapse_inertia_and_action_sources(self) -> None:
        inertia = hqiv_inertia_factor(a_loc=2.0, phi=3.0)
        data = SSTTransportPointData(
            lapse=1.5,
            rho=4.0,
            inertia_factor=inertia,
            k=2.0,
            omega=5.0,
            action_stress_norm=1.2,
            strain_norm=10.0,
            beta_star=0.09,
            bradshaw_min=0.0,
            bradshaw_max=1.0,
            k_dot=0.2,
            omega_dot=0.3,
            convective_k=0.4,
            convective_omega=0.5,
            production_k=2.0,
            destruction_k=0.7,
            diffusion_k=0.1,
            production_omega=3.0,
            destruction_omega=1.0,
            diffusion_omega=0.2,
            cross_diffusion_omega=0.05,
            action_k_source=0.25,
            action_omega_source=0.5,
        )
        self.assertAlmostEqual(
            sst_k_residual(data),
            1.5 * 4.0 * inertia * (0.2 + 0.4) - (2.0 - 0.7 + 0.1 + 0.25),
        )
        self.assertAlmostEqual(
            sst_omega_residual(data),
            1.5 * 4.0 * inertia * (0.3 + 0.5) - (3.0 - 1.0 + 0.2 + 0.05 + 0.5),
        )

    def test_dynamic_bradshaw_coefficients(self) -> None:
        self.assertAlmostEqual(
            dynamic_bradshaw_from_stress(
                density=2.0,
                k=4.0,
                action_stress_norm=2.48,
                lo=0.0,
                hi=1.0,
            ),
            0.31,
        )
        self.assertEqual(
            dynamic_bradshaw_from_stress(
                density=1.0,
                k=1.0,
                action_stress_norm=5.0,
                lo=0.0,
                hi=0.5,
            ),
            0.5,
        )
        self.assertAlmostEqual(
            dynamic_bradshaw_from_equilibrium(
                density=2.0,
                k=4.0,
                omega=10.0,
                beta_star=0.09,
                strain_norm=2.0,
                action_k_source=2.24,
                lo=0.0,
                hi=1.0,
            ),
            0.31,
        )

    def test_sst_data_exposes_dynamic_bradshaw(self) -> None:
        data = SSTTransportPointData(
            lapse=1.0,
            rho=2.0,
            inertia_factor=1.0,
            k=4.0,
            omega=10.0,
            action_stress_norm=2.48,
            strain_norm=2.0,
            beta_star=0.09,
            bradshaw_min=0.0,
            bradshaw_max=1.0,
            k_dot=0.0,
            omega_dot=0.0,
            convective_k=0.0,
            convective_omega=0.0,
            production_k=0.0,
            destruction_k=0.0,
            diffusion_k=0.0,
            production_omega=0.0,
            destruction_omega=0.0,
            diffusion_omega=0.0,
            cross_diffusion_omega=0.0,
            action_k_source=2.24,
            action_omega_source=0.0,
        )
        self.assertAlmostEqual(data.dynamic_bradshaw_stress(), 0.31)
        self.assertAlmostEqual(data.dynamic_bradshaw_equilibrium(), 0.31)


if __name__ == "__main__":
    unittest.main()
