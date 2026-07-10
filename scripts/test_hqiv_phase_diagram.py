#!/usr/bin/env python3
"""Tests for generalized HQIV phase diagram engine."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

_REPO = Path(__file__).resolve().parent.parent
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))
if str(_REPO / "scripts") not in sys.path:
    sys.path.insert(0, str(_REPO / "scripts"))

import hqiv_thermodynamic_phase_from_tp as tptp
from hqiv_lab.phase_diagram import (
    MixtureComponent,
    end_members_for_molecule,
    liquid_mixture_curvature_fraction,
    low_density_liquid_fraction,
    metastable_liquid_allowed,
    metastable_liquid_kinetic_floor_k,
    mixture_curvature_fraction,
    phase_diagram_point,
    supports_two_liquid_branch,
    tetrahedral_melt_density_ratio,
)
from hqiv_lab.coordination import IntermolecularMotif, infer_monomer_geometry
from hqiv_lab.spec import resolve_spec


class PhaseDiagramTests(unittest.TestCase):
    def test_end_members_ordered(self) -> None:
        low, high = end_members_for_molecule("H2O")
        self.assertLess(low.rho_curv, high.rho_curv)
        self.assertAlmostEqual(high.rho_curv, 1.0)

    def test_mixture_fraction_endpoints(self) -> None:
        rho_l = tetrahedral_melt_density_ratio(4)
        self.assertAlmostEqual(
            liquid_mixture_curvature_fraction(1.0, rho_l, 1.0),
            rho_l,
            places=6,
        )
        self.assertAlmostEqual(
            liquid_mixture_curvature_fraction(0.0, rho_l, 1.0),
            1.0,
            places=6,
        )

    def test_h2o_supports_two_liquid(self) -> None:
        mono = infer_monomer_geometry(resolve_spec("H2O"))
        self.assertTrue(supports_two_liquid_branch(mono.motif))
        self.assertFalse(supports_two_liquid_branch(IntermolecularMotif.APOLAR_CLOSE_PACK))

    def test_metastable_liquid_at_supercooled_high_p(self) -> None:
        mat = tptp.material_scales_bulk_h2o()
        t_melt, _ = tptp.characteristic_temperatures_K(mat)
        floor = metastable_liquid_kinetic_floor_k(t_melt)
        self.assertGreater(floor, 50.0)
        self.assertLess(floor, 150.0)
        env = tptp.ThermodynamicEnvironment(200.0, 1250.0 * tptp.STP_PRESSURE_PA)
        state = tptp.derive_phase(env, mat)
        self.assertEqual(state.phase, tptp.DerivedPhase.METASTABLE_LIQUID)

    def test_low_density_fraction_pressure_tilt(self) -> None:
        mat = tptp.material_scales_bulk_h2o()
        f_low_p = low_density_liquid_fraction(200.0, tptp.STP_PRESSURE_PA, mat)
        f_high_p = low_density_liquid_fraction(200.0, 1250.0 * tptp.STP_PRESSURE_PA, mat)
        self.assertGreater(f_low_p, f_high_p)

    def test_phase_diagram_point_h2o_cytosol(self) -> None:
        pt = phase_diagram_point("H2O", temperature_k=310.15)
        self.assertEqual(pt.derived_phase, "liquid")
        self.assertAlmostEqual(pt.rho_curv, 1.0, places=3)

    def test_mixture_readout(self) -> None:
        mix = (MixtureComponent("H2O", 0.8), MixtureComponent("CH3OH", 0.2))
        rho = mixture_curvature_fraction(mix, temperature_k=310.15, pressure_pa=tptp.STP_PRESSURE_PA)
        self.assertGreater(rho, 0.0)
        self.assertLessEqual(rho, 1.0)
        pt = phase_diagram_point(mix, temperature_k=310.15)
        self.assertIn(pt.derived_phase, ("liquid", "metastable_liquid"))

    def test_low_density_fraction_self_consistent(self) -> None:
        from hqiv_lab.phase_diagram import (
            _boltzmann_f_ldl,
            cohesive_delta_ev_bare,
            cohesive_delta_ev_dressed,
            end_members_for_molecule,
            liquid_branch_free_energy_ev,
            low_density_free_energy_minimum,
            outside_curvature_mixture_dress,
            ldl_hdl_conversion_barrier_ev_per_contact,
            mixture_latent_barrier_factor,
        )

        mat = tptp.material_scales_bulk_h2o()
        low, high = end_members_for_molecule("H2O")
        f = low_density_liquid_fraction(220.0, tptp.STP_PRESSURE_PA, mat)
        rho = liquid_mixture_curvature_fraction(f, low.rho_curv, high.rho_curv)
        delta_bare = cohesive_delta_ev_bare(220.0, tptp.STP_PRESSURE_PA, mat)
        delta_dressed = cohesive_delta_ev_dressed(
            220.0, tptp.STP_PRESSURE_PA, mat, rho, molecule="H2O"
        )
        self.assertLess(delta_dressed, delta_bare)
        b_hom, geff, fb = outside_curvature_mixture_dress(rho, mat.contact_xi, "H2O")
        self.assertLess(b_hom, 1.0)
        self.assertLess(fb, 0.0)
        self.assertNotAlmostEqual(f, _boltzmann_f_ldl(delta_bare, 8.617333262e-11 * 220.0), places=3)
        mix = mixture_latent_barrier_factor(f)
        self.assertGreater(mix, 0.0)
        l_branch = ldl_hdl_conversion_barrier_ev_per_contact("H2O", mat)
        self.assertGreater(l_branch, abs(delta_bare))
        minimum = low_density_free_energy_minimum(220.0, tptp.STP_PRESSURE_PA, mat)
        e_min = minimum["free_energy_ev"]
        self.assertLessEqual(e_min, liquid_branch_free_energy_ev(0.0, 220.0, tptp.STP_PRESSURE_PA, mat))
        self.assertLessEqual(e_min, liquid_branch_free_energy_ev(1.0, 220.0, tptp.STP_PRESSURE_PA, mat))
        self.assertGreater(minimum["free_energy_curvature_ev"], 0.0)

    def test_latent_barrier_mixed_state_shape(self) -> None:
        from hqiv_lab.phase_diagram import mixture_latent_barrier_factor

        self.assertAlmostEqual(mixture_latent_barrier_factor(0.0), 0.0)
        self.assertAlmostEqual(mixture_latent_barrier_factor(1.0), 0.0)
        self.assertGreater(mixture_latent_barrier_factor(0.5), mixture_latent_barrier_factor(0.1))

    def test_nucleation_defect_raises_local_f_ldl(self) -> None:
        mat = tptp.material_scales_bulk_h2o()
        f_base = low_density_liquid_fraction(220.0, tptp.STP_PRESSURE_PA, mat)
        f_defect = low_density_liquid_fraction(
            220.0,
            tptp.STP_PRESSURE_PA,
            mat,
            local_coordination_excess=0.25,
        )
        self.assertGreater(f_defect, f_base)

    def test_hoh_angle_mixture_endpoints(self) -> None:
        from hqiv_lab.phase_diagram import (
            hoh_angle_dynamic_gas_deg,
            hoh_angle_mixture_deg,
            hoh_angle_tetrahedral_deg,
            HOH_ANGLE_GAS_REFERENCE_DEG,
        )

        self.assertAlmostEqual(hoh_angle_tetrahedral_deg(), 109.4712, places=3)
        self.assertAlmostEqual(hoh_angle_mixture_deg(1.0), hoh_angle_tetrahedral_deg(), places=4)
        self.assertAlmostEqual(hoh_angle_mixture_deg(0.0), hoh_angle_dynamic_gas_deg(), places=4)
        # Comparison quarantine: refined torque-tree denominator lands inside experimental band.
        self.assertLess(
            abs(hoh_angle_dynamic_gas_deg() - HOH_ANGLE_GAS_REFERENCE_DEG),
            0.01,
        )
        from hqiv_lab.phase_diagram import WATER_HOH_ANGLE_OBSERVATIONS

        primary = next(o for o in WATER_HOH_ANGLE_OBSERVATIONS if o.get("primary_comparison"))
        self.assertAlmostEqual(primary["theta_deg"], HOH_ANGLE_GAS_REFERENCE_DEG, places=3)

    def test_widom_proxy_peak_supercooled(self) -> None:
        from hqiv_lab.phase_diagram import (
            material_scales_for_spec,
            widom_second_order_window_center_k,
            widom_second_order_window_weight,
            widom_line_compressibility_proxy,
            widom_proxy_peak_at_pressure,
        )
        from hqiv_lab.spec import resolve_spec

        mat = material_scales_for_spec(resolve_spec("H2O"), bulk=True)
        t_melt, _ = tptp.characteristic_temperatures_K(mat)
        center = widom_second_order_window_center_k(t_melt)
        self.assertGreater(center, 220.0)
        self.assertLess(center, 235.0)
        self.assertGreater(
            widom_second_order_window_weight(center, t_melt),
            widom_second_order_window_weight(150.0, t_melt),
        )
        v_310 = widom_line_compressibility_proxy(310.15, tptp.STP_PRESSURE_PA, mat)
        v_200 = widom_line_compressibility_proxy(200.0, tptp.STP_PRESSURE_PA, mat)
        self.assertGreater(v_200, v_310)
        peak = widom_proxy_peak_at_pressure(mat, tptp.STP_PRESSURE_PA)
        self.assertGreater(peak["compressibility_proxy"], 0.0)
        self.assertGreaterEqual(peak["temperature_K"], 150.0)
        self.assertLess(peak["temperature_K"], 280.0)


if __name__ == "__main__":
    unittest.main()
