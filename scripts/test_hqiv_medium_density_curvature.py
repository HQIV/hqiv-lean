#!/usr/bin/env python3
"""Medium-density scaling for κ₆ second-order curvature."""

from __future__ import annotations

import hqiv_dynamic_binding_chart as chart
import hqiv_curvature_contact_network as ccn
import hqiv_lean_physics_primitives as lean
import hqiv_thermodynamic_phase_from_tp as tptp


def test_density_scaling_recovers_dilute_at_zero() -> None:
    xi = lean.xi_from_compton_triplet((4, 3, 1))
    fb2 = lean.dynamic_binding_curvature_feedback_second_order_at_xi(xi)
    assert lean.curvature_second_order_scaled_for_medium_density(xi, 0.0) == 1.0
    assert (
        lean.curvature_second_order_scaled_for_medium_density(xi, 1.0) == fb2
    )


def test_bulk_h2o_melt_uses_phase_curvature_with_n() -> None:
    mat = tptp.material_scales_bulk_h2o()
    rho_kappa = tptp.resolved_medium_density_fraction(mat)
    assert mat.refractive_index_solid is not None
    assert mat.refractive_index_solid > 1.0
    assert 0.85 <= rho_kappa <= 1.0
    t_sl = tptp.solid_liquid_transition_temperature_K(mat)
    assert 270.0 <= t_sl <= 276.0


def test_gmtkn_h2o_network_density_partial() -> None:
    bench = next(b for b in chart.GMTKN55_SUITE if b.name == "H2O")
    net = ccn.build_network_from_molecule(bench.name, bench.fragments, bench.bonds)
    rho = ccn.medium_density_fraction_from_network(net)
    assert rho == 0.25  # 1 steric point / 4 ice reference


if __name__ == "__main__":
    test_density_scaling_recovers_dilute_at_zero()
    test_bulk_h2o_melt_uses_phase_curvature_with_n()
    test_gmtkn_h2o_network_density_partial()
    print("test_hqiv_medium_density_curvature: OK")
