#!/usr/bin/env python3
"""κ₆ feedback from phase curvature (ρ_geom + solid n)."""

from __future__ import annotations

import hqiv_phase_geometry_density as pgd
import hqiv_thermodynamic_phase_from_tp as tptp


def test_optical_curvature_zero_at_unity_n() -> None:
    assert pgd.optical_curvature_density_fraction(1.0) == 0.0


def test_phase_curvature_dresses_geometry_with_n() -> None:
    rho_geom = 0.876
    n = 1.28
    rho_kappa = pgd.phase_curvature_density_fraction(rho_geom, n)
    assert rho_kappa > rho_geom
    assert rho_kappa <= 1.0


def test_kappa6_feedback_matches_melt_readout_h2o() -> None:
    out = pgd.melt_readout_with_phase_geometry("H2O", allotrope="Ih")
    mat = tptp.material_scales_bulk_h2o()
    fb_direct = pgd.kappa6_feedback_from_phase_curvature(
        mat.contact_xi,
        out["curvature_density_fraction"],
        out["refractive_index_solid"],
    )
    assert abs(fb_direct - out["kappa6_feedback"]) < 1e-9
    assert out["phase_curvature_density_fraction"] == tptp.resolved_medium_density_fraction(mat)


def test_species_kappa6_feedback_differs_by_n() -> None:
    h2o = pgd.melt_readout_with_phase_geometry("H2O")
    ch4 = pgd.melt_readout_with_phase_geometry("CH4", temperature_at_melt_k=90.0)
    assert ch4["T_sl_at_pressure_K"] < h2o["T_sl_at_pressure_K"] - 50.0


if __name__ == "__main__":
    test_optical_curvature_zero_at_unity_n()
    test_phase_curvature_dresses_geometry_with_n()
    test_kappa6_feedback_matches_melt_readout_h2o()
    test_species_kappa6_feedback_differs_by_n()
    print("test_hqiv_phase_curvature_kappa6: OK")
