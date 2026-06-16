"""Variational crust torque + environment η alignment tests."""

from __future__ import annotations

import math
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_compact_object_mass import (  # noqa: E402
    aligning_b_for_torque_t,
    aligning_torque_enhancement_factor,
    breakup_omega_rad_s,
    charmed_baryon_hep_decay_readout,
    coefficient_calibration_witness,
    compact_object_shear_coupling,
    crust_jxb_aligning_torque_n_m,
    crust_misalign_torque_from_accelerations_si,
    crust_misalign_torque_from_stress_div_si,
    crust_shear_torque_si,
    induction_resistivity_eta_from_environment,
    pair_production_witness,
    quantify_spindown_charm_retreat_feedback,
    nicer_j0030_surface_multipole_witness,
    nicer_j0740_surface_multipole_witness,
    zonal_multipole_coefficients,
    radius_uniform_density,
    slip_torque_balance_for_star,
    NS_SURFACE_T_K,
    RHO_CRUST_KG_M3,
    RHO_NUCLEAR_KG_M3,
    H_CRUST_TORQUE_M,
    M_SUN_KG,
)


def test_shear_coupling_and_torque_paths_agree() -> None:
    a_grav = 1.0e12
    a_lt = 1.0e6
    a_par = 1.0e4
    chi = compact_object_shear_coupling(a_lt, a_par, a_grav)
    radius = 1.0e4
    col = math.radians(55.0)
    tau_div = crust_misalign_torque_from_stress_div_si(
        radius,
        a_grav,
        chi,
        col,
        rho_crust_kg_m3=RHO_CRUST_KG_M3,
        h_crust_m=H_CRUST_TORQUE_M,
        rho_nuclear_kg_m3=RHO_NUCLEAR_KG_M3,
    )
    tau_acc = crust_misalign_torque_from_accelerations_si(
        radius, a_grav, a_lt, a_par, col,
    )
    tau_legacy = crust_shear_torque_si(
        1.0, radius, chi, a_grav, col,
    )
    assert tau_div == tau_acc
    assert tau_div == tau_legacy


def test_induction_eta_positive_and_slip_row_fields() -> None:
    eta_slow = induction_resistivity_eta_from_environment(0.2, 1.0e5)
    assert eta_slow > 0.0
    row = slip_torque_balance_for_star(1.4, 640.0, "test ms")
    assert row.eta_induction > 0.0
    assert row.tau_misalign_variational_n_m == row.tau_misalign_n_m
    assert row.outside_temperature_effective_K > NS_SURFACE_T_K
    assert row.beta_spin_over_c > 0.1
    assert row.cmb_doppler_boost > 1.0
    assert row.B_align_t >= row.B_eff_t
    assert row.aligning_enhancement_factor > 1.0
    assert row.tau_align_enhanced_n_m > row.tau_align_b_eff_n_m
    assert row.torque_ratio_aligning_enhanced < row.torque_ratio_b_eff


def test_aligning_torque_helpers_and_ms_closes_enhanced() -> None:
    b_align = aligning_b_for_torque_t(1.0e8, 1.0e5, 1.0e4, 3.0e6, 1.0e3)
    assert b_align > 1.0e8
    enhance = aligning_torque_enhancement_factor(0.1, 0.98)
    assert enhance > 2.0
    tau_jxb = crust_jxb_aligning_torque_n_m(
        1.0e4, 1.0e8, 2.0 * math.pi * 640.0, 1.0e4, 1.0e6, 1.0e12, 0.98,
    )
    assert tau_jxb > 0.0
    row = slip_torque_balance_for_star(1.4, 640.0, "ms enhanced close")
    assert row.closes_with_aligning_enhanced
    assert row.alpha_equilibrium_aligning_enhanced_deg < 90.0


def test_coefficient_calibration_witness_discharge() -> None:
    cal = coefficient_calibration_witness()
    assert cal["eta_ns_surface_spin_boosted"] > 0.0
    assert len(cal["calibration_grid"]) > 0
    mid_sigma = cal["tau_ohm_yr_at_sigma_stellar_radius"]["sigma_1000000000"]
    assert 1.0e3 < mid_sigma < 1.0e6
    assert mid_sigma > 5.0e3  # within one dex of literature τ_ohm lower bound


def test_spin_boosts_eta_vs_static_surface() -> None:
    r = 1.0e4
    omega_ms = 2.0 * math.pi * 640.0
    eta_static = induction_resistivity_eta_from_environment(0.2, NS_SURFACE_T_K)
    eta_spin = induction_resistivity_eta_from_environment(
        0.2,
        NS_SURFACE_T_K,
        omega_rad_s=omega_ms,
        radius_m=r,
        colatitude_rad=math.radians(55.0),
    )
    assert eta_spin > eta_static


def test_pair_cascade_at_high_spin() -> None:
    mass_kg = 1.98 * M_SUN_KG
    r = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    om_break = breakup_omega_rad_s(mass_kg, r)
    row = slip_torque_balance_for_star(
        1.98,
        om_break / (2.0 * math.pi),
        "breakup pair test",
        B_surface_t=1.0e8,
    )
    assert row.omega_over_breakup > 0.99
    assert row.pair_cascade_scatters >= 1


def test_pair_witness_direct_subthreshold_ms() -> None:
    pair = pair_production_witness(1.0e5, 0.2, 0.3, 1.0e8)
    assert float(pair["pair_production_margin_direct"]) < 1.0


def test_spindown_charm_retreat_feedback() -> None:
    report = quantify_spindown_charm_retreat_feedback(1.98, omega_end_fraction=0.5)
    before = report["before"]
    after = report["after"]
    assert before["r_charm_m"] >= after["r_charm_m"]
    assert before["epsilon_surface"] >= after["epsilon_surface"]
    assert report["delta_mass_from_spin_kg"] > 0.0
    assert report["delta_mass_from_charm_weak_kg"] > 0.0
    assert report["delta_mass_total_kg"] > report["delta_mass_from_spin_kg"]
    assert report["delta_charm_shell_mass_kg"] >= 0.0
    assert report["charm_to_nuclear_phase_mass_kg"] <= 0.0
    assert report["B_charm_before_t"] >= report["B_charm_after_t"]
    assert report["B_transition_from_retreat_t"] >= 0.0
    assert "hep_decay_readout" in report
    hep = report["hep_decay_readout"]
    assert float(hep["width_per_s_effective"]) > 0.0
    assert float(hep["dominant_q_mev"]) > 0.0
    assert report["B_transition_schematic_t"] > 0.0
    assert report["B_transition_from_retreat_t"] > 0.0


def test_charmed_baryon_hep_decay_readout() -> None:
    readout = charmed_baryon_hep_decay_readout()
    assert readout["species_id"] == "lambda_c"
    assert float(readout["width_per_s_ns"]) > 0.0
    assert float(readout["ledger_coupling"]) > 0.0


def test_surface_multipole_j0030() -> None:
    nicer = nicer_j0030_surface_multipole_witness()
    verdict = nicer["verdict"]
    assert isinstance(verdict, list)
    assert "quadrupole_present" in verdict
    assert "m1_from_tau_mis" in verdict
    assert nicer["hqiv_emission_l2_over_l0"] > 0.0
    qc = nicer["quantitative_comparison"]
    assert qc["m1_azimuthal_fraction"] > 0.01
    assert qc["longitude_separation_deg"] is not None
    coeffs = zonal_multipole_coefficients([1.0, 0.5, 0.0], [1.0, 0.5, 0.0], [0.0, 0.5, 1.0])
    assert coeffs[0] > 0.0


def test_surface_multipole_j0740() -> None:
    nicer = nicer_j0740_surface_multipole_witness()
    qc = nicer["quantitative_comparison"]
    assert qc["m1_azimuthal_fraction"] > 0.01
    assert float(qc["azimuthal_offset_from_antipode_deg"]) >= 25.0
    assert qc["hqiv_exceeds_antipodal_offset_threshold"]
    assert "non_antipodal_like_nicer" in nicer["verdict"]


if __name__ == "__main__":
    test_shear_coupling_and_torque_paths_agree()
    test_induction_eta_positive_and_slip_row_fields()
    test_aligning_torque_helpers_and_ms_closes_enhanced()
    test_coefficient_calibration_witness_discharge()
    test_spin_boosts_eta_vs_static_surface()
    test_pair_cascade_at_high_spin()
    test_pair_witness_direct_subthreshold_ms()
    test_spindown_charm_retreat_feedback()
    test_charmed_baryon_hep_decay_readout()
    test_surface_multipole_j0030()
    test_surface_multipole_j0740()
    print("ok")
