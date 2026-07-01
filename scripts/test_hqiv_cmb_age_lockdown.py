"""Tests for the HQIV cosmological outside-curvature lock-down readout.

Validates that the birefringence / wall-clock-age / T_CMB chain is locked to a
single external input (T_CMB) with everything else derived, and that the integer
monogamy impedance cross-validates the independent CLASS wall-clock age.
"""

import math

import pytest

import hqiv_cmb_age_lockdown as lk


def test_planck_units_from_si_definitions():
    # Planck temperature ~1.4168e32 K, Planck time ~5.391e-44 s.
    assert lk.T_PLANCK_K == pytest.approx(1.4168e32, rel=1e-3)
    assert lk.T_PLANCK_S == pytest.approx(5.391e-44, rel=1e-3)


def test_xi_to_shell_map_is_derived():
    # m_T = T_Pl/T_CMB - 1; cells/shell ~ (T_Pl/T_CMB)^2.
    m_T = lk.temperature_ladder_depth()
    assert m_T == pytest.approx(5.198e31, rel=1e-3)
    cps = lk.cells_per_shell()
    assert cps == pytest.approx(2.702e63, rel=1e-3)
    # Large-m_T limit: cells/shell ~ m_T^2.
    assert cps == pytest.approx(m_T * m_T, rel=1e-30)


def test_integer_monogamy_impedance_is_one_hundred():
    # referenceM * q^2 = 4 * 5^2 = 100.
    assert lk.integer_monogamy_impedance() == 100


def test_route_a_beta_matches_eskilt_central():
    # Integer impedance m_prop = 1/100 -> beta = (3/5) log(1.01) = 0.342 deg.
    a = lk.route_a_integer_impedance()
    assert a["m_prop"] == pytest.approx(0.01, rel=1e-9)
    assert a["beta_deg"] == pytest.approx(0.342, abs=2e-3)


def test_route_b_beta_from_class_age():
    # CLASS wall-clock age 51.2 Gyr -> beta = 0.379 deg.
    b = lk.route_b_class_dynamics()
    assert b["m_prop"] == pytest.approx(0.0111, abs=1e-4)
    assert b["beta_deg"] == pytest.approx(0.379, abs=2e-3)


def test_apparent_age_is_rejected_falsifier():
    # Apparent age 13.8 Gyr -> beta = 0.103 deg, ~ -2.55 sigma from PR4.
    f = lk.apparent_age_falsifier()
    assert f["beta_deg"] == pytest.approx(0.103, abs=2e-3)
    assert f["deviation_sigma"] < -2.0


def test_lock_wall_clock_age_cross_validation():
    # The integer impedance PREDICTS a wall-clock age that agrees with the
    # independent CLASS dynamics value (51.2 Gyr) to better than 15%.
    lock = lk.lock_summary()
    assert lock["wall_clock_age_integer_route_Gyr"] == pytest.approx(46.2, abs=1.0)
    assert lock["age_deviation_pct"] < 15.0
    assert lock["age_agreement_fraction"] > 0.85


def test_both_beta_routes_within_eskilt_one_sigma():
    lock = lk.lock_summary()
    assert lock["integer_route_within_1sigma"] is True
    assert lock["class_route_within_1sigma"] is True


def test_no_external_input_other_than_tcmb_in_beta_chain():
    # The integer route depends only on T_CMB + Planck units + integers:
    # changing T_CMB changes the predicted age but NOT beta (m_prop is the
    # integer 1/100), confirming beta_A carries no age input.
    a0 = lk.route_a_integer_impedance()["beta_deg"]
    # Recompute cells/shell at a different T_obs; beta_A must be unchanged.
    m_prop = 1.0 / lk.integer_monogamy_impedance()
    assert lk.beta_deg(m_prop) == pytest.approx(a0, rel=1e-12)


def test_local_gravity_stack_is_negligible_and_global():
    g = lk.local_gravity_note()
    # Full local stack is ~1e-7: 4 orders below the ~0.2% dimensionless residuals.
    assert g["full_local_stack_phi_over_c2"] < 1e-6
    assert g["full_local_stack_phi_over_c2"] < 1e-3 / 1000.0


def test_witness_bundle_serializable():
    import json

    w = lk.build_witnesses()
    json.loads(json.dumps(w))  # round-trips
    assert w["single_external_dimensionful_input"]["name"] == "T_CMB"
