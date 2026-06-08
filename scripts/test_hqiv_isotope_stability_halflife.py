#!/usr/bin/env python3
"""Tests for HQIV isotope stability and half-life readout."""

from __future__ import annotations

import math

import hqiv_dynamic_nucleon_pn as pn
import hqiv_dynamic_beta_isotope as dbi
import hqiv_isotope_stability_halflife as ish


def test_parse_p120_defaults_to_proton_count_120() -> None:
    A, Z, label = ish.parse_isotope_label("P120")
    assert A == 240
    assert Z == 120
    assert label == "P120"


def test_free_neutron_endpoint_q_matches_mass_gap_minus_electron() -> None:
    row = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True)
    assert row.beta_minus_endpoint_q_mev is not None
    assert abs(row.beta_minus_endpoint_q_mev - 0.782) < 0.01
    assert row.neutron_excess_drive_mev == 0.0


def test_free_neutron_has_active_beta_minus() -> None:
    row = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True)
    assert row.active_channel == "beta_minus"
    assert not row.dynamically_stable
    assert row.half_life_seconds is not None
    assert row.half_life_seconds > 0.0


def test_qualified_neutron_half_life_near_experiment() -> None:
    row = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True, lab_temperature_K=300.0)
    assert row.half_life_seconds is not None
    ratio = row.half_life_seconds / 879.4
    assert 0.75 <= ratio <= 1.15


def test_tritium_half_life_uses_valence_partner_well() -> None:
    """T width well sits between symmetric cluster/A and full partner cluster/(A−1)."""
    env = pn.caustic_environment_for_A(3)
    total = pn.cluster_caustic_total_mev(3)
    pair = pn.pn_pair_readout(env)
    width_well = dbi.beta_width_well_depth_mev(
        3,
        1,
        cluster_total_mev=total,
        proton_mass_mev=pair.proton.mass_mev,
        neutron_mass_mev=pair.neutron.mass_mev,
    )
    assert env.well_depth_mev < width_well < total / 2.0


def test_tritium_half_life_near_reference_ballpark() -> None:
    n = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True)
    t = ish.stability_readout(
        3, 1, label="T", em_tipping_qualified=True, molecular_host=""
    )
    assert n.half_life_seconds is not None
    assert t.half_life_seconds is not None
    assert t.half_life_seconds > n.half_life_seconds * 1000.0
    ref_seconds = 12.32 * 365.25 * 24.0 * 3600.0
    ratio = t.half_life_seconds / ref_seconds
    assert 0.75 <= ratio <= 1.25


def test_geometry_factor_is_unity_for_free_neutron() -> None:
    assert dbi.beta_geometry_width_factor(1, residual_mev=0.293, well_depth_mev=0.0, bonded=False) == 1.0


def test_geometry_factor_suppresses_bonded_cluster() -> None:
    free = dbi.beta_geometry_width_factor(1, residual_mev=0.293, well_depth_mev=3.5, bonded=False)
    bonded = dbi.beta_geometry_width_factor(3, residual_mev=0.293, well_depth_mev=3.5, bonded=True)
    assert free == 1.0
    assert bonded < 1.0e-4


def test_he4_is_only_structurally_shielded_without_em_tipping() -> None:
    row = ish.stability_readout(4, 2, label="He4")
    assert row.structurally_shielded
    assert not row.em_tipping_qualified
    assert not row.dynamically_stable
    assert row.half_life_seconds is None
    assert row.beta_minus_endpoint_q_mev is None


def test_he4_stable_after_em_tipping_qualified() -> None:
    row = ish.stability_readout(4, 2, label="He4", em_tipping_qualified=True)
    assert row.dynamically_stable
    assert row.half_life_seconds is None


def test_p120_candidate_reports_stability() -> None:
    row = ish.stability_readout(240, 120, label="P120")
    assert row.A == 240
    assert row.Z == 120
    assert row.N == 120
    assert row.structurally_shielded
    assert not row.dynamically_stable
    assert row.half_life_seconds is None or math.isfinite(row.half_life_seconds)


def test_weak_beta_half_life_requires_positive_endpoint_q() -> None:
    closed = dbi.weak_beta_half_life_seconds(-0.1, 0.293)
    open_ = dbi.weak_beta_half_life_seconds(0.782, 0.293)
    assert math.isinf(closed)
    assert open_ < math.inf


def test_lab_temperature_changes_half_life_factor() -> None:
    cmb = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True, lab_temperature_K=ish.CMB_TEMPERATURE_K)
    room = ish.stability_readout(1, 0, label="n", em_tipping_qualified=True, lab_temperature_K=300.0)
    assert room.half_life_seconds is not None
    assert cmb.half_life_seconds is not None
    assert room.half_life_seconds < cmb.half_life_seconds
    assert ish.lab_outside_curvature_lifetime_factor(300.0) < 1.0


def test_neutrino_mass_increases_half_life() -> None:
    massless = dbi.weak_beta_half_life_seconds(0.782, 0.293, neutrino_mass_mev=0.0)
    massive = dbi.weak_beta_half_life_seconds(
        0.782, 0.293, neutrino_mass_mev=ish.model_electron_neutrino_mass_mev()
    )
    assert massive > massless


def test_weak_fano_hopf_bridge_increases_half_life() -> None:
    no_bridge = dbi.weak_beta_half_life_seconds(0.782, 0.293, weak_bridge_energy_mev=0.0)
    with_bridge = dbi.weak_beta_half_life_seconds(0.782, 0.293, weak_bridge_energy_mev=1.0e-6)
    assert with_bridge > no_bridge


if __name__ == "__main__":
    test_parse_p120_defaults_to_proton_count_120()
    test_free_neutron_endpoint_q_matches_mass_gap_minus_electron()
    test_free_neutron_has_active_beta_minus()
    test_qualified_neutron_half_life_near_experiment()
    test_tritium_half_life_uses_valence_partner_well()
    test_tritium_half_life_near_reference_ballpark()
    test_geometry_factor_is_unity_for_free_neutron()
    test_geometry_factor_suppresses_bonded_cluster()
    test_he4_is_only_structurally_shielded_without_em_tipping()
    test_he4_stable_after_em_tipping_qualified()
    test_p120_candidate_reports_stability()
    test_weak_beta_half_life_requires_positive_endpoint_q()
    test_lab_temperature_changes_half_life_factor()
    test_neutrino_mass_increases_half_life()
    test_weak_fano_hopf_bridge_increases_half_life()
    print("test_hqiv_isotope_stability_halflife: OK")
