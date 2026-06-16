#!/usr/bin/env python3
"""Tests for proton inner/outside mass decomposition and lab environment slots."""

from __future__ import annotations

import hqiv_proton_mass_decomposition as pmd
import hqiv_nuclear_outside_temperature_dynamics as notd


def test_outside_increment_zero_at_lockin_neutral() -> None:
    env = notd.LabOutsideEnvironment(
        lab_xi=notd.XI_LOCKIN,
        gravity_tier="none",
        cmb_dipole_velocity_m_s=0.0,
    )
    row = pmd.proton_mass_decomposition(env)
    assert abs(row.outside_total_increment_mev) < 1e-12
    assert abs(row.observed_dynamic_mev - row.inner_raw_mev) < 1e-9


def test_lab_slots_ppm_budget_ordering() -> None:
    block = pmd.witness_decomposition_block(gravity_tier="full")
    ppm = block["slot_ppm_budget"]
    assert abs(ppm["temperature_support_vs_cmb_ppm"]) > 100.0
    assert abs(ppm["gravity_geff_ppm_on_trace"]) < 1.0
    assert 0.0 < abs(ppm["cmb_dipole_kinetic_ppm_on_trace"]) < 1.0
    assert abs(ppm["combined_hadronic_chart_ppm"]) < 1.0
    assert block["xi_chart"]["xi_cmb_monopole"] > block["xi_chart"]["xi_lab_room_300K"]


def test_bbn_cosmic_modulator_weakens_free_branch() -> None:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    env = notd.LabOutsideEnvironment(
        lab_xi=bbn_xi,
        gravity_tier="none",
        cmb_dipole_velocity_m_s=0.0,
    )
    assert env.lab_modulator() < env.anchor_modulator()


def test_lab_environment_combined_phi_includes_dipole() -> None:
    env = notd.LabOutsideEnvironment(gravity_tier="full")
    assert env.combined_phi_epsilon > env.gravity_phi_epsilon
    assert env.cmb_proper_motion_v_over_c > 1.0e-3


if __name__ == "__main__":
    test_outside_increment_zero_at_lockin_neutral()
    test_lab_slots_ppm_budget_ordering()
    test_bbn_cosmic_modulator_weakens_free_branch()
    test_lab_environment_combined_phi_includes_dipole()
    print("test_hqiv_proton_mass_decomposition: OK")
