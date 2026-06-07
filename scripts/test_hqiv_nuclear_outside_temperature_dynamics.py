#!/usr/bin/env python3
"""Tests for outside-curvature temperature dynamics and β± slots."""

from __future__ import annotations

import hqiv_nuclear_caustic_binding as ncb
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_outside_temperature_dynamics as notd

REFERENCE_M = notd.REFERENCE_M
XI_LOCKIN = notd.XI_LOCKIN


def test_lockin_modulator_is_unity() -> None:
    assert notd.outside_curvature_binding_modulator(XI_LOCKIN, bonded=True) == 1.0
    assert notd.outside_curvature_binding_modulator(XI_LOCKIN, bonded=False) == 1.0


def test_bbn_temperature_weakens_outside_modulator() -> None:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    bonded = notd.outside_curvature_binding_modulator(bbn_xi, bonded=True)
    free = notd.outside_curvature_binding_modulator(bbn_xi, bonded=False)
    assert bonded < 1.0
    assert free < bonded


def test_lockin_structural_binding_unchanged() -> None:
    m = REFERENCE_M
    A = 2
    m_c = ncur.nucleus_curvature_shell(A)
    structural, _, out_struct, _ = ncb.nuclear_cluster_binding_mev(m, A, m_cluster=m_c)
    dynamic, _, out_dyn, _, _ = notd.nuclear_cluster_binding_at_xi(
        m, A, m_cluster=m_c, xi=XI_LOCKIN, bonded=True
    )
    assert abs(structural - dynamic) < 1e-9
    assert abs(out_struct - out_dyn) < 1e-9


def test_free_beta_minus_overlap_has_curvature_deficit() -> None:
    bbn_xi = notd.xi_from_T_MeV(0.1)
    readout = notd.beta_decay_readout("beta_minus", xi=bbn_xi, bonded=False)
    assert readout.overlap_mev >= notd.NUCLEON_ISOSPIN_GAP_MEV
    assert readout.outside_modulator < 1.0


def test_bonded_beta_minus_stable_in_well() -> None:
    readout = notd.beta_decay_readout(
        "beta_minus", xi=XI_LOCKIN, bonded=True, well_depth_mev=5.0
    )
    assert readout.stable_bonded


def test_he4_lockin_report() -> None:
    rep = notd.lockin_binding_report(4)
    assert rep["lockin_total_mev"] > rep["bbn_total_mev"]
    print("lockin He4:", rep)


def test_earth_surface_phi_epsilon_order_of_magnitude() -> None:
    assert 6e-10 < notd.earth_surface_phi_epsilon() < 8e-10


def test_solar_and_galactic_phi_epsilon_order() -> None:
    earth = notd.earth_surface_phi_epsilon()
    sun = notd.solar_phi_epsilon_at_distance()
    galaxy = notd.galactic_circular_phi_epsilon()
    assert sun > 10 * earth
    assert galaxy > 10 * sun


def test_local_lab_gravity_binding_stack_full() -> None:
    stack = notd.local_lab_gravity_binding_stack("full")
    assert abs(stack.total - (stack.earth + stack.sun + stack.galaxy)) < 1e-20
    assert stack.galaxy > stack.sun > stack.earth


def test_outside_gravity_geff_modulator_earth_bump() -> None:
    eps = notd.local_lab_gravity_phi_epsilon("full")
    factor = notd.outside_gravity_geff_modulator(eps)
    assert factor > 1.0
    assert factor < 1.0 + 2e-7


def test_combined_outside_support_includes_gravity() -> None:
    full_eps = notd.local_lab_gravity_phi_epsilon("full")
    earth_eps = notd.local_lab_gravity_phi_epsilon("earth")
    none = notd.lab_outside_support_lifetime_factor(
        300.0, phi_gravity_epsilon=0.0, reference_K=2.725
    )
    earth_only = notd.lab_outside_support_lifetime_factor(
        300.0, phi_gravity_epsilon=earth_eps, reference_K=2.725
    )
    full_stack = notd.lab_outside_support_lifetime_factor(
        300.0, phi_gravity_epsilon=full_eps, reference_K=2.725
    )
    assert full_stack < earth_only < none
    ppm = 1e6 * (full_stack / none - 1.0)
    assert ppm < -0.1


def test_hybrid_binding_q_anchors_lockin_valley() -> None:
    import hqiv_bbn_abundances as bbn

    m_p = notd.niob.PROTON_MEV
    hybrid = notd.binding_q_hybrid_at_xi(REFERENCE_M, m_p, XI_LOCKIN, xi_lock=XI_LOCKIN)
    legacy = bbn.lockin_binding_q(m_p, REFERENCE_M)
    for h, leg in zip(hybrid, legacy[:3]):
        assert abs(h - leg) < 1e-6 * max(abs(leg), 1.0)


def test_local_curvature_neutrino_width_witness_export() -> None:
    witness = notd.local_curvature_neutrino_width_witness()
    assert witness["opacity_oom_at_lockin_barn"] > 3e8
    lab = witness["lab_readout"]
    assert lab["width_factor"] > 1.06
    assert len(witness["bbn_epochs"]) == 4
    bbn = witness["bbn_epochs"][2]
    assert abs(bbn["T_MeV"] - 0.1) < 1e-9


if __name__ == "__main__":
    test_lockin_modulator_is_unity()
    test_bbn_temperature_weakens_outside_modulator()
    test_lockin_structural_binding_unchanged()
    test_free_beta_minus_overlap_has_curvature_deficit()
    test_bonded_beta_minus_stable_in_well()
    test_he4_lockin_report()
    test_earth_surface_phi_epsilon_order_of_magnitude()
    test_solar_and_galactic_phi_epsilon_order()
    test_local_lab_gravity_binding_stack_full()
    test_outside_gravity_geff_modulator_earth_bump()
    test_combined_outside_support_includes_gravity()
    test_hybrid_binding_q_anchors_lockin_valley()
    test_local_curvature_neutrino_width_witness_export()
    print("test_hqiv_nuclear_outside_temperature_dynamics: OK")
