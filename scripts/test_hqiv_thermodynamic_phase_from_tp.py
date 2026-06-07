#!/usr/bin/env python3
"""Tests for (T, P) → derived phase (not phase-as-input)."""

from __future__ import annotations

import hqiv_thermodynamic_phase_from_tp as tptp


def test_ch4_stp_is_gas_or_cluster_not_solid() -> None:
    env = tptp.ThermodynamicEnvironment.stp()
    mat = tptp.material_scales_from_network_name("CH4")
    st = tptp.derive_phase(env, mat)
    assert st.phase in (
        tptp.DerivedPhase.GAS,
        tptp.DerivedPhase.MOLECULAR_CLUSTER,
        tptp.DerivedPhase.SUPERCRITICAL,
    )
    assert st.phase != tptp.DerivedPhase.SOLID


def test_ice_cold_is_solid() -> None:
    env = tptp.ThermodynamicEnvironment(150.0, tptp.STP_PRESSURE_PA)
    mat = tptp.material_scales_from_network_name("H2O")
    st = tptp.derive_phase(env, mat)
    assert st.phase == tptp.DerivedPhase.SOLID
    assert st.periodic_weight > 0.0


def test_h2o_bulk_solid_liquid_transition_at_1atm() -> None:
    """Bulk ice: solid below T_sl, liquid above at 1 atm."""
    mat = tptp.material_scales_bulk_h2o()
    t_sl = tptp.solid_liquid_transition_temperature_K(mat)
    assert 270.0 <= t_sl <= 276.0
    p = tptp.STP_PRESSURE_PA
    st_cold = tptp.derive_phase(tptp.ThermodynamicEnvironment(271.0, p), mat)
    assert st_cold.phase == tptp.DerivedPhase.SOLID
    st_warm = tptp.derive_phase(tptp.ThermodynamicEnvironment(273.0, p), mat)
    assert st_warm.phase == tptp.DerivedPhase.LIQUID
    st_melt = tptp.derive_phase(tptp.ThermodynamicEnvironment(273.15, p), mat)
    assert st_melt.phase == tptp.DerivedPhase.LIQUID


def test_protein_cytosol_liquid_like() -> None:
    env = tptp.ThermodynamicEnvironment.protein_cytosol()
    mat = tptp.material_scales_from_network_name("protein_12mer")
    mat = tptp.MaterialThermodynamicScales(
        name="protein_12mer",
        characteristic_binding_ev=mat.characteristic_binding_ev,
        contact_points=mat.contact_points,
        molecular_weight_amu=12.0 * 110.0,
        intermolecular_contacts=1,
    )
    st = tptp.derive_phase(env, mat)
    assert st.phase == tptp.DerivedPhase.LIQUID
    assert 0.15 <= st.coordination_fraction <= 1.0


if __name__ == "__main__":
    test_ch4_stp_is_gas_or_cluster_not_solid()
    test_ice_cold_is_solid()
    test_h2o_bulk_solid_liquid_transition_at_1atm()
    test_protein_cytosol_liquid_like()
    print("test_hqiv_thermodynamic_phase_from_tp: OK")
