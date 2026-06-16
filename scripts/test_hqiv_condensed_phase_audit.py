#!/usr/bin/env python3
"""Tests for condensed-phase trace audit and species melt witnesses."""

from __future__ import annotations

import hqiv_condensed_phase_audit as audit
import hqiv_phase_geometry_density as pgd
from hqiv_lab.species_panel import CONDENSED_SPECIES_PANEL, panel_entry


def test_audit_contact_xi_consistent() -> None:
    payload = audit.build_payload()
    assert payload["summary"]["all_contact_xi_traces_consistent"]
    assert abs(payload["expected_contact_xi_compton_431"] - 11.0 / 3.0) < 1e-9


def test_h2o_density_near_nist_after_lapse_overlap() -> None:
    row = next(r for r in audit.build_payload()["species"] if r["molecule"] == "H2O")
    assert row["benchmark"]["density_error_pct"] < 1.0
    assert abs(row["geometry"]["density_g_cm3"] - 0.917) < 0.015
    assert abs(row["geometry"]["neighbor_lapse_overlap_factor"] - 0.95) < 1e-9


def test_ch4_density_at_melt_not_reference_t() -> None:
    entry = panel_entry("CH4")
    at_melt = pgd.melt_readout_with_phase_geometry(
        "CH4",
        allotrope=entry.allotrope,
        temperature_at_melt_k=entry.witness_temperature_k,
    )
    at_ref = pgd.melt_readout_with_phase_geometry(
        "CH4",
        allotrope=entry.allotrope,
        temperature_at_melt_k=273.15,
    )
    assert at_melt["density_g_cm3"] > 0.51
    assert at_ref["density_g_cm3"] < 0.49
    assert abs(at_melt["density_g_cm3"] - entry.nist_solid_density_g_cm3) / entry.nist_solid_density_g_cm3 < 0.02


def test_hf_density_near_nist_after_linear_halogen_fixes() -> None:
    row = next(r for r in audit.build_payload()["species"] if r["molecule"] == "HF")
    assert row["benchmark"]["density_error_pct"] < 2.0
    assert abs(row["geometry"]["density_g_cm3"] - 1.15) < 0.02
    assert row["geometry"]["halogen_strong_hbond_leg_factor"] < 1.0
    assert row["geometry"]["linear_chain_zigzag_lattice_open_factor"] > 1.0


def test_panel_species_within_nist_density_envelope() -> None:
    payload = audit.build_payload()
    for row in payload["species"]:
        assert row["benchmark"]["density_error_pct"] < 8.0, row["molecule"]
        assert row["benchmark"]["T_sl_error_pct"] < 2.0, row["molecule"]


def test_witness_json_roundtrip() -> None:
    payload = audit.build_payload()
    assert len(payload["species"]) == len(CONDENSED_SPECIES_PANEL)


if __name__ == "__main__":
    for fn in (
        test_audit_contact_xi_consistent,
        test_h2o_density_near_nist_after_lapse_overlap,
        test_ch4_density_at_melt_not_reference_t,
        test_hf_density_near_nist_after_linear_halogen_fixes,
        test_panel_species_within_nist_density_envelope,
        test_witness_json_roundtrip,
    ):
        fn()
    print("test_hqiv_condensed_phase_audit: OK")
