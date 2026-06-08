#!/usr/bin/env python3
"""Tests for dynamic isotope β-channel readouts."""

from __future__ import annotations

import hqiv_dynamic_beta_isotope as dbi
import hqiv_nuclear_outside_temperature_dynamics as notd


def _row(rows, name: str):
    return next(r for r in rows if r.name == name)


def test_lockin_rows_include_ladder_isotopes() -> None:
    rows = dbi.build_rows()
    assert [r.name for r in rows] == ["p", "n", "D", "He3", "He4"]
    assert _row(rows, "D").valley_count == 2
    assert _row(rows, "He3").valley_count == 4
    assert _row(rows, "He4").valley_count == 6


def test_free_neutron_endpoint_q_is_mass_gap_minus_electron() -> None:
    row = _row(dbi.build_rows(), "n")
    assert row.beta_minus_endpoint_q_mev is not None
    assert abs(row.beta_minus_endpoint_q_mev - 0.782) < 0.01


def test_delta_m_preserved_for_all_isotopes() -> None:
    rows = dbi.build_rows()
    deltas = {round(r.delta_m_mev, 12) for r in rows}
    assert len(deltas) == 1


def test_beta_minus_residual_is_mass_gap_minus_overlap() -> None:
    row = _row(dbi.build_rows(), "He4")
    assert abs(row.beta_minus_residual_mev - (row.beta_minus_mass_gap_mev - row.beta_minus_overlap_mev)) < 1e-12


def test_bbn_temperature_changes_mass_budget_not_gap() -> None:
    lock = _row(dbi.build_rows(), "He4")
    bbn = _row(dbi.build_rows(xi=notd.xi_from_T_MeV(0.1)), "He4")
    assert bbn.mass_budget_mev > lock.mass_budget_mev
    assert bbn.delta_m_mev == lock.delta_m_mev


def test_payload_exports_lockin_and_bbn() -> None:
    payload = dbi.build_payload()
    assert len(payload["lockin"]) == 5
    assert len(payload["bbn_0_1_MeV"]) == 5


if __name__ == "__main__":
    test_lockin_rows_include_ladder_isotopes()
    test_delta_m_preserved_for_all_isotopes()
    test_beta_minus_residual_is_mass_gap_minus_overlap()
    test_bbn_temperature_changes_mass_budget_not_gap()
    test_payload_exports_lockin_and_bbn()
    print("test_hqiv_dynamic_beta_isotope: OK")
