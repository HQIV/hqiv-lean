#!/usr/bin/env python3
"""Tests for the parameter-free dynamic binding chart."""

from __future__ import annotations

import hqiv_dynamic_binding_chart as chart
import hqiv_nuclear_curvature_binding as ncb
from fragment_aware_bonded_horizon import FragmentConfig


def _row(name: str) -> dict:
    payload = chart.build_chart_payload()
    return next(r for r in payload["molecules"] if r["name"] == name)


def test_lih_uses_lean_heavy_hydride_compton_triplet() -> None:
    row = _row("LiH")
    assert row["compton_triplet_m"] == (4, 3, 1)
    assert row["nuclei"][0]["m_nuclear"] > chart.REFERENCE_M - 1


def test_h2_within_eight_percent() -> None:
    row = _row("H2")
    assert abs(row["error_pct"]) < 9.0, row


def test_networked_vev_reported_alongside_bare() -> None:
    row = _row("LiH")
    assert row["vev_geometric_mean_bare"] > 0.0
    assert row["vev_geometric_mean"] > 0.0


def test_ch4_within_ten_percent() -> None:
    row = _row("CH4")
    assert row["h_h_repulsive_contact_points"] == 4
    assert abs(row["error_pct"]) < 10.0, row


def test_diatomic_hydrides_bounded() -> None:
    for name in ("LiH", "HF"):
        row = _row(name)
        assert abs(row["error_pct"]) < 30.0, row


def test_polyatomic_atomization_positive_and_bounded() -> None:
    payload = chart.build_chart_payload()
    for name in ("H2O", "CH4", "NH3"):
        row = next(r for r in payload["molecules"] if r["name"] == name)
        assert row["binding_ev"] > 0.0
        assert abs(row["error_pct"]) < 45.0, row


def test_h2o_electronic_shell_readout() -> None:
    row = _row("H2O")
    shell = row["shell_readout"]
    assert shell["electronic_shell_slots"] == ["2s", "2p", "1s"]
    assert shell["electron_split"] == [10, 8, 2]
    assert tuple(row["compton_triplet_m"]) == (4, 3, 1)


def test_nuclear_shell_from_mass_number() -> None:
    assert ncb.nucleus_curvature_shell(1) == ncb.REFERENCE_M
    assert ncb.nucleus_curvature_shell(7) > ncb.REFERENCE_M


def test_nuclear_rows_present() -> None:
    row = _row("HF")
    assert len(row["nuclei"]) == 2
    assert "per_nucleon_binding_mev" in row["nuclei"][0]
    assert row["nuclear_binding_uniformity"]["count"] == 2.0


def test_no_kappa_bind_in_payload() -> None:
    payload = chart.build_chart_payload()
    assert payload["parameter_policy"] == "no_fitted_coefficients"
    assert "kappa_bind" not in payload
    assert "compton_triplet" in payload["shell_assignment_rules"]
    assert payload["binding_curvature_feedback_at_xi_lockin"] > 1.0


def test_dynamic_feedback_from_xi_contact() -> None:
    row = _row("CH4")
    assert row["contact_xi"] > 1.0
    assert row["dynamic_binding_curvature_feedback"] > 1.0
    assert 0.0 < row["geometry_alignment_factor"] <= 1.0


if __name__ == "__main__":
    test_lih_uses_lean_heavy_hydride_compton_triplet()
    test_h2_within_eight_percent()
    test_networked_vev_reported_alongside_bare()
    test_ch4_within_ten_percent()
    test_diatomic_hydrides_bounded()
    test_polyatomic_atomization_positive_and_bounded()
    test_h2o_electronic_shell_readout()
    test_nuclear_shell_from_mass_number()
    test_nuclear_rows_present()
    test_no_kappa_bind_in_payload()
    test_dynamic_feedback_from_xi_contact()
    print("test_hqiv_dynamic_binding_chart: OK")
