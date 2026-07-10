#!/usr/bin/env python3
"""Tests for the chemistry residual-correlation audit."""

from __future__ import annotations

import hqiv_chemistry_residual_correlation_audit as audit


def test_payload_has_quarantine_and_anchor_policy() -> None:
    payload = audit.build_payload()
    assert "comparison_policy" in payload
    assert "no comparison value is used to tune" in payload["comparison_policy"]
    assert payload["anchor_policy"]["alpha"].endswith("3/5")
    assert payload["anchor_policy"]["gamma"].endswith("2/5")
    assert "referenceM = 4" in payload["anchor_policy"]["referenceM"]
    assert "not performed" in payload["anchor_policy"]["counterfactual_anchor_variation"]


def test_condensed_phase_correlation_schema_is_finite_where_available() -> None:
    payload = audit.build_payload()
    condensed = payload["condensed_phase"]
    assert condensed["n"] >= 4
    corr = condensed["correlations"]["refractive_index_abs_error_pct"][
        "phase_curvature_density_fraction"
    ]
    assert corr["available"]
    assert corr["n"] == condensed["n"]
    assert -1.0 <= corr["pearson_r"] <= 1.0


def test_spectroscopy_geometry_reliability_exposes_known_residual_pattern() -> None:
    payload = audit.build_payload()
    groups = payload["spectroscopy"]["group_means_by_geometry_reliability"]
    reliable = groups["True"]["mean_abs_error_pct"]["omega_e_abs_error_pct"]
    unreliable = groups["False"]["mean_abs_error_pct"]["omega_e_abs_error_pct"]
    assert unreliable > reliable
    corr = payload["spectroscopy"]["correlations"]["omega_e_abs_error_pct"][
        "geometry_reliable_numeric"
    ]
    assert corr["available"]
    assert corr["pearson_r"] < 0.0


def test_reliable_spectroscopy_keeps_polar_vs_homonuclear_split() -> None:
    payload = audit.build_payload()
    groups = payload["spectroscopy"]["group_means_reliable_geometry_by_class"]
    assert groups["homonuclear"]["n"] >= 3
    assert groups["polar_or_ionic"]["n"] >= 3
    polar = groups["polar_or_ionic"]["mean_abs_error_pct"]["r_e_abs_error_pct"]
    homonuclear = groups["homonuclear"]["mean_abs_error_pct"]["r_e_abs_error_pct"]
    assert polar > homonuclear


def test_forward_prediction_candidates_are_unscored() -> None:
    payload = audit.build_payload()
    candidates = payload["forward_prediction_candidates"]
    assert candidates["phase_grid_rows"]
    assert candidates["cooling_sweep_rows"]
    for row in candidates["phase_grid_rows"] + candidates["cooling_sweep_rows"]:
        assert row["benchmark_status"].startswith("forward_prediction_or_unscored")


if __name__ == "__main__":
    for fn in (
        test_payload_has_quarantine_and_anchor_policy,
        test_condensed_phase_correlation_schema_is_finite_where_available,
        test_spectroscopy_geometry_reliability_exposes_known_residual_pattern,
        test_reliable_spectroscopy_keeps_polar_vs_homonuclear_split,
        test_forward_prediction_candidates_are_unscored,
    ):
        fn()
    print("test_hqiv_chemistry_residual_correlation_audit: OK")
