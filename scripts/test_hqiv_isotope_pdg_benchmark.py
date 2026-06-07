#!/usr/bin/env python3
"""Tests for isotope reference benchmark harness."""

from __future__ import annotations

import hqiv_isotope_pdg_benchmark as bench


def test_benchmark_has_light_reference_panel() -> None:
    labels = [r.label for r in bench.REFERENCE_ISOTOPES]
    assert labels == ["p", "n", "D", "T", "He3", "He4"]


def test_free_pn_masses_are_close_to_references() -> None:
    payload = bench.build_payload(qualify_em_tipping=False)
    rows = {r["label"]: r for r in payload["rows"]}
    assert abs(rows["p"]["mass_error_mev"]) < 1e-3
    assert abs(rows["n"]["mass_error_mev"]) < 1e-3


def test_qualified_neutron_has_half_life_ratio() -> None:
    payload = bench.build_payload(qualify_em_tipping=True, lab_temperature_K=300.0)
    rows = {r["label"]: r for r in payload["rows"]}
    assert rows["p"]["predicted_channel"] == "stable"
    assert rows["n"]["predicted_half_life_seconds"] is not None
    assert rows["n"]["half_life_ratio_pred_over_ref"] is not None
    assert 0.75 <= rows["n"]["half_life_ratio_pred_over_ref"] <= 1.15
    assert rows["T"]["predicted_channel"] == "beta_minus"
    assert rows["T"]["predicted_half_life_seconds"] is not None
    assert rows["T"]["half_life_ratio_pred_over_ref"] is not None
    assert 0.25 <= rows["T"]["half_life_ratio_pred_over_ref"] <= 2.5
    assert rows["He4"]["predicted_channel"] == "stable"
    assert len(payload["neutron_lifetime_temperature_sweep"]) == 4
    sweep = payload["neutron_lifetime_temperature_sweep"]
    assert sweep[-1]["predicted_half_life_seconds"] < sweep[0]["predicted_half_life_seconds"]


def test_unqualified_does_not_claim_stability() -> None:
    payload = bench.build_payload(qualify_em_tipping=False)
    rows = {r["label"]: r for r in payload["rows"]}
    assert rows["He4"]["predicted_structurally_shielded"]
    assert not rows["He4"]["predicted_stable_qualified"]


if __name__ == "__main__":
    test_benchmark_has_light_reference_panel()
    test_free_pn_masses_are_close_to_references()
    test_qualified_neutron_has_half_life_ratio()
    test_unqualified_does_not_claim_stability()
    print("test_hqiv_isotope_pdg_benchmark: OK")
