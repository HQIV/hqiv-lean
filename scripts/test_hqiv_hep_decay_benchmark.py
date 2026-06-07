#!/usr/bin/env python3
"""Regression tests for HEP decay observations vs predictions benchmark."""

from __future__ import annotations

import hqiv_hep_decay_benchmark as bench


def test_full_benchmark_passes_without_known_gaps() -> None:
    payload = bench.build_payload()
    assert payload["summary"]["fail"] == 0
    assert payload["summary"].get("known_gap", 0) == 0
    assert payload["summary"]["pass"] >= 80


def test_observations_file_loads() -> None:
    obs = bench.load_json(bench.DEFAULT_OBSERVATIONS)
    assert obs.get("mass_panel")
    assert obs.get("decay_channels")


def test_payload_builds_with_summary() -> None:
    payload = bench.build_payload()
    assert payload["summary"]["total"] > 0
    assert payload["summary"]["pass"] > 0
    assert payload["comparison_policy"]


def test_proton_and_neutron_mass_tight() -> None:
    payload = bench.build_payload()
    rows = {r["case_id"]: r for r in payload["rows"] if r["panel"] == "mass"}
    assert rows["p"]["status"] == "pass"
    assert rows["n"]["status"] == "pass"
    assert abs(rows["p"]["error"]) < 1e-2


def test_lhc_kinematics_passes() -> None:
    payload = bench.build_payload()
    rows = {r["case_id"]: r for r in payload["rows"] if r["panel"] == "kinematics"}
    assert rows["LHC_pp_13TeV"]["status"] == "pass"


def test_delta_decay_topology_open() -> None:
    payload = bench.build_payload()
    open_row = next(
        r for r in payload["rows"] if r["case_id"] == "delta_p_strong_p_pi_open"
    )
    assert open_row["status"] == "pass"
    assert open_row["predicted"] is True


def test_branching_sums_normalized() -> None:
    payload = bench.build_payload()
    sums = [
        r
        for r in payload["rows"]
        if r["quantity"] == "branching_sum" and r["status"] != "skip"
    ]
    assert sums
    assert all(r["status"] == "pass" for r in sums)


def test_environment_ordering() -> None:
    payload = bench.build_payload()
    env_rows = {r["case_id"]: r for r in payload["rows"] if r["panel"] == "environment"}
    assert env_rows["B_field_increases_weak_dressing"]["status"] == "pass"
    assert env_rows["trap_reduces_weak_dressing"]["status"] == "pass"


def test_pi_plus_half_life_matches_reference() -> None:
    payload = bench.build_payload()
    row = next(
        r for r in payload["rows"]
        if r["case_id"] == "pi_plus" and r["panel"] == "half_life"
    )
    assert row["status"] == "pass"


def test_phi_kk_q_matches_reference() -> None:
    payload = bench.build_payload()
    row = next(r for r in payload["rows"] if r["case_id"] == "phi_strong_KK_q")
    assert row["status"] == "pass"


if __name__ == "__main__":
    test_full_benchmark_passes_without_known_gaps()
    test_observations_file_loads()
    test_payload_builds_with_summary()
    test_proton_and_neutron_mass_tight()
    test_lhc_kinematics_passes()
    test_delta_decay_topology_open()
    test_branching_sums_normalized()
    test_environment_ordering()
    test_pi_plus_half_life_matches_reference()
    test_phi_kk_q_matches_reference()
    print("test_hqiv_hep_decay_benchmark: OK")
