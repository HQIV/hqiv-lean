#!/usr/bin/env python3
"""Tests for the HQIV bond-state network layer (inside/outside curvature)."""

from __future__ import annotations

import math

import hqiv_bond_state_network as bsn
import hqiv_curvature_bond_state as cbs


def _case(name: str) -> bsn.MoleculeCase:
    return next(case for case in bsn.CASES if case.name == name)


def test_trace8_add_identity() -> None:
    a = bsn.Trace8((1.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    b = bsn.Trace8((0.5, 1.0, 3.0, 0.0, 0.0, 0.0, 0.0, 0.0))
    assert (a + b).values == (1.5, 3.0, 3.0, 0.0, 0.0, 0.0, 0.0, 0.0)


def test_geff_theta_coupling_matches_alpha() -> None:
    theta = math.pi / 4.0
    phi = theta / cbs.phase_theta()
    expected = phi ** cbs.ALPHA
    assert math.isclose(cbs.outside_contact_coupling(theta), expected, rel_tol=1e-12)


def test_h2_has_outside_contact_without_hyperclosure() -> None:
    row = bsn.evaluate_case(_case("H2"))
    assert row.outside_contact_ev > 0.0
    assert row.hyperclosure_trace_l1 == 0.0
    assert len(row.bonds) == 1
    assert row.bonds[0]["geff_theta_coupling"] > 0.0


def test_polyatomic_has_graph_hyperclosure() -> None:
    row = bsn.evaluate_case(_case("CH4"))
    assert row.outside_contact_ev > 0.0
    assert row.hyperclosure_trace_l1 > 0.0
    assert len(row.bonds) == 4


def test_predicted_is_inside_outside_sum() -> None:
    for case in bsn.CASES:
        row = bsn.evaluate_case(case)
        recomposed = -(row.inside_surplus_ev) + row.outside_contact_ev + row.hyperclosure_ev
        assert math.isclose(row.predicted_ev, recomposed, rel_tol=0.0, abs_tol=1e-9)


def test_payload_exports_all_cases() -> None:
    payload = bsn.build_payload()
    assert payload["parameter_policy"] == "no_fitted_coefficients"
    assert "inside" in payload["physics"]
    assert "outside" in payload["physics"]
    assert len(payload["cases"]) == len(bsn.CASES)


def test_molecular_host_t2_few_ppm() -> None:
    row = bsn.molecular_host_readout("T2", nucleus_label="T")
    assert 1e-6 < row["phi_epsilon"] < 1e-3
    assert 1.0 < row["geff_ppm"] < 20.0


def test_molecular_host_t2o_sub_ppm() -> None:
    row = bsn.molecular_host_readout("T2O", nucleus_label="T")
    assert row["geff_ppm"] < 1.0


if __name__ == "__main__":
    test_trace8_add_identity()
    test_geff_theta_coupling_matches_alpha()
    test_h2_has_outside_contact_without_hyperclosure()
    test_polyatomic_has_graph_hyperclosure()
    test_predicted_is_inside_outside_sum()
    test_payload_exports_all_cases()
    test_molecular_host_t2_few_ppm()
    test_molecular_host_t2o_sub_ppm()
    print("test_hqiv_bond_state_network: OK")
