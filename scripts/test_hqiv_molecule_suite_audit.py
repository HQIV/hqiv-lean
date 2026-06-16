#!/usr/bin/env python3
"""Tests for expanded non-quantum molecule suite."""

from __future__ import annotations

import hqiv_dynamic_binding_chart as chart
import hqiv_electronic_valence_shells as evs
from fragment_aware_bonded_horizon import FragmentConfig


def test_lif_compton_triplet_not_homonuclear() -> None:
    frags = (FragmentConfig("Li", 3, 3), FragmentConfig("F", 9, 9))
    assert evs.is_ionic_diatomic(frags)
    assert evs.chemistry_compton_triplet(frags) == (4, 3, 1)


def test_nacl_ionic_lattice_dress() -> None:
    bench = next(b for b in chart.EXPANDED_MOLECULE_SUITE if b.name == "NaCl")
    row = chart.dynamic_binding_for_benchmark(bench)
    assert row.compton_triplet_m == (5, 4, 1)
    assert abs(row.error_pct) < 20.0, row


def test_period3_hydrides_improved() -> None:
    payload = chart.build_chart_payload()
    for name in ("HCl", "HBr"):
        row = next(r for r in payload["expanded_molecules"] if r["name"] == name)
        assert abs(row["error_pct"]) < 8.0, row


def test_f2_halogen_bounded() -> None:
    row = next(
        r for r in chart.build_chart_payload()["open_shell_diagnostics"] if r["name"] == "F2"
    )
    assert abs(row["error_pct"]) < 5.0, row


def test_c2h2_conjugated_homonuclear_improved() -> None:
    row = next(r for r in chart.build_chart_payload()["expanded_molecules"] if r["name"] == "C2H2")
    assert abs(row["error_pct"]) < 5.0, row


def test_open_shell_diagnostics_tight() -> None:
    for row in chart.build_chart_payload()["open_shell_diagnostics"]:
        assert abs(row["error_pct"]) < 5.0, row


def test_bond_state_witness_present() -> None:
    payload = chart.build_chart_payload()
    hcn = next(r for r in payload["expanded_molecules"] if r["name"] == "HCN")
    assert hcn.get("bond_state_witness") is not None
    assert "hyperclosure_ev" in hcn["bond_state_witness"]


def test_expanded_conjugated_and_period3_improved() -> None:
    payload = chart.build_chart_payload()
    hcn = next(r for r in payload["expanded_molecules"] if r["name"] == "HCN")
    ph3 = next(r for r in payload["expanded_molecules"] if r["name"] == "PH3")
    assert abs(hcn["error_pct"]) < 35.0, hcn
    assert abs(ph3["error_pct"]) < 42.0, ph3


def test_core_gmtkn55_tight() -> None:
    payload = chart.build_chart_payload()
    for name in ("H2", "NH3", "CH4"):
        row = next(r for r in payload["molecules"] if r["name"] == name)
        assert abs(row["error_pct"]) < 6.0, row


def test_expanded_suite_count() -> None:
    assert len(chart.EXPANDED_MOLECULE_SUITE) == 8
    assert len(chart.ALL_MOLECULE_BENCHMARKS) == 6 + 8 + 5


def test_molecule_suite_audit_runs() -> None:
    from hqiv_molecule_suite_audit import build_audit_payload

    payload = build_audit_payload()
    assert payload["summary"]["total_molecules"] == len(chart.ALL_MOLECULE_BENCHMARKS)
    core = payload["panels"][0]
    assert core["count"] == 6
    expanded = payload["panels"][1]
    assert expanded["count"] == 8
    cs = payload["summary"]["combined_core_plus_expanded"]
    assert cs["count"] == 14


def test_chart_payload_includes_expanded() -> None:
    payload = chart.build_chart_payload()
    assert len(payload["expanded_molecules"]) == 8
    assert payload["expanded_summary"]["count"] == 8


if __name__ == "__main__":
    test_lif_compton_triplet_not_homonuclear()
    test_nacl_ionic_lattice_dress()
    test_period3_hydrides_improved()
    test_f2_halogen_bounded()
    test_c2h2_conjugated_homonuclear_improved()
    test_open_shell_diagnostics_tight()
    test_bond_state_witness_present()
    test_expanded_conjugated_and_period3_improved()
    test_expanded_suite_count()
    test_core_gmtkn55_tight()
    test_molecule_suite_audit_runs()
    test_chart_payload_includes_expanded()
    print("test_hqiv_molecule_suite_audit: OK")
