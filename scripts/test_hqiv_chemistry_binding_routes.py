#!/usr/bin/env python3
"""Binding route provenance registry tests."""

from __future__ import annotations

import hqiv_chemistry_binding_routes as routes


def test_scaffold_routes_are_explicit() -> None:
    scaffolds = routes.scaffold_routes()
    assert "homonuclear_open_shell_exponent" in scaffolds
    assert "bent_hyperclosure_period3_channel" in scaffolds
    assert len(scaffolds) >= 5


def test_provenance_payload_honest_policy() -> None:
    payload = routes.binding_chart_provenance_payload()
    assert "python_scaffold" in payload["parameter_policy"]
    assert payload["scaffold_route_count"] == len(scaffolds := routes.scaffold_routes())
    assert payload["route_registry"]["lone_pair_surplus_dress"]["status"] == "lean_certified"


if __name__ == "__main__":
    test_scaffold_routes_are_explicit()
    test_provenance_payload_honest_policy()
    print("test_hqiv_chemistry_binding_routes: OK")
