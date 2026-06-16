#!/usr/bin/env python3
"""Tests for per-contact α-emission ledgers."""

from __future__ import annotations

import math

import hqiv_curvature_binding_core as cbc
import hqiv_post_alpha_sphere_touching as touch


def test_two_alpha_contact_ledger_counts() -> None:
    delta = cbc.multi_alpha_trapped_inside_delta_mev(4, 8, 4)
    assert delta is not None and delta > 0.0
    ledger = touch.two_alpha_interface_contact_ledger(8, 4, 2, delta)
    assert ledger is not None
    assert ledger.barbell_contact_units == 4
    assert ledger.mass_contact_count == 5
    assert ledger.constructive_valley_increment == 2


def test_be8_local_contact_witness_ballpark() -> None:
    delta = cbc.multi_alpha_trapped_inside_delta_mev(4, 8, 4)
    assert delta is not None
    ledger = touch.two_alpha_interface_contact_ledger(8, 4, 2, delta)
    assert ledger is not None
    q, well, valley, width = cbc.two_alpha_local_contact_width_mev(4, ledger)
    assert 0.085 < q < 0.095
    assert 9.0 < well < 11.5
    assert valley == 2.0
    assert 5.0e-6 < width < 9.0e-6
    tau = math.log(2.0) * 6.582119569e-22 / width
    assert 0.75 * 6.7e-17 <= tau <= 1.25 * 6.7e-17


if __name__ == "__main__":
    test_two_alpha_contact_ledger_counts()
    test_be8_local_contact_witness_ballpark()
    print("test_hqiv_alpha_local_contact: OK")
