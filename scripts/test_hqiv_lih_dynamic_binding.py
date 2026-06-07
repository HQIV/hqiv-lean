#!/usr/bin/env python3
"""Tests for LiH dynamic binding calculator."""

from __future__ import annotations

import hqiv_lih_dynamic_binding as lih_dyn


def test_primary_binding_near_reference() -> None:
    payload = lih_dyn.build_payload()
    primary = payload["primary_binding_ev"]
    err = abs(payload["primary_error_pct"])
    assert 2.0 < primary < 3.0, primary
    assert err < 5.0, err


def test_dynamic_valence_below_static() -> None:
    vt = lih_dyn.build_payload()["valence_trace_dimless"]
    assert vt["dynamic_full_p"] < vt["static_full_p"]


def test_shell_rows_cover_compton_triplet() -> None:
    rows = lih_dyn.shell_dynamic_rows()
    sites = {r.site for r in rows}
    assert sites == {"Li_s", "Li_p", "H_s"}
    assert all(r.tuft_vev_factor > 0 for r in rows)


if __name__ == "__main__":
    test_primary_binding_near_reference()
    test_dynamic_valence_below_static()
    test_shell_rows_cover_compton_triplet()
    print("test_hqiv_lih_dynamic_binding: OK")
