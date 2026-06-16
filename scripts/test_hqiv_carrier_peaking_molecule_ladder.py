#!/usr/bin/env python3
"""Tests for carrier-peaking molecule ladder (LiF, H2O)."""

from __future__ import annotations

import json
from pathlib import Path

from hqiv_lab.carrier_peaking import (
    GeometryLevelSpec,
    build_sparse_carrier,
    mixed_radix_flat,
    run_carrier_peaking,
    shells_from_compton_list,
    sparse_basis_card,
)


def test_mixed_radix_injective_64() -> None:
    flats = [mixed_radix_flat(GeometryLevelSpec(a, b0, b1)) for a in range(4) for b0 in range(4) for b1 in range(4)]
    assert len(flats) == 64
    assert len(set(flats)) == 64


def test_sparse_carrier_smaller_than_dense_card() -> None:
    L = 11
    flats = list(range(64))
    seed = build_sparse_carrier(L, flats)
    assert len(seed) <= 64
    assert len(seed) < sparse_basis_card(L)


def test_lif_h2o_ladder_runs() -> None:
    from hqiv_carrier_peaking_molecule_ladder import LadderConfig, run_ladder

    report = run_ladder(LadderConfig(L=11, n_levels=4))
    assert report["summary"]["count"] == 2
    names = {r["molecule"] for r in report["molecules"]}
    assert names == {"LiF", "H2O"}

    for row in report["molecules"]:
        assert row["scaling_summary"]["mixed_radix_injective"]
        assert row["scaling_summary"]["sparse_support_independent_of_L_card"]
        assert row["scaling_summary"]["dense_card_grows_quadratically"]
        pri = row["encodings"]["mixed_radix"]
        assert pri["sparse_evolved_len"] == 2 * pri["sparse_seed_len"]
        assert pri["compression_vs_dense_card"] > 1.0


def test_h2o_more_geometry_levels_than_lif() -> None:
    from hqiv_carrier_peaking_molecule_ladder import LIF_BENCHMARK, LadderConfig, audit_molecule
    import hqiv_dynamic_binding_chart as chart

    h2o = next(b for b in chart.GMTKN55_SUITE if b.name == "H2O")
    cfg = LadderConfig()
    lif_row = audit_molecule(LIF_BENCHMARK, cfg)
    h2o_row = audit_molecule(h2o, cfg)
    assert h2o_row["geometry_level_count"] > lif_row["geometry_level_count"]


def test_carrier_peaking_flip_signal_h2o() -> None:
    """H₂O mixed-radix grid should produce nonzero OSH flip signal at L=11."""
    L = 11
    shells = shells_from_compton_list([4, 3, 1, 1, 1], L)
    flats = [mixed_radix_flat(GeometryLevelSpec(a, b0, b1)) for a in range(4) for b0 in range(4) for b1 in range(4)]
    rep = run_carrier_peaking(L, shells, flats)
    assert rep["flip_count"] > 0
    assert len(rep["peaks16"]) >= 1


def test_json_audit_file() -> None:
    path = Path(__file__).resolve().parent.parent / "data" / "carrier_peaking_molecule_ladder.json"
    if not path.is_file():
        return
    payload = json.loads(path.read_text())
    assert payload["program"] == "hqiv_carrier_peaking_molecule_ladder"
    assert len(payload["molecules"]) >= 2


if __name__ == "__main__":
    test_mixed_radix_injective_64()
    test_sparse_carrier_smaller_than_dense_card()
    test_lif_h2o_ladder_runs()
    test_h2o_more_geometry_levels_than_lif()
    test_carrier_peaking_flip_signal_h2o()
    test_json_audit_file()
    print("test_hqiv_carrier_peaking_molecule_ladder: OK")
