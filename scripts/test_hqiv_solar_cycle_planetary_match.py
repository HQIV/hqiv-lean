#!/usr/bin/env python3
"""Tests for solar cycle vs planetary alignment matching."""

from __future__ import annotations

import json
import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_solar_cycle_planetary_match as match
import hqiv_solar_dynamics as sd


def test_extrema_data_loads():
    path = _ROOT / "data" / "solar_cycle_extrema.json"
    cycles = match.load_cycles(path)
    assert len(cycles) >= 14
    assert cycles[-1]["number"] == 25


def test_active_belt_witness_latitudes():
    belt = sd.solar_active_belt_witness()
    assert 23.0 < belt["latitude_monogamy_deg"] < 24.0
    assert 26.0 < belt["latitude_rindler_half_deg"] < 27.0


def test_readout_fields():
    row = {
        "minimum": {"year": 2019, "month": 12, "sn": 1.8},
        "maximum": {"year": 2024, "month": 10, "sn": 160.8},
    }
    lat = sd.solar_active_belt_witness()["latitude_monogamy_deg"]
    mn = match.readout_at(25, "minimum", row, active_belt_latitude_deg=lat)
    mx = match.readout_at(25, "maximum", row, active_belt_latitude_deg=lat)
    assert 0 <= mn.lon_jupiter_deg < 360
    assert mx.activity_score > 0
    assert mn.iso_date == "2019-12-15"


def test_target_model_improves_composite():
    cycles = match.load_cycles(_ROOT / "data" / "solar_cycle_extrema.json")
    fit = match.fit_target_model(cycles)
    best = fit["selected"]
    assert best["composite_target_score"] >= 0.55
    assert best["latitude_deg"] in {
        sd.solar_active_belt_witness()["latitude_monogamy_deg"],
        sd.solar_active_belt_witness()["latitude_rindler_half_deg"],
        sd.solar_active_belt_witness()["latitude_legacy_obs_deg"],
    }
    assert best["candidate"] == "rindler_half"


def test_analyze_produces_summary():
    cycles = match.load_cycles(_ROOT / "data" / "solar_cycle_extrema.json")
    lat = sd.solar_active_belt_witness()["latitude_monogamy_deg"]
    report = match.analyze_cycles(cycles, active_belt_latitude_deg=lat, use_target_model=True)
    assert report["cycle_count"] == len(cycles)
    s = report["summary"]
    for key in (
        "gnevyshev_ohl_match_rate",
        "activity_score_higher_at_max_rate",
        "hqiv_coupling_higher_at_max_rate",
    ):
        assert 0.0 <= s[key] <= 1.0


def test_gnevyshev_ohl_symmetry():
    assert match.gnevyshev_ohl_same_side(0.0, 10.0) is True
    assert match.gnevyshev_ohl_same_side(0.0, 180.0) is False


def test_report_json_roundtrip(tmp_path: Path):
    cycles = match.load_cycles(_ROOT / "data" / "solar_cycle_extrema.json")
    report = match.build_report(cycles)
    out = tmp_path / "match.json"
    out.write_text(json.dumps(report), encoding="utf-8")
    loaded = json.loads(out.read_text(encoding="utf-8"))
    assert "fit" in loaded
    assert loaded["fit"]["analysis"]["cycle_count"] == report["fit"]["analysis"]["cycle_count"]


if __name__ == "__main__":
    for fn in (
        test_extrema_data_loads,
        test_active_belt_witness_latitudes,
        test_readout_fields,
        test_target_model_improves_composite,
        test_analyze_produces_summary,
        test_gnevyshev_ohl_symmetry,
    ):
        fn()
    test_report_json_roundtrip(Path("/tmp"))
    print("All tests passed.")
