#!/usr/bin/env python3
"""
Match SILSO solar-cycle minima/maxima to planetary alignments and HQIV readouts.

Uses mean-element heliocentric longitudes (Meeus-class, few-degree accuracy) for
Jupiter, Saturn, Uranus, Neptune. Compares baseline and **target-model** scores:

  • Gnevyshev–Ohl rule (odd cycles: J+S same side at max; even: opposite)
  • HQIV activity score (shear @ active belt + env phase + planetary coupling)
  • Active-belt latitude candidates from compact_object_witness (23° / 27°)

Data: data/solar_cycle_extrema.json (SILSO cycles 12–25).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_solar_cycle_planetary_match.py
  PYTHONPATH=scripts python3 scripts/hqiv_solar_cycle_planetary_match.py --json data/solar_cycle_planetary_alignment_match.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any, Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_solar_dynamics as sd

ExtremumKind = Literal["minimum", "maximum"]

# Mean daily motion in ecliptic longitude (deg/day), J2000-class means.
_PLANET_MEAN_MOTION = {
    "jupiter": (34.351519, 0.0830853007),
    "saturn": (50.077444, 0.0334442282),
    "uranus": (314.055005, 0.01172834),
    "neptune": (304.348665, 0.00598127),
}

J2000_EPOCH = date(2000, 1, 1)


def iso_from_ym(year: int, month: int, day: int = 15) -> str:
    """Mid-month ISO date for a year/month extrema marker."""
    return date(year, month, day).isoformat()


def days_since_j2000_from_ym(year: int, month: int, day: int = 15) -> float:
    return float(date(year, month, day).toordinal() - J2000_EPOCH.toordinal())


def mean_ecliptic_longitude_deg(planet: str, year: int, month: int) -> float:
    l0, rate = _PLANET_MEAN_MOTION[planet]
    d = days_since_j2000_from_ym(year, month)
    return (l0 + rate * d) % 360.0


def unit_ecliptic(lon_deg: float) -> tuple[float, float]:
    r = math.radians(lon_deg)
    return math.cos(r), math.sin(r)


def angular_separation_deg(lon_a: float, lon_b: float) -> float:
    return abs((lon_a - lon_b + 180.0) % 360.0 - 180.0)


def gnevyshev_ohl_same_side(lon_j: float, lon_s: float) -> bool:
    """True when Jupiter and Saturn heliocentric ecliptic vectors have positive dot product."""
    uj = unit_ecliptic(lon_j)
    us = unit_ecliptic(lon_s)
    return uj[0] * us[0] + uj[1] * us[1] > 0.0


def outer_planet_collinearity(lons: dict[str, float]) -> float:
    """|Σ unit vectors| / N — 1 when perfectly collinear, ~0 when spread."""
    sx = sy = 0.0
    n = 0
    for lon in lons.values():
        ux, uy = unit_ecliptic(lon)
        sx += ux
        sy += uy
        n += 1
    if n == 0:
        return 0.0
    return math.hypot(sx, sy) / n


def jupiter_year_fraction(year: int, month: int) -> float:
    years = days_since_j2000_from_ym(year, month) / 365.25
    return years / sd.JUPITER_ORBITAL_PERIOD_YEARS % 1.0


@dataclass(frozen=True)
class ExtremumReadout:
    cycle: int
    kind: ExtremumKind
    year: int
    month: int
    iso_date: str
    sunspot_smoothed: float
    lon_jupiter_deg: float
    lon_saturn_deg: float
    lon_uranus_deg: float
    lon_neptune_deg: float
    jupiter_saturn_separation_deg: float
    gnevyshev_ohl_same_side: bool
    outer_collinearity: float
    jupiter_year_fraction: float
    hqiv_planetary_coupling: float
    hqiv_planetary_multiplier: float
    hqiv_environment_phase: float
    hqiv_outside_gate: float
    activity_score: float
    active_belt_latitude_deg: float


def readout_at(
    cycle: int,
    kind: ExtremumKind,
    row: dict[str, Any],
    *,
    active_belt_latitude_deg: float,
    use_target_model: bool = True,
) -> ExtremumReadout:
    ext = row[kind]
    y, m = int(ext["year"]), int(ext["month"])
    iso = iso_from_ym(y, m)
    lon_j = mean_ecliptic_longitude_deg("jupiter", y, m)
    lon_s = mean_ecliptic_longitude_deg("saturn", y, m)
    lon_u = mean_ecliptic_longitude_deg("uranus", y, m)
    lon_n = mean_ecliptic_longitude_deg("neptune", y, m)
    yf = jupiter_year_fraction(y, m)
    align_sin = (
        sd.planetary_alignment_sin_from_separation(angular_separation_deg(lon_j, lon_s))
        if use_target_model
        else 0.5
    )
    planetary = sd.solar_planetary_magnetic_coupling(year_fraction=yf, alignment_sin=align_sin)
    outside = sd.solar_whim_galactic_outside_gate()
    env_phase = sd.solar_cycle_environment_phase(
        sd.DEFAULT_M_PHOTO,
        sd.DEFAULT_M_CORONA,
        sd.DEFAULT_HOPF_WINDING,
        year_fraction=yf,
        alignment_sin=align_sin,
    )
    activity = sd.solar_extremum_activity_score(
        cycle_number=cycle,
        at_maximum=(kind == "maximum"),
        year=y,
        month=m,
        active_belt_latitude_deg=active_belt_latitude_deg,
        lon_jupiter_deg=lon_j,
        lon_saturn_deg=lon_s,
        jupiter_year_fraction=yf,
    )
    return ExtremumReadout(
        cycle=cycle,
        kind=kind,
        year=y,
        month=m,
        iso_date=iso,
        sunspot_smoothed=float(ext["sn"]),
        lon_jupiter_deg=lon_j,
        lon_saturn_deg=lon_s,
        lon_uranus_deg=lon_u,
        lon_neptune_deg=lon_n,
        jupiter_saturn_separation_deg=angular_separation_deg(lon_j, lon_s),
        gnevyshev_ohl_same_side=gnevyshev_ohl_same_side(lon_j, lon_s),
        outer_collinearity=outer_planet_collinearity(
            {"jupiter": lon_j, "saturn": lon_s, "uranus": lon_u, "neptune": lon_n}
        ),
        jupiter_year_fraction=yf,
        hqiv_planetary_coupling=planetary["planetary_magnetic_coupling"],
        hqiv_planetary_multiplier=planetary["combined_multiplier"],
        hqiv_environment_phase=env_phase,
        hqiv_outside_gate=outside["combined_outside_gate"],
        activity_score=activity["activity_score"],
        active_belt_latitude_deg=active_belt_latitude_deg,
    )


@dataclass(frozen=True)
class CycleMatchRow:
    cycle: int
    parity: str
    minimum: ExtremumReadout
    maximum: ExtremumReadout
    gnevyshev_ohl_predicted_same_at_max: bool
    gnevyshev_ohl_match: bool
    hqiv_coupling_higher_at_max: bool
    hqiv_environment_phase_higher_at_max: bool
    activity_score_higher_at_max: bool
    collinearity_higher_at_max: bool
    jupiter_saturn_closer_at_max: bool


def load_cycles(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload["cycles"]


def analyze_cycles(
    cycles: list[dict[str, Any]],
    *,
    active_belt_latitude_deg: float,
    use_target_model: bool = True,
) -> dict[str, Any]:
    rows: list[CycleMatchRow] = []
    for row in cycles:
        n = int(row["number"])
        mn = readout_at(
            n, "minimum", row,
            active_belt_latitude_deg=active_belt_latitude_deg,
            use_target_model=use_target_model,
        )
        mx = readout_at(
            n, "maximum", row,
            active_belt_latitude_deg=active_belt_latitude_deg,
            use_target_model=use_target_model,
        )
        odd = n % 2 == 1
        predicted_same = odd
        go_match = mx.gnevyshev_ohl_same_side == predicted_same
        rows.append(
            CycleMatchRow(
                cycle=n,
                parity="odd" if odd else "even",
                minimum=mn,
                maximum=mx,
                gnevyshev_ohl_predicted_same_at_max=predicted_same,
                gnevyshev_ohl_match=go_match,
                hqiv_coupling_higher_at_max=mx.hqiv_planetary_coupling > mn.hqiv_planetary_coupling,
                hqiv_environment_phase_higher_at_max=mx.hqiv_environment_phase > mn.hqiv_environment_phase,
                activity_score_higher_at_max=mx.activity_score > mn.activity_score,
                collinearity_higher_at_max=mx.outer_collinearity > mn.outer_collinearity,
                jupiter_saturn_closer_at_max=mx.jupiter_saturn_separation_deg < mn.jupiter_saturn_separation_deg,
            )
        )

    n = len(rows)

    def rate(attr: str) -> float:
        return sum(1 for r in rows if getattr(r, attr)) / max(n, 1)

    max_near_jupiter_crest = sum(
        1
        for r in rows
        if abs(math.cos(2.0 * math.pi * r.maximum.jupiter_year_fraction)) > 0.7
    ) / max(n, 1)

    composite_target = (
        rate("gnevyshev_ohl_match")
        + rate("activity_score_higher_at_max")
        + rate("hqiv_coupling_higher_at_max")
    ) / 3.0

    return {
        "active_belt_latitude_deg": active_belt_latitude_deg,
        "use_target_model": use_target_model,
        "cycle_count": n,
        "summary": {
            "gnevyshev_ohl_match_rate": rate("gnevyshev_ohl_match"),
            "activity_score_higher_at_max_rate": rate("activity_score_higher_at_max"),
            "hqiv_coupling_higher_at_max_rate": rate("hqiv_coupling_higher_at_max"),
            "hqiv_environment_phase_higher_at_max_rate": rate("hqiv_environment_phase_higher_at_max"),
            "collinearity_higher_at_max_rate": rate("collinearity_higher_at_max"),
            "jupiter_saturn_closer_at_max_rate": rate("jupiter_saturn_closer_at_max"),
            "maximum_near_jupiter_harmonic_crest_rate": max_near_jupiter_crest,
            "composite_target_score": composite_target,
        },
        "cycles": [
            {
                "cycle": r.cycle,
                "parity": r.parity,
                "minimum": asdict(r.minimum),
                "maximum": asdict(r.maximum),
                "matches": {
                    "gnevyshev_ohl": r.gnevyshev_ohl_match,
                    "activity_score_max_gt_min": r.activity_score_higher_at_max,
                    "hqiv_coupling_max_gt_min": r.hqiv_coupling_higher_at_max,
                    "hqiv_environment_phase_max_gt_min": r.hqiv_environment_phase_higher_at_max,
                    "outer_collinearity_max_gt_min": r.collinearity_higher_at_max,
                    "jupiter_saturn_closer_at_max": r.jupiter_saturn_closer_at_max,
                },
            }
            for r in rows
        ],
    }


def fit_target_model(cycles: list[dict[str, Any]]) -> dict[str, Any]:
    """
    Select active-belt latitude and baseline vs target model by composite score.

    Candidates: monogamy (≈23.6°), Rindler-half (≈26.6°), legacy 30°.
    """
    belt = sd.solar_active_belt_witness()
    candidates = [
        ("monogamy", belt["latitude_monogamy_deg"]),
        ("rindler_half", belt["latitude_rindler_half_deg"]),
        ("legacy_obs", belt["latitude_legacy_obs_deg"]),
    ]
    baseline_rows: list[dict[str, Any]] = []
    target_rows: list[dict[str, Any]] = []
    for name, lat in candidates:
        baseline_rows.append(
            {
                "candidate": name,
                "latitude_deg": lat,
                **analyze_cycles(cycles, active_belt_latitude_deg=lat, use_target_model=False)["summary"],
            }
        )
        target_rows.append(
            {
                "candidate": name,
                "latitude_deg": lat,
                **analyze_cycles(cycles, active_belt_latitude_deg=lat, use_target_model=True)["summary"],
            }
        )
    best_baseline = max(baseline_rows, key=lambda r: r["composite_target_score"])
    best_target = max(
        target_rows,
        key=lambda r: (
            r["composite_target_score"],
            -abs(
                sd.solar_cycle_oscillator(active_belt_latitude_deg=r["latitude_deg"]).estimated_period_years
                - sd.JUPITER_ORBITAL_PERIOD_YEARS
            ),
        ),
    )
    chosen_lat = best_target["latitude_deg"]
    chosen_name = best_target["candidate"]
    detailed = analyze_cycles(
        cycles,
        active_belt_latitude_deg=chosen_lat,
        use_target_model=True,
    )
    cycle = sd.solar_cycle_oscillator(active_belt_latitude_deg=chosen_lat)
    return {
        "active_belt_witness": belt,
        "candidate_scores_baseline": baseline_rows,
        "candidate_scores_target_model": target_rows,
        "selected": {
            "candidate": chosen_name,
            "latitude_deg": chosen_lat,
            "use_target_model": True,
            "composite_target_score": best_target["composite_target_score"],
            "estimated_cycle_years": cycle.estimated_period_years,
        },
        "analysis": detailed,
    }


def build_report(cycles: list[dict[str, Any]]) -> dict[str, Any]:
    fit = fit_target_model(cycles)
    return {
        "source": "scripts/hqiv_solar_cycle_planetary_match.py",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "data_source": "data/solar_cycle_extrema.json",
        "target_model": {
            "description": (
                "Shear gate at compact-object active belt + measured J–S alignment "
                "+ Gnevyshev–Ohl parity dressing; latitude chosen to maximize composite score."
            ),
            "compact_object_witness_ref": "papers/compact_object_witness",
            "claim_status": "historical_alignment_target_model — not a Lean theorem",
        },
        "fit": fit,
        "summary": fit["analysis"]["summary"],
        "cycles": fit["analysis"]["cycles"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Solar cycle vs planetary alignment match")
    parser.add_argument(
        "--data",
        type=str,
        default=str(_ROOT / "data" / "solar_cycle_extrema.json"),
        help="SILSO extrema JSON",
    )
    parser.add_argument("--json", type=str, default="", help="Write match report JSON")
    args = parser.parse_args()

    cycles = load_cycles(Path(args.data))
    report = build_report(cycles)
    sel = report["fit"]["selected"]
    s = report["summary"]

    if args.json:
        out = Path(args.json)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out}")

    print(f"Cycles analyzed: {report['fit']['analysis']['cycle_count']} (12–25)")
    print(f"Selected belt: {sel['candidate']} @ {sel['latitude_deg']:.2f}° latitude")
    print(f"Estimated HQIV cycle: {sel['estimated_cycle_years']:.1f} yr")
    print(f"Composite target score: {sel['composite_target_score']:.1%}")
    print(f"Gnevyshev–Ohl match rate:        {s['gnevyshev_ohl_match_rate']:.1%}")
    print(f"Activity score max > min:          {s['activity_score_higher_at_max_rate']:.1%}")
    print(f"HQIV coupling max > min:           {s['hqiv_coupling_higher_at_max_rate']:.1%}")
    print(f"HQIV env phase max > min:          {s['hqiv_environment_phase_higher_at_max_rate']:.1%}")


if __name__ == "__main__":
    main()
