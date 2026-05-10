#!/usr/bin/env python3
"""
GRACE / GRACE-FO: order-of-magnitude acceleration anomaly calculator.

This script does **not** download Level-1 products; it gives reproducible numbers from
constants and user-supplied fractional shifts, plus optional CSV aggregation for ACC
columns you export yourself (e.g. from ISDC / PO.DAAC).

References (constants / mission context):
  - WGS84 Earth gravitational constant GM and equatorial radius (public).
  - GRACE / GRACE-FO mission handbooks (NASA / GFZ) for nominal altitude and separation.

HQIV tie (toy, not Lean-proved mapping):
  In `Hqiv/Physics/GlobalDetuning.lean`, lapse excess above 1 is `Φ + φ·t`.
  For a **hypothesis scan** only, you may set `--delta-g-over-g` explicitly, or use
  `--lapse-excess` with `--lapse-to-dg-model linear` so that
      δg/g ≈ alpha * lapse_excess
  mirroring the exponent `alpha = 3/5` from `Hqiv/Geometry/HQVMetric.lean` / `cubic_phase_relax_probe.py`.

Units:
  - 1 mGal = 1e-5 m/s²
  - 1 E (Eötvös) = 1e-9 s⁻²; for a perturbation δa (m/s²) one often reports δa * 1e9 as “mE” scale
    when comparing to gravity-gradient literature (check definition in each paper).

Examples:
  python3 scripts/grace_acceleration_anomaly.py
  python3 scripts/grace_acceleration_anomaly.py --delta-g-over-g 1e-9
  python3 scripts/grace_acceleration_anomaly.py --lapse-excess 1e-10 --lapse-to-dg-model linear
  python3 scripts/grace_acceleration_anomaly.py --csv path/to/acc_column.csv --col acc_m_s2
"""

from __future__ import annotations

import argparse
import csv
import math
import statistics
import sys
from dataclasses import dataclass

# Mirror HQIV imprint from `scripts/cubic_phase_relax_probe.py` / Lean `alpha_eq_3_5`.
ALPHA_HQIV = 3.0 / 5.0

# WGS84 (CODATA-style geodesy constants, widely tabulated)
GM_EARTH_M3_S2 = 3.986004418e14
R_EARTH_EQUATOR_M = 6_378_137.0

# Nominal GRACE / GRACE-FO LEO band (mean altitude varies; use as default)
DEFAULT_ALTITUDE_KM = 490.0
# Along-track separation at launch (GRACE ~220 km; GRACE-FO similar class)
DEFAULT_ALONG_TRACK_SEP_KM = 220.0


@dataclass(frozen=True)
class OrbitGeometry:
    altitude_km: float
    along_track_sep_km: float
    earth_radius_m: float
    gm_m3_s2: float

    @property
    def r_orbit_m(self) -> float:
        return self.earth_radius_m + self.altitude_km * 1000.0


def newtonian_g_m_s2(geom: OrbitGeometry) -> float:
    """Central-field magnitude |g| = GM / r^2 at circular orbit radius r."""
    r = geom.r_orbit_m
    return geom.gm_m3_s2 / (r * r)


def delta_a_from_fractional_g(g: float, delta_g_over_g: float) -> float:
    """δa ≈ g * (δG_eff / G) for a multiplicative shift in the coupling."""
    return g * delta_g_over_g


def mGal_from_m_s2(a: float) -> float:
    return a / 1e-5


def eotvos_times_1e9_from_m_s2(a: float) -> float:
    """Report δa * 1e9 (often printed as “nE” or compared to mE tables — verify paper conventions)."""
    return a * 1e9


def monopole_tidal_scale_m_s2(geom: OrbitGeometry) -> float:
    """
    Order-of-magnitude scale for *differential* Newtonian acceleration between two points
    separated by arc length L along a circular orbit of radius r in a pure monopole field:

        |Δa| ~ (GM / r^2) * (L / r) = GM * L / r^3.

    This is the magnitude of the difference of two nearly-equal centripetal acceleration
    vectors tilted by angle L/r. LOS projection in GRACE is a fraction of this; use as an
    upper-scale sanity bracket, not as the KBR observable.
    """
    r = geom.r_orbit_m
    L = geom.along_track_sep_km * 1000.0
    return geom.gm_m3_s2 * L / (r**3)


def delta_g_over_g_from_lapse_model(lapse_excess: float, alpha: float, model: str) -> float:
    if model == "linear":
        return alpha * lapse_excess
    if model == "none":
        raise ValueError("model none — pass --delta-g-over-g instead")
    raise ValueError(f"unknown lapse model: {model}")


def read_acc_csv(path: str, col: str) -> list[float]:
    out: list[float] = []
    with open(path, newline="", encoding="utf-8") as f:
        rdr = csv.DictReader(f)
        if col not in (rdr.fieldnames or []):
            raise SystemExit(f"column {col!r} not in CSV headers: {rdr.fieldnames}")
        for row in rdr:
            v = row.get(col, "").strip()
            if not v:
                continue
            out.append(float(v))
    return out


def summarize_acc(values: list[float]) -> dict[str, float]:
    if not values:
        raise ValueError("no values")
    mu = statistics.fmean(values)
    vr = statistics.pvariance(values) if len(values) > 1 else 0.0
    sigma = math.sqrt(vr)
    mx = max(abs(x - mu) for x in values)
    return {"mean_m_s2": mu, "rms_m_s2": sigma, "max_abs_dev_m_s2": mx, "n": float(len(values))}


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--altitude-km", type=float, default=DEFAULT_ALTITUDE_KM)
    p.add_argument("--along-track-km", type=float, default=DEFAULT_ALONG_TRACK_SEP_KM)
    p.add_argument("--earth-radius-m", type=float, default=R_EARTH_EQUATOR_M)
    p.add_argument("--gm", type=float, default=GM_EARTH_M3_S2, help="GM in m^3/s^2")
    p.add_argument("--delta-g-over-g", type=float, default=None, help="fractional shift in effective coupling")
    p.add_argument(
        "--target-delta-a-m-s2",
        type=float,
        default=None,
        help="infer δg/g = δa / |g| needed to produce this acceleration anomaly (m/s^2)",
    )
    p.add_argument("--lapse-excess", type=float, default=None, help="toy Φ+φ·t increment (dimensionless)")
    p.add_argument("--alpha", type=float, default=ALPHA_HQIV)
    p.add_argument(
        "--lapse-to-dg-model",
        choices=("linear", "none"),
        default="linear",
        help="if --lapse-excess set: δg/g = alpha * lapse_excess (linear toy)",
    )
    p.add_argument(
        "--no-baseline",
        action="store_true",
        help="skip printing Newtonian |g| and monopole tidal bracket",
    )
    p.add_argument("--csv", type=str, default=None, help="CSV with accelerometer residual column")
    p.add_argument("--col", type=str, default="acc_m_s2", help="CSV column name for acceleration (m/s^2)")

    args = p.parse_args(argv)

    geom = OrbitGeometry(
        altitude_km=args.altitude_km,
        along_track_sep_km=args.along_track_km,
        earth_radius_m=args.earth_radius_m,
        gm_m3_s2=args.gm,
    )
    g = newtonian_g_m_s2(geom)
    tidal = monopole_tidal_scale_m_s2(geom)

    if not args.no_baseline:
        print("=== Orbit / Newtonian baseline ===")
        print(f"  r = R_Earth + h = {geom.r_orbit_m:.1f} m  (h = {geom.altitude_km:.1f} km)")
        print(f"  |g| = GM/r^2 = {g:.6f} m/s^2")
        print(f"  |g| = {mGal_from_m_s2(g):.3f} mGal")
        print(f"  Monopole tidal vector-difference scale GM*L/r^3 = {tidal:.6e} m/s^2 (~upper bracket, not LOS)")
        print(f"  Same in mGal: {mGal_from_m_s2(tidal):.6f}")
        print()

    dg: float | None = args.delta_g_over_g
    if dg is None and args.lapse_excess is not None:
        if args.lapse_to_dg_model == "none":
            print("error: --lapse-excess requires a model; use --lapse-to-dg-model linear", file=sys.stderr)
            return 2
        dg = delta_g_over_g_from_lapse_model(args.lapse_excess, args.alpha, args.lapse_to_dg_model)

    if args.target_delta_a_m_s2 is not None:
        tgt = args.target_delta_a_m_s2
        req = tgt / g if g != 0 else float("nan")
        print("=== Target acceleration → fractional coupling ===")
        print(f"  target δa = {tgt:.6e} m/s^2  ({mGal_from_m_s2(tgt):.6f} mGal)")
        print(f"  implied δg/g = δa / |g| = {req:.6e}")
        print()

    if dg is not None:
        da = delta_a_from_fractional_g(g, dg)
        print("=== Fractional coupling anomaly ===")
        print(f"  δg/g = {dg:.6e}")
        print(f"  δa ≈ g * (δg/g) = {da:.6e} m/s^2")
        print(f"       = {mGal_from_m_s2(da):.6f} mGal")
        print(f"  δa * 1e9 (E-type scalar) = {eotvos_times_1e9_from_m_s2(da):.6f}")
        if args.lapse_excess is not None:
            print(f"  (from lapse_excess={args.lapse_excess:g}, alpha={args.alpha}, model={args.lapse_to_dg_model})")
        print()

    if args.csv:
        vals = read_acc_csv(args.csv, args.col)
        s = summarize_acc(vals)
        print("=== CSV accelerometer column summary ===")
        print(f"  n = {int(s['n'])}")
        print(f"  mean = {s['mean_m_s2']:.6e} m/s^2  ({mGal_from_m_s2(s['mean_m_s2']):.6f} mGal)")
        print(f"  rms about mean = {s['rms_m_s2']:.6e} m/s^2  ({mGal_from_m_s2(s['rms_m_s2']):.6f} mGal)")
        print(f"  max |x - mean| = {s['max_abs_dev_m_s2']:.6e} m/s^2  ({mGal_from_m_s2(s['max_abs_dev_m_s2']):.6f} mGal)")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
