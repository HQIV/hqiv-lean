#!/usr/bin/env python3
"""
Fano-angle slice isolation + FFT periodicity probe.

Goal:
- Assign shell samples to one of 7 Fano-plane angular slices.
- Keep only slices/vectors that do not instantly decay.
- Run FFT on each retained slice and report dominant periodicities.

Input JSON format:
{
  "samples": [
    {"m": 0, "theta": 0.12, "value": 1.03},
    {"m": 1, "theta": 0.15, "value": 0.92}
  ]
}

Where:
- m: shell index (integer)
- theta: angle in radians (any real; wrapped mod 2*pi)
- value: real signal/amplitude (float)

Usage:
  python3 scripts/fano_slice_fft_probe.py --input data/my_samples.json
  python3 scripts/fano_slice_fft_probe.py --input data/my_samples.json --output data/fano_fft_report.json
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


TWO_PI = 2.0 * math.pi
FANO_ANGLES = [TWO_PI * k / 7.0 for k in range(7)]


@dataclass(frozen=True)
class Sample:
    m: int
    theta: float
    value: float


def wrap_angle(theta: float) -> float:
    return theta % TWO_PI


def circular_distance(a: float, b: float) -> float:
    d = abs(a - b) % TWO_PI
    return min(d, TWO_PI - d)


def nearest_fano_index(theta: float) -> int:
    t = wrap_angle(theta)
    return min(range(7), key=lambda i: circular_distance(t, FANO_ANGLES[i]))


def fit_log_decay_slope(series: list[tuple[int, float]]) -> float:
    """
    Fit slope of log(|value| + eps) vs shell index m.
    More negative => faster decay.
    """
    if len(series) < 2:
        return float("-inf")
    eps = 1e-12
    xs = [float(m) for m, _ in series]
    ys = [math.log(abs(v) + eps) for _, v in series]
    xbar = sum(xs) / len(xs)
    ybar = sum(ys) / len(ys)
    num = sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys))
    den = sum((x - xbar) ** 2 for x in xs)
    if den == 0.0:
        return float("-inf")
    return num / den


def dft_real(values: list[float]) -> list[complex]:
    n = len(values)
    out: list[complex] = []
    for k in range(n):
        s = 0j
        for t, x in enumerate(values):
            s += x * cmath.exp(-2j * math.pi * k * t / n)
        out.append(s)
    return out


def dominant_frequency(values: list[float]) -> dict[str, float]:
    n = len(values)
    if n < 2:
        return {"k": 0.0, "amplitude": 0.0, "period_shells": float("inf")}
    spec = dft_real(values)
    # Ignore DC component k=0
    candidates = range(1, n // 2 + 1)
    k_star = max(candidates, key=lambda k: abs(spec[k]))
    amp = abs(spec[k_star])
    period = float(n) / float(k_star) if k_star != 0 else float("inf")
    return {"k": float(k_star), "amplitude": amp, "period_shells": period}


def build_series_by_slice(samples: list[Sample]) -> dict[int, list[tuple[int, float]]]:
    buckets: dict[int, list[tuple[int, float]]] = {i: [] for i in range(7)}
    for s in samples:
        idx = nearest_fano_index(s.theta)
        buckets[idx].append((s.m, s.value))
    for idx in buckets:
        buckets[idx].sort(key=lambda t: t[0])
    return buckets


def densify_series(series: list[tuple[int, float]]) -> list[float]:
    """
    Convert sparse shell-value pairs to dense vector from min_m..max_m.
    Missing shells are filled with 0.
    """
    if not series:
        return []
    m_min = series[0][0]
    m_max = series[-1][0]
    arr = [0.0] * (m_max - m_min + 1)
    for m, v in series:
        arr[m - m_min] = v
    return arr


def run_probe(samples: list[Sample], max_decay_slope: float, min_points: int) -> dict[str, Any]:
    by_slice = build_series_by_slice(samples)
    report_slices: list[dict[str, Any]] = []
    retained = 0

    for idx, series in by_slice.items():
        slope = fit_log_decay_slope(series)
        dense = densify_series(series)
        keep = len(series) >= min_points and slope >= max_decay_slope
        dom = dominant_frequency(dense) if keep else {"k": 0.0, "amplitude": 0.0, "period_shells": float("inf")}
        if keep:
            retained += 1
        report_slices.append(
            {
                "slice_index": idx,
                "fano_angle_rad": FANO_ANGLES[idx],
                "points": len(series),
                "decay_slope_log_abs": slope,
                "kept_for_fft": keep,
                "dominant_frequency": dom,
            }
        )

    report_slices.sort(key=lambda r: r["slice_index"])
    return {
        "summary": {
            "total_samples": len(samples),
            "slices_total": 7,
            "slices_retained": retained,
            "max_decay_slope": max_decay_slope,
            "min_points": min_points,
        },
        "slices": report_slices,
    }


def parse_samples(obj: dict[str, Any]) -> list[Sample]:
    raw = obj.get("samples")
    if not isinstance(raw, list):
        raise ValueError("Input JSON must contain a `samples` list.")
    out: list[Sample] = []
    for i, item in enumerate(raw):
        try:
            out.append(
                Sample(
                    m=int(item["m"]),
                    theta=float(item["theta"]),
                    value=float(item["value"]),
                )
            )
        except Exception as ex:
            raise ValueError(f"Invalid sample at index {i}: {item}") from ex
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Fano-angle slice FFT periodicity probe.")
    parser.add_argument("--input", required=True, help="Input JSON file containing `samples`.")
    parser.add_argument(
        "--output",
        default="data/fano_slice_fft_report.json",
        help="Output report JSON path (default: data/fano_slice_fft_report.json).",
    )
    parser.add_argument(
        "--max-decay-slope",
        type=float,
        default=-0.02,
        help="Keep slices with fitted log-decay slope >= this threshold (default: -0.02).",
    )
    parser.add_argument(
        "--min-points",
        type=int,
        default=16,
        help="Minimum sample count in a slice to run FFT (default: 16).",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        raise SystemExit(f"Missing input file: {input_path}")
    data = json.loads(input_path.read_text())
    samples = parse_samples(data)
    report = run_probe(samples, max_decay_slope=args.max_decay_slope, min_points=args.min_points)

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2))

    print("Fano slice FFT probe")
    print("=" * 24)
    print(f"samples        : {report['summary']['total_samples']}")
    print(f"slices retained: {report['summary']['slices_retained']} / 7")
    print(f"output         : {output_path}")


if __name__ == "__main__":
    main()

