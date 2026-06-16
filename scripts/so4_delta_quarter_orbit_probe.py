#!/usr/bin/env python3
"""
Probe SO(4) = SO(3) + Delta quarter-turn hits from harmonic Delta orbits.

Model
-----
Treat the harmonic/Delta channel as a phase orbit modulo one full turn:

    phase_fraction(n) = H_n mod 1

and compare it with the free-axis quarter-turn target:

    quarter = 1/4  <=>  angle = pi/2.

The HQIV curvature-weighted companion is also scanned:

    K_n = H_n + alpha * sum_{m=0}^{n-1} log(m+1)/(m+1),
    alpha = 3/5 by default.

This is exploratory numerics.  It does not prove that the harmonic orbit selects
zeta zeros; it identifies shell indices where the Delta/harmonic phase is close
to a quarter-turn on the free axis.
"""

from __future__ import annotations

import argparse
import heapq
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data" / "so4_delta_quarter_orbit_probe.json"


@dataclass(frozen=True)
class QuarterHit:
    n: int
    channel: str
    value: float
    phase_fraction: float
    circular_error_to_quarter: float
    angle_rad: float
    angle_deg: float
    harmonic_term: float
    delta_to_previous: float


def frac(x: float) -> float:
    return x - math.floor(x)


def circular_distance(a: float, b: float) -> float:
    d = abs(a - b) % 1.0
    return min(d, 1.0 - d)


def push_hit(heap: list[tuple[float, int, QuarterHit]], limit: int, hit: QuarterHit) -> None:
    item = (-hit.circular_error_to_quarter, hit.n, hit)
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif item > heap[0]:
        heapq.heapreplace(heap, item)


def scan(limit_n: int, top: int, alpha: float) -> dict:
    quarter = 0.25
    harmonic_heap: list[tuple[float, int, QuarterHit]] = []
    curvature_heap: list[tuple[float, int, QuarterHit]] = []

    h = 0.0
    log_tail = 0.0
    prev_h = 0.0
    prev_k = 0.0

    for n in range(1, limit_n + 1):
        term = 1.0 / n
        h += term
        log_tail += math.log(n) / n
        k = h + alpha * log_tail

        for channel, value, prev, heap in (
            ("harmonic_H", h, prev_h, harmonic_heap),
            ("curvature_K", k, prev_k, curvature_heap),
        ):
            phase_fraction = frac(value)
            error = circular_distance(phase_fraction, quarter)
            angle = math.tau * phase_fraction
            push_hit(
                heap,
                top,
                QuarterHit(
                    n=n,
                    channel=channel,
                    value=value,
                    phase_fraction=phase_fraction,
                    circular_error_to_quarter=error,
                    angle_rad=angle,
                    angle_deg=math.degrees(angle),
                    harmonic_term=term,
                    delta_to_previous=value - prev,
                ),
            )

        prev_h = h
        prev_k = k

    def unpack(heap: list[tuple[float, int, QuarterHit]]) -> list[QuarterHit]:
        return [item[2] for item in sorted(heap, key=lambda x: (-x[0], x[1]))]

    return {
        "model": {
            "quarter_turn_fraction": quarter,
            "quarter_turn_angle_rad": math.pi / 2,
            "alpha": alpha,
            "limit_n": limit_n,
        },
        "harmonic_H_hits": [asdict(hit) for hit in unpack(harmonic_heap)],
        "curvature_K_hits": [asdict(hit) for hit in unpack(curvature_heap)],
    }


def print_hits(label: str, rows: list[dict]) -> None:
    print(label)
    print("n       phase_frac       err_to_1/4       angle_deg      term")
    for row in rows:
        print(
            f"{row['n']:7d} {row['phase_fraction']:16.12f} "
            f"{row['circular_error_to_quarter']:16.3e} "
            f"{row['angle_deg']:14.8f} {row['harmonic_term']:12.6e}"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=100_000, help="largest shell index to scan")
    parser.add_argument("--top", type=int, default=12, help="number of closest hits to keep")
    parser.add_argument("--alpha", type=float, default=3.0 / 5.0, help="HQIV alpha weight")
    parser.add_argument("--json", action="store_true", help="print JSON to stdout")
    parser.add_argument("--write", type=Path, default=None, help="write JSON report path")
    args = parser.parse_args()

    payload = scan(args.limit, args.top, args.alpha)

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print_hits("Bare harmonic orbit H_n mod 1", payload["harmonic_H_hits"])
        print()
        print_hits("Curvature-weighted orbit K_n mod 1", payload["curvature_K_hits"])

    out = args.write
    if out is not None:
        if not out.is_absolute():
            out = ROOT / out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
