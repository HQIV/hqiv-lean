#!/usr/bin/env python3
"""
Join SO(4) zero-orbit harmonic tails with Delta quarter-turn shell hits.

Inputs:
* ``so4_hopf_zero_orbit_probe.py`` gives zero-derived one-term harmonic indices
  k_zero = 1 + 2 gamma_n.
* ``so4_delta_quarter_orbit_probe.py`` gives shell indices where H_n or K_n
  nearly lands on a free-axis quarter-turn.

This script ranks near coincidences between those two families under a few
simple comparison maps:

* direct: quarter_shell ~= k_zero
* ratio: quarter_shell / k_zero
* modulo phase: frac(k_zero) vs quarter phase error is not meaningful by itself,
  but nearby integer indices are reported.

It is an exploration tool, not a proof.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import so4_delta_quarter_orbit_probe as quarter_probe
import so4_hopf_zero_orbit_probe as zero_probe

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data" / "so4_zero_quarter_join_probe.json"


@dataclass(frozen=True)
class JoinHit:
    zero_n: int
    gamma: float
    zero_harmonic_index_real: float
    zero_nearest_harmonic_index: int
    quarter_channel: str
    quarter_shell: int
    quarter_phase_fraction: float
    quarter_error_to_1_4: float
    direct_shell_minus_zero_index: float
    direct_abs_error: float
    shell_to_zero_ratio: float
    nearest_integer_ratio: int
    ratio_error: float
    scaled_zero_index_at_ratio: float


def best_join_hits(
    zero_rows: list[zero_probe.ZeroOrbitProbe],
    quarter_payload: dict,
    top: int,
) -> list[JoinHit]:
    quarter_rows = []
    for key in ("harmonic_H_hits", "curvature_K_hits"):
        quarter_rows.extend(quarter_payload[key])

    hits: list[JoinHit] = []
    for z in zero_rows:
        k = z.harmonic_index_real
        for q in quarter_rows:
            shell = int(q["n"])
            ratio = shell / k
            nearest_ratio = max(1, round(ratio))
            scaled = nearest_ratio * k
            hits.append(
                JoinHit(
                    zero_n=z.n,
                    gamma=z.gamma,
                    zero_harmonic_index_real=k,
                    zero_nearest_harmonic_index=z.nearest_harmonic_index,
                    quarter_channel=str(q["channel"]),
                    quarter_shell=shell,
                    quarter_phase_fraction=float(q["phase_fraction"]),
                    quarter_error_to_1_4=float(q["circular_error_to_quarter"]),
                    direct_shell_minus_zero_index=shell - k,
                    direct_abs_error=abs(shell - k),
                    shell_to_zero_ratio=ratio,
                    nearest_integer_ratio=nearest_ratio,
                    ratio_error=shell - scaled,
                    scaled_zero_index_at_ratio=scaled,
                )
            )

    # Prefer integer-ratio coincidences, with quarter precision as a tie-breaker.
    hits.sort(key=lambda h: (abs(h.ratio_error), h.quarter_error_to_1_4, h.direct_abs_error))
    return hits[:top]


def print_table(rows: list[JoinHit]) -> None:
    print(
        "zero  channel       q_shell  k_zero       ratio   ratio_err  "
        "q_err_1/4"
    )
    for row in rows:
        print(
            f"{row.zero_n:4d}  {row.quarter_channel:11s} "
            f"{row.quarter_shell:7d} {row.zero_harmonic_index_real:11.6f} "
            f"{row.nearest_integer_ratio:5d} {row.ratio_error:11.5f} "
            f"{row.quarter_error_to_1_4:10.3e}"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zeros", type=int, default=50, help="number of zeta zeros to probe")
    parser.add_argument("--limit", type=int, default=100_000, help="quarter-turn shell scan limit")
    parser.add_argument("--quarter-top", type=int, default=100, help="quarter hits per channel")
    parser.add_argument("--top", type=int, default=25, help="joined hits to report")
    parser.add_argument("--alpha", type=float, default=3.0 / 5.0, help="HQIV alpha weight")
    parser.add_argument("--json", action="store_true", help="print JSON to stdout")
    parser.add_argument("--write", type=Path, default=None, help="write JSON report path")
    args = parser.parse_args()

    zero_rows = zero_probe.run(args.zeros)
    quarter_payload = quarter_probe.scan(args.limit, args.quarter_top, args.alpha)
    join_rows = best_join_hits(zero_rows, quarter_payload, args.top)
    payload = {
        "description": "Join zeta-zero harmonic-tail indices with Delta quarter-turn shell hits",
        "parameters": {
            "zeros": args.zeros,
            "limit": args.limit,
            "quarter_top": args.quarter_top,
            "alpha": args.alpha,
        },
        "model": {
            "zero_index": "k_zero = 1 + 2 * gamma_n",
            "quarter_shell": "n where H_n mod 1 or K_n mod 1 ~= 1/4",
            "rank": "small abs(quarter_shell - round(quarter_shell/k_zero)*k_zero)",
        },
        "rows": [asdict(row) for row in join_rows],
    }

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print_table(join_rows)

    out = args.write
    if out is not None:
        if not out.is_absolute():
            out = ROOT / out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
