#!/usr/bin/env python3
"""
Log-edge two-prime phase probe (Route D).

Computes Lean-aligned `linePhase` readouts for primes 2 and 3 at known
nontrivial zeta zero heights and checks the unconditional height-pinning
lemma `two_prime_phases_pin_height` numerically.

Lean: `Hqiv/Story/S3LogPhaseEdge.two_prime_phases_pin_height`
"""

from __future__ import annotations

import argparse
import json
import cmath
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import mpmath as mp

FIRST_ZETA_ZEROS = [
    14.134725141734693790457251983562,
    21.022039638771554992628479593896,
    25.010857580145688763213790992562,
    30.424876125859513210311897530584,
    32.935061587739189690662368964074,
    37.586178158825671257217763480705,
    40.918719012147495187398126914633,
    43.327073280914999519496122165406,
    48.005150881167159727942472749427,
    49.773832477672302181916784678563,
]

DEFAULT_PRIMES = (2, 3, 5)


def line_phase(n: int, t: float) -> complex:
    """`linePhase n t = exp(-i t log n)` (Lean `S3LogPhaseEdge`)."""
    return cmath.exp(-1j * float(t) * math.log(n))


def phases_agree(z1: complex, z2: complex, tol: float = 1e-12) -> bool:
    if abs(z1) == 0 or abs(z2) == 0:
        return abs(z1 - z2) <= tol
    ratio = z1 / z2
    return abs(abs(ratio) - 1.0) <= tol and abs(mp.arg(ratio)) <= tol


@dataclass(frozen=True)
class ZeroPhaseRow:
    height: float
    zeta_abs: float
    phases: dict[int, complex]


@dataclass(frozen=True)
class PinCheck:
    t1: float
    t2: float
    primes: list[int]
    phases_match: bool
    heights_equal: bool


def probe_zero_phases(
    heights: list[float],
    primes: tuple[int, ...],
    mp_dps: int,
) -> list[ZeroPhaseRow]:
    mp.mp.dps = mp_dps
    rows: list[ZeroPhaseRow] = []
    for t in heights:
        s = mp.mpf("0.5") + 1j * mp.mpf(t)
        zeta_abs = float(abs(mp.zeta(s)))
        phase_map = {p: line_phase(p, t) for p in primes}
        rows.append(ZeroPhaseRow(height=t, zeta_abs=zeta_abs, phases=phase_map))
    return rows


def check_two_prime_pinning(
    heights: list[float],
    primes: tuple[int, ...],
    tol: float,
) -> list[PinCheck]:
    checks: list[PinCheck] = []
    for i, t1 in enumerate(heights):
        for t2 in heights[i + 1:]:
            match = all(
                phases_agree(line_phase(p, t1), line_phase(p, t2), tol) for p in primes
            )
            checks.append(
                PinCheck(
                    t1=t1,
                    t2=t2,
                    primes=list(primes),
                    phases_match=match,
                    heights_equal=abs(t1 - t2) <= tol,
                )
            )
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description="Log-edge two-prime phase probe")
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "data" / "log_edge_two_prime_phase_probe.json",
    )
    parser.add_argument("--mp-dps", type=int, default=50)
    parser.add_argument("--tol", type=float, default=1e-10)
    parser.add_argument("--count", type=int, default=len(FIRST_ZETA_ZEROS))
    args = parser.parse_args()

    heights = FIRST_ZETA_ZEROS[: max(1, args.count)]
    primes = DEFAULT_PRIMES

    rows = probe_zero_phases(heights, primes, args.mp_dps)
    pin_checks = check_two_prime_pinning(heights, primes, args.tol)

    false_pins = [c for c in pin_checks if c.phases_match and not c.heights_equal]
    ghost_pins = [c for c in pin_checks if not c.phases_match and c.heights_equal]

    payload = {
        "schema": "hqiv.log_edge_two_prime_phase_probe.v1",
        "lean_module": "Hqiv/Story/S3LogPhaseEdge.lean",
        "lean_theorems": [
            "two_prime_phases_pin_height",
            "three_prime_phases_pin_height",
        ],
        "primes": list(primes),
        "mp_dps": args.mp_dps,
        "tol": args.tol,
        "zero_count": len(heights),
        "zeros": [
            {
                "height": r.height,
                "zeta_abs": r.zeta_abs,
                "phases": {
                    str(p): {"re": pval.real, "im": pval.imag} for p, pval in r.phases.items()
                },
            }
            for r in rows
        ],
        "pin_checks": [asdict(c) for c in pin_checks],
        "summary": {
            "all_distinct_heights_distinct_phases": not false_pins,
            "false_pin_count": len(false_pins),
            "ghost_pin_count": len(ghost_pins),
            "min_zeta_abs": min(r.zeta_abs for r in rows),
            "max_zeta_abs": max(r.zeta_abs for r in rows),
        },
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    print(
        f"zeros={len(heights)} pin_checks={len(pin_checks)} "
        f"false_pins={len(false_pins)} min|zeta|={payload['summary']['min_zeta_abs']:.3e}"
    )


if __name__ == "__main__":
    main()
