#!/usr/bin/env python3
"""
Explore SO(4) / Hopf-fiber zero orbits against one-term harmonic tails.

Model being probed
------------------
For a critical-line zeta zero rho_n = 1/2 + i gamma_n:

* the origin-centered tangent through (0, 0) and (1/2, gamma_n) has ratio 2 gamma_n;
* the SO(4) doubled readout is (1, 2 gamma_n);
* the projective intercept is u / (1 + u), where u = 2 gamma_n;
* the complementary tail 1 / (1 + u) is a single harmonic-term-shaped value.

This script does not prove zero localization.  It is a numerical exploration of
whether the zero orbit's projective complement shadows one harmonic term 1/k.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "data" / "so4_hopf_zero_orbit_probe.json"

FIRST_ZERO_FALLBACK = (
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
)


@dataclass(frozen=True)
class ZeroOrbitProbe:
    n: int
    gamma: float
    tangent_ratio: float
    doubled_endpoint: tuple[float, float]
    origin_axis_angle_rad: float
    origin_axis_angle_deg: float
    projective_intercept: float
    harmonic_tail: float
    harmonic_index_real: float
    nearest_harmonic_index: int
    nearest_harmonic_term: float
    harmonic_tail_error: float
    harmonic_tail_rel_error: float
    phase_mod_tau: float
    phase_turn_fraction: float


def zeta_zero_ordinates(count: int) -> list[float]:
    """Return the first ``count`` positive zeta-zero ordinates."""
    try:
        import mpmath as mp  # type: ignore

        mp.mp.dps = 40
        return [float(mp.im(mp.zetazero(n))) for n in range(1, count + 1)]
    except Exception:
        if count > len(FIRST_ZERO_FALLBACK):
            raise RuntimeError(
                "mpmath zeta zeros unavailable and fallback only contains "
                f"{len(FIRST_ZERO_FALLBACK)} zeros"
            )
        return list(FIRST_ZERO_FALLBACK[:count])


def probe_zero(n: int, gamma: float) -> ZeroOrbitProbe:
    tangent_ratio = 2.0 * gamma
    projective_intercept = tangent_ratio / (1.0 + tangent_ratio)
    harmonic_tail = 1.0 - projective_intercept
    harmonic_index_real = 1.0 / harmonic_tail
    nearest_harmonic_index = max(1, round(harmonic_index_real))
    nearest_harmonic_term = 1.0 / nearest_harmonic_index
    harmonic_tail_error = harmonic_tail - nearest_harmonic_term
    harmonic_tail_rel_error = harmonic_tail_error / nearest_harmonic_term
    phase_mod_tau = math.fmod(gamma, math.tau)
    if phase_mod_tau < 0:
        phase_mod_tau += math.tau
    return ZeroOrbitProbe(
        n=n,
        gamma=gamma,
        tangent_ratio=tangent_ratio,
        doubled_endpoint=(1.0, tangent_ratio),
        origin_axis_angle_rad=math.atan(tangent_ratio),
        origin_axis_angle_deg=math.degrees(math.atan(tangent_ratio)),
        projective_intercept=projective_intercept,
        harmonic_tail=harmonic_tail,
        harmonic_index_real=harmonic_index_real,
        nearest_harmonic_index=nearest_harmonic_index,
        nearest_harmonic_term=nearest_harmonic_term,
        harmonic_tail_error=harmonic_tail_error,
        harmonic_tail_rel_error=harmonic_tail_rel_error,
        phase_mod_tau=phase_mod_tau,
        phase_turn_fraction=phase_mod_tau / math.tau,
    )


def run(count: int) -> list[ZeroOrbitProbe]:
    return [probe_zero(i, gamma) for i, gamma in enumerate(zeta_zero_ordinates(count), 1)]


def print_table(rows: Iterable[ZeroOrbitProbe]) -> None:
    print(
        "n  gamma              tan=2gamma        tail=1/(1+2g)   "
        "nearest 1/k       rel_err      angle_deg"
    )
    for row in rows:
        print(
            f"{row.n:2d} {row.gamma:17.12f} {row.tangent_ratio:17.12f} "
            f"{row.harmonic_tail:15.12f} 1/{row.nearest_harmonic_index:<4d} "
            f"{row.harmonic_tail_rel_error: .3e} {row.origin_axis_angle_deg:10.6f}"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=10, help="number of zeta zeros to probe")
    parser.add_argument("--json", action="store_true", help="print JSON to stdout")
    parser.add_argument("--write", type=Path, default=None, help="write JSON report path")
    args = parser.parse_args()

    rows = run(args.count)
    payload = {
        "description": "SO(4) Hopf zero orbit tangent/harmonic-tail probe",
        "model": {
            "zero_point": "(1/2, gamma_n)",
            "tangent_ratio": "2 * gamma_n",
            "doubled_endpoint": "(1, 2 * gamma_n)",
            "projective_intercept": "(2 * gamma_n) / (1 + 2 * gamma_n)",
            "harmonic_tail": "1 / (1 + 2 * gamma_n)",
        },
        "rows": [asdict(row) for row in rows],
    }

    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print_table(rows)

    out = args.write
    if out is not None:
        if not out.is_absolute():
            out = ROOT / out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
