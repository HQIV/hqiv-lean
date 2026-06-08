#!/usr/bin/env python3
"""
Search/check bounded-window absolute peaks for slice-defect profiles.

This mirrors the Lean-side predicate:
  Hqiv.Physics.IsWindowAbsPeak (sliceDefectProfileAtZ r observedArea z) N m
which unfolds to:
  ∀ n < N, |defect(n)| ≤ |defect(m)|.

Input JSON may use either:
  A) direct defect profile values at fixed z:
     {
       "defect_profile": [..],   # defect[m]
       "N": 40,                  # optional; default = len(profile)
       "candidate_m": 12         # optional; default = argmax |defect|
     }

  B) observed + radius ladder (fixed z):
     {
       "z": 0.3,
       "radii": [..],            # interpreted as r(m+1), index m
       "observed_area": [..],    # observed_area(m, z), same indexing
       "N": 40,                  # optional
       "candidate_m": 12         # optional
     }

Output JSON contains a machine-checkable witness of all inequalities on range(N).
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class PeakCheckResult:
    n: int
    abs_defect_n: float
    abs_defect_candidate: float
    holds: bool


def pi_slice_area_baseline(radius: float, z: float) -> float:
    return math.pi * (radius * radius - z * z)


def build_defect_profile_from_observed(
    z: float,
    radii_mplus1: list[float],
    observed_area: list[float],
) -> list[float]:
    if len(radii_mplus1) != len(observed_area):
        raise ValueError("`radii` and `observed_area` must have the same length.")
    return [
        observed_area[m] - pi_slice_area_baseline(radii_mplus1[m], z)
        for m in range(len(observed_area))
    ]


def argmax_abs(xs: list[float], window_n: int) -> int:
    return max(range(window_n), key=lambda i: abs(xs[i]))


def check_window_abs_peak(
    defect_profile: list[float],
    n_window: int,
    candidate_m: int,
) -> list[PeakCheckResult]:
    if n_window <= 0:
        raise ValueError("N must be positive.")
    if n_window > len(defect_profile):
        raise ValueError(f"N={n_window} exceeds profile length={len(defect_profile)}.")
    if not (0 <= candidate_m < n_window):
        raise ValueError(f"candidate_m={candidate_m} must satisfy 0 <= candidate_m < N={n_window}.")

    abs_candidate = abs(defect_profile[candidate_m])
    return [
        PeakCheckResult(
            n=n,
            abs_defect_n=abs(defect_profile[n]),
            abs_defect_candidate=abs_candidate,
            holds=(abs(defect_profile[n]) <= abs_candidate),
        )
        for n in range(n_window)
    ]


def parse_input(data: dict[str, Any]) -> tuple[list[float], int, int, dict[str, Any]]:
    if "defect_profile" in data:
        profile = [float(x) for x in data["defect_profile"]]
        if not profile:
            raise ValueError("`defect_profile` cannot be empty.")
        n_window = int(data.get("N", len(profile)))
        candidate = int(data.get("candidate_m", argmax_abs(profile, n_window)))
        meta = {"mode": "direct_defect_profile"}
        return profile, n_window, candidate, meta

    required = {"z", "radii", "observed_area"}
    if required.issubset(data.keys()):
        z = float(data["z"])
        radii = [float(x) for x in data["radii"]]
        observed = [float(x) for x in data["observed_area"]]
        profile = build_defect_profile_from_observed(z=z, radii_mplus1=radii, observed_area=observed)
        n_window = int(data.get("N", len(profile)))
        candidate = int(data.get("candidate_m", argmax_abs(profile, n_window)))
        meta = {
            "mode": "observed_minus_pi_baseline",
            "z": z,
        }
        return profile, n_window, candidate, meta

    raise ValueError(
        "Input JSON must contain either `defect_profile`, "
        "or all of: `z`, `radii`, `observed_area`."
    )


def build_output(
    profile: list[float],
    n_window: int,
    candidate_m: int,
    checks: list[PeakCheckResult],
    meta: dict[str, Any],
) -> dict[str, Any]:
    all_holds = all(c.holds for c in checks)
    return {
        "meta": meta,
        "N": n_window,
        "candidate_m": candidate_m,
        "candidate_abs_defect": abs(profile[candidate_m]),
        "all_holds": all_holds,
        "checks": [
            {
                "n": c.n,
                "abs_defect_n": c.abs_defect_n,
                "abs_defect_candidate": c.abs_defect_candidate,
                "holds": c.holds,
            }
            for c in checks
        ],
        "lean_target_shape": (
            "IsWindowAbsPeak (sliceDefectProfileAtZ r observedArea z) N candidate_m "
            "(equivalently: forall n in Finset.range N, |defect n| <= |defect candidate_m|)"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Search/check bounded-window abs-defect peak witness.")
    parser.add_argument(
        "--input",
        required=True,
        help="Input JSON file (profile or observed/baseline mode).",
    )
    parser.add_argument(
        "--output",
        default="data/slice_defect_peak_witness.json",
        help="Output witness JSON path (default: data/slice_defect_peak_witness.json).",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        raise SystemExit(f"Missing input file: {input_path}")

    data = json.loads(input_path.read_text())
    profile, n_window, candidate_m, meta = parse_input(data)
    checks = check_window_abs_peak(profile, n_window=n_window, candidate_m=candidate_m)
    witness = build_output(profile, n_window=n_window, candidate_m=candidate_m, checks=checks, meta=meta)

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(witness, indent=2))

    print("Slice defect peak search/check")
    print("=" * 36)
    print(f"mode         : {meta['mode']}")
    print(f"N            : {n_window}")
    print(f"candidate_m  : {candidate_m}")
    print(f"all_holds    : {witness['all_holds']}")
    print(f"output       : {output_path}")
    if not witness["all_holds"]:
        bad = [c["n"] for c in witness["checks"] if not c["holds"]]
        print(f"violations   : {bad}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()

