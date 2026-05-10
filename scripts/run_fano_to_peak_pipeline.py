#!/usr/bin/env python3
"""
End-to-end adapter:
  raw Fano-angle samples -> FFT slice probe -> defect-profile input -> peak witness

This is a practical workflow wrapper for Path C in the roadmap.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


TWO_PI = 2.0 * math.pi
FANO_ANGLES = [TWO_PI * k / 7.0 for k in range(7)]


def wrap_angle(theta: float) -> float:
    return theta % TWO_PI


def circular_distance(a: float, b: float) -> float:
    d = abs(a - b) % TWO_PI
    return min(d, TWO_PI - d)


def nearest_fano_index(theta: float) -> int:
    t = wrap_angle(theta)
    return min(range(7), key=lambda i: circular_distance(t, FANO_ANGLES[i]))


def run_cmd(cmd: list[str], cwd: Path) -> None:
    proc = subprocess.run(cmd, cwd=str(cwd), check=False)
    if proc.returncode != 0:
        raise SystemExit(proc.returncode)


def parse_samples(samples_path: Path) -> list[dict[str, Any]]:
    obj = json.loads(samples_path.read_text())
    samples = obj.get("samples")
    if not isinstance(samples, list):
        raise ValueError("Input must contain `samples` list.")
    return samples


def build_defect_profile_from_retained_slices(
    samples: list[dict[str, Any]],
    retained_slices: set[int],
) -> list[float]:
    if not samples:
        raise ValueError("No samples found.")
    max_m = max(int(s["m"]) for s in samples)
    sums = [0.0] * (max_m + 1)
    counts = [0] * (max_m + 1)

    for s in samples:
        m = int(s["m"])
        theta = float(s["theta"])
        value = float(s["value"])
        idx = nearest_fano_index(theta)
        if idx in retained_slices:
            # Use absolute amplitude as a stable defect-like proxy.
            sums[m] += abs(value)
            counts[m] += 1

    profile: list[float] = []
    for m in range(max_m + 1):
        if counts[m] == 0:
            profile.append(0.0)
        else:
            profile.append(sums[m] / counts[m])
    return profile


def main() -> None:
    parser = argparse.ArgumentParser(description="Run Fano FFT -> peak witness pipeline.")
    parser.add_argument("--input", required=True, help="Input raw samples JSON ({samples:[...]})")
    parser.add_argument(
        "--fft-report",
        default="data/fano_slice_fft_report.pipeline.json",
        help="FFT probe report output path",
    )
    parser.add_argument(
        "--peak-input",
        default="data/slice_defect_peak_input.pipeline.json",
        help="Intermediate peak-check input JSON path",
    )
    parser.add_argument(
        "--peak-witness",
        default="data/slice_defect_peak_witness.pipeline.json",
        help="Final peak witness output JSON path",
    )
    parser.add_argument("--max-decay-slope", type=float, default=-0.02)
    parser.add_argument("--min-points", type=int, default=16)
    parser.add_argument(
        "--N",
        type=int,
        default=0,
        help="Window size. 0 means full profile length.",
    )
    parser.add_argument(
        "--candidate-mode",
        choices=["auto", "last"],
        default="auto",
        help="auto=argmax abs(defect), last=use N-1.",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    samples_path = Path(args.input)
    if not samples_path.is_absolute():
        samples_path = repo_root / samples_path
    if not samples_path.exists():
        raise SystemExit(f"Missing input file: {samples_path}")

    fft_report_path = Path(args.fft_report)
    if not fft_report_path.is_absolute():
        fft_report_path = repo_root / fft_report_path
    peak_input_path = Path(args.peak_input)
    if not peak_input_path.is_absolute():
        peak_input_path = repo_root / peak_input_path
    peak_witness_path = Path(args.peak_witness)
    if not peak_witness_path.is_absolute():
        peak_witness_path = repo_root / peak_witness_path

    fft_report_path.parent.mkdir(parents=True, exist_ok=True)
    peak_input_path.parent.mkdir(parents=True, exist_ok=True)
    peak_witness_path.parent.mkdir(parents=True, exist_ok=True)

    run_cmd(
        [
            sys.executable,
            "scripts/fano_slice_fft_probe.py",
            "--input",
            str(samples_path),
            "--output",
            str(fft_report_path),
            "--max-decay-slope",
            str(args.max_decay_slope),
            "--min-points",
            str(args.min_points),
        ],
        cwd=repo_root,
    )

    fft_report = json.loads(fft_report_path.read_text())
    retained = {
        int(row["slice_index"])
        for row in fft_report.get("slices", [])
        if bool(row.get("kept_for_fft"))
    }
    if not retained:
        raise SystemExit("No retained slices from FFT probe. Relax thresholds.")

    samples = parse_samples(samples_path)
    defect_profile = build_defect_profile_from_retained_slices(samples, retained)
    if not defect_profile:
        raise SystemExit("Empty defect profile after retained-slice aggregation.")

    n_window = len(defect_profile) if args.N <= 0 else min(args.N, len(defect_profile))
    if n_window <= 0:
        raise SystemExit("Window N must be positive after clipping.")

    if args.candidate_mode == "last":
        candidate_m = n_window - 1
    else:
        candidate_m = max(range(n_window), key=lambda i: abs(defect_profile[i]))

    peak_input = {
        "defect_profile": defect_profile,
        "N": n_window,
        "candidate_m": candidate_m,
        "meta": {
            "source": "run_fano_to_peak_pipeline",
            "retained_slices": sorted(retained),
            "candidate_mode": args.candidate_mode,
        },
    }
    peak_input_path.write_text(json.dumps(peak_input, indent=2))

    run_cmd(
        [
            sys.executable,
            "scripts/search_slice_defect_peak.py",
            "--input",
            str(peak_input_path),
            "--output",
            str(peak_witness_path),
        ],
        cwd=repo_root,
    )

    witness = json.loads(peak_witness_path.read_text())
    print("Fano->Peak pipeline complete")
    print("=" * 27)
    print(f"retained slices : {sorted(retained)}")
    print(f"N               : {witness['N']}")
    print(f"candidate_m     : {witness['candidate_m']}")
    print(f"all_holds       : {witness['all_holds']}")
    print(f"fft report      : {fft_report_path}")
    print(f"peak witness    : {peak_witness_path}")


if __name__ == "__main__":
    main()

