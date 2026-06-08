#!/usr/bin/env python3
"""
Batch sweep for frame-well curvature probe.

It evaluates multiple axis-horizon configurations, ranks them by
excitation null-test p-value (then chosen score), and writes summary files.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import os
import subprocess
import sys
from dataclasses import dataclass, asdict

import frame_well_curvature_probe as probe


@dataclass
class BatchRow:
    run_id: str
    axis_horizons: str
    chosen_score: float
    empirical_p_value: float
    lockin_well_identity: float
    axis_mean_l2: float
    axis_min_l2: float
    baseline_horizon: int
    best_axis: str
    best_axis_p_value: float
    mean_axis_p_value: float


def parse_axis_names(raw: str) -> list[str]:
    names = [x.strip() for x in raw.split(",") if x.strip()]
    if not names:
        raise ValueError("axis names cannot be empty")
    return names


def parse_range(raw: str) -> list[int]:
    # format: start:end (inclusive) or comma list
    raw = raw.strip()
    if ":" in raw:
        a, b = raw.split(":", 1)
        start = int(a.strip())
        end = int(b.strip())
        if end < start:
            raise ValueError("range end < start")
        return list(range(start, end + 1))
    return [int(x.strip()) for x in raw.split(",") if x.strip()]


def axis_map_to_str(axis_map: dict[str, int]) -> str:
    return ",".join(f"{k}:{v}" for k, v in axis_map.items())


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Batch sweep for frame well curvature postulate")
    p.add_argument("--m-min", type=int, default=1)
    p.add_argument("--m-max", type=int, default=24)
    p.add_argument("--axis-names", type=str, default="axis1,axis2,axis3,lockin")
    p.add_argument("--horizon-range", type=str, default="3:8")
    p.add_argument("--lockin-horizon", type=int, default=4)
    p.add_argument("--require-unique", action=argparse.BooleanOptionalAction, default=True)
    p.add_argument("--excitation-shells", type=str, default="1,4,7,10")
    p.add_argument("--null-trials", type=int, default=2000)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--max-runs", type=int, default=200)
    p.add_argument("--out-prefix", type=str, default="scripts/frame_well_batch")
    p.add_argument(
        "--plot-top-k",
        type=int,
        default=0,
        help="if >0, generate plots for top-k ranked runs",
    )
    return p


def main() -> None:
    args = build_parser().parse_args()
    axis_names = parse_axis_names(args.axis_names)
    horizon_vals = parse_range(args.horizon_range)
    excitation_shells = probe.parse_csv_ints(args.excitation_shells)

    if "lockin" not in axis_names:
        axis_names.append("lockin")

    combos = itertools.product(horizon_vals, repeat=len(axis_names) - 1)
    rows: list[BatchRow] = []
    reports: dict[str, dict[str, object]] = {}

    run_count = 0
    for combo in combos:
        axis_map: dict[str, int] = {}
        j = 0
        for name in axis_names:
            if name == "lockin":
                axis_map[name] = args.lockin_horizon
            else:
                axis_map[name] = combo[j]
                j += 1

        if args.require_unique:
            vals = [axis_map[n] for n in axis_names if n != "lockin"]
            if len(set(vals)) < len(vals):
                continue

        run_id = f"run_{run_count:04d}"
        report = probe.build_report(
            m_min=args.m_min,
            m_max=args.m_max,
            horizons=sorted(set(axis_map.values())),
            axis_horizons=axis_map,
            excitation_shells=excitation_shells,
            null_trials=args.null_trials,
            rng_seed=args.seed + run_count,
        )

        axis_l2_values = list(report["axis_discrimination_l2"].values())  # type: ignore[index]
        axis_tests = report.get("axis_excitation_tests", {})
        axis_items = [(name, float(payload["empirical_p_value"])) for name, payload in axis_tests.items()]
        if axis_items:
            best_axis, best_axis_p = min(axis_items, key=lambda x: x[1])
            mean_axis_p = sum(p for _, p in axis_items) / len(axis_items)
        else:
            best_axis, best_axis_p, mean_axis_p = ("lockin", 1.0, 1.0)
        row = BatchRow(
            run_id=run_id,
            axis_horizons=axis_map_to_str(axis_map),
            chosen_score=float(report["excitation_null_test"]["chosen_score"]),  # type: ignore[index]
            empirical_p_value=float(report["excitation_null_test"]["empirical_p_value"]),  # type: ignore[index]
            lockin_well_identity=float(report["lockin_checks"]["well_depth_lockin_identity"]),  # type: ignore[index]
            axis_mean_l2=mean([float(x) for x in axis_l2_values]),
            axis_min_l2=min([float(x) for x in axis_l2_values]) if axis_l2_values else 0.0,
            baseline_horizon=int(report["excitation_null_test"]["baseline_horizon"]),  # type: ignore[index]
            best_axis=best_axis,
            best_axis_p_value=best_axis_p,
            mean_axis_p_value=mean_axis_p,
        )
        rows.append(row)
        reports[run_id] = report

        run_count += 1
        if args.max_runs > 0 and run_count >= args.max_runs:
            break

    rows.sort(key=lambda r: (r.best_axis_p_value, r.empirical_p_value, r.chosen_score, -r.axis_mean_l2))

    out_csv = f"{args.out_prefix}_summary.csv"
    out_json = f"{args.out_prefix}_summary.json"
    out_reports = f"{args.out_prefix}_reports.json"

    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(asdict(rows[0]).keys()) if rows else list(BatchRow.__annotations__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))

    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"count": len(rows), "rows": [asdict(r) for r in rows]}, f, indent=2, sort_keys=True)

    with open(out_reports, "w", encoding="utf-8") as f:
        json.dump(reports, f, indent=2, sort_keys=True)

    # Optional plotting of top-k runs via the plot helper.
    if args.plot_top_k > 0 and rows:
        top_dir = f"{args.out_prefix}_plots"
        os.makedirs(top_dir, exist_ok=True)
        plot_script = os.path.join(os.path.dirname(__file__), "frame_well_curvature_plot.py")
        for row in rows[: args.plot_top_k]:
            rpt_path = os.path.join(top_dir, f"{row.run_id}.json")
            png_path = os.path.join(top_dir, f"{row.run_id}.png")
            with open(rpt_path, "w", encoding="utf-8") as f:
                json.dump(reports[row.run_id], f, indent=2, sort_keys=True)
            cmd = [sys.executable, plot_script, "--input-json", rpt_path, "--output-png", png_path]
            subprocess.run(cmd, check=False)

    print(
        json.dumps(
            {
                "runs_evaluated": len(rows),
                "summary_csv": out_csv,
                "summary_json": out_json,
                "reports_json": out_reports,
                "best_run": asdict(rows[0]) if rows else None,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
