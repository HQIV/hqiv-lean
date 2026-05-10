#!/usr/bin/env python3
"""
Probe the postulate:
  well depth is set by curvature + Omega_k in the conserved frame,
  on the same Rindler horizon support.

The script is intentionally standalone and does not touch Lean files.
It reuses primitives from `scripts/cubic_phase_relax_probe.py`.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import random
from dataclasses import asdict, dataclass

import cubic_phase_relax_probe as cp


EPS_DEN = 1e-12


def parse_csv_ints(raw: str) -> list[int]:
    out: list[int] = []
    for token in raw.split(","):
        tok = token.strip()
        if not tok:
            continue
        out.append(int(tok))
    return out


def parse_axis_horizons(raw: str) -> dict[str, int]:
    out: dict[str, int] = {}
    for chunk in raw.split(","):
        item = chunk.strip()
        if not item:
            continue
        if ":" not in item:
            raise ValueError(f"bad axis horizon '{item}', expected name:int")
        name, hs = item.split(":", 1)
        out[name.strip()] = int(hs.strip())
    if not out:
        raise ValueError("axis-horizons parse produced an empty mapping")
    return out


def well_depth(m: int, horizon: int, *, use_rindler: bool) -> float:
    numer = cp.shell_shape(m) * abs(cp.omega_k_at_horizon(m, horizon) - 1.0)
    if use_rindler:
        return numer / (cp.rindler_detuning_shared(float(m)) + EPS_DEN)
    return numer


def theta_proxy(m: int, horizon: int) -> float:
    """Dimensionless phase proxy built from curvature/Omega_k on Rindler support."""
    wd = well_depth(m, horizon, use_rindler=True)
    return 2.0 * math.pi * abs(wd)


def quantum_lock_rows(ms: list[int], horizon: int, w_phase: float, w_curv: float) -> list[dict[str, float | int]]:
    rows: list[dict[str, float | int]] = []
    if len(ms) < 2:
        return rows
    for i in range(len(ms) - 1):
        m = ms[i]
        m_next = ms[i + 1]
        dtheta = theta_proxy(m_next, horizon) - theta_proxy(m, horizon)
        phase_error = abs(dtheta - 2.0 * math.pi)
        curvature_error = abs(cp.omega_k_at_horizon(m, horizon) - 1.0)
        score = w_phase * phase_error + w_curv * curvature_error
        rows.append(
            {
                "m": m,
                "m_next": m_next,
                "horizon": horizon,
                "dtheta": dtheta,
                "phase_error": phase_error,
                "curvature_error": curvature_error,
                "joint_score": score,
            }
        )
    rows.sort(key=lambda r: float(r["joint_score"]))
    return rows


def finite_diff_std(values: list[float]) -> float:
    if len(values) < 3:
        return 0.0
    diffs = [values[i + 1] - values[i] for i in range(len(values) - 1)]
    mean = sum(diffs) / len(diffs)
    var = sum((d - mean) ** 2 for d in diffs) / len(diffs)
    return math.sqrt(var)


def local_minima(ms: list[int], vals: list[float]) -> list[int]:
    if len(vals) < 3:
        return []
    mins: list[int] = []
    for i in range(1, len(vals) - 1):
        if vals[i] <= vals[i - 1] and vals[i] <= vals[i + 1]:
            mins.append(ms[i])
    return mins


def excitation_distance_score(target_shells: list[int], minima: list[int]) -> float:
    if not target_shells:
        return 0.0
    if not minima:
        return float("inf")
    total = 0.0
    for t in target_shells:
        total += min(abs(t - m) for m in minima)
    return total / len(target_shells)


@dataclass
class HorizonSeriesStats:
    horizon: int
    lockin_well_depth: float
    min_m: int
    min_value: float
    mean_value: float
    smoothness_rindler: float
    smoothness_no_rindler: float
    excitation_score: float
    minima_shells: list[int]


def build_report(
    m_min: int,
    m_max: int,
    horizons: list[int],
    axis_horizons: dict[str, int],
    excitation_shells: list[int],
    null_trials: int,
    rng_seed: int,
) -> dict[str, object]:
    if m_min < 0:
        raise ValueError("m_min must be >= 0")
    if m_max <= m_min + 2:
        raise ValueError("m_max must be at least m_min + 3")

    ms = list(range(m_min, m_max + 1))
    if not horizons:
        horizons = sorted(set(axis_horizons.values()))
    # Always include every horizon referenced by axis labels.
    horizons = sorted(set(horizons).union(set(axis_horizons.values())))

    horizon_stats: list[HorizonSeriesStats] = []
    raw_series: dict[str, dict[str, list[float]]] = {}
    for h in horizons:
        rindler_vals = [well_depth(m, h, use_rindler=True) for m in ms]
        no_rindler_vals = [well_depth(m, h, use_rindler=False) for m in ms]
        mins = local_minima(ms, rindler_vals)
        ex_score = excitation_distance_score(excitation_shells, mins)
        min_idx = min(range(len(ms)), key=lambda i: rindler_vals[i])
        stats = HorizonSeriesStats(
            horizon=h,
            lockin_well_depth=well_depth(cp.M_LOCKIN, h, use_rindler=True),
            min_m=ms[min_idx],
            min_value=rindler_vals[min_idx],
            mean_value=sum(rindler_vals) / len(rindler_vals),
            smoothness_rindler=finite_diff_std(rindler_vals),
            smoothness_no_rindler=finite_diff_std(no_rindler_vals),
            excitation_score=ex_score,
            minima_shells=mins,
        )
        horizon_stats.append(stats)
        raw_series[str(h)] = {"rindler": rindler_vals, "no_rindler": no_rindler_vals}

    lockin_identity_error = abs(cp.omega_k_at_horizon(cp.M_LOCKIN, cp.M_LOCKIN) - 1.0)
    lockin_well_identity = well_depth(cp.M_LOCKIN, cp.M_LOCKIN, use_rindler=True)

    axis_names = sorted(axis_horizons.keys())
    axis_pair_dist: dict[str, float] = {}
    for i in range(len(axis_names)):
        for j in range(i + 1, len(axis_names)):
            ai = axis_names[i]
            aj = axis_names[j]
            hi = axis_horizons[ai]
            hj = axis_horizons[aj]
            vi = raw_series[str(hi)]["rindler"]
            vj = raw_series[str(hj)]["rindler"]
            d2 = sum((x - y) ** 2 for x, y in zip(vi, vj)) / len(vi)
            axis_pair_dist[f"{ai}~{aj}"] = math.sqrt(d2)

    # Null test helper: random shell targets vs chosen excitation shells.
    rnd = random.Random(rng_seed)
    all_shells = ms[:]
    k = len(excitation_shells)

    def score_with_null(minima: list[int]) -> tuple[float, float, list[float]]:
        chosen = excitation_distance_score(excitation_shells, minima)
        null_scores_local: list[float] = []
        if k > 0 and k <= len(all_shells):
            for _ in range(max(1, null_trials)):
                trial_targets = rnd.sample(all_shells, k)
                null_scores_local.append(excitation_distance_score(trial_targets, minima))
        sorted_null = sorted(null_scores_local)
        if sorted_null:
            better_or_equal_local = sum(1 for s in sorted_null if s <= chosen)
            p_local = better_or_equal_local / len(sorted_null)
        else:
            p_local = 1.0
        return chosen, p_local, sorted_null

    baseline_h = axis_horizons.get("lockin", cp.M_LOCKIN)
    baseline_minima = local_minima(ms, raw_series[str(baseline_h)]["rindler"])
    chosen_score, p_value, null_scores_sorted = score_with_null(baseline_minima)

    per_axis = {}
    for axis_name, axis_h in axis_horizons.items():
        mins = local_minima(ms, raw_series[str(axis_h)]["rindler"])
        axis_score, axis_p, _ = score_with_null(mins)
        per_axis[axis_name] = {
            "horizon": axis_h,
            "chosen_score": axis_score,
            "empirical_p_value": axis_p,
            "minima_shells": mins,
        }

    quantum_axes = {}
    quantum_all_rows: list[dict[str, float | int | str]] = []
    for axis_name, axis_h in axis_horizons.items():
        qrows = quantum_lock_rows(ms, axis_h, w_phase=1.0, w_curv=1.0)
        quantum_axes[axis_name] = qrows[:10]
        for row in qrows:
            enriched = dict(row)
            enriched["axis"] = axis_name
            quantum_all_rows.append(enriched)
    quantum_all_rows.sort(key=lambda r: float(r["joint_score"]))

    return {
        "config": {
            "m_min": m_min,
            "m_max": m_max,
            "horizons": horizons,
            "axis_horizons": axis_horizons,
            "excitation_shells": excitation_shells,
            "null_trials": null_trials,
            "rng_seed": rng_seed,
            "referenceM": cp.REFERENCE_M,
            "M_LOCKIN": cp.M_LOCKIN,
            "C_RINDLER_SHARED": cp.C_RINDLER_SHARED,
        },
        "lockin_checks": {
            "omega_k_lockin_identity_error": lockin_identity_error,
            "well_depth_lockin_identity": lockin_well_identity,
        },
        "horizon_stats": [asdict(x) for x in horizon_stats],
        "axis_discrimination_l2": axis_pair_dist,
        "excitation_null_test": {
            "baseline_horizon": baseline_h,
            "chosen_score": chosen_score,
            "null_scores_summary": {
                "count": len(null_scores_sorted),
                "mean": (sum(null_scores_sorted) / len(null_scores_sorted)) if null_scores_sorted else None,
                "p10": null_scores_sorted[max(0, int(0.10 * len(null_scores_sorted)) - 1)] if null_scores_sorted else None,
                "p50": null_scores_sorted[max(0, int(0.50 * len(null_scores_sorted)) - 1)] if null_scores_sorted else None,
                "p90": null_scores_sorted[max(0, int(0.90 * len(null_scores_sorted)) - 1)] if null_scores_sorted else None,
            },
            "empirical_p_value": p_value,
        },
        "axis_excitation_tests": per_axis,
        "quantum_lock_sweep": {
            "target_dtheta": 2.0 * math.pi,
            "weights": {"phase": 1.0, "curvature": 1.0},
            "top_20_global": quantum_all_rows[:20],
            "top_10_per_axis": quantum_axes,
        },
        "series": {"m": ms, "by_horizon": raw_series},
    }


def write_horizon_csv(path: str, report: dict[str, object]) -> None:
    rows = report["horizon_stats"]  # type: ignore[index]
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "horizon",
                "lockin_well_depth",
                "min_m",
                "min_value",
                "mean_value",
                "smoothness_rindler",
                "smoothness_no_rindler",
                "excitation_score",
                "minima_shells",
            ],
        )
        writer.writeheader()
        for row in rows:  # type: ignore[assignment]
            row_out = dict(row)
            row_out["minima_shells"] = ",".join(str(x) for x in row_out["minima_shells"])
            writer.writerow(row_out)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Frame-dependent curvature/Omega_k well-depth probe")
    p.add_argument("--m-min", type=int, default=1)
    p.add_argument("--m-max", type=int, default=24)
    p.add_argument("--horizons", type=str, default="2,3,4,5,6,8,10")
    p.add_argument(
        "--axis-horizons",
        type=str,
        default="axis1:3,axis2:4,axis3:5,lockin:4",
        help="comma-separated name:horizon pairs",
    )
    p.add_argument(
        "--excitation-shells",
        type=str,
        default="1,4,7,10",
        help="comma-separated shells used for the null-distance score",
    )
    p.add_argument("--null-trials", type=int, default=2000)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--json-out", type=str, default=None, help="optional output JSON path")
    p.add_argument("--csv-out", type=str, default=None, help="optional horizon-level CSV path")
    return p


def main() -> None:
    args = build_parser().parse_args()
    horizons = parse_csv_ints(args.horizons)
    axis_horizons = parse_axis_horizons(args.axis_horizons)
    excitation_shells = parse_csv_ints(args.excitation_shells)
    report = build_report(
        m_min=args.m_min,
        m_max=args.m_max,
        horizons=horizons,
        axis_horizons=axis_horizons,
        excitation_shells=excitation_shells,
        null_trials=args.null_trials,
        rng_seed=args.seed,
    )
    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, sort_keys=True)
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
    if args.csv_out:
        write_horizon_csv(args.csv_out, report)


if __name__ == "__main__":
    main()
