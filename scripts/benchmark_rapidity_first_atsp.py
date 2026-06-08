#!/usr/bin/env python3
"""
Benchmark rapidity-first ATSP search against the directed-torus baseline.

This harness is designed for research iteration:
- run the new rapidity-first shell ladder on random asymmetric instances;
- optionally compare against the existing directed-torus solver;
- cache exact small/medium-n optima by matrix hash so expensive exact runs
  (e.g. n=11 or n=12) can be paid once and reused later.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from directed_torus_atsp_oracle import (
    closed_tour_cost,
    directed_torus_atsp_solver,
    edge_overlap_ratio,
    exact_atsp_small,
    random_asymmetric_matrix,
)
from rapidity_first_atsp_oracle import rapidity_first_solver


@dataclass
class TrialResult:
    n: int
    seed: int
    rapidity_time_s: float
    rapidity_cost: float
    directed_time_s: float | None
    directed_cost: float | None
    exact_cost: float | None
    exact_cache_hit: bool
    ref_source: str
    reference_exact: float | None
    reference_best_known: float | None
    reference_lower_bound: float | None
    reference_tour: list[int] | None
    rapidity_ref_edge_overlap: float | None
    rapidity_ref_exact_match: bool | None
    directed_ref_edge_overlap: float | None
    directed_ref_exact_match: bool | None


def pctl(xs: list[float], q: float) -> float:
    if not xs:
        return 0.0
    ys = sorted(xs)
    idx = int(max(0, min(len(ys) - 1, round((len(ys) - 1) * q))))
    return ys[idx]


def mean_or_zero(xs: list[float]) -> float:
    return statistics.mean(xs) if xs else 0.0


def matrix_hash(dist: list[list[float]]) -> str:
    payload = json.dumps(dist, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def load_known_reference(path: Path | None) -> dict[str, Any]:
    if path is None:
        return {}
    if not path.exists():
        return {}
    with path.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    if not isinstance(data, dict):
        return {}
    return data


def lookup_known_reference(
    *,
    known_ref: dict[str, Any],
    instance_id: str,
    mhash: str,
) -> dict[str, Any]:
    if not known_ref:
        return {}
    by_instance = known_ref.get("by_instance_id", {})
    if isinstance(by_instance, dict):
        row = by_instance.get(instance_id)
        if isinstance(row, dict):
            return row
    by_hash = known_ref.get("by_matrix_hash", {})
    if isinstance(by_hash, dict):
        row = by_hash.get(mhash)
        if isinstance(row, dict):
            return row
    return {}


def extract_reference_tour(row: dict[str, Any]) -> list[int] | None:
    for key in ("exact_tour", "solution_tour", "reference_tour", "tour"):
        val = row.get(key)
        if isinstance(val, list) and all(isinstance(x, int) for x in val):
            return list(val)
    return None


def load_exact_cache(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"entries": {}}
    with path.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    if not isinstance(data, dict):
        return {"entries": {}}
    entries = data.get("entries")
    if not isinstance(entries, dict):
        data["entries"] = {}
    return data


def save_exact_cache(path: Path, cache: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        json.dump(cache, fh, indent=2, sort_keys=True)


def get_exact_cost_cached(
    dist: list[list[float]],
    *,
    cache: dict[str, Any],
    cache_mode: str,
    cache_path: Path,
    verbose: bool,
) -> tuple[float | None, bool]:
    if cache_mode == "off":
        cost, _ = exact_atsp_small(dist)
        return float(cost), False

    key = matrix_hash(dist)
    entries = cache.setdefault("entries", {})
    row = entries.get(key)
    if isinstance(row, dict) and "exact_cost" in row:
        return float(row["exact_cost"]), True

    if cache_mode == "readonly":
        return None, False

    n = len(dist)
    if verbose:
        print(f"[exact-cache miss] computing exact optimum for n={n} key={key[:12]}...")
    t0 = time.perf_counter()
    cost, tour = exact_atsp_small(dist)
    elapsed = time.perf_counter() - t0
    entries[key] = {
        "n": n,
        "matrix_hash": key,
        "exact_cost": float(cost),
        "exact_tour": list(tour),
        "elapsed_s": elapsed,
        "computed_at": datetime.now(timezone.utc).isoformat(),
    }
    cache["updated_at"] = datetime.now(timezone.utc).isoformat()
    save_exact_cache(cache_path, cache)
    return float(cost), False


def run_trial(
    *,
    n: int,
    seed: int,
    run_directed: bool,
    exact_if_at_most: int,
    cache: dict[str, Any],
    cache_mode: str,
    cache_path: Path,
    known_ref: dict[str, Any],
    use_known_reference: bool,
    verbose: bool,
    directed_max_steps: int,
    directed_top_k: int,
    rapidity_top_k: int,
    shell_count: int,
    slots_per_shell: int,
    omega_mode: str,
    slot_family: str,
    flip_prune: bool,
    local_search_mode: str,
    local_search_topk: int,
    local_search_rounds: int,
    local_search_two_opt_span_cap: int,
    local_search_relocate_move_cap: int,
    rapidity_prune: bool,
    orthogonal_boundary: bool,
    pool_limit: int,
    pool_keep_per_band: int,
) -> TrialResult:
    dist = random_asymmetric_matrix(n, seed)
    mhash = matrix_hash(dist)
    instance_id = f"rand-n{n}-seed{seed}"

    ref_row = (
        lookup_known_reference(known_ref=known_ref, instance_id=instance_id, mhash=mhash)
        if use_known_reference
        else {}
    )
    reference_tour = extract_reference_tour(ref_row) if ref_row else None
    reference_exact = float(ref_row["exact_cost"]) if "exact_cost" in ref_row else None
    reference_best_known = float(ref_row["best_known"]) if "best_known" in ref_row else None
    reference_lower_bound = float(ref_row["lower_bound"]) if "lower_bound" in ref_row else None
    ref_source = "none"
    if reference_tour is not None and reference_exact is None:
        reference_exact = float(closed_tour_cost(dist, reference_tour))
        ref_source = "known_solution_tour"
    elif reference_exact is not None:
        ref_source = "known_exact"
    elif reference_best_known is not None:
        ref_source = "known_best_known"
    elif reference_lower_bound is not None:
        ref_source = "known_lower_bound"
    if verbose and ref_source != "none":
        print(f"[known-reference hit] id={instance_id} hash={mhash[:12]} source={ref_source}")

    t0 = time.perf_counter()
    rapidity = rapidity_first_solver(
        dist=dist,
        top_k=rapidity_top_k,
        shell_count=shell_count,
        slots_per_shell=slots_per_shell,
        omega_mode=omega_mode,
        slot_family=slot_family,
        flip_prune=flip_prune,
        local_search_mode=local_search_mode,
        local_search_topk=local_search_topk,
        local_search_rounds=local_search_rounds,
        local_search_two_opt_span_cap=local_search_two_opt_span_cap,
        local_search_relocate_move_cap=local_search_relocate_move_cap,
        rapidity_prune=rapidity_prune,
        orthogonal_boundary=orthogonal_boundary,
        pool_limit=pool_limit,
        pool_keep_per_band=pool_keep_per_band,
    )
    rapidity_time_s = time.perf_counter() - t0
    rapidity_cost = float(rapidity["best_by_cost"]["tour_cost"])
    rapidity_tour = list(rapidity["best_by_cost"]["tour"])

    directed_time_s: float | None = None
    directed_cost: float | None = None
    directed_tour: list[int] | None = None
    if run_directed:
        t1 = time.perf_counter()
        directed = directed_torus_atsp_solver(
            dist=dist,
            optimizer="iterative-peel-anneal",
            max_steps=directed_max_steps,
            top_k=directed_top_k,
            iterative_rounds=4,
            iterative_arity_start=2,
            iterative_stage_topk=max(12, directed_top_k),
            iterative_early_stop_patience=2,
            iterative_early_stop_tol=1e-9,
            rapidity_prune=True,
            rapidity_prune_scale=1.0,
            rapidity_prune_scale_mode="sqrt-n-over-arity",
            anneal_rapidity_barrier=True,
            anneal_barrier_strength=1.0,
            anneal_rapidity_window=4,
            anneal_rapidity_weight=0.25,
            anneal_rapidity_jitter_weight=0.10,
            anneal_shell_width=0.25,
            anneal_shell_keep_per_band=0,
        )
        directed_time_s = time.perf_counter() - t1
        directed_cost = float(directed["best_by_cost"]["tour_cost"])
        directed_tour = list(directed["best_by_cost"]["tour"])

    exact_cost: float | None = None
    exact_cache_hit = False
    if reference_exact is not None:
        exact_cost = reference_exact
    elif n <= exact_if_at_most and reference_best_known is None and reference_lower_bound is None:
        exact_cost, exact_cache_hit = get_exact_cost_cached(
            dist,
            cache=cache,
            cache_mode=cache_mode,
            cache_path=cache_path,
            verbose=verbose,
        )
        if exact_cost is not None:
            ref_source = "exact_cache_hit" if exact_cache_hit else "exact_computed"

    rapidity_ref_edge_overlap: float | None = None
    rapidity_ref_exact_match: bool | None = None
    directed_ref_edge_overlap: float | None = None
    directed_ref_exact_match: bool | None = None
    if reference_tour is not None:
        rapidity_ref_edge_overlap = edge_overlap_ratio(rapidity_tour, reference_tour)
        rapidity_ref_exact_match = rapidity_ref_edge_overlap >= 1.0 - 1e-12
        if directed_tour is not None:
            directed_ref_edge_overlap = edge_overlap_ratio(directed_tour, reference_tour)
            directed_ref_exact_match = directed_ref_edge_overlap >= 1.0 - 1e-12

    return TrialResult(
        n=n,
        seed=seed,
        rapidity_time_s=rapidity_time_s,
        rapidity_cost=rapidity_cost,
        directed_time_s=directed_time_s,
        directed_cost=directed_cost,
        exact_cost=exact_cost,
        exact_cache_hit=exact_cache_hit,
        ref_source=ref_source,
        reference_exact=reference_exact,
        reference_best_known=reference_best_known,
        reference_lower_bound=reference_lower_bound,
        reference_tour=reference_tour,
        rapidity_ref_edge_overlap=rapidity_ref_edge_overlap,
        rapidity_ref_exact_match=rapidity_ref_exact_match,
        directed_ref_edge_overlap=directed_ref_edge_overlap,
        directed_ref_exact_match=directed_ref_exact_match,
    )


def prewarm_exact_cache(
    *,
    n_min: int,
    n_max: int,
    trials: int,
    seed_base: int,
    exact_if_at_most: int,
    cache: dict[str, Any],
    cache_mode: str,
    cache_path: Path,
    verbose: bool,
) -> tuple[int, int]:
    hits = 0
    misses = 0
    if cache_mode not in {"readwrite", "readonly"}:
        return hits, misses
    for n in range(n_min, n_max + 1):
        if n > exact_if_at_most:
            continue
        for trial in range(trials):
            seed = seed_base + 10007 * n + trial
            dist = random_asymmetric_matrix(n, seed)
            key = matrix_hash(dist)
            if key in cache.get("entries", {}):
                hits += 1
                continue
            if cache_mode == "readonly":
                misses += 1
                continue
            _, hit = get_exact_cost_cached(
                dist,
                cache=cache,
                cache_mode=cache_mode,
                cache_path=cache_path,
                verbose=verbose,
            )
            hits += 1 if hit else 0
            misses += 0 if hit else 1
    return hits, misses


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Benchmark rapidity-first ATSP with cache-backed exact checks")
    p.add_argument("--n-min", type=int, default=8, help="minimum city count")
    p.add_argument("--n-max", type=int, default=12, help="maximum city count")
    p.add_argument("--trials", type=int, default=6, help="instances per n")
    p.add_argument("--seed-base", type=int, default=1234, help="seed base")
    p.add_argument(
        "--run-directed",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="also benchmark the existing directed-torus solver",
    )
    p.add_argument("--directed-max-steps", type=int, default=500, help="max steps for directed-torus solver")
    p.add_argument("--directed-top-k", type=int, default=12, help="top-k for directed-torus solver")
    p.add_argument("--rapidity-top-k", type=int, default=12, help="top-k retained by rapidity-first solver")
    p.add_argument("--shell-count", type=int, default=24, help="rapidity-first shell count")
    p.add_argument("--slots-per-shell", type=int, default=8, help="periodic slots per shell")
    p.add_argument(
        "--omega-mode",
        choices=("unit", "reciprocal", "sqrt-reciprocal", "log-reciprocal", "one-over-k", "root-scale"),
        default="root-scale",
        help="rapidity shell weighting mode",
    )
    p.add_argument(
        "--slot-family",
        choices=("periodic", "one-over-k", "reflected", "hybrid"),
        default="hybrid",
        help="slot family inside each shell",
    )
    p.add_argument(
        "--flip-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable OSHoracle-style flip prune in rapidity-first solver",
    )
    p.add_argument(
        "--local-search-mode",
        choices=("off", "2opt", "relocate", "both"),
        default="both",
        help="lightweight local completion mode for rapidity-first solver",
    )
    p.add_argument("--local-search-topk", type=int, default=2, help="top shell candidates to improve locally")
    p.add_argument("--local-search-rounds", type=int, default=1, help="local completion rounds")
    p.add_argument(
        "--local-search-two-opt-span-cap",
        type=int,
        default=12,
        help="speed-oriented 2-opt reversal span cap passed to rapidity-first solver (0 => full)",
    )
    p.add_argument(
        "--local-search-relocate-move-cap",
        type=int,
        default=8,
        help="speed-oriented relocate move cap passed to rapidity-first solver (0 => full)",
    )
    p.add_argument(
        "--rapidity-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable rapidity-dominated-edge pruning in rapidity-first solver",
    )
    p.add_argument(
        "--orthogonal-boundary",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable orthogonal LB/UB shell boundary in rapidity-first solver",
    )
    p.add_argument("--pool-limit", type=int, default=64, help="global pool limit for rapidity-first solver")
    p.add_argument("--pool-keep-per-band", type=int, default=0, help="optional keep-per-rapidity-band cap")
    p.add_argument(
        "--exact-if-at-most",
        type=int,
        default=12,
        help="use exact checker for n <= threshold, subject to cache mode",
    )
    p.add_argument(
        "--exact-cache-json",
        type=str,
        default="data/atsp_exact_cache.json",
        help="path to exact-result cache JSON",
    )
    p.add_argument(
        "--exact-cache-mode",
        choices=("off", "readonly", "readwrite"),
        default="readwrite",
        help="off=always recompute exact, readonly=use cache if present, readwrite=fill missing cache entries",
    )
    p.add_argument(
        "--prewarm-exact-cache",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="compute missing cached exact optima for selected instances before benchmarking",
    )
    p.add_argument(
        "--known-reference-json",
        type=str,
        default=None,
        help=(
            "optional JSON with known exact/best-known/lower-bound references and/or solution tours; "
            "keys may be under by_instance_id or by_matrix_hash"
        ),
    )
    p.add_argument(
        "--use-known-reference",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="if true, skip brute-force exact solves when known references are available",
    )
    p.add_argument("--print-trials", action="store_true", help="print per-trial rows before summary")
    p.add_argument("--verbose", action="store_true", help="print cache activity for exact solves")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.n_min < 2 or args.n_max < args.n_min:
        raise SystemExit("require 2 <= n-min <= n-max")
    if args.trials < 1:
        raise SystemExit("--trials must be >= 1")
    if args.directed_max_steps < 1:
        raise SystemExit("--directed-max-steps must be >= 1")
    if args.directed_top_k < 1:
        raise SystemExit("--directed-top-k must be >= 1")
    if args.rapidity_top_k < 1:
        raise SystemExit("--rapidity-top-k must be >= 1")
    if args.shell_count < 1:
        raise SystemExit("--shell-count must be >= 1")
    if args.slots_per_shell < 1:
        raise SystemExit("--slots-per-shell must be >= 1")
    if args.local_search_topk < 1:
        raise SystemExit("--local-search-topk must be >= 1")
    if args.local_search_rounds < 1:
        raise SystemExit("--local-search-rounds must be >= 1")
    if args.local_search_two_opt_span_cap < 0:
        raise SystemExit("--local-search-two-opt-span-cap must be >= 0")
    if args.local_search_relocate_move_cap < 0:
        raise SystemExit("--local-search-relocate-move-cap must be >= 0")
    if args.pool_limit < 1:
        raise SystemExit("--pool-limit must be >= 1")
    if args.pool_keep_per_band < 0:
        raise SystemExit("--pool-keep-per-band must be >= 0")
    if args.exact_if_at_most < 0:
        raise SystemExit("--exact-if-at-most must be >= 0")

    cache_path = Path(args.exact_cache_json)
    cache = load_exact_cache(cache_path)
    known_ref_path = Path(args.known_reference_json) if args.known_reference_json else None
    known_ref = load_known_reference(known_ref_path)

    if args.prewarm_exact_cache:
        hits, misses = prewarm_exact_cache(
            n_min=args.n_min,
            n_max=args.n_max,
            trials=args.trials,
            seed_base=args.seed_base,
            exact_if_at_most=args.exact_if_at_most,
            cache=cache,
            cache_mode=args.exact_cache_mode,
            cache_path=cache_path,
            verbose=args.verbose,
        )
        print(
            f"# prewarm_exact_cache hits={hits} misses_filled={misses} "
            f"mode={args.exact_cache_mode} path={cache_path}"
        )

    rows: list[TrialResult] = []
    for n in range(args.n_min, args.n_max + 1):
        for trial in range(args.trials):
            seed = args.seed_base + 10007 * n + trial
            row = run_trial(
                n=n,
                seed=seed,
                run_directed=args.run_directed,
                exact_if_at_most=args.exact_if_at_most,
                cache=cache,
                cache_mode=args.exact_cache_mode,
                cache_path=cache_path,
                known_ref=known_ref,
                use_known_reference=args.use_known_reference,
                verbose=args.verbose,
                directed_max_steps=args.directed_max_steps,
                directed_top_k=args.directed_top_k,
                rapidity_top_k=args.rapidity_top_k,
                shell_count=args.shell_count,
                slots_per_shell=args.slots_per_shell,
                omega_mode=args.omega_mode,
                slot_family=args.slot_family,
                flip_prune=args.flip_prune,
                local_search_mode=args.local_search_mode,
                local_search_topk=args.local_search_topk,
                local_search_rounds=args.local_search_rounds,
                local_search_two_opt_span_cap=args.local_search_two_opt_span_cap,
                local_search_relocate_move_cap=args.local_search_relocate_move_cap,
                rapidity_prune=args.rapidity_prune,
                orthogonal_boundary=args.orthogonal_boundary,
                pool_limit=args.pool_limit,
                pool_keep_per_band=args.pool_keep_per_band,
            )
            rows.append(row)
            if args.print_trials:
                print(
                    "trial,"
                    f"n={row.n},seed={row.seed},"
                    f"rapidity_s={row.rapidity_time_s:.6f},rapidity_cost={row.rapidity_cost:.6f},"
                    f"directed_s={0.0 if row.directed_time_s is None else row.directed_time_s:.6f},"
                    f"directed_cost={0.0 if row.directed_cost is None else row.directed_cost:.6f},"
                    f"exact_cost={'' if row.exact_cost is None else f'{row.exact_cost:.6f}'},"
                    f"exact_cache_hit={row.exact_cache_hit},"
                    f"ref_source={row.ref_source},"
                    f"best_known={'' if row.reference_best_known is None else f'{row.reference_best_known:.6f}'},"
                    f"lower_bound={'' if row.reference_lower_bound is None else f'{row.reference_lower_bound:.6f}'},"
                    f"rapidity_ref_overlap={'' if row.rapidity_ref_edge_overlap is None else f'{row.rapidity_ref_edge_overlap:.6f}'},"
                    f"directed_ref_overlap={'' if row.directed_ref_edge_overlap is None else f'{row.directed_ref_edge_overlap:.6f}'}"
                )

    if args.run_directed:
        print(
            "n,"
            "rapidity_mean_s,rapidity_p90_s,rapidity_cost_mean,"
            "directed_mean_s,directed_p90_s,directed_cost_mean,"
            "hybrid_cost_mean,"
            "rapidity_gap_mean,directed_gap_mean,hybrid_gap_mean,"
            "wins_rapidity,wins_directed,wins_tie,"
            "exact_cache_hits,exact_cache_misses"
        )
    else:
        print(
            "n,"
            "rapidity_mean_s,rapidity_p90_s,rapidity_cost_mean,"
            "rapidity_gap_mean,"
            "exact_cache_hits,exact_cache_misses"
        )

    for n in range(args.n_min, args.n_max + 1):
        group = [r for r in rows if r.n == n]
        rapidity_times = [r.rapidity_time_s for r in group]
        rapidity_costs = [r.rapidity_cost for r in group]
        exact_hits = sum(1 for r in group if r.exact_cost is not None and r.exact_cache_hit)
        exact_misses = sum(1 for r in group if r.exact_cost is not None and not r.exact_cache_hit)
        known_ref_used = sum(1 for r in group if r.ref_source.startswith("known_"))
        known_solution_used = sum(1 for r in group if r.reference_tour is not None)
        rapidity_gaps = [r.rapidity_cost - r.exact_cost for r in group if r.exact_cost is not None]
        rapidity_best_known_regret = [
            r.rapidity_cost - r.reference_best_known
            for r in group
            if r.reference_best_known is not None
        ]
        rapidity_excess_over_lb = [
            r.rapidity_cost - r.reference_lower_bound
            for r in group
            if r.reference_lower_bound is not None
        ]
        rapidity_ref_overlap = [
            r.rapidity_ref_edge_overlap
            for r in group
            if r.rapidity_ref_edge_overlap is not None
        ]
        rapidity_ref_exact_rate = [
            1.0 if r.rapidity_ref_exact_match else 0.0
            for r in group
            if r.rapidity_ref_exact_match is not None
        ]

        if not args.run_directed:
            print(
                f"{n},"
                f"{statistics.mean(rapidity_times):.6f},{pctl(rapidity_times,0.9):.6f},{statistics.mean(rapidity_costs):.6f},"
                f"{mean_or_zero(rapidity_gaps):.6f},"
                f"{exact_hits},{exact_misses}"
            )
            if rapidity_best_known_regret or rapidity_excess_over_lb or known_ref_used:
                print(
                    f"# n={n} known_ref_used={known_ref_used} known_solution_used={known_solution_used} "
                    f"rapidity_regret_vs_best_known={mean_or_zero(rapidity_best_known_regret):.6f} "
                    f"rapidity_excess_over_lb={mean_or_zero(rapidity_excess_over_lb):.6f} "
                    f"rapidity_ref_overlap={mean_or_zero(rapidity_ref_overlap):.6f} "
                    f"rapidity_ref_exact_rate={mean_or_zero(rapidity_ref_exact_rate):.6f}"
                )
            continue

        directed_times = [r.directed_time_s for r in group if r.directed_time_s is not None]
        directed_costs = [r.directed_cost for r in group if r.directed_cost is not None]
        hybrid_costs = [
            min(r.rapidity_cost, float(r.directed_cost))
            for r in group
            if r.directed_cost is not None
        ]
        directed_gaps = [
            float(r.directed_cost) - r.exact_cost
            for r in group
            if r.directed_cost is not None and r.exact_cost is not None
        ]
        hybrid_gaps = [
            min(r.rapidity_cost, float(r.directed_cost)) - r.exact_cost
            for r in group
            if r.directed_cost is not None and r.exact_cost is not None
        ]
        directed_best_known_regret = [
            float(r.directed_cost) - r.reference_best_known
            for r in group
            if r.directed_cost is not None and r.reference_best_known is not None
        ]
        hybrid_best_known_regret = [
            min(r.rapidity_cost, float(r.directed_cost)) - r.reference_best_known
            for r in group
            if r.directed_cost is not None and r.reference_best_known is not None
        ]
        directed_excess_over_lb = [
            float(r.directed_cost) - r.reference_lower_bound
            for r in group
            if r.directed_cost is not None and r.reference_lower_bound is not None
        ]
        hybrid_excess_over_lb = [
            min(r.rapidity_cost, float(r.directed_cost)) - r.reference_lower_bound
            for r in group
            if r.directed_cost is not None and r.reference_lower_bound is not None
        ]
        directed_ref_overlap = [
            r.directed_ref_edge_overlap
            for r in group
            if r.directed_ref_edge_overlap is not None
        ]
        directed_ref_exact_rate = [
            1.0 if r.directed_ref_exact_match else 0.0
            for r in group
            if r.directed_ref_exact_match is not None
        ]
        wins_rapidity = 0
        wins_directed = 0
        wins_tie = 0
        for r in group:
            if r.directed_cost is None:
                continue
            if abs(r.rapidity_cost - float(r.directed_cost)) <= 1e-9:
                wins_tie += 1
            elif r.rapidity_cost < float(r.directed_cost):
                wins_rapidity += 1
            else:
                wins_directed += 1

        print(
            f"{n},"
            f"{statistics.mean(rapidity_times):.6f},{pctl(rapidity_times,0.9):.6f},{statistics.mean(rapidity_costs):.6f},"
            f"{statistics.mean(directed_times):.6f},{pctl(directed_times,0.9):.6f},{statistics.mean(directed_costs):.6f},"
            f"{statistics.mean(hybrid_costs):.6f},"
            f"{mean_or_zero(rapidity_gaps):.6f},{mean_or_zero(directed_gaps):.6f},{mean_or_zero(hybrid_gaps):.6f},"
            f"{wins_rapidity},{wins_directed},{wins_tie},"
            f"{exact_hits},{exact_misses}"
        )
        if (
            rapidity_best_known_regret
            or directed_best_known_regret
            or hybrid_best_known_regret
            or rapidity_excess_over_lb
            or directed_excess_over_lb
            or hybrid_excess_over_lb
            or known_ref_used
        ):
            print(
                f"# n={n} known_ref_used={known_ref_used} known_solution_used={known_solution_used} "
                f"regret(best_known): rapidity={mean_or_zero(rapidity_best_known_regret):.6f} "
                f"directed={mean_or_zero(directed_best_known_regret):.6f} "
                f"hybrid={mean_or_zero(hybrid_best_known_regret):.6f} "
                f"excess(lb): rapidity={mean_or_zero(rapidity_excess_over_lb):.6f} "
                f"directed={mean_or_zero(directed_excess_over_lb):.6f} "
                f"hybrid={mean_or_zero(hybrid_excess_over_lb):.6f} "
                f"overlap(ref): rapidity={mean_or_zero(rapidity_ref_overlap):.6f} "
                f"directed={mean_or_zero(directed_ref_overlap):.6f} "
                f"exact_match_rate(ref): rapidity={mean_or_zero(rapidity_ref_exact_rate):.6f} "
                f"directed={mean_or_zero(directed_ref_exact_rate):.6f}"
            )


if __name__ == "__main__":
    main()
