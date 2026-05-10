#!/usr/bin/env python3
"""
Run the rapidity-first ATSP solver on named TSPLIB ATSP instances.

Current scope:
- parses TSPLIB95 ATSP files with `EDGE_WEIGHT_TYPE: EXPLICIT`
- supports `EDGE_WEIGHT_FORMAT: FULL_MATRIX`
- reads best-known values from `bestSolutions.txt`
- reports ratio vs best-known and the Lean-envelope reference `1 + n^(1/n)`

This is meant for practical benchmarking on real named instances, separate from
the random-matrix research harness.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Any

from rapidity_first_atsp_oracle import rapidity_first_solver


def parse_best_solutions(path: Path) -> dict[str, float]:
    out: dict[str, float] = {}
    if not path.exists():
        return out
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or ":" not in line:
            continue
        name, value = line.split(":", 1)
        name = name.strip()
        value = value.strip()
        try:
            out[name] = float(value)
        except ValueError:
            continue
    return out


def parse_tsplib_atsp(path: Path) -> tuple[str, list[list[float]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    meta: dict[str, str] = {}
    numbers: list[float] = []
    in_weights = False
    for raw in lines:
        line = raw.strip()
        if not line:
            continue
        if line == "EOF":
            break
        if in_weights:
            numbers.extend(float(tok) for tok in line.split())
            continue
        if line.startswith("EDGE_WEIGHT_SECTION"):
            in_weights = True
            continue
        if ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip()

    name = meta.get("NAME", path.stem)
    typ = meta.get("TYPE", "")
    ewt = meta.get("EDGE_WEIGHT_TYPE", "")
    ewf = meta.get("EDGE_WEIGHT_FORMAT", "")
    if typ != "ATSP":
        raise ValueError(f"{path.name}: expected TYPE=ATSP, got {typ!r}")
    if ewt != "EXPLICIT":
        raise ValueError(f"{path.name}: only EXPLICIT edge weights supported, got {ewt!r}")
    if ewf != "FULL_MATRIX":
        raise ValueError(f"{path.name}: only FULL_MATRIX supported, got {ewf!r}")
    dim = int(meta["DIMENSION"])
    if len(numbers) != dim * dim:
        raise ValueError(f"{path.name}: expected {dim*dim} weights, got {len(numbers)}")
    matrix: list[list[float]] = []
    idx = 0
    for i in range(dim):
        row = numbers[idx : idx + dim]
        if len(row) != dim:
            raise ValueError(f"{path.name}: malformed row length at row {i}")
        row[i] = 0.0
        matrix.append(row)
        idx += dim
    return name, matrix


def list_default_instances(data_dir: Path) -> list[Path]:
    names = ["br17.atsp", "ftv33.atsp", "ftv35.atsp", "ftv38.atsp", "ftv44.atsp"]
    return [data_dir / name for name in names if (data_dir / name).exists()]


def run_named_instance(
    path: Path,
    *,
    best_known: dict[str, float],
    shell_count: int,
    slots_per_shell: int,
    local_search_mode: str,
    local_search_topk: int,
    local_search_rounds: int,
    local_search_two_opt_span_cap: int,
    local_search_relocate_move_cap: int,
    rapidity_prune: bool,
    orthogonal_boundary: bool,
    pool_limit: int,
) -> dict[str, Any]:
    name, dist = parse_tsplib_atsp(path)
    payload = rapidity_first_solver(
        dist=dist,
        shell_count=shell_count,
        slots_per_shell=slots_per_shell,
        local_search_mode=local_search_mode,
        local_search_topk=local_search_topk,
        local_search_rounds=local_search_rounds,
        local_search_two_opt_span_cap=local_search_two_opt_span_cap,
        local_search_relocate_move_cap=local_search_relocate_move_cap,
        rapidity_prune=rapidity_prune,
        orthogonal_boundary=orthogonal_boundary,
        pool_limit=pool_limit,
    )
    n = payload["n_cities"]
    solver_cost = float(payload["best_by_cost"]["tour_cost"])
    best = best_known.get(name)
    ratio = solver_cost / best if best is not None and best > 0 else math.inf
    envelope = 1.0 + float(n) ** (1.0 / float(n))
    return {
        "name": name,
        "n": n,
        "solver_cost": solver_cost,
        "best_known": best,
        "ratio_vs_best_known": ratio,
        "envelope_1_plus_n_pow_1_over_n": envelope,
        "under_envelope": ratio <= envelope if math.isfinite(ratio) else False,
        "best_tour": payload["best_by_cost"]["tour"],
        "best_shell": payload["best_by_cost"]["shell_step"],
        "best_rapidity": payload["best_by_cost"]["rapidity_term"],
        "best_jitter": payload["best_by_cost"]["rapidity_jitter"],
        "unique_tours_sampled": payload["unique_tours_sampled"],
        "coverage_ratio": payload["coverage_ratio"],
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Run rapidity-first solver on named TSPLIB ATSP instances")
    p.add_argument(
        "--data-dir",
        type=str,
        default="data/tsplib_atsp",
        help="directory containing .atsp files and bestSolutions.txt",
    )
    p.add_argument(
        "--instances",
        nargs="*",
        default=[],
        help="specific .atsp filenames or bare instance names to run (default: small downloaded set)",
    )
    p.add_argument("--shell-count", type=int, default=24, help="rapidity-first shell count")
    p.add_argument("--slots-per-shell", type=int, default=8, help="periodic slots per shell")
    p.add_argument(
        "--local-search-mode",
        choices=("off", "2opt", "relocate", "both"),
        default="both",
        help="local completion mode",
    )
    p.add_argument("--local-search-topk", type=int, default=2, help="top shell candidates to improve locally")
    p.add_argument("--local-search-rounds", type=int, default=1, help="local completion rounds")
    p.add_argument("--local-search-two-opt-span-cap", type=int, default=12, help="2-opt span cap (0 => full)")
    p.add_argument("--local-search-relocate-move-cap", type=int, default=8, help="relocate move cap (0 => full)")
    p.add_argument(
        "--rapidity-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable rapidity-dominated-edge prune",
    )
    p.add_argument(
        "--orthogonal-boundary",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable orthogonal shell barrier",
    )
    p.add_argument("--pool-limit", type=int, default=64, help="global retained candidate pool limit")
    return p


def main() -> None:
    args = build_parser().parse_args()
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

    data_dir = Path(args.data_dir)
    best_known = parse_best_solutions(data_dir / "bestSolutions.txt")

    if args.instances:
        paths: list[Path] = []
        for item in args.instances:
            p = data_dir / item
            if p.exists():
                paths.append(p)
                continue
            p2 = data_dir / f"{item}.atsp"
            if p2.exists():
                paths.append(p2)
                continue
            raise SystemExit(f"instance not found: {item}")
    else:
        paths = list_default_instances(data_dir)

    print(
        "instance,n,solver_cost,best_known,ratio_vs_best_known,"
        "envelope_1_plus_n_pow_1_over_n,under_envelope,unique_sampled,coverage_ratio"
    )
    for path in paths:
        row = run_named_instance(
            path,
            best_known=best_known,
            shell_count=args.shell_count,
            slots_per_shell=args.slots_per_shell,
            local_search_mode=args.local_search_mode,
            local_search_topk=args.local_search_topk,
            local_search_rounds=args.local_search_rounds,
            local_search_two_opt_span_cap=args.local_search_two_opt_span_cap,
            local_search_relocate_move_cap=args.local_search_relocate_move_cap,
            rapidity_prune=args.rapidity_prune,
            orthogonal_boundary=args.orthogonal_boundary,
            pool_limit=args.pool_limit,
        )
        print(
            f"{row['name']},{row['n']},{row['solver_cost']:.6f},"
            f"{'' if row['best_known'] is None else f'{row['best_known']:.6f}'},"
            f"{row['ratio_vs_best_known']:.6f},"
            f"{row['envelope_1_plus_n_pow_1_over_n']:.6f},"
            f"{row['under_envelope']},"
            f"{row['unique_tours_sampled']},{row['coverage_ratio']:.6f}"
        )


if __name__ == "__main__":
    main()
