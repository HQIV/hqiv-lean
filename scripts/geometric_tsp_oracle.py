#!/usr/bin/env python3
"""
Geometric TSP oracle prototype.

Idea:
- treat n-city tours as points on an n-arity arc;
- map arc position -> permutation code (factoradic / Lehmer decode);
- score by closed-tour length on an arbitrary distance matrix;
- search geometrically with rapidity + golden-angle drift.

This script is intentionally explicit and auditable:
- exact verifier for small n (optional);
- no external solver dependency;
- JSON output includes candidate trace summary.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from dataclasses import asdict, dataclass
from typing import Any

PHI = (1.0 + math.sqrt(5.0)) / 2.0
GOLDEN_ANGLE = 2.0 * math.pi / (PHI**2)


@dataclass
class TSPCandidate:
    step: int
    seed_idx: int
    arc_frac: float
    root_distance: float
    permutation_code: int
    tour: list[int]
    tour_cost: float


def morley_seeds() -> list[float]:
    return [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]


def rapidity_delta(scale: int) -> float:
    return math.pi / (4.0 * math.log(scale + 1.0))


def factoradic_to_permutation(code: int, n: int) -> list[int]:
    """Decode integer code in [0, n!-1] into a permutation of [0..n-1]."""
    elems = list(range(n))
    out: list[int] = []
    rem = code
    for k in range(n, 0, -1):
        f = math.factorial(k - 1)
        idx = rem // f if f > 0 else 0
        rem = rem % f if f > 0 else 0
        if idx >= len(elems):
            idx = len(elems) - 1
        out.append(elems.pop(idx))
    return out


def closed_tour_cost(dist: list[list[float]], tour: list[int]) -> float:
    n = len(tour)
    if n == 0:
        return 0.0
    total = 0.0
    for i in range(n):
        a = tour[i]
        b = tour[(i + 1) % n]
        total += dist[a][b]
    return total


def validate_distance_matrix(dist: list[list[float]]) -> None:
    n = len(dist)
    if n < 2:
        raise ValueError("distance matrix must have at least 2 cities")
    for row in dist:
        if len(row) != n:
            raise ValueError("distance matrix must be square")
    for i in range(n):
        for j in range(n):
            if i == j and dist[i][j] != 0:
                raise ValueError("distance matrix diagonal must be zero")
            if dist[i][j] < 0:
                raise ValueError("distance matrix entries must be nonnegative")


def generate_random_euclidean_matrix(n: int, seed: int) -> list[list[float]]:
    rng = random.Random(seed)
    pts = [(rng.random(), rng.random()) for _ in range(n)]
    dist = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            dx = pts[i][0] - pts[j][0]
            dy = pts[i][1] - pts[j][1]
            dist[i][j] = math.hypot(dx, dy)
    return dist


def exact_tsp_cost_small(dist: list[list[float]]) -> tuple[float, list[int]]:
    """
    Exact closed TSP by brute force fixing city 0 as start.
    Intended for small n only (n <= 10 practical).
    """
    n = len(dist)
    best_cost = math.inf
    best_tour: list[int] = []
    for perm in itertools.permutations(range(1, n)):
        tour = [0, *perm]
        c = closed_tour_cost(dist, tour)
        if c < best_cost:
            best_cost = c
            best_tour = list(tour)
    return best_cost, best_tour


def geometric_tsp_solver(
    dist: list[list[float]],
    max_steps: int = 1500,
    top_k: int = 5,
) -> dict[str, Any]:
    validate_distance_matrix(dist)
    n = len(dist)
    seeds = morley_seeds()
    arc_len = math.pi / float(n)
    delta = rapidity_delta(n * n)
    perm_space = math.factorial(n)

    alpha = 0.0
    seen_codes: set[int] = set()
    candidates: list[TSPCandidate] = []
    best: TSPCandidate | None = None
    root_best: TSPCandidate | None = None

    for step in range(max_steps):
        drift = step * GOLDEN_ANGLE
        for seed_idx, seed in enumerate(seeds):
            angle = (alpha + seed + drift) % arc_len
            frac = angle / arc_len if arc_len > 0 else 0.0
            root_distance = min(frac, 1.0 - frac)
            code = min(perm_space - 1, max(0, int(round(frac * (perm_space - 1)))))
            if code in seen_codes:
                continue
            seen_codes.add(code)
            tour = factoradic_to_permutation(code, n)
            cost = closed_tour_cost(dist, tour)
            cand = TSPCandidate(
                step=step,
                seed_idx=seed_idx,
                arc_frac=frac,
                root_distance=root_distance,
                permutation_code=code,
                tour=tour,
                tour_cost=cost,
            )
            candidates.append(cand)
            if best is None or cand.tour_cost < best.tour_cost:
                best = cand
            if root_best is None or cand.root_distance < root_best.root_distance:
                root_best = cand
        alpha += delta
        if len(seen_codes) >= perm_space:
            break

    candidates_sorted = sorted(candidates, key=lambda c: (c.tour_cost, c.root_distance))
    root_sorted = sorted(candidates, key=lambda c: (c.root_distance, c.tour_cost))
    return {
        "n_cities": n,
        "max_steps": max_steps,
        "unique_tours_sampled": len(candidates),
        "tour_space_size": perm_space,
        "coverage_ratio": (len(candidates) / perm_space) if perm_space > 0 else 0.0,
        "best_tour": asdict(best) if best is not None else None,
        "root_closest_tour": asdict(root_best) if root_best is not None else None,
        "top_k_by_cost": [asdict(c) for c in candidates_sorted[:top_k]],
        "top_k_by_root_distance": [asdict(c) for c in root_sorted[:top_k]],
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Geometric n-arity arc TSP prototype")
    p.add_argument("--matrix-json", type=str, default=None, help="path to square distance matrix JSON")
    p.add_argument("--demo-cities", type=int, default=8, help="cities for random Euclidean demo if no matrix provided")
    p.add_argument("--demo-seed", type=int, default=42, help="seed for random demo matrix")
    p.add_argument("--max-steps", type=int, default=1500, help="geometric walk steps")
    p.add_argument("--top-k", type=int, default=5, help="top candidates to report")
    p.add_argument(
        "--exact-if-at-most",
        type=int,
        default=9,
        help="run exact brute-force verifier when n <= this threshold",
    )
    p.add_argument("--json", action="store_true", help="emit full JSON payload")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.max_steps <= 0:
        raise SystemExit("--max-steps must be > 0")
    if args.top_k <= 0:
        raise SystemExit("--top-k must be > 0")

    if args.matrix_json:
        with open(args.matrix_json, "r", encoding="utf-8") as fh:
            dist = json.load(fh)
    else:
        dist = generate_random_euclidean_matrix(args.demo_cities, args.demo_seed)

    payload = geometric_tsp_solver(dist, max_steps=args.max_steps, top_k=args.top_k)
    n = payload["n_cities"]
    if n <= args.exact_if_at_most:
        exact_cost, exact_tour = exact_tsp_cost_small(dist)
        payload["exact_optimal_cost"] = exact_cost
        payload["exact_optimal_tour"] = exact_tour
        if payload["best_tour"] is not None:
            payload["best_vs_exact_gap"] = payload["best_tour"]["tour_cost"] - exact_cost
        else:
            payload["best_vs_exact_gap"] = None

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print(
        f"n={payload['n_cities']} sampled={payload['unique_tours_sampled']}/{payload['tour_space_size']} "
        f"coverage={payload['coverage_ratio']:.4f}"
    )
    if payload["best_tour"] is not None:
        b = payload["best_tour"]
        print(
            f"best_cost={b['tour_cost']:.6f} step={b['step']} root_distance={b['root_distance']:.6f} "
            f"tour={b['tour']}"
        )
    if payload["root_closest_tour"] is not None:
        r = payload["root_closest_tour"]
        print(
            f"root_closest_cost={r['tour_cost']:.6f} step={r['step']} "
            f"root_distance={r['root_distance']:.6f} tour={r['tour']}"
        )
    if "exact_optimal_cost" in payload:
        print(
            f"exact_optimal_cost={payload['exact_optimal_cost']:.6f} "
            f"gap={payload['best_vs_exact_gap']:.6f}"
        )


if __name__ == "__main__":
    main()

