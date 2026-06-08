#!/usr/bin/env python3
"""
Edge-space ATSP oracle prototype (OSHoracle-style scaffold).

Key idea:
- treat directed edges as dimensions (n*(n-1) channels),
- run peel/anneal over edge-space random walks,
- project edge-priority states back to Hamiltonian tours,
- use hard UB prune (safe) + optional soft LB/UB band prune (heuristic).
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
class EdgeSpaceCandidate:
    round_idx: int
    arity: int
    step: int
    tour: list[int]
    tour_cost: float
    rapidity_min_window: float
    rapidity_jitter: float
    effective_score: float
    hard_kept: bool
    soft_kept: bool
    bond_dim: int
    trunc_residual: float
    trunc_residual_ratio: float
    trunc_error_bound_empirical: float
    trunc_error_bound_certified: float
    topology_marker_mean: float
    topology_marker_abs_mean: float
    topology_marker_jitter: float
    topology_regularizer: float
    topology_weight_applied: float


@dataclass
class TensorChainState:
    local: list[list[float]]
    weight: list[float]
    bond_dim: int
    trunc_residual: float
    trunc_residual_ratio: float
    trunc_error_bound_empirical: float
    trunc_error_bound_certified: float


def validate_distance_matrix(dist: list[list[float]]) -> None:
    n = len(dist)
    if n < 2:
        raise ValueError("distance matrix must have at least 2 cities")
    for row in dist:
        if len(row) != n:
            raise ValueError("distance matrix must be square")
    for i in range(n):
        if dist[i][i] != 0:
            raise ValueError("distance matrix diagonal must be zero")


def random_asymmetric_matrix(n: int, seed: int) -> list[list[float]]:
    rng = random.Random(seed)
    pts = [(rng.random(), rng.random(), rng.random()) for _ in range(n)]
    heading = [(rng.random() - 0.5, rng.random() - 0.5, rng.random() - 0.5) for _ in range(n)]
    dist = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            dx = pts[j][0] - pts[i][0]
            dy = pts[j][1] - pts[i][1]
            dz = pts[j][2] - pts[i][2]
            eu = math.sqrt(dx * dx + dy * dy + dz * dz)
            directional = 0.2 * dx * heading[i][0] + 0.2 * dy * heading[i][1] + 0.2 * dz * heading[i][2]
            dist[i][j] = max(1e-6, eu + directional + 0.05 * rng.random() + 0.15)
    return dist


def exact_atsp_small(dist: list[list[float]]) -> tuple[float, list[int]]:
    n = len(dist)
    best = math.inf
    best_tour: list[int] = []
    for perm in itertools.permutations(range(1, n)):
        tour = [0, *perm]
        c = closed_tour_cost(dist, tour)
        if c < best:
            best = c
            best_tour = list(tour)
    return best, best_tour


def closed_tour_cost(dist: list[list[float]], tour: list[int]) -> float:
    n = len(tour)
    return sum(dist[tour[i]][tour[(i + 1) % n]] for i in range(n))


def global_lower_bound_atsp(dist: list[list[float]]) -> float:
    n = len(dist)
    out_lb = sum(min(dist[i][j] for j in range(n) if j != i) for i in range(n))
    in_lb = sum(min(dist[i][j] for i in range(n) if i != j) for j in range(n))
    return max(out_lb, in_lb)


def detect_uniform_cost_matrix(dist: list[list[float]], tol: float = 1e-12) -> tuple[bool, float]:
    n = len(dist)
    vals = [dist[i][j] for i in range(n) for j in range(n) if i != j]
    if not vals:
        return True, 0.0
    vmin = min(vals)
    vmax = max(vals)
    spread = vmax - vmin
    return spread <= max(0.0, tol), spread


def build_directed_edges(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(n) if i != j]


def min_subpath_rapidity(tour: list[int], dist: list[list[float]], window: int = 4) -> float:
    n = len(tour)
    if n == 0:
        return 0.0
    w = max(1, min(window, n))
    edges = [dist[tour[i]][tour[(i + 1) % n]] for i in range(n)]
    best = math.inf
    for i in range(n):
        s = 0.0
        for j in range(w):
            s += edges[(i + j) % n]
        best = min(best, s / float(w))
    return best if math.isfinite(best) else 0.0


def subpath_rapidity_jitter(tour: list[int], dist: list[list[float]], window: int = 4) -> float:
    n = len(tour)
    if n == 0:
        return 0.0
    w = max(1, min(window, n))
    edges = [dist[tour[i]][tour[(i + 1) % n]] for i in range(n)]
    vals = []
    for i in range(n):
        s = 0.0
        for j in range(w):
            s += edges[(i + j) % n]
        vals.append(s / float(w))
    mu = sum(vals) / float(len(vals))
    var = sum((x - mu) ** 2 for x in vals) / float(len(vals))
    return math.sqrt(max(0.0, var))


def topology_cycle_marker_stats(
    tour: list[int], dist: list[list[float]], window: int = 3
) -> tuple[float, float, float]:
    """
    Lightweight topological proxy from directed cycle circulation:
    compare each local forward 3-cycle cost against reverse orientation.
    Returns (mean_marker, abs_mean_marker, marker_jitter).
    """
    n = len(tour)
    if n < 3:
        return 0.0, 0.0, 0.0
    w = max(3, min(window, n))
    vals: list[float] = []
    for i in range(n):
        a = tour[i]
        b = tour[(i + 1) % n]
        c = tour[(i + w - 1) % n]
        fwd = dist[a][b] + dist[b][c] + dist[c][a]
        rev = dist[a][c] + dist[c][b] + dist[b][a]
        denom = max(1e-9, fwd + rev)
        vals.append((fwd - rev) / denom)
    mu = sum(vals) / float(len(vals))
    abs_mu = sum(abs(x) for x in vals) / float(len(vals))
    var = sum((x - mu) ** 2 for x in vals) / float(len(vals))
    return mu, abs_mu, math.sqrt(max(0.0, var))


def resolve_topology_weight(
    policy: str,
    base_weight: float,
    residual_metric: float,
    residual_gate_threshold: float,
    arity: int,
    n: int,
    residual_floor: float,
    arity_exponent: float,
    max_weight: float,
) -> float:
    bw = max(0.0, base_weight)
    if bw <= 0.0:
        return 0.0
    if policy == "off":
        return 0.0
    if policy == "fixed":
        return min(max_weight, bw)
    gate_t = max(1e-12, residual_gate_threshold)
    floor = min(1.0, max(0.0, residual_floor))
    residual_scale = 1.0 if residual_metric <= gate_t else floor
    nn = max(1, n)
    kk = max(1, min(arity, nn))
    t = float(kk) / float(nn)
    exp = max(0.0, arity_exponent)
    arity_scale = t**exp if exp > 0.0 else 1.0
    if policy == "residual-gated":
        return min(max_weight, bw * residual_scale)
    if policy == "arity-ramp":
        return min(max_weight, bw * arity_scale)
    if policy == "residual-arity":
        return min(max_weight, bw * residual_scale * arity_scale)
    raise ValueError(f"unknown topology policy: {policy}")


def tensor_chain_seed(m: int, seed_idx: int, chi_max: int, chi_target: int) -> TensorChainState:
    chi_work = max(2, min(max(2, chi_max), max(2, 2 * chi_target)))
    local: list[list[float]] = []
    for i in range(m):
        row = []
        for r in range(chi_work):
            v = 0.5 + 0.5 * math.sin((i + 1) * (seed_idx + 1) * 0.07 + r / PHI)
            row.append(v)
        local.append(row)
    weight = [0.5 + 0.5 * math.cos((seed_idx + 1) * 0.23 + r * 0.11) for r in range(chi_work)]
    return TensorChainState(
        local=local,
        weight=weight,
        bond_dim=chi_work,
        trunc_residual=0.0,
        trunc_residual_ratio=0.0,
        trunc_error_bound_empirical=0.0,
        trunc_error_bound_certified=0.0,
    )


def tensor_chain_priorities(state: TensorChainState) -> list[float]:
    out: list[float] = []
    for row in state.local:
        s = 0.0
        for r, w in enumerate(state.weight):
            s += row[r] * w
        out.append(s)
    return out


def tensor_chain_step(state: TensorChainState, step: int, arity: int, chi_target: int) -> TensorChainState:
    # Catenary-like widening on peel side, converging as arity increases.
    scale = 1.0 + 0.25 * (math.cosh(1.5 / max(1.0, float(arity))) - 1.0)
    drift = GOLDEN_ANGLE * (step + 1)
    m = len(state.local)
    chi = state.bond_dim
    local = [row[:] for row in state.local]
    weight = state.weight[:]

    for i in range(m):
        left_i = (i - 1) % m
        right_i = (i + 1) % m
        for r in range(chi):
            neighbor_mix = 0.5 * (state.local[left_i][r] + state.local[right_i][r])
            local[i][r] = (
                0.70 * state.local[i][r]
                + 0.25 * neighbor_mix
                + 0.05 * math.sin(drift + i / PHI + 0.13 * r) * scale
            )
            # Phase-2 proof channel assumes local amplitudes are unit-bounded.
            local[i][r] = min(1.0, max(0.0, local[i][r]))

    for r in range(chi):
        weight[r] = (
            0.92 * state.weight[r]
            + 0.08 * math.cos(drift + r * 0.17) * scale
        )

    # Normalize weights to stable numeric range.
    wnorm = math.sqrt(sum(w * w for w in weight))
    if wnorm > 1e-12:
        weight = [w / wnorm for w in weight]

    # Truncate to target bond dimension and report dropped channel mass.
    tgt = max(2, min(chi, chi_target))
    if tgt == chi:
        return TensorChainState(
            local=local,
            weight=weight,
            bond_dim=chi,
            trunc_residual=0.0,
            trunc_residual_ratio=0.0,
            trunc_error_bound_empirical=0.0,
            trunc_error_bound_certified=0.0,
        )

    # Rank channels by weighted energy contribution.
    channel_score: list[tuple[float, int]] = []
    for r in range(chi):
        avg = sum(local[i][r] for i in range(m)) / float(max(1, m))
        channel_score.append((abs(weight[r]) * avg, r))
    channel_score.sort(reverse=True)
    keep = {idx for _, idx in channel_score[:tgt]}
    dropped = [idx for idx in range(chi) if idx not in keep]
    residual = sum(abs(weight[idx]) for idx in dropped)
    total_mass = sum(abs(w) for w in weight)
    residual_ratio = residual / max(1e-12, total_mass)

    # Empirical and certified bounds for projection error from truncation.
    # Certified channel (proved in Lean): if local amplitudes are in [0, 1],
    # then per-edge priority truncation error is at most dropped weight mass.
    dropped_abs = [abs(weight[idx]) for idx in dropped]
    empirical_bound = 0.0
    for i in range(m):
        edge_err = 0.0
        for t, idx in enumerate(dropped):
            edge_err += dropped_abs[t] * abs(local[i][idx])
        if edge_err > empirical_bound:
            empirical_bound = edge_err
    certified_bound = residual

    remap = sorted(keep)
    new_local: list[list[float]] = []
    for i in range(m):
        new_local.append([local[i][idx] for idx in remap])
    new_weight = [weight[idx] for idx in remap]
    return TensorChainState(
        local=new_local,
        weight=new_weight,
        bond_dim=tgt,
        trunc_residual=residual,
        trunc_residual_ratio=residual_ratio,
        trunc_error_bound_empirical=empirical_bound,
        trunc_error_bound_certified=certified_bound,
    )


def would_form_small_cycle(succ: list[int], u: int, v: int, selected: int, n: int) -> bool:
    # Follow successor chain from v; if we get back to u before final edge, it is a strict subtour.
    cur = v
    hops = 0
    while cur != -1 and hops <= n:
        if cur == u:
            return selected < n - 1
        cur = succ[cur]
        hops += 1
    return False


def project_edge_priorities_to_tour(
    n: int,
    edges: list[tuple[int, int]],
    priorities: list[float],
    dist: list[list[float]],
) -> list[int]:
    ranked = sorted(
        range(len(edges)),
        key=lambda idx: (priorities[idx], dist[edges[idx][0]][edges[idx][1]]),
    )
    succ = [-1] * n
    pred = [-1] * n
    selected = 0
    for idx in ranked:
        u, v = edges[idx]
        if succ[u] != -1 or pred[v] != -1:
            continue
        if would_form_small_cycle(succ, u, v, selected, n):
            continue
        succ[u] = v
        pred[v] = u
        selected += 1
        if selected == n:
            break

    if selected < n:
        # Deterministic repair from city 0 based on edge priorities.
        tour = [0]
        used = {0}
        cur = 0
        for _ in range(n - 1):
            choices = [(priorities[i], dist[cur][j], j) for i, (u, j) in enumerate(edges) if u == cur and j not in used]
            if not choices:
                rest = [j for j in range(n) if j not in used]
                if not rest:
                    break
                nxt = rest[0]
            else:
                choices.sort()
                nxt = choices[0][2]
            tour.append(nxt)
            used.add(nxt)
            cur = nxt
        if len(tour) < n:
            tour.extend([j for j in range(n) if j not in used])
        return tour[:n]

    # Decode cycle by following successor from 0.
    tour = [0]
    seen = {0}
    cur = 0
    for _ in range(n - 1):
        nxt = succ[cur]
        if nxt == -1 or nxt in seen:
            break
        tour.append(nxt)
        seen.add(nxt)
        cur = nxt
    if len(tour) < n:
        tour.extend([j for j in range(n) if j not in seen])
    return tour[:n]


def rotate_tour_to_zero(tour: list[int]) -> list[int]:
    if not tour:
        return tour
    if 0 not in tour:
        return tour
    i0 = tour.index(0)
    return tour[i0:] + tour[:i0]


def two_opt_best_neighbor(tour: list[int], dist: list[list[float]]) -> tuple[list[int], float]:
    n = len(tour)
    if n < 4:
        return tour, closed_tour_cost(dist, tour)
    base = closed_tour_cost(dist, tour)
    best_tour = tour
    best_cost = base
    for i in range(n - 1):
        for j in range(i + 2, n):
            if i == 0 and j == n - 1:
                continue
            cand = tour[: i + 1] + list(reversed(tour[i + 1 : j + 1])) + tour[j + 1 :]
            c = closed_tour_cost(dist, cand)
            if c + 1e-12 < best_cost:
                best_tour = cand
                best_cost = c
    return best_tour, best_cost


def three_opt_sampled_best_neighbor(
    tour: list[int], dist: list[list[float]], trials: int, rng: random.Random
) -> tuple[list[int], float]:
    n = len(tour)
    if n < 6 or trials <= 0:
        return tour, closed_tour_cost(dist, tour)
    base = closed_tour_cost(dist, tour)
    best_tour = tour
    best_cost = base
    for _ in range(trials):
        i, j, k = sorted(rng.sample(range(1, n), 3))
        if not (i < j < k):
            continue
        a = tour[:i]
        b = tour[i:j]
        c = tour[j:k]
        d = tour[k:]
        candidates = [
            a + list(reversed(b)) + c + d,
            a + b + list(reversed(c)) + d,
            a + c + b + d,
            a + list(reversed(c)) + b + d,
        ]
        for cand in candidates:
            cc = closed_tour_cost(dist, cand)
            if cc + 1e-12 < best_cost:
                best_tour = cand
                best_cost = cc
    return best_tour, best_cost


def seeded_local_completion(
    seeds: list[list[int]],
    dist: list[list[float]],
    rounds: int = 2,
    use_3opt: bool = True,
    three_opt_trials: int = 32,
    rng_seed: int = 12345,
) -> list[tuple[list[int], float, float]]:
    out: list[tuple[list[int], float, float]] = []
    rng = random.Random(rng_seed)
    for seed in seeds:
        cur = rotate_tour_to_zero(seed)
        base_cost = closed_tour_cost(dist, cur)
        best = cur
        best_cost = base_cost
        for _ in range(max(1, rounds)):
            improved = False
            t2, c2 = two_opt_best_neighbor(best, dist)
            if c2 + 1e-12 < best_cost:
                best = rotate_tour_to_zero(t2)
                best_cost = c2
                improved = True
            if use_3opt:
                t3, c3 = three_opt_sampled_best_neighbor(best, dist, max(0, three_opt_trials), rng)
                if c3 + 1e-12 < best_cost:
                    best = rotate_tour_to_zero(t3)
                    best_cost = c3
                    improved = True
            if not improved:
                break
        out.append((best, base_cost, best_cost))
    return out


def solve_edge_space_atsp(
    dist: list[list[float]],
    rounds: int = 3,
    peel_start: int = 2,
    max_steps: int = 800,
    top_k: int = 12,
    rapidity_window: int = 4,
    soft_alpha: float = 0.85,
    use_soft_prune: bool = True,
    chi_max: int = 24,
    chi_base: int = 4,
    residual_gate_threshold: float = 0.20,
    residual_gate_strength: float = 1.0,
    residual_gate_use_ratio: bool = True,
    topology_regularizer_weight: float = 0.0,
    topology_jitter_weight: float = 0.5,
    topology_window: int = 3,
    topology_policy: str = "fixed",
    topology_residual_floor: float = 0.0,
    topology_arity_exponent: float = 0.5,
    topology_max_weight: float = 1.0,
    seeded_local_search: bool = True,
    seeded_local_topk: int = 8,
    seeded_local_rounds: int = 2,
    seeded_use_3opt: bool = True,
    seeded_three_opt_trials: int = 32,
    degenerate_uniform_tol: float = 1e-12,
    degenerate_short_circuit: bool = False,
) -> dict[str, Any]:
    validate_distance_matrix(dist)
    n = len(dist)
    edges = build_directed_edges(n)
    m = len(edges)
    edge_mean = sum(dist[i][j] for i in range(n) for j in range(n) if i != j) / float(max(1, n * (n - 1)))
    lb = global_lower_bound_atsp(dist)
    ub = math.inf
    pool: list[EdgeSpaceCandidate] = []
    trace: list[dict[str, Any]] = []
    soft_coupling_trigger_count = 0
    soft_coupling_total_count = 0
    seeded_local_candidates_added = 0
    seeded_local_improvements = 0
    degenerate_uniform_detected, degenerate_uniform_spread = detect_uniform_cost_matrix(
        dist, tol=degenerate_uniform_tol
    )

    if degenerate_uniform_detected and degenerate_short_circuit:
        tour = list(range(n))
        cost = closed_tour_cost(dist, tour)
        ub = cost
        rap = min_subpath_rapidity(tour, dist, rapidity_window)
        jit = subpath_rapidity_jitter(tour, dist, rapidity_window)
        top_mean, top_abs_mean, top_jitter = topology_cycle_marker_stats(
            tour, dist, window=topology_window
        )
        top_weight = resolve_topology_weight(
            policy=topology_policy,
            base_weight=topology_regularizer_weight,
            residual_metric=0.0,
            residual_gate_threshold=residual_gate_threshold,
            arity=n,
            n=n,
            residual_floor=topology_residual_floor,
            arity_exponent=topology_arity_exponent,
            max_weight=max(0.0, topology_max_weight),
        )
        top_reg = top_weight * (top_abs_mean + max(0.0, topology_jitter_weight) * top_jitter)
        eff = (
            cost / max(1e-9, edge_mean * n)
            + 0.20 * (rap / max(1e-9, edge_mean))
            + 0.10 * (jit / max(1e-9, edge_mean))
            + top_reg
        )
        pool = [
            EdgeSpaceCandidate(
                round_idx=0,
                arity=n,
                step=0,
                tour=tour,
                tour_cost=cost,
                rapidity_min_window=rap,
                rapidity_jitter=jit,
                effective_score=eff,
                hard_kept=True,
                soft_kept=True,
                bond_dim=0,
                trunc_residual=0.0,
                trunc_residual_ratio=0.0,
                trunc_error_bound_empirical=0.0,
                trunc_error_bound_certified=0.0,
                topology_marker_mean=top_mean,
                topology_marker_abs_mean=top_abs_mean,
                topology_marker_jitter=top_jitter,
                topology_regularizer=top_reg,
                topology_weight_applied=top_weight,
            )
        ]
        trace.append(
            {
                "round": 0,
                "arity": n,
                "lb": lb,
                "ub": ub,
                "soft_bound": ub,
                "soft_alpha_effective": 1.0,
                "soft_alpha_effective_mean": 1.0,
                "pool_size": len(pool),
                "chi_target": 0,
                "topology_weight_mean": top_weight,
                "mode": "degenerate-short-circuit",
            }
        )

    if not (degenerate_uniform_detected and degenerate_short_circuit):
        for ridx in range(max(1, rounds)):
            for arity in range(max(1, peel_start), n + 1):
                chi_target = max(2, min(chi_max, chi_base + arity // 2))
                seeds = [tensor_chain_seed(m, s, chi_max=chi_max, chi_target=chi_target) for s in range(3)]
                stage_topology_weight_sum = 0.0
                stage_alpha_sum = 0.0
                stage_count = 0
                for sidx, state in enumerate(seeds):
                    cur = state
                    steps = max(4, max_steps // max(1, n - arity + 1))
                    for step in range(steps):
                        cur = tensor_chain_step(cur, step, arity, chi_target=chi_target)
                        priorities = tensor_chain_priorities(cur)
                        tour = project_edge_priorities_to_tour(n, edges, priorities, dist)
                        cost = closed_tour_cost(dist, tour)
                        rap = min_subpath_rapidity(tour, dist, rapidity_window)
                        jit = subpath_rapidity_jitter(tour, dist, rapidity_window)
                        top_mean, top_abs_mean, top_jitter = topology_cycle_marker_stats(
                            tour, dist, window=topology_window
                        )
                        residual_metric_for_topology = (
                            cur.trunc_residual_ratio if residual_gate_use_ratio else cur.trunc_error_bound_certified
                        )
                        top_weight = resolve_topology_weight(
                            policy=topology_policy,
                            base_weight=topology_regularizer_weight,
                            residual_metric=max(0.0, residual_metric_for_topology),
                            residual_gate_threshold=residual_gate_threshold,
                            arity=arity,
                            n=n,
                            residual_floor=topology_residual_floor,
                            arity_exponent=topology_arity_exponent,
                            max_weight=max(0.0, topology_max_weight),
                        )
                        top_reg = top_weight * (
                            top_abs_mean + max(0.0, topology_jitter_weight) * top_jitter
                        )
                        eff = (
                            cost / max(1e-9, edge_mean * n)
                            + 0.20 * (rap / max(1e-9, edge_mean))
                            + 0.10 * (jit / max(1e-9, edge_mean))
                            + top_reg
                        )
                        prev_ub = ub
                        if cost < ub:
                            ub = cost
                        hard_kept = cost <= ub + 1e-9

                        # Phase-3 boundary coupling: only tighten soft boundary when
                        # truncation residual is below certified gate threshold.
                        raw_residual_metric = (
                            cur.trunc_residual_ratio if residual_gate_use_ratio else cur.trunc_error_bound_certified
                        )
                        residual_metric = max(0.0, raw_residual_metric)
                        gate_t = max(1e-12, residual_gate_threshold)
                        gate_strength = max(0.0, residual_gate_strength)
                        base_alpha = max(0.0, min(1.0, soft_alpha))
                        if residual_metric <= gate_t:
                            soft_coupling_trigger_count += 1
                            # Stronger tightening as residual gets smaller.
                            tighten = max(0.0, min(1.0, 1.0 - residual_metric / gate_t))
                            alpha_eff = 1.0 - (1.0 - base_alpha) * min(1.0, gate_strength * tighten)
                        else:
                            # Above gate: no shrink (soft boundary coincides with UB).
                            alpha_eff = 1.0
                        soft_coupling_total_count += 1
                        stage_topology_weight_sum += top_weight
                        stage_alpha_sum += alpha_eff
                        stage_count += 1

                        soft_bound = lb + alpha_eff * max(0.0, ub - lb)
                        if not use_soft_prune or not math.isfinite(prev_ub):
                            soft_kept = True
                        else:
                            # Witness-safe soft prune: never drop current UB witness.
                            soft_bound_prev = lb + alpha_eff * max(0.0, prev_ub - lb)
                            soft_kept = (cost <= soft_bound_prev + 1e-9) or (cost <= ub + 1e-9)
                        cand = EdgeSpaceCandidate(
                            round_idx=ridx + 1,
                            arity=arity,
                            step=step + sidx * steps,
                            tour=tour,
                            tour_cost=cost,
                            rapidity_min_window=rap,
                            rapidity_jitter=jit,
                            effective_score=eff,
                            hard_kept=hard_kept,
                            soft_kept=soft_kept,
                            bond_dim=cur.bond_dim,
                            trunc_residual=cur.trunc_residual,
                            trunc_residual_ratio=cur.trunc_residual_ratio,
                            trunc_error_bound_empirical=cur.trunc_error_bound_empirical,
                            trunc_error_bound_certified=cur.trunc_error_bound_certified,
                            topology_marker_mean=top_mean,
                            topology_marker_abs_mean=top_abs_mean,
                            topology_marker_jitter=top_jitter,
                            topology_regularizer=top_reg,
                            topology_weight_applied=top_weight,
                        )
                        if hard_kept and soft_kept:
                            pool.append(cand)
                pool.sort(key=lambda c: (c.effective_score, c.tour_cost))
                # Keep diverse elite set.
                dedupe: dict[tuple[int, ...], EdgeSpaceCandidate] = {}
                for c in pool:
                    key = tuple(c.tour)
                    if key not in dedupe:
                        dedupe[key] = c
                pool = sorted(dedupe.values(), key=lambda c: (c.effective_score, c.tour_cost))[
                    : max(top_k, 4 * top_k)
                ]
                trace.append(
                    {
                        "round": ridx + 1,
                        "arity": arity,
                        "lb": lb,
                        "ub": ub,
                        "soft_bound": lb + alpha_eff * max(0.0, ub - lb),
                        "soft_alpha_effective": alpha_eff,
                        "soft_alpha_effective_mean": stage_alpha_sum / float(max(1, stage_count)),
                        "pool_size": len(pool),
                        "chi_target": chi_target,
                        "topology_weight_mean": stage_topology_weight_sum / float(max(1, stage_count)),
                    }
                )

    if seeded_local_search and pool:
        seeds = [c.tour for c in sorted(pool, key=lambda c: c.tour_cost)[: max(1, seeded_local_topk)]]
        refined = seeded_local_completion(
            seeds=seeds,
            dist=dist,
            rounds=seeded_local_rounds,
            use_3opt=seeded_use_3opt,
            three_opt_trials=seeded_three_opt_trials,
            rng_seed=(n * 7919 + rounds * 104729),
        )
        for idx, (rtour, seed_cost, rcost) in enumerate(refined):
            if rcost + 1e-12 < seed_cost:
                seeded_local_improvements += 1
            rap = min_subpath_rapidity(rtour, dist, rapidity_window)
            jit = subpath_rapidity_jitter(rtour, dist, rapidity_window)
            top_mean, top_abs_mean, top_jitter = topology_cycle_marker_stats(
                rtour, dist, window=topology_window
            )
            residual_metric_for_topology = 0.0
            top_weight = resolve_topology_weight(
                policy=topology_policy,
                base_weight=topology_regularizer_weight,
                residual_metric=residual_metric_for_topology,
                residual_gate_threshold=residual_gate_threshold,
                arity=n,
                n=n,
                residual_floor=topology_residual_floor,
                arity_exponent=topology_arity_exponent,
                max_weight=max(0.0, topology_max_weight),
            )
            top_reg = top_weight * (top_abs_mean + max(0.0, topology_jitter_weight) * top_jitter)
            eff = (
                rcost / max(1e-9, edge_mean * n)
                + 0.20 * (rap / max(1e-9, edge_mean))
                + 0.10 * (jit / max(1e-9, edge_mean))
                + top_reg
            )
            prev_ub = ub
            if rcost < ub:
                ub = rcost
            hard_kept = rcost <= ub + 1e-9
            gate_t = max(1e-12, residual_gate_threshold)
            gate_strength = max(0.0, residual_gate_strength)
            base_alpha = max(0.0, min(1.0, soft_alpha))
            if 0.0 <= gate_t:
                soft_coupling_trigger_count += 1
                tighten = 1.0
                alpha_eff = 1.0 - (1.0 - base_alpha) * min(1.0, gate_strength * tighten)
            else:
                alpha_eff = 1.0
            soft_coupling_total_count += 1
            if not use_soft_prune or not math.isfinite(prev_ub):
                soft_kept = True
            else:
                soft_bound_prev = lb + alpha_eff * max(0.0, prev_ub - lb)
                soft_kept = (rcost <= soft_bound_prev + 1e-9) or (rcost <= ub + 1e-9)
            cand = EdgeSpaceCandidate(
                round_idx=rounds + 1,
                arity=n,
                step=-(idx + 1),
                tour=rotate_tour_to_zero(rtour),
                tour_cost=rcost,
                rapidity_min_window=rap,
                rapidity_jitter=jit,
                effective_score=eff,
                hard_kept=hard_kept,
                soft_kept=soft_kept,
                bond_dim=0,
                trunc_residual=0.0,
                trunc_residual_ratio=0.0,
                trunc_error_bound_empirical=0.0,
                trunc_error_bound_certified=0.0,
                topology_marker_mean=top_mean,
                topology_marker_abs_mean=top_abs_mean,
                topology_marker_jitter=top_jitter,
                topology_regularizer=top_reg,
                topology_weight_applied=top_weight,
            )
            if hard_kept and soft_kept:
                pool.append(cand)
                seeded_local_candidates_added += 1

    if not pool:
        # Fallback exact smallest witness for safety.
        c, t = exact_atsp_small(dist) if n <= 10 else (math.inf, list(range(n)))
        best = EdgeSpaceCandidate(1, n, 0, t, c, 0.0, 0.0, c, True, True, 0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        pool = [best]

    by_cost = sorted(pool, key=lambda c: c.tour_cost)
    by_eff = sorted(pool, key=lambda c: c.effective_score)
    mean_bond_dim = sum(c.bond_dim for c in pool) / float(max(1, len(pool)))
    mean_trunc_residual = sum(c.trunc_residual for c in pool) / float(max(1, len(pool)))
    mean_trunc_residual_ratio = sum(c.trunc_residual_ratio for c in pool) / float(max(1, len(pool)))
    mean_trunc_error_bound_empirical = sum(c.trunc_error_bound_empirical for c in pool) / float(max(1, len(pool)))
    mean_trunc_error_bound_certified = sum(c.trunc_error_bound_certified for c in pool) / float(max(1, len(pool)))
    mean_topology_marker_mean = sum(c.topology_marker_mean for c in pool) / float(max(1, len(pool)))
    mean_topology_marker_abs_mean = sum(c.topology_marker_abs_mean for c in pool) / float(max(1, len(pool)))
    mean_topology_marker_jitter = sum(c.topology_marker_jitter for c in pool) / float(max(1, len(pool)))
    mean_topology_regularizer = sum(c.topology_regularizer for c in pool) / float(max(1, len(pool)))
    mean_topology_weight_applied = sum(c.topology_weight_applied for c in pool) / float(max(1, len(pool)))
    out: dict[str, Any] = {
        "n_cities": n,
        "edge_dimensions": m,
        "lb": lb,
        "ub": ub,
        "soft_alpha": soft_alpha,
        "soft_prune_enabled": use_soft_prune,
        "residual_gate_threshold": residual_gate_threshold,
        "residual_gate_strength": residual_gate_strength,
        "residual_gate_use_ratio": residual_gate_use_ratio,
        "topology_regularizer_weight": topology_regularizer_weight,
        "topology_jitter_weight": topology_jitter_weight,
        "topology_window": topology_window,
        "topology_policy": topology_policy,
        "topology_residual_floor": topology_residual_floor,
        "topology_arity_exponent": topology_arity_exponent,
        "topology_max_weight": topology_max_weight,
        "degenerate_uniform_tol": degenerate_uniform_tol,
        "degenerate_uniform_detected": degenerate_uniform_detected,
        "degenerate_uniform_spread": degenerate_uniform_spread,
        "degenerate_short_circuit": degenerate_short_circuit,
        "seeded_local_search": seeded_local_search,
        "seeded_local_topk": seeded_local_topk,
        "seeded_local_rounds": seeded_local_rounds,
        "seeded_use_3opt": seeded_use_3opt,
        "seeded_three_opt_trials": seeded_three_opt_trials,
        "seeded_local_candidates_added": seeded_local_candidates_added,
        "seeded_local_improvements": seeded_local_improvements,
        "soft_coupling_trigger_count": soft_coupling_trigger_count,
        "soft_coupling_total_count": soft_coupling_total_count,
        "soft_coupling_trigger_rate": (
            float(soft_coupling_trigger_count) / float(max(1, soft_coupling_total_count))
        ),
        "chi_max": chi_max,
        "chi_base": chi_base,
        "rounds": rounds,
        "peel_start": peel_start,
        "max_steps": max_steps,
        "mean_bond_dim": mean_bond_dim,
        "mean_trunc_residual": mean_trunc_residual,
        "mean_trunc_residual_ratio": mean_trunc_residual_ratio,
        "mean_trunc_error_bound_empirical": mean_trunc_error_bound_empirical,
        "mean_trunc_error_bound_certified": mean_trunc_error_bound_certified,
        "mean_topology_marker_mean": mean_topology_marker_mean,
        "mean_topology_marker_abs_mean": mean_topology_marker_abs_mean,
        "mean_topology_marker_jitter": mean_topology_marker_jitter,
        "mean_topology_regularizer": mean_topology_regularizer,
        "mean_topology_weight_applied": mean_topology_weight_applied,
        "best_by_cost": asdict(by_cost[0]),
        "best_by_effective_score": asdict(by_eff[0]),
        "top_k_by_cost": [asdict(c) for c in by_cost[:top_k]],
        "top_k_by_effective_score": [asdict(c) for c in by_eff[:top_k]],
        "trace": trace,
    }
    return out


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Edge-space OSHoracle-style ATSP prototype")
    p.add_argument("--matrix-json", type=str, default=None, help="path to square distance matrix JSON")
    p.add_argument("--demo-cities", type=int, default=10, help="city count for random asymmetric demo")
    p.add_argument("--demo-seed", type=int, default=1234, help="seed for random demo matrix")
    p.add_argument("--rounds", type=int, default=3, help="macro peel+anneal rounds")
    p.add_argument("--peel-start", type=int, default=2, help="starting arity for peel ladder")
    p.add_argument("--max-steps", type=int, default=800, help="edge-space random-walk budget per stage")
    p.add_argument("--top-k", type=int, default=12, help="top candidates to report")
    p.add_argument("--rapidity-window", type=int, default=4, help="subpath window for rapidity bookkeeping")
    p.add_argument("--soft-alpha", type=float, default=0.85, help="soft prune boundary LB + alpha*(UB-LB)")
    p.add_argument("--soft-prune", action=argparse.BooleanOptionalAction, default=True, help="enable heuristic soft boundary in addition to hard UB prune")
    p.add_argument("--residual-gate-threshold", type=float, default=0.20, help="Phase-3 gate: shrink soft boundary only when residual metric <= threshold")
    p.add_argument("--residual-gate-strength", type=float, default=1.0, help="Phase-3 coupling strength in [0,+inf), 1.0 = full programmed tighten")
    p.add_argument("--residual-gate-use-ratio", action=argparse.BooleanOptionalAction, default=True, help="Phase-3 gate metric: residual ratio when true, certified absolute residual when false")
    p.add_argument("--topology-regularizer-weight", type=float, default=0.0, help="Phase-4 optional topology channel weight (score-only, never pruning)")
    p.add_argument("--topology-jitter-weight", type=float, default=0.5, help="Phase-4 topology jitter contribution inside regularizer")
    p.add_argument("--topology-window", type=int, default=3, help="Phase-4 cycle marker window (>=3)")
    p.add_argument("--topology-policy", type=str, default="fixed", choices=["off", "fixed", "residual-gated", "arity-ramp", "residual-arity"], help="Phase-5 topology weighting policy")
    p.add_argument("--topology-residual-floor", type=float, default=0.0, help="Phase-5 residual policy floor in [0,1] when residual gate fails")
    p.add_argument("--topology-arity-exponent", type=float, default=0.5, help="Phase-5 arity ramp exponent")
    p.add_argument("--topology-max-weight", type=float, default=1.0, help="Phase-5 cap for applied topology weight")
    p.add_argument("--seeded-local-search", action=argparse.BooleanOptionalAction, default=True, help="run stage-2 seeded local completion (2-opt / sampled 3-opt)")
    p.add_argument("--seeded-local-topk", type=int, default=8, help="number of geometric seeds sent to stage-2 local completion")
    p.add_argument("--seeded-local-rounds", type=int, default=2, help="max local-improvement rounds per seed")
    p.add_argument("--seeded-use-3opt", action=argparse.BooleanOptionalAction, default=True, help="enable sampled 3-opt style moves in stage-2 completion")
    p.add_argument("--seeded-three-opt-trials", type=int, default=32, help="sampled 3-opt trials per local round")
    p.add_argument("--degenerate-uniform-tol", type=float, default=1e-12, help="uniform-cost detector tolerance on off-diagonal spread")
    p.add_argument("--degenerate-short-circuit", action=argparse.BooleanOptionalAction, default=False, help="if uniform-cost is detected, route directly to geometric regularizer witness")
    p.add_argument("--chi-max", type=int, default=24, help="maximum tensor-chain bond dimension")
    p.add_argument("--chi-base", type=int, default=4, help="base target bond dimension at low arity")
    p.add_argument("--exact-if-at-most", type=int, default=10, help="run exact brute-force checker if n <= threshold")
    p.add_argument("--json", action="store_true", help="emit JSON payload")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.rounds < 1:
        raise SystemExit("--rounds must be >= 1")
    if args.peel_start < 1:
        raise SystemExit("--peel-start must be >= 1")
    if args.max_steps < 1:
        raise SystemExit("--max-steps must be >= 1")
    if args.top_k < 1:
        raise SystemExit("--top-k must be >= 1")
    if args.rapidity_window < 1:
        raise SystemExit("--rapidity-window must be >= 1")
    if not (0.0 <= args.soft_alpha <= 1.0):
        raise SystemExit("--soft-alpha must be in [0,1]")
    if args.residual_gate_threshold < 0.0:
        raise SystemExit("--residual-gate-threshold must be >= 0")
    if args.residual_gate_strength < 0.0:
        raise SystemExit("--residual-gate-strength must be >= 0")
    if args.topology_regularizer_weight < 0.0:
        raise SystemExit("--topology-regularizer-weight must be >= 0")
    if args.topology_jitter_weight < 0.0:
        raise SystemExit("--topology-jitter-weight must be >= 0")
    if args.topology_window < 3:
        raise SystemExit("--topology-window must be >= 3")
    if not (0.0 <= args.topology_residual_floor <= 1.0):
        raise SystemExit("--topology-residual-floor must be in [0,1]")
    if args.topology_arity_exponent < 0.0:
        raise SystemExit("--topology-arity-exponent must be >= 0")
    if args.topology_max_weight < 0.0:
        raise SystemExit("--topology-max-weight must be >= 0")
    if args.seeded_local_topk < 1:
        raise SystemExit("--seeded-local-topk must be >= 1")
    if args.seeded_local_rounds < 1:
        raise SystemExit("--seeded-local-rounds must be >= 1")
    if args.seeded_three_opt_trials < 0:
        raise SystemExit("--seeded-three-opt-trials must be >= 0")
    if args.degenerate_uniform_tol < 0.0:
        raise SystemExit("--degenerate-uniform-tol must be >= 0")
    if args.chi_max < 2:
        raise SystemExit("--chi-max must be >= 2")
    if args.chi_base < 2:
        raise SystemExit("--chi-base must be >= 2")

    if args.matrix_json:
        with open(args.matrix_json, "r", encoding="utf-8") as fh:
            dist = json.load(fh)
    else:
        dist = random_asymmetric_matrix(args.demo_cities, args.demo_seed)

    payload = solve_edge_space_atsp(
        dist=dist,
        rounds=args.rounds,
        peel_start=args.peel_start,
        max_steps=args.max_steps,
        top_k=args.top_k,
        rapidity_window=args.rapidity_window,
        soft_alpha=args.soft_alpha,
        use_soft_prune=args.soft_prune,
        chi_max=args.chi_max,
        chi_base=args.chi_base,
        residual_gate_threshold=args.residual_gate_threshold,
        residual_gate_strength=args.residual_gate_strength,
        residual_gate_use_ratio=args.residual_gate_use_ratio,
        topology_regularizer_weight=args.topology_regularizer_weight,
        topology_jitter_weight=args.topology_jitter_weight,
        topology_window=args.topology_window,
        topology_policy=args.topology_policy,
        topology_residual_floor=args.topology_residual_floor,
        topology_arity_exponent=args.topology_arity_exponent,
        topology_max_weight=args.topology_max_weight,
        seeded_local_search=args.seeded_local_search,
        seeded_local_topk=args.seeded_local_topk,
        seeded_local_rounds=args.seeded_local_rounds,
        seeded_use_3opt=args.seeded_use_3opt,
        seeded_three_opt_trials=args.seeded_three_opt_trials,
        degenerate_uniform_tol=args.degenerate_uniform_tol,
        degenerate_short_circuit=args.degenerate_short_circuit,
    )

    n = payload["n_cities"]
    if n <= args.exact_if_at_most:
        exact_cost, exact_tour = exact_atsp_small(dist)
        payload["exact_optimal_cost"] = exact_cost
        payload["exact_optimal_tour"] = exact_tour
        payload["gap_best_cost"] = payload["best_by_cost"]["tour_cost"] - exact_cost
        payload["gap_best_effective"] = payload["best_by_effective_score"]["tour_cost"] - exact_cost

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print(
        f"n={payload['n_cities']} edge_dims={payload['edge_dimensions']} "
        f"lb={payload['lb']:.6f} ub={payload['ub']:.6f}"
    )
    b = payload["best_by_cost"]
    e = payload["best_by_effective_score"]
    print(f"best_cost={b['tour_cost']:.6f} tour={b['tour']} r={b['round_idx']} k={b['arity']}")
    print(
        f"best_effective_cost={e['tour_cost']:.6f} score={e['effective_score']:.6f} "
        f"rap={e['rapidity_min_window']:.6f} jitter={e['rapidity_jitter']:.6f} "
        f"bond_dim={e['bond_dim']} trunc_res={e['trunc_residual']:.6f} "
        f"trunc_ratio={e['trunc_residual_ratio']:.6f} "
        f"err_emp={e['trunc_error_bound_empirical']:.6f} "
        f"err_cert={e['trunc_error_bound_certified']:.6f} "
        f"top_abs={e['topology_marker_abs_mean']:.6f} "
        f"top_jit={e['topology_marker_jitter']:.6f} "
        f"top_reg={e['topology_regularizer']:.6f}"
    )
    print(
        f"topology policy={payload['topology_policy']} "
        f"w_base={payload['topology_regularizer_weight']:.4f} "
        f"w_mean={payload['mean_topology_weight_applied']:.4f}"
    )
    print(
        f"soft_coupling trigger_rate={payload['soft_coupling_trigger_rate']:.3f} "
        f"({payload['soft_coupling_trigger_count']}/{payload['soft_coupling_total_count']}) "
        f"gate={payload['residual_gate_threshold']:.6f} "
        f"use_ratio={payload['residual_gate_use_ratio']}"
    )
    print(
        f"seeded_local enabled={payload['seeded_local_search']} "
        f"added={payload['seeded_local_candidates_added']} "
        f"improved={payload['seeded_local_improvements']}"
    )
    print(
        f"degenerate_uniform detected={payload['degenerate_uniform_detected']} "
        f"spread={payload['degenerate_uniform_spread']:.6g} "
        f"short_circuit={payload['degenerate_short_circuit']}"
    )
    if "exact_optimal_cost" in payload:
        print(
            f"exact_optimal_cost={payload['exact_optimal_cost']:.6f} "
            f"gap(best/effective)=({payload['gap_best_cost']:.6f},{payload['gap_best_effective']:.6f})"
        )


if __name__ == "__main__":
    main()

