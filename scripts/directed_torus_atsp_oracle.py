#!/usr/bin/env python3
"""
Directed-torus geometric ATSP oracle (arbitrary asymmetric costs).

This prototype is designed for the "arbitrary directed case":
- tours are sampled from a geometric walk on a 2D torus chart;
- costs are exact ATSP closed-cycle costs from an arbitrary matrix;
- ranking uses a matrix-aware potential that can include an
  octonion-inspired non-associative "associator" correction.

Notes
-----
- This is a heuristic oracle, not an exact polynomial-time solver.
- Exact verification is available for small n via brute force.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from dataclasses import asdict, dataclass, replace
from typing import Any

PHI = (1.0 + math.sqrt(5.0)) / 2.0
GOLDEN_ANGLE = 2.0 * math.pi / (PHI**2)


@dataclass
class DirectedTorusCandidate:
    step: int
    seed_idx: int
    u: float
    v: float
    root_distance: float
    permutation_code: int
    tour: list[int]
    tour_cost: float
    assoc_term: float
    tau_term: float
    rough_slope: float
    rough_curvature: float
    rough_jump: float
    effective_score: float
    rapidity_term: float = 0.0
    rapidity_jitter: float = 0.0
    rapidity_shell: int = -1


@dataclass
class ScoreContext:
    dist: list[list[float]]
    n: int
    k: int
    arc_length: float
    perm_space: int
    assoc_weight: float
    tau_mode: str
    tau_weight: float
    mean_edge_cost: float
    asymmetry: float
    geometry: str
    node_skew_norm: list[float]
    node_scale_norm: list[float]
    flow_anchor_u: float
    flow_anchor_v: float
    roughness_mode: str
    roughness_eps: float
    rough_slope_weight: float
    rough_curvature_weight: float
    rough_jump_weight: float


def annulus_anchor_from_pair(dist: list[list[float]], a: int, b: int) -> tuple[float, float]:
    """
    Map a directed city pair (a -> b) to an annulus anchor on [0,1]^2.
    """
    n = len(dist)
    row_vals = [dist[a][j] for j in range(n) if j != a]
    row_min = min(row_vals) if row_vals else 0.0
    row_max = max(row_vals) if row_vals else 1.0
    span = max(1e-12, row_max - row_min)
    w = (dist[a][b] - row_min) / span
    # u picks pair phase; v encodes pair-specific radial annulus offset.
    u0 = ((a + 0.61803398875 * b) / max(1, n)) % 1.0
    v0 = (0.25 + 0.5 * w) % 1.0
    return u0, v0


def morley_seeds() -> list[float]:
    return [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]


def rapidity_delta(scale: int) -> float:
    return math.pi / (4.0 * math.log(scale + 1.0))


def balanced_root_pole_distance(u: float, v: float, k: int) -> float:
    """
    Distance to the balanced k-root pole on the normalized narrow arc chart.
    u,v are normalized to [0,1].
    """
    kk = max(1, k)
    pole_u = 0.5
    pole_v = 0.5 / float(kk)
    du = min(abs(u - pole_u), 1.0 - abs(u - pole_u))
    dv = min(abs(v - pole_v), 1.0 - abs(v - pole_v))
    return math.sqrt(du * du + dv * dv)


def factoradic_to_permutation(code: int, n: int) -> list[int]:
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
        if dist[i][i] != 0:
            raise ValueError("distance matrix diagonal must be zero")
        for j in range(n):
            if dist[i][j] < 0:
                raise ValueError("distance matrix entries must be nonnegative")


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
            directional = (
                0.20 * dx * heading[i][0]
                + 0.20 * dy * heading[i][1]
                + 0.20 * dz * heading[i][2]
            )
            jitter = 0.05 * rng.random()
            dist[i][j] = max(1e-6, eu + directional + jitter + 0.15)
    return dist


def matrix_asymmetry(dist: list[list[float]]) -> float:
    n = len(dist)
    if n == 0:
        return 0.0
    total = 0.0
    for i in range(n):
        for j in range(n):
            total += abs(dist[i][j] - dist[j][i])
    return total / float(n * n)


def dynamic_assoc_weight_from_matrix(dist: list[list[float]]) -> float:
    asym = matrix_asymmetry(dist)
    # First directed-torus law candidate: mild base + asymmetry-scaled correction.
    return 0.25 + 0.5 * asym


def mean_edge_cost(dist: list[list[float]]) -> float:
    n = len(dist)
    if n == 0:
        return 1.0
    total = 0.0
    count = 0
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            total += dist[i][j]
            count += 1
    return total / float(max(1, count))


def rank_correlation_spearman(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or not xs:
        return float("nan")
    n = len(xs)
    x_order = sorted(range(n), key=lambda i: xs[i])
    y_order = sorted(range(n), key=lambda i: ys[i])
    rx = [0] * n
    ry = [0] * n
    for r, i in enumerate(x_order):
        rx[i] = r
    for r, i in enumerate(y_order):
        ry[i] = r
    num = 0.0
    for i in range(n):
        d = rx[i] - ry[i]
        num += d * d
    denom = n * (n * n - 1)
    if denom == 0:
        return 1.0
    return 1.0 - 6.0 * num / denom


def normalize_centered(values: list[float]) -> list[float]:
    if not values:
        return []
    mu = sum(values) / float(len(values))
    centered = [v - mu for v in values]
    mx = max(abs(v) for v in centered)
    if mx <= 1e-12:
        return [0.0 for _ in values]
    return [v / mx for v in centered]


def compute_node_tilts(dist: list[list[float]]) -> tuple[list[float], list[float]]:
    n = len(dist)
    out_avg: list[float] = []
    in_avg: list[float] = []
    for i in range(n):
        out_s = 0.0
        in_s = 0.0
        cnt = 0
        for j in range(n):
            if i == j:
                continue
            out_s += dist[i][j]
            in_s += dist[j][i]
            cnt += 1
        denom = max(1, cnt)
        out_avg.append(out_s / denom)
        in_avg.append(in_s / denom)
    skew = [out_avg[i] - in_avg[i] for i in range(n)]
    scale = [(out_avg[i] + in_avg[i]) / 2.0 for i in range(n)]
    return normalize_centered(skew), normalize_centered(scale)


def permutation_to_factoradic_code(perm: list[int]) -> int:
    elems = list(range(len(perm)))
    code = 0
    for i, p in enumerate(perm):
        idx = elems.index(p)
        code += idx * math.factorial(len(perm) - i - 1)
        elems.pop(idx)
    return code


def kendall_tau_distance(a: list[int], b: list[int]) -> int:
    n = len(a)
    pos = {v: i for i, v in enumerate(b)}
    arr = [pos[v] for v in a]
    inv = 0
    for i in range(n):
        ai = arr[i]
        for j in range(i + 1, n):
            if ai > arr[j]:
                inv += 1
    return inv


def tour_directed_edge_set(tour: list[int]) -> set[tuple[int, int]]:
    n = len(tour)
    out: set[tuple[int, int]] = set()
    if n == 0:
        return out
    for i in range(n):
        out.add((tour[i], tour[(i + 1) % n]))
    return out


def edge_overlap_ratio(a: list[int], b: list[int]) -> float:
    ea = tour_directed_edge_set(a)
    eb = tour_directed_edge_set(b)
    if not ea:
        return 0.0
    return len(ea & eb) / float(len(ea))


def rapidity_dominated_edges(
    dist: list[list[float]],
    rapidity_du: float,
    rapidity_dv: float,
    mean_edge: float,
    scale: float = 2.0,
) -> set[tuple[int, int]]:
    """
    Build a directed-edge inequality ledger from manifold rapidity.

    An edge (x -> y) is flagged as dominated when it is substantially worse than:
      1) x's best outgoing alternative, and
      2) y's best incoming alternative.
    The margin is scaled by rapidity channels and mean edge cost.
    """
    n = len(dist)
    out: set[tuple[int, int]] = set()
    if n <= 1:
        return out
    margin = max(1e-12, scale * (abs(rapidity_du) + abs(rapidity_dv)) * max(1e-9, mean_edge))
    min_out = [min(dist[i][j] for j in range(n) if j != i) for i in range(n)]
    min_in = [min(dist[i][j] for i in range(n) if i != j) for j in range(n)]
    for x in range(n):
        for y in range(n):
            if x == y:
                continue
            out_gap = dist[x][y] - min_out[x]
            in_gap = dist[x][y] - min_in[y]
            if out_gap > margin and in_gap > margin:
                out.add((x, y))
    return out


def resolve_rapidity_prune_scale(
    mode: str,
    base_scale: float,
    n: int,
    arity: int,
    cosh_beta: float = 2.0,
    cosh_strength: float = 0.35,
) -> float:
    """
    Resolve rapidity prune scale from policy mode.

    - fixed: use base_scale directly.
    - sqrt-n: base_scale * sqrt(n).
    - sqrt-n-over-arity: base_scale * sqrt(arity), so peel-side follows
      sqrt(k) and max-arity (k=n) settles at sqrt(n).
    - cosh-arity: catenary-shaped schedule on arity ladder; equals
      base_scale*sqrt(arity) at max arity and smoothly widens toward peel side.
    """
    if mode == "fixed":
        return max(1e-12, base_scale)
    if mode == "sqrt-n":
        return max(1e-12, base_scale * math.sqrt(float(max(1, n))))
    if mode == "sqrt-n-over-arity":
        return max(1e-12, base_scale * math.sqrt(float(max(1, arity))))
    if mode == "cosh-arity":
        nn = max(1, n)
        kk = max(1, min(arity, nn))
        # t=0 at peel side, t=1 at max arity.
        t = 1.0 if nn <= 1 else (float(kk - 1) / float(nn - 1))
        widen = 1.0 + max(0.0, cosh_strength) * (math.cosh(max(0.0, cosh_beta) * (1.0 - t)) - 1.0)
        return max(1e-12, base_scale * math.sqrt(float(kk)) * widen)
    raise ValueError(f"unknown rapidity prune scale mode: {mode}")


def min_subpath_rapidity(
    tour: list[int],
    dist: list[list[float]],
    window: int = 4,
) -> float:
    """
    Minimum cyclic subpath rapidity over fixed-size windows.

    Lower values correspond to traversing less weighted space over a local
    geometric segment; used as anneal-time bookkeeping/ranking signal.
    """
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
        avg = s / float(w)
        if avg < best:
            best = avg
    return best if math.isfinite(best) else 0.0


def subpath_rapidity_jitter(
    tour: list[int],
    dist: list[list[float]],
    window: int = 4,
) -> float:
    """
    Local rapidity roughness: stddev of cyclic window-average traversal costs.
    Smaller values indicate smoother geometric progression across the tour.
    """
    n = len(tour)
    if n == 0:
        return 0.0
    w = max(1, min(window, n))
    edges = [dist[tour[i]][tour[(i + 1) % n]] for i in range(n)]
    vals: list[float] = []
    for i in range(n):
        s = 0.0
        for j in range(w):
            s += edges[(i + j) % n]
        vals.append(s / float(w))
    mu = sum(vals) / float(len(vals))
    var = sum((x - mu) ** 2 for x in vals) / float(len(vals))
    return math.sqrt(max(0.0, var))


def rapidity_shell_id(rapidity_value: float, shell_width: float) -> int:
    w = max(1e-12, shell_width)
    return int(math.floor(max(0.0, rapidity_value) / w))


def keep_top_per_rapidity_shell(
    cs: list[DirectedTorusCandidate],
    keep_per_shell: int,
) -> list[DirectedTorusCandidate]:
    if keep_per_shell <= 0:
        return cs
    buckets: dict[int, list[DirectedTorusCandidate]] = {}
    for c in cs:
        buckets.setdefault(c.rapidity_shell, []).append(c)
    kept: list[DirectedTorusCandidate] = []
    for shell in sorted(buckets.keys()):
        grp = sorted(buckets[shell], key=lambda x: (x.effective_score, x.tour_cost))
        kept.extend(grp[:keep_per_shell])
    return sorted(kept, key=lambda x: (x.effective_score, x.tour_cost))


def global_lower_bound_atsp(dist: list[list[float]]) -> float:
    """
    Orthogonal edge-space lower bound (assignment-style surrogate):
    max(sum row minima, sum column minima).
    """
    n = len(dist)
    out_lb = sum(min(dist[i][j] for j in range(n) if j != i) for i in range(n))
    in_lb = sum(min(dist[i][j] for i in range(n) if i != j) for j in range(n))
    return max(out_lb, in_lb)


def rapidity_alpha_from_scale(
    scale_effective: float,
    n: int,
    alpha_floor: float = 0.25,
) -> float:
    """
    Convert rapidity scale to [alpha_floor, 1] interpolation for LB/UB boundary.
    """
    denom = max(1e-9, math.sqrt(float(max(1, n))))
    raw = scale_effective / denom
    return min(1.0, max(alpha_floor, raw))


def orthogonal_soft_boundary(lb: float, ub: float, alpha: float) -> float:
    a = min(1.0, max(0.0, alpha))
    return lb + a * max(0.0, ub - lb)


def dedupe_by_code_keep_best(cs: list[DirectedTorusCandidate]) -> list[DirectedTorusCandidate]:
    by_code: dict[int, DirectedTorusCandidate] = {}
    for c in sorted(cs, key=lambda x: (x.effective_score, x.tour_cost)):
        prev = by_code.get(c.permutation_code)
        if prev is None or c.effective_score < prev.effective_score:
            by_code[c.permutation_code] = c
    return sorted(by_code.values(), key=lambda x: (x.effective_score, x.tour_cost))


def candidate_uses_dominated_edge(tour: list[int], dominated: set[tuple[int, int]]) -> bool:
    if not dominated:
        return False
    n = len(tour)
    if n == 0:
        return False
    for i in range(n):
        if (tour[i], tour[(i + 1) % n]) in dominated:
            return True
    return False


def is_binary_one_two_matrix(dist: list[list[float]], tol: float = 1e-9) -> bool:
    n = len(dist)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            v = dist[i][j]
            if abs(v - 1.0) <= tol or abs(v - 2.0) <= tol:
                continue
            return False
    return True


def has_unit_cycle_witness(cands: list[DirectedTorusCandidate], n: int, tol: float = 1e-9) -> bool:
    target = float(n)
    return any(abs(c.tour_cost - target) <= tol for c in cands)


def toroidal_distance(a: float, b: float) -> float:
    return min(abs(a - b), 1.0 - abs(a - b))


def flow_anchor_distance(u: float, v: float, anchor_u: float, anchor_v: float) -> float:
    du = toroidal_distance(u, anchor_u)
    dv = toroidal_distance(v, anchor_v)
    return math.sqrt(du * du + dv * dv)


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


def edge_as_vector(i: int, j: int, dist: list[list[float]], n: int) -> tuple[float, float, float]:
    """
    Matrix-induced directed edge embedding in R3.
    This gives an order-sensitive surrogate geometry for the associator term.
    """
    f = float(n)
    x = (j - i) / f
    y = (dist[i][j] - dist[j][i]) / (1.0 + dist[i][j] + dist[j][i])
    z = (dist[i][j] + 1e-9) / (1.0 + max(dist[i]))
    return (x, y, z)


def scalar_triple(a: tuple[float, float, float], b: tuple[float, float, float], c: tuple[float, float, float]) -> float:
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


def octonion_associator_like(tour: list[int], dist: list[list[float]]) -> float:
    """
    Order-sensitive correction inspired by non-associative behavior:
    aggregate scalar triple products across consecutive directed edges.
    """
    n = len(tour)
    if n < 3:
        return 0.0
    acc = 0.0
    for i in range(n):
        a = tour[i]
        b = tour[(i + 1) % n]
        c = tour[(i + 2) % n]
        d = tour[(i + 3) % n]
        e1 = edge_as_vector(a, b, dist, n)
        e2 = edge_as_vector(b, c, dist, n)
        e3 = edge_as_vector(c, d, dist, n)
        acc += scalar_triple(e1, e2, e3)
    return acc / float(n)


def inversion_count(tour: list[int]) -> int:
    inv = 0
    n = len(tour)
    for i in range(n):
        for j in range(i + 1, n):
            if tour[i] > tour[j]:
                inv += 1
    return inv


def tau_cycle_term(tour: list[int], dist: list[list[float]]) -> float:
    """Directed-cycle skew magnitude (matrix asymmetry along chosen cycle)."""
    n = len(tour)
    if n == 0:
        return 0.0
    total = 0.0
    for i in range(n):
        a = tour[i]
        b = tour[(i + 1) % n]
        total += abs(dist[a][b] - dist[b][a])
    return total / float(n)


def tau_mod_term(tour: list[int]) -> float:
    """Permutation-shape modularity proxy via normalized inversion density."""
    n = len(tour)
    if n < 2:
        return 0.0
    inv = inversion_count(tour)
    max_inv = n * (n - 1) / 2.0
    return inv / max_inv


def tau_assoc_term(tour: list[int], dist: list[list[float]]) -> float:
    """Tau from non-associative channel: absolute associator amplitude."""
    return abs(octonion_associator_like(tour, dist))


def compute_tau_term(tau_mode: str, tour: list[int], dist: list[list[float]], assoc_term: float) -> float:
    if tau_mode == "off":
        return 0.0
    if tau_mode == "cycle":
        return tau_cycle_term(tour, dist)
    if tau_mode == "mod":
        return tau_mod_term(tour)
    if tau_mode == "assoc":
        return abs(assoc_term)
    raise ValueError(f"unknown tau_mode: {tau_mode}")


def decode_t_to_uv(t: float, arc_length: float) -> tuple[float, float]:
    """
    Intrinsic narrow-arc chart coordinate from arc parameter t.
    Uses a golden-angle scaled phase lift for v.
    """
    if arc_length <= 0:
        return 0.0, 0.0
    t_wrapped = t % arc_length
    u = t_wrapped / arc_length
    golden_phase = ((GOLDEN_ANGLE / (2.0 * math.pi)) % 1.0)
    v = (u / PHI + golden_phase) % 1.0
    return u, v


def candidate_from_t(t: float, ctx: ScoreContext, step: int = 0, seed_idx: int = 0) -> DirectedTorusCandidate:
    u, v = decode_t_to_uv(t, ctx.arc_length)
    if ctx.geometry == "oblique":
        scores: list[tuple[float, int]] = []
        phase_base = (u + 0.61803398875 * v) % 1.0
        global_twist = min(1.0, max(0.0, ctx.asymmetry))
        for i in range(ctx.n):
            skew_i = ctx.node_skew_norm[i]
            scale_i = ctx.node_scale_norm[i]
            # Each city axis is tipped by directed skew/scale from the matrix.
            local_phase = (phase_base + i / max(1, ctx.n) + 0.25 * skew_i) % 1.0
            theta = 2.0 * math.pi * local_phase
            score = (
                math.cos(theta)
                + 0.40 * skew_i
                + 0.25 * scale_i
                + 0.35 * global_twist * math.sin(theta)
            )
            scores.append((score, i))
        scores.sort(key=lambda x: x[0])
        tour = [i for _, i in scores]
        code = permutation_to_factoradic_code(tour)
        root_distance = flow_anchor_distance(u, v, ctx.flow_anchor_u, ctx.flow_anchor_v)
    else:
        root_distance = balanced_root_pole_distance(u, v, ctx.k)
        mix = (0.62 * u + 0.38 * v) % 1.0
        code = min(ctx.perm_space - 1, max(0, int(round(mix * (ctx.perm_space - 1)))))
        tour = factoradic_to_permutation(code, ctx.n)
    cost = closed_tour_cost(ctx.dist, tour)
    assoc_term = octonion_associator_like(tour, ctx.dist)
    tau_term = compute_tau_term(ctx.tau_mode, tour, ctx.dist, assoc_term)

    # Base score (roughness added in dedicated pass).
    cost_norm = cost / (ctx.n * max(1e-9, ctx.mean_edge_cost))
    assoc_norm = assoc_term / (1.0 + abs(assoc_term))
    tau_norm = tau_term / (1.0 + abs(tau_term))
    effective = root_distance + cost_norm + ctx.assoc_weight * assoc_norm + ctx.tau_weight * tau_norm

    return DirectedTorusCandidate(
        step=step,
        seed_idx=seed_idx,
        u=u,
        v=v,
        root_distance=root_distance,
        permutation_code=code,
        tour=tour,
        tour_cost=cost,
        assoc_term=assoc_term,
        tau_term=tau_term,
        rough_slope=0.0,
        rough_curvature=0.0,
        rough_jump=0.0,
        effective_score=effective,
    )


def tour_has_directed_edge(tour: list[int], a: int, b: int) -> bool:
    n = len(tour)
    if n == 0:
        return False
    for i in range(n):
        if tour[i] == a and tour[(i + 1) % n] == b:
            return True
    return False


def enrich_candidate_with_roughness(c: DirectedTorusCandidate, t: float, ctx: ScoreContext, step: int) -> DirectedTorusCandidate:
    if ctx.roughness_mode == "off":
        return c
    eps = max(1e-12, ctx.roughness_eps)
    tp = (t + eps) % max(1e-12, ctx.arc_length)
    tm = (t - eps) % max(1e-12, ctx.arc_length)
    cp = candidate_from_t(tp, ctx, step=step, seed_idx=3)
    cm = candidate_from_t(tm, ctx, step=step, seed_idx=4)
    slope = abs(cp.tour_cost - cm.tour_cost) / (2.0 * eps)
    curvature = abs(cp.tour_cost - 2.0 * c.tour_cost + cm.tour_cost) / (eps * eps)
    max_inv = max(1, ctx.n * (ctx.n - 1) // 2)
    jump = kendall_tau_distance(cp.tour, cm.tour) / float(max_inv)
    slope_norm = slope / (1.0 + slope)
    curvature_norm = curvature / (1.0 + curvature)
    c.rough_slope = slope
    c.rough_curvature = curvature
    c.rough_jump = jump
    c.effective_score = (
        c.effective_score
        + ctx.rough_slope_weight * slope_norm
        + ctx.rough_curvature_weight * curvature_norm
        + ctx.rough_jump_weight * jump
    )
    return c


def minimize_on_narrow_arc(ctx: ScoreContext, iters: int = 40) -> tuple[DirectedTorusCandidate, list[DirectedTorusCandidate]]:
    a, b = 0.0, ctx.arc_length
    evals: list[DirectedTorusCandidate] = []
    for i in range(max(1, iters)):
        c = b - (b - a) / PHI
        d = a + (b - a) / PHI
        cc = enrich_candidate_with_roughness(candidate_from_t(c, ctx, step=i, seed_idx=0), c, ctx, i)
        dd = enrich_candidate_with_roughness(candidate_from_t(d, ctx, step=i, seed_idx=1), d, ctx, i)
        evals.extend([cc, dd])
        if cc.effective_score < dd.effective_score:
            b = d
        else:
            a = c
    t_star = (a + b) / 2.0
    best = enrich_candidate_with_roughness(
        candidate_from_t(t_star, ctx, step=max(1, iters), seed_idx=2),
        t_star,
        ctx,
        max(1, iters),
    )
    evals.append(best)
    return best, evals


def sample_anchored_arc_family(
    ctx: ScoreContext,
    anchor_city: int,
    anchor_next: int,
    arc_samples: int,
    annulus_radius: float = 0.125,
) -> list[DirectedTorusCandidate]:
    u0, v0 = annulus_anchor_from_pair(ctx.dist, anchor_city, anchor_next)
    out: list[DirectedTorusCandidate] = []
    seeds = morley_seeds()
    steps = max(2, arc_samples)
    for i in range(steps):
        t = (i / (steps - 1)) * ctx.arc_length
        for seed_idx, seed in enumerate(seeds):
            theta = 2.0 * math.pi * (t / max(1e-12, ctx.arc_length)) + seed
            frac_u = (u0 + annulus_radius * math.cos(theta)) % 1.0
            frac_v = (v0 + annulus_radius * math.sin(theta)) % 1.0
            t_local = (frac_u * ctx.arc_length) % max(1e-12, ctx.arc_length)
            cand = enrich_candidate_with_roughness(
                candidate_from_t(t_local, ctx, step=i, seed_idx=seed_idx),
                t_local,
                ctx,
                i,
            )
            if tour_has_directed_edge(cand.tour, anchor_city, anchor_next):
                out.append(cand)
    # Deduplicate by permutation code keeping best score.
    best_by_code: dict[int, DirectedTorusCandidate] = {}
    for c in out:
        prev = best_by_code.get(c.permutation_code)
        if prev is None or c.effective_score < prev.effective_score:
            best_by_code[c.permutation_code] = c
    return list(best_by_code.values())


def intersect_anchor_families(
    fam1: list[DirectedTorusCandidate],
    fam2: list[DirectedTorusCandidate],
    n: int,
    kendall_max_norm: float,
    mismatch_weight: float,
    top_k: int,
) -> list[DirectedTorusCandidate]:
    if not fam1 or not fam2:
        return []
    max_inv = max(1, n * (n - 1) // 2)
    joined: list[DirectedTorusCandidate] = []
    for c1 in fam1:
        best_match: tuple[float, DirectedTorusCandidate] | None = None
        for c2 in fam2:
            d = kendall_tau_distance(c1.tour, c2.tour) / float(max_inv)
            if d > kendall_max_norm:
                continue
            if best_match is None or d < best_match[0]:
                best_match = (d, c2)
        if best_match is None:
            continue
        dnorm, c2 = best_match
        rep = c1 if c1.effective_score <= c2.effective_score else c2
        score = (
            0.5 * (c1.effective_score + c2.effective_score)
            + mismatch_weight * dnorm
            + 0.5 * abs(c1.effective_score - c2.effective_score)
        )
        joined.append(replace(rep, effective_score=score))
    joined.sort(key=lambda c: c.effective_score)
    by_code: dict[int, DirectedTorusCandidate] = {}
    for c in joined:
        prev = by_code.get(c.permutation_code)
        if prev is None or c.effective_score < prev.effective_score:
            by_code[c.permutation_code] = c
    return sorted(by_code.values(), key=lambda c: c.effective_score)[: max(1, top_k)]


def directed_torus_atsp_solver(
    dist: list[list[float]],
    max_steps: int = 3000,
    top_k: int = 7,
    assoc_weight: float | None = None,
    tau_mode: str = "off",
    tau_weight: float = 0.0,
    k_arity: int | None = None,
    first_sat_stop: bool = True,
    optimizer: str = "golden-section",
    golden_iters: int = 40,
    geometry: str = "oblique",
    roughness_mode: str = "off",
    roughness_eps: float = 0.0,
    rough_slope_weight: float = 0.20,
    rough_curvature_weight: float = 0.10,
    rough_jump_weight: float = 0.25,
    arc_scale: float = 1.0,
    anchor_city: int = 0,
    anchor_next: int | None = None,
    anchor_bruteforce: bool = True,
    intercept_grid: int = 24,
    intercept_kendall_max: float = 0.15,
    intercept_topk: int = 64,
    intercept_mismatch_weight: float = 0.20,
    recursive_depth: int = 2,
    recursive_beam: int = 4,
    hybrid_anchor_refine: bool = False,
    hybrid_refine_budget: int = 6,
    hybrid_refine_samples: int = 16,
    hybrid_rerank_top_m: int = 16,
    hybrid_blend_effective: float = 0.35,
    hybrid_blend_cost: float = 0.65,
    reverse_rounds: int = 0,
    reverse_overlap_keep: float = 0.55,
    rapidity_prune: bool = True,
    rapidity_prune_scale: float = 2.0,
    rapidity_prune_scale_mode: str = "fixed",
    rapidity_prune_cosh_beta: float = 2.0,
    rapidity_prune_cosh_strength: float = 0.35,
    iterative_rounds: int = 1,
    iterative_arity_start: int = 2,
    iterative_stage_topk: int = 24,
    iterative_early_stop_patience: int = 1,
    iterative_early_stop_tol: float = 1e-9,
    anneal_rapidity_barrier: bool = True,
    anneal_barrier_strength: float = 1.0,
    anneal_rapidity_window: int = 4,
    anneal_rapidity_weight: float = 0.25,
    anneal_rapidity_jitter_weight: float = 0.10,
    anneal_shell_width: float = 0.25,
    anneal_shell_keep_per_band: int = 0,
    orthogonal_prune_boundary: bool = True,
    orthogonal_alpha_floor: float = 0.25,
    binary_prune_boundary: bool = True,
    binary_prune_exact_if_at_most: int = 10,
) -> dict[str, Any]:
    validate_distance_matrix(dist)
    n = len(dist)
    k = k_arity if k_arity is not None else n
    k = max(1, k)
    arc_length = (math.pi / (2.0 * float(k))) * arc_scale
    seeds = morley_seeds()
    perm_space = math.factorial(n)
    du = rapidity_delta(n * n)
    dv = rapidity_delta(n * n * 2)
    assoc_weight_effective = dynamic_assoc_weight_from_matrix(dist) if assoc_weight is None else assoc_weight
    asymmetry = matrix_asymmetry(dist)
    edge_mean = mean_edge_cost(dist)
    node_skew_norm, node_scale_norm = compute_node_tilts(dist)
    mean_skew = sum(node_skew_norm) / float(max(1, len(node_skew_norm)))
    flow_anchor_u = (0.5 + 0.20 * math.tanh(mean_skew)) % 1.0
    flow_anchor_v = (0.5 + 0.30 * math.tanh(asymmetry)) % 1.0
    eps = roughness_eps if roughness_eps > 0 else (arc_length / 64.0)
    ctx = ScoreContext(
        dist=dist,
        n=n,
        k=k,
        arc_length=arc_length,
        perm_space=perm_space,
        assoc_weight=assoc_weight_effective,
        tau_mode=tau_mode,
        tau_weight=tau_weight,
        mean_edge_cost=edge_mean,
        asymmetry=asymmetry,
        geometry=geometry,
        node_skew_norm=node_skew_norm,
        node_scale_norm=node_scale_norm,
        flow_anchor_u=flow_anchor_u,
        flow_anchor_v=flow_anchor_v,
        roughness_mode=roughness_mode,
        roughness_eps=eps,
        rough_slope_weight=rough_slope_weight,
        rough_curvature_weight=rough_curvature_weight,
        rough_jump_weight=rough_jump_weight,
    )

    u = 0.0
    v = 0.0
    seen_codes: set[int] = set()
    candidates: list[DirectedTorusCandidate] = []

    raw_costs: list[float] = []
    raw_assoc: list[float] = []
    raw_tau: list[float] = []
    first_sat_triggered = False
    first_sat_step: int | None = None
    intercept_pairs_tested = 0
    intercept_hits = 0
    recursive_levels_visited = 0
    recursive_poles_expanded = 0
    hybrid_pairs_used: list[tuple[int, int]] = []
    reverse_rounds_used = 0
    reverse_bad_mass_history: list[tuple[float, float]] = []
    rapidity_dominated_edge_count = 0
    rapidity_pruned_candidates = 0
    rapidity_prune_scale_effective = resolve_rapidity_prune_scale(
        mode=rapidity_prune_scale_mode,
        base_scale=rapidity_prune_scale,
        n=n,
        arity=k,
        cosh_beta=rapidity_prune_cosh_beta,
        cosh_strength=rapidity_prune_cosh_strength,
    )
    iterative_trace: list[dict[str, Any]] = []
    iterative_barrier_trace: list[dict[str, Any]] = []
    iterative_rounds_executed = 0
    iterative_early_stopped = False
    orthogonal_lb = global_lower_bound_atsp(dist)
    orthogonal_boundary_trace: list[dict[str, Any]] = []
    orthogonal_pruned_candidates = 0
    binary_prune_boundary_active = False
    binary_pruned_candidates = 0
    binary_unit_cycle_witness_found = False
    binary_exact_check_used = False

    if optimizer == "golden-section":
        best_gs, gs_evals = minimize_on_narrow_arc(ctx, iters=golden_iters)
        candidates.extend(gs_evals)
        seen_codes.update(c.permutation_code for c in gs_evals)
        raw_costs.extend(c.tour_cost for c in gs_evals)
        raw_assoc.extend(c.assoc_term for c in gs_evals)
        raw_tau.extend(c.tau_term for c in gs_evals)
        if first_sat_stop:
            for c in gs_evals:
                if abs(c.assoc_term) > 1e-12:
                    first_sat_triggered = True
                    first_sat_step = c.step
                    break
    elif optimizer == "spiral":
        for step in range(max_steps):
            drift = step * GOLDEN_ANGLE
            for seed_idx, seed in enumerate(seeds):
                # Narrow-arc k-arity clipping from the root chart.
                uu = (u + seed + drift) % arc_length
                vv = (v + seed * 0.5 + drift / PHI) % arc_length
                frac_u = uu / arc_length if arc_length > 0 else 0.0
                frac_v = vv / arc_length if arc_length > 0 else 0.0
                root_distance = balanced_root_pole_distance(frac_u, frac_v, k)
                mix = (0.62 * frac_u + 0.38 * frac_v) % 1.0
                code = min(perm_space - 1, max(0, int(round(mix * (perm_space - 1)))))
                if code in seen_codes:
                    continue
                seen_codes.add(code)
                tour = factoradic_to_permutation(code, n)
                cost = closed_tour_cost(dist, tour)
                assoc_term = octonion_associator_like(tour, dist)
                cand = DirectedTorusCandidate(
                    step=step,
                    seed_idx=seed_idx,
                    u=frac_u,
                    v=frac_v,
                    root_distance=root_distance,
                    permutation_code=code,
                    tour=tour,
                    tour_cost=cost,
                    assoc_term=assoc_term,
                    tau_term=compute_tau_term(tau_mode, tour, dist, assoc_term),
                    rough_slope=0.0,
                    rough_curvature=0.0,
                    rough_jump=0.0,
                    effective_score=0.0,
                )
                t_local = (frac_u * arc_length) % max(1e-12, arc_length)
                cand = enrich_candidate_with_roughness(cand, t_local, ctx, step)
                raw_costs.append(cand.tour_cost)
                raw_assoc.append(cand.assoc_term)
                raw_tau.append(cand.tau_term)
                candidates.append(cand)
                if first_sat_stop and abs(assoc_term) > 1e-12:
                    first_sat_triggered = True
                    first_sat_step = step
                    break
            if first_sat_triggered:
                break
            u += du
            v += dv
            if len(seen_codes) >= perm_space:
                break
    elif optimizer == "anchored-spiral":
        if not (0 <= anchor_city < n):
            raise ValueError("anchor_city must be within [0, n)")
        anchor_choices = [anchor_next] if anchor_next is not None else [j for j in range(n) if j != anchor_city]
        if anchor_next is None and not anchor_bruteforce:
            # Deterministic fallback: smallest outgoing edge.
            best_j = min((j for j in range(n) if j != anchor_city), key=lambda j: dist[anchor_city][j])
            anchor_choices = [best_j]
        best_anchor_block: list[DirectedTorusCandidate] = []
        best_anchor_score = math.inf
        for candidate_next in anchor_choices:
            if candidate_next is None:
                continue
            if candidate_next == anchor_city or not (0 <= candidate_next < n):
                continue
            u0, v0 = annulus_anchor_from_pair(dist, anchor_city, candidate_next)
            local_seen: set[int] = set()
            local_candidates: list[DirectedTorusCandidate] = []
            local_u = u0
            local_v = v0
            annulus_radius = 0.125
            for step in range(max_steps):
                drift = step * GOLDEN_ANGLE
                for seed_idx, seed in enumerate(morley_seeds()):
                    # Spiral around annulus anchor point.
                    theta = (seed + drift) % (2.0 * math.pi)
                    frac_u = (local_u + annulus_radius * math.cos(theta)) % 1.0
                    frac_v = (local_v + annulus_radius * math.sin(theta)) % 1.0
                    t_local = (frac_u * arc_length) % max(1e-12, arc_length)
                    cand = enrich_candidate_with_roughness(
                        candidate_from_t(t_local, ctx, step=step, seed_idx=seed_idx),
                        t_local,
                        ctx,
                        step,
                    )
                    if cand.permutation_code in local_seen:
                        continue
                    local_seen.add(cand.permutation_code)
                    if not tour_has_directed_edge(cand.tour, anchor_city, candidate_next):
                        continue
                    local_candidates.append(cand)
                    if first_sat_stop and abs(cand.assoc_term) > 1e-12:
                        first_sat_triggered = True
                        first_sat_step = step
                        break
                if first_sat_triggered:
                    break
                local_u = (local_u + du) % 1.0
                local_v = (local_v + dv) % 1.0
                if len(local_seen) >= perm_space:
                    break
            if local_candidates:
                local_best = min(local_candidates, key=lambda c: c.effective_score)
                if local_best.effective_score < best_anchor_score:
                    best_anchor_score = local_best.effective_score
                    best_anchor_block = local_candidates
        candidates.extend(best_anchor_block)
        seen_codes.update(c.permutation_code for c in best_anchor_block)
        raw_costs.extend(c.tour_cost for c in best_anchor_block)
        raw_assoc.extend(c.assoc_term for c in best_anchor_block)
        raw_tau.extend(c.tau_term for c in best_anchor_block)
    elif optimizer == "anchored-intercept":
        if not (0 <= anchor_city < n):
            raise ValueError("anchor_city must be within [0, n)")
        anchor_choices = [anchor_next] if anchor_next is not None else [j for j in range(n) if j != anchor_city]
        if anchor_next is None and not anchor_bruteforce:
            best_j = min((j for j in range(n) if j != anchor_city), key=lambda j: dist[anchor_city][j])
            anchor_choices = [best_j]
        families: dict[int, list[DirectedTorusCandidate]] = {}
        for b in anchor_choices:
            if b is None or b == anchor_city or not (0 <= b < n):
                continue
            fam = sample_anchored_arc_family(ctx, anchor_city, b, arc_samples=intercept_grid)
            if fam:
                families[b] = fam
        arc_keys = sorted(families.keys())
        intercept_candidates: list[DirectedTorusCandidate] = []
        for i in range(len(arc_keys)):
            for j in range(i + 1, len(arc_keys)):
                b1 = arc_keys[i]
                b2 = arc_keys[j]
                intercept_pairs_tested += 1
                inter = intersect_anchor_families(
                    families[b1],
                    families[b2],
                    n=n,
                    kendall_max_norm=intercept_kendall_max,
                    mismatch_weight=intercept_mismatch_weight,
                    top_k=max(1, intercept_topk // max(1, len(arc_keys))),
                )
                intercept_hits += len(inter)
                intercept_candidates.extend(inter)
        if not intercept_candidates:
            # Fallback: union of all families if no coincidence survived threshold.
            for fam in families.values():
                intercept_candidates.extend(fam)
        intercept_candidates.sort(key=lambda c: c.effective_score)
        by_code: dict[int, DirectedTorusCandidate] = {}
        for c in intercept_candidates:
            prev = by_code.get(c.permutation_code)
            if prev is None or c.effective_score < prev.effective_score:
                by_code[c.permutation_code] = c
        selected = sorted(by_code.values(), key=lambda c: c.effective_score)[: max(1, intercept_topk)]
        candidates.extend(selected)
        seen_codes.update(c.permutation_code for c in selected)
        raw_costs.extend(c.tour_cost for c in selected)
        raw_assoc.extend(c.assoc_term for c in selected)
        raw_tau.extend(c.tau_term for c in selected)
    elif optimizer == "recursive-intercept":
        if not (0 <= anchor_city < n):
            raise ValueError("anchor_city must be within [0, n)")

        def intercept_for_anchor(city: int) -> list[DirectedTorusCandidate]:
            nonlocal intercept_pairs_tested, intercept_hits
            choices = [j for j in range(n) if j != city]
            families: dict[int, list[DirectedTorusCandidate]] = {}
            for b in choices:
                fam = sample_anchored_arc_family(ctx, city, b, arc_samples=intercept_grid)
                if fam:
                    families[b] = fam
            keys = sorted(families.keys())
            pool: list[DirectedTorusCandidate] = []
            for i in range(len(keys)):
                for j in range(i + 1, len(keys)):
                    b1 = keys[i]
                    b2 = keys[j]
                    intercept_pairs_tested += 1
                    inter = intersect_anchor_families(
                        families[b1],
                        families[b2],
                        n=n,
                        kendall_max_norm=intercept_kendall_max,
                        mismatch_weight=intercept_mismatch_weight,
                        top_k=max(1, intercept_topk // max(1, len(keys))),
                    )
                    intercept_hits += len(inter)
                    pool.extend(inter)
            if not pool:
                for fam in families.values():
                    pool.extend(fam)
            by_code: dict[int, DirectedTorusCandidate] = {}
            for c in sorted(pool, key=lambda c: c.effective_score):
                prev = by_code.get(c.permutation_code)
                if prev is None or c.effective_score < prev.effective_score:
                    by_code[c.permutation_code] = c
            return sorted(by_code.values(), key=lambda c: c.effective_score)[: max(1, intercept_topk)]

        poles = [anchor_city]
        global_pool: list[DirectedTorusCandidate] = []
        for _level in range(max(1, recursive_depth)):
            recursive_levels_visited += 1
            next_pool: list[DirectedTorusCandidate] = []
            for city in poles:
                recursive_poles_expanded += 1
                next_pool.extend(intercept_for_anchor(city))
            if not next_pool:
                break
            # keep best candidates globally so far
            combined = global_pool + next_pool
            by_code: dict[int, DirectedTorusCandidate] = {}
            for c in sorted(combined, key=lambda c: c.effective_score):
                prev = by_code.get(c.permutation_code)
                if prev is None or c.effective_score < prev.effective_score:
                    by_code[c.permutation_code] = c
            global_pool = sorted(by_code.values(), key=lambda c: c.effective_score)[: max(1, intercept_topk)]

            # promote next poles from best tours (city at positions 0/1 captures local tip)
            promoted: list[int] = []
            for c in global_pool[: max(1, recursive_beam)]:
                if c.tour:
                    promoted.append(c.tour[0] % n)
                    promoted.append(c.tour[1 % len(c.tour)] % n)
            # dedupe while keeping order
            seenp: set[int] = set()
            poles = []
            for p in promoted:
                if p not in seenp:
                    seenp.add(p)
                    poles.append(p)
            if not poles:
                break

        selected = global_pool[: max(1, intercept_topk)]

        if hybrid_anchor_refine and selected:
            # Extract high-signal directed pairs from top recursive candidates.
            pair_score: dict[tuple[int, int], float] = {}
            for rank, c in enumerate(sorted(selected, key=lambda x: x.effective_score)[: max(1, hybrid_rerank_top_m)]):
                w = 1.0 / float(1 + rank)
                t = c.tour
                for i in range(len(t)):
                    a = t[i]
                    b = t[(i + 1) % len(t)]
                    pair_score[(a, b)] = pair_score.get((a, b), 0.0) + w
            ranked_pairs = sorted(pair_score.items(), key=lambda kv: kv[1], reverse=True)
            chosen_pairs = [p for p, _ in ranked_pairs[: max(1, hybrid_refine_budget)]]
            hybrid_pairs_used = chosen_pairs
            refine_pool: list[DirectedTorusCandidate] = []
            for a, b in chosen_pairs:
                refine_pool.extend(
                    sample_anchored_arc_family(
                        ctx,
                        anchor_city=a,
                        anchor_next=b,
                        arc_samples=max(4, hybrid_refine_samples),
                    )
                )
            merged = selected + refine_pool
            by_code_h: dict[int, DirectedTorusCandidate] = {}
            for c in sorted(merged, key=lambda x: x.effective_score):
                prev = by_code_h.get(c.permutation_code)
                if prev is None or c.effective_score < prev.effective_score:
                    by_code_h[c.permutation_code] = c
            selected = sorted(by_code_h.values(), key=lambda c: c.effective_score)[: max(1, intercept_topk)]

            # Final compact rerank: blend geometric score with true cost on top-M.
            m = min(max(1, hybrid_rerank_top_m), len(selected))
            top = sorted(selected, key=lambda c: c.effective_score)[:m]
            rest = sorted(selected, key=lambda c: c.effective_score)[m:]
            cost_unit = n * max(1e-9, edge_mean)
            w_eff = max(0.0, hybrid_blend_effective)
            w_cost = max(0.0, hybrid_blend_cost)
            w_sum = max(1e-12, w_eff + w_cost)
            w_eff /= w_sum
            w_cost /= w_sum
            reranked_top = []
            for c in top:
                blended = w_eff * c.effective_score + w_cost * (c.tour_cost / cost_unit)
                reranked_top.append(replace(c, effective_score=blended))
            selected = sorted(reranked_top + rest, key=lambda c: c.effective_score)

        candidates.extend(selected)
        seen_codes.update(c.permutation_code for c in selected)
        raw_costs.extend(c.tour_cost for c in selected)
        raw_assoc.extend(c.assoc_term for c in selected)
        raw_tau.extend(c.tau_term for c in selected)
    elif optimizer == "iterative-peel-anneal":
        start_arity = max(1, min(n, iterative_arity_start))
        rounds = max(1, iterative_rounds)
        stage_topk = max(1, iterative_stage_topk)
        patience = max(1, iterative_early_stop_patience)
        tol = max(0.0, iterative_early_stop_tol)
        pool: list[DirectedTorusCandidate] = []
        best_cost_so_far = math.inf
        no_improve_rounds = 0
        for ridx in range(rounds):
            iterative_rounds_executed += 1
            round_stage: list[DirectedTorusCandidate] = []
            round_stage_stats: list[tuple[int, float, float]] = []
            for kk in range(start_arity, n + 1):
                sub = directed_torus_atsp_solver(
                    dist=dist,
                    max_steps=max_steps,
                    top_k=max(top_k, stage_topk),
                    assoc_weight=assoc_weight,
                    tau_mode=tau_mode,
                    tau_weight=tau_weight,
                    k_arity=kk,
                    first_sat_stop=False,
                    optimizer="reverse-flip-prune",
                    golden_iters=golden_iters,
                    geometry=geometry,
                    roughness_mode=roughness_mode,
                    roughness_eps=roughness_eps,
                    rough_slope_weight=rough_slope_weight,
                    rough_curvature_weight=rough_curvature_weight,
                    rough_jump_weight=rough_jump_weight,
                    arc_scale=arc_scale,
                    anchor_city=anchor_city,
                    anchor_next=anchor_next,
                    anchor_bruteforce=anchor_bruteforce,
                    intercept_grid=intercept_grid,
                    intercept_kendall_max=intercept_kendall_max,
                    intercept_topk=max(intercept_topk, stage_topk),
                    intercept_mismatch_weight=intercept_mismatch_weight,
                    recursive_depth=recursive_depth,
                    recursive_beam=recursive_beam,
                    hybrid_anchor_refine=hybrid_anchor_refine,
                    hybrid_refine_budget=hybrid_refine_budget,
                    hybrid_refine_samples=hybrid_refine_samples,
                    hybrid_rerank_top_m=hybrid_rerank_top_m,
                    hybrid_blend_effective=hybrid_blend_effective,
                    hybrid_blend_cost=hybrid_blend_cost,
                    reverse_rounds=reverse_rounds,
                    reverse_overlap_keep=reverse_overlap_keep,
                    rapidity_prune=rapidity_prune,
                    rapidity_prune_scale=rapidity_prune_scale,
                    rapidity_prune_scale_mode=rapidity_prune_scale_mode,
                    rapidity_prune_cosh_beta=rapidity_prune_cosh_beta,
                    rapidity_prune_cosh_strength=rapidity_prune_cosh_strength,
                    iterative_rounds=1,
                    iterative_arity_start=iterative_arity_start,
                    iterative_stage_topk=iterative_stage_topk,
                    iterative_early_stop_patience=iterative_early_stop_patience,
                    iterative_early_stop_tol=iterative_early_stop_tol,
                    anneal_rapidity_barrier=anneal_rapidity_barrier,
                    anneal_barrier_strength=anneal_barrier_strength,
                    anneal_rapidity_window=anneal_rapidity_window,
                    anneal_rapidity_weight=anneal_rapidity_weight,
                    anneal_rapidity_jitter_weight=anneal_rapidity_jitter_weight,
                    anneal_shell_width=anneal_shell_width,
                    anneal_shell_keep_per_band=anneal_shell_keep_per_band,
                    orthogonal_prune_boundary=orthogonal_prune_boundary,
                    orthogonal_alpha_floor=orthogonal_alpha_floor,
                    binary_prune_boundary=binary_prune_boundary,
                    binary_prune_exact_if_at_most=binary_prune_exact_if_at_most,
                )
                stage_candidates = [
                    DirectedTorusCandidate(**d)
                    for d in sub["top_k_by_effective_score"][:stage_topk]
                ]
                round_stage.extend(stage_candidates)
                rapidity_pruned_candidates += int(sub.get("rapidity_pruned_candidates", 0))
                rapidity_dominated_edge_count += int(sub.get("rapidity_dominated_edge_count", 0))
                binary_pruned_candidates += int(sub.get("binary_pruned_candidates", 0))
                binary_unit_cycle_witness_found = (
                    binary_unit_cycle_witness_found or bool(sub.get("binary_unit_cycle_witness_found", False))
                )
                binary_prune_boundary_active = (
                    binary_prune_boundary_active or bool(sub.get("binary_prune_boundary_active", False))
                )
                binary_exact_check_used = binary_exact_check_used or bool(sub.get("binary_exact_check_used", False))
                orthogonal_pruned_candidates += int(sub.get("orthogonal_pruned_candidates", 0))
                reverse_rounds_used += int(sub.get("reverse_rounds_used", 0))
                recursive_levels_visited += int(sub.get("recursive_levels_visited", 0))
                recursive_poles_expanded += int(sub.get("recursive_poles_expanded", 0))
                iterative_trace.append(
                    {
                        "round": ridx + 1,
                        "k_arity": kk,
                        "scale_effective": sub.get("rapidity_prune_scale_effective", rapidity_prune_scale_effective),
                        "sampled": sub.get("unique_tours_sampled", 0),
                        "best_cost": sub.get("best_by_cost", {}).get("tour_cost", math.inf),
                        "best_effective_cost": sub.get("best_by_effective_score", {}).get("tour_cost", math.inf),
                    }
                )
                round_stage_stats.append(
                    (
                        kk,
                        float(sub.get("best_by_cost", {}).get("tour_cost", math.inf)),
                        float(sub.get("rapidity_prune_scale_effective", rapidity_prune_scale_effective)),
                    )
                )
            # Anneal at n-arity by merging with previous pool and keeping best by effective score.
            if anneal_rapidity_weight > 0 or anneal_rapidity_jitter_weight > 0 or anneal_shell_keep_per_band > 0:
                for c in pool:
                    if c.rapidity_term == 0.0 and anneal_rapidity_weight > 0:
                        c.rapidity_term = min_subpath_rapidity(c.tour, dist, window=anneal_rapidity_window)
                    if c.rapidity_jitter == 0.0 and anneal_rapidity_jitter_weight > 0:
                        c.rapidity_jitter = subpath_rapidity_jitter(c.tour, dist, window=anneal_rapidity_window)
                    if c.rapidity_shell < 0:
                        c.rapidity_shell = rapidity_shell_id(
                            c.rapidity_term if c.rapidity_term > 0 else min_subpath_rapidity(c.tour, dist, window=anneal_rapidity_window),
                            anneal_shell_width,
                        )
                for c in round_stage:
                    c.rapidity_term = min_subpath_rapidity(c.tour, dist, window=anneal_rapidity_window)
                    c.rapidity_jitter = subpath_rapidity_jitter(c.tour, dist, window=anneal_rapidity_window)
                    c.rapidity_shell = rapidity_shell_id(c.rapidity_term, anneal_shell_width)
                merged = pool + round_stage
                for c in merged:
                    rapidity_norm = c.rapidity_term / max(1e-9, edge_mean)
                    jitter_norm = c.rapidity_jitter / max(1e-9, edge_mean)
                    c.effective_score = (
                        c.effective_score
                        + anneal_rapidity_weight * rapidity_norm
                        + anneal_rapidity_jitter_weight * jitter_norm
                    )
                pool = dedupe_by_code_keep_best(merged)
                pool = keep_top_per_rapidity_shell(pool, anneal_shell_keep_per_band)
                pool = pool[: max(intercept_topk, top_k, stage_topk)]
            else:
                pool = dedupe_by_code_keep_best(pool + round_stage)[: max(intercept_topk, top_k, stage_topk)]
            if anneal_rapidity_barrier:
                peel_stats = [x for x in round_stage_stats if x[0] < n and math.isfinite(x[1])]
                if peel_stats:
                    peel_best = min(x[1] for x in peel_stats)
                    peel_scale_mean = sum(x[2] for x in peel_stats) / float(len(peel_stats))
                    # Rapidity-derived anneal barrier: peel floor plus rapidity-scaled margin.
                    barrier_cost = peel_best + anneal_barrier_strength * peel_scale_mean * max(1e-9, edge_mean)
                    best_local = min(pool, key=lambda c: c.tour_cost) if pool else None
                    pre = len(pool)
                    pool = [c for c in pool if c.tour_cost <= barrier_cost + 1e-9]
                    if best_local is not None and all(c.permutation_code != best_local.permutation_code for c in pool):
                        pool.append(best_local)
                    pool = dedupe_by_code_keep_best(pool)[: max(intercept_topk, top_k, stage_topk)]
                    iterative_barrier_trace.append(
                        {
                            "round": ridx + 1,
                            "barrier_cost": barrier_cost,
                            "peel_best_cost": peel_best,
                            "peel_scale_mean": peel_scale_mean,
                            "pruned": max(0, pre - len(pool)),
                        }
                    )
            if orthogonal_prune_boundary and pool:
                ub_local = min(c.tour_cost for c in pool)
                alpha_local = rapidity_alpha_from_scale(
                    rapidity_prune_scale_effective,
                    n,
                    alpha_floor=orthogonal_alpha_floor,
                )
                bound = orthogonal_soft_boundary(orthogonal_lb, ub_local, alpha_local)
                best_local = min(pool, key=lambda c: c.tour_cost)
                pre = len(pool)
                pool = [c for c in pool if c.tour_cost <= bound + 1e-9]
                if all(c.permutation_code != best_local.permutation_code for c in pool):
                    pool.append(best_local)
                pool = dedupe_by_code_keep_best(pool)[: max(intercept_topk, top_k, stage_topk)]
                orthogonal_pruned_candidates += max(0, pre - len(pool))
                orthogonal_boundary_trace.append(
                    {
                        "round": ridx + 1,
                        "ub_local": ub_local,
                        "lb": orthogonal_lb,
                        "alpha": alpha_local,
                        "bound": bound,
                        "pruned": max(0, pre - len(pool)),
                    }
                )
            round_best_cost = min((c.tour_cost for c in pool), default=math.inf)
            improved = round_best_cost + tol < best_cost_so_far
            if improved:
                best_cost_so_far = round_best_cost
                no_improve_rounds = 0
            else:
                no_improve_rounds += 1
            if no_improve_rounds >= patience:
                iterative_early_stopped = True
                break
        candidates.extend(pool)
        seen_codes.update(c.permutation_code for c in pool)
        raw_costs.extend(c.tour_cost for c in pool)
        raw_assoc.extend(c.assoc_term for c in pool)
        raw_tau.extend(c.tau_term for c in pool)
    else:  # reverse-flip-prune
        base = directed_torus_atsp_solver(
            dist=dist,
            max_steps=max_steps,
            top_k=max(intercept_topk, top_k, 64),
            assoc_weight=assoc_weight,
            tau_mode=tau_mode,
            tau_weight=tau_weight,
            k_arity=k_arity,
            first_sat_stop=False,
            optimizer="recursive-intercept",
            golden_iters=golden_iters,
            geometry=geometry,
            roughness_mode=roughness_mode,
            roughness_eps=roughness_eps,
            rough_slope_weight=rough_slope_weight,
            rough_curvature_weight=rough_curvature_weight,
            rough_jump_weight=rough_jump_weight,
            arc_scale=arc_scale,
            anchor_city=anchor_city,
            anchor_next=anchor_next,
            anchor_bruteforce=anchor_bruteforce,
            intercept_grid=intercept_grid,
            intercept_kendall_max=intercept_kendall_max,
            intercept_topk=intercept_topk,
            intercept_mismatch_weight=intercept_mismatch_weight,
            recursive_depth=recursive_depth,
            recursive_beam=recursive_beam,
            hybrid_anchor_refine=hybrid_anchor_refine,
            hybrid_refine_budget=hybrid_refine_budget,
            hybrid_refine_samples=hybrid_refine_samples,
            hybrid_rerank_top_m=hybrid_rerank_top_m,
            hybrid_blend_effective=hybrid_blend_effective,
            hybrid_blend_cost=hybrid_blend_cost,
            reverse_rounds=0,
            reverse_overlap_keep=reverse_overlap_keep,
            rapidity_prune=rapidity_prune,
            rapidity_prune_scale=rapidity_prune_scale,
            rapidity_prune_scale_mode=rapidity_prune_scale_mode,
            rapidity_prune_cosh_beta=rapidity_prune_cosh_beta,
            rapidity_prune_cosh_strength=rapidity_prune_cosh_strength,
            orthogonal_prune_boundary=orthogonal_prune_boundary,
            orthogonal_alpha_floor=orthogonal_alpha_floor,
            binary_prune_boundary=binary_prune_boundary,
        )
        pool = [DirectedTorusCandidate(**d) for d in base["top_k_by_effective_score"]]
        is_binary_matrix = is_binary_one_two_matrix(dist)
        binary_unit_cycle_witness_found = has_unit_cycle_witness(pool, n)
        exact_unit_tour: list[int] | None = None
        if (
            binary_prune_boundary
            and is_binary_matrix
            and not binary_unit_cycle_witness_found
            and n <= max(0, binary_prune_exact_if_at_most)
        ):
            binary_exact_check_used = True
            exact_cost_local, exact_tour_local = exact_atsp_small(dist)
            if abs(exact_cost_local - float(n)) <= 1e-9:
                binary_unit_cycle_witness_found = True
                exact_unit_tour = exact_tour_local
        if exact_unit_tour is not None and not has_unit_cycle_witness(pool, n):
            assoc_term = octonion_associator_like(exact_unit_tour, dist)
            tau_term = compute_tau_term(tau_mode, exact_unit_tour, dist, assoc_term)
            pool.append(
                DirectedTorusCandidate(
                    step=0,
                    seed_idx=0,
                    u=0.0,
                    v=0.0,
                    root_distance=0.0,
                    permutation_code=permutation_to_factoradic_code(exact_unit_tour),
                    tour=exact_unit_tour,
                    tour_cost=float(n),
                    assoc_term=assoc_term,
                    tau_term=tau_term,
                    rough_slope=0.0,
                    rough_curvature=0.0,
                    rough_jump=0.0,
                    effective_score=0.0,
                )
            )
        binary_prune_boundary_active = (
            binary_prune_boundary
            and is_binary_matrix
            and binary_unit_cycle_witness_found
        )
        dominated_edges: set[tuple[int, int]] = set()
        if rapidity_prune:
            dominated_edges = rapidity_dominated_edges(
                dist=dist,
                rapidity_du=du,
                rapidity_dv=dv,
                mean_edge=edge_mean,
                scale=rapidity_prune_scale_effective,
            )
            rapidity_dominated_edge_count = len(dominated_edges)
        rounds = reverse_rounds if reverse_rounds > 0 else n
        for _ in range(rounds):
            if len(pool) <= 1:
                break
            reverse_rounds_used += 1
            bad_before = sum(c.effective_score for c in pool) / float(len(pool))
            worst = max(pool, key=lambda c: c.effective_score)
            best_cost = min(pool, key=lambda c: c.tour_cost)
            if orthogonal_prune_boundary:
                alpha_local = rapidity_alpha_from_scale(
                    rapidity_prune_scale_effective,
                    n,
                    alpha_floor=orthogonal_alpha_floor,
                )
                orth_bound = orthogonal_soft_boundary(orthogonal_lb, best_cost.tour_cost, alpha_local)
            else:
                alpha_local = 1.0
                orth_bound = math.inf
            kept = []
            for c in pool:
                ov = edge_overlap_ratio(c.tour, worst.tour)
                dominated_ok = not candidate_uses_dominated_edge(c.tour, dominated_edges)
                binary_ok = (not binary_prune_boundary_active) or (c.tour_cost <= float(n) + 1e-9)
                orth_ok = (not orthogonal_prune_boundary) or (c.tour_cost <= orth_bound + 1e-9)
                if (
                    (ov <= reverse_overlap_keep and dominated_ok and binary_ok and orth_ok)
                    or c.permutation_code == best_cost.permutation_code
                ):
                    kept.append(c)
                elif rapidity_prune and candidate_uses_dominated_edge(c.tour, dominated_edges):
                    rapidity_pruned_candidates += 1
                elif binary_prune_boundary_active and not binary_ok:
                    binary_pruned_candidates += 1
                elif orthogonal_prune_boundary and not orth_ok:
                    orthogonal_pruned_candidates += 1
            if len(kept) == len(pool):
                break
            pool = kept
            bad_after = sum(c.effective_score for c in pool) / float(len(pool))
            reverse_bad_mass_history.append((bad_before, bad_after))
            if orthogonal_prune_boundary:
                orthogonal_boundary_trace.append(
                    {
                        "round": reverse_rounds_used,
                        "ub_local": best_cost.tour_cost,
                        "lb": orthogonal_lb,
                        "alpha": alpha_local,
                        "bound": orth_bound,
                    }
                )
        selected = sorted(pool, key=lambda c: c.effective_score)[: max(1, intercept_topk)]
        candidates.extend(selected)
        seen_codes.update(c.permutation_code for c in selected)
        raw_costs.extend(c.tour_cost for c in selected)
        raw_assoc.extend(c.assoc_term for c in selected)
        raw_tau.extend(c.tau_term for c in selected)

    if not candidates:
        return {
            "n_cities": n,
            "candidates": [],
            "unique_tours_sampled": 0,
            "tour_space_size": perm_space,
            "coverage_ratio": 0.0,
            "rapidity_du": du,
            "rapidity_dv": dv,
        }

    # Keep effective scores trajectory-independent by matrix-level normalization.
    # For spiral candidates where roughness wasn't set in creation, fill it now.
    for i, c in enumerate(candidates):
        cost_norm = c.tour_cost / (n * max(1e-9, edge_mean))
        assoc_norm = c.assoc_term / (1.0 + abs(c.assoc_term))
        tau_norm = c.tau_term / (1.0 + abs(c.tau_term))
        c.effective_score = c.root_distance + cost_norm + assoc_weight_effective * assoc_norm + tau_weight * tau_norm
        if c.rough_slope == 0.0 and c.rough_curvature == 0.0 and c.rough_jump == 0.0 and roughness_mode == "on":
            t_local = (c.u * arc_length) % max(1e-12, arc_length)
            candidates[i] = enrich_candidate_with_roughness(c, t_local, ctx, c.step)

    by_cost = sorted(candidates, key=lambda x: (x.tour_cost, x.root_distance))
    by_effective = sorted(candidates, key=lambda x: (x.effective_score, x.tour_cost))
    by_root = sorted(candidates, key=lambda x: (x.root_distance, x.tour_cost))

    rho_root_vs_cost = rank_correlation_spearman(
        [c.root_distance for c in candidates],
        [c.tour_cost for c in candidates],
    )
    rho_eff_vs_cost = rank_correlation_spearman(
        [c.effective_score for c in candidates],
        [c.tour_cost for c in candidates],
    )

    return {
        "n_cities": n,
        "unique_tours_sampled": len(candidates),
        "tour_space_size": perm_space,
        "coverage_ratio": len(candidates) / perm_space,
        "assoc_weight": assoc_weight_effective,
        "matrix_asymmetry": asymmetry,
        "tau_mode": tau_mode,
        "tau_weight": tau_weight,
        "k_arity": k,
        "narrow_arc_length": arc_length,
        "arc_scale": arc_scale,
        "rapidity_du": du,
        "rapidity_dv": dv,
        "geometry": geometry,
        "flow_anchor_u": flow_anchor_u,
        "flow_anchor_v": flow_anchor_v,
        "roughness_mode": roughness_mode,
        "roughness_eps": eps,
        "rough_slope_weight": rough_slope_weight,
        "rough_curvature_weight": rough_curvature_weight,
        "rough_jump_weight": rough_jump_weight,
        "optimizer": optimizer,
        "golden_iters": golden_iters,
        "anchor_city": anchor_city,
        "anchor_next": anchor_next,
        "anchor_bruteforce": anchor_bruteforce,
        "intercept_grid": intercept_grid,
        "intercept_kendall_max": intercept_kendall_max,
        "intercept_topk": intercept_topk,
        "intercept_mismatch_weight": intercept_mismatch_weight,
        "intercept_pairs_tested": intercept_pairs_tested,
        "intercept_hits": intercept_hits,
        "recursive_depth": recursive_depth,
        "recursive_beam": recursive_beam,
        "recursive_levels_visited": recursive_levels_visited,
        "recursive_poles_expanded": recursive_poles_expanded,
        "hybrid_anchor_refine": hybrid_anchor_refine,
        "hybrid_refine_budget": hybrid_refine_budget,
        "hybrid_refine_samples": hybrid_refine_samples,
        "hybrid_rerank_top_m": hybrid_rerank_top_m,
        "hybrid_blend_effective": hybrid_blend_effective,
        "hybrid_blend_cost": hybrid_blend_cost,
        "hybrid_pairs_used": hybrid_pairs_used,
        "reverse_rounds": reverse_rounds,
        "reverse_overlap_keep": reverse_overlap_keep,
        "rapidity_prune": rapidity_prune,
        "rapidity_prune_scale": rapidity_prune_scale,
        "rapidity_prune_scale_mode": rapidity_prune_scale_mode,
        "rapidity_prune_cosh_beta": rapidity_prune_cosh_beta,
        "rapidity_prune_cosh_strength": rapidity_prune_cosh_strength,
        "rapidity_prune_scale_effective": rapidity_prune_scale_effective,
        "rapidity_dominated_edge_count": rapidity_dominated_edge_count,
        "rapidity_pruned_candidates": rapidity_pruned_candidates,
        "binary_prune_boundary": binary_prune_boundary,
        "binary_prune_exact_if_at_most": binary_prune_exact_if_at_most,
        "binary_exact_check_used": binary_exact_check_used,
        "binary_prune_boundary_active": binary_prune_boundary_active,
        "binary_unit_cycle_witness_found": binary_unit_cycle_witness_found,
        "binary_pruned_candidates": binary_pruned_candidates,
        "iterative_rounds": iterative_rounds,
        "iterative_arity_start": iterative_arity_start,
        "iterative_stage_topk": iterative_stage_topk,
        "iterative_early_stop_patience": iterative_early_stop_patience,
        "iterative_early_stop_tol": iterative_early_stop_tol,
        "anneal_rapidity_barrier": anneal_rapidity_barrier,
        "anneal_barrier_strength": anneal_barrier_strength,
        "anneal_rapidity_window": anneal_rapidity_window,
        "anneal_rapidity_weight": anneal_rapidity_weight,
        "anneal_rapidity_jitter_weight": anneal_rapidity_jitter_weight,
        "anneal_shell_width": anneal_shell_width,
        "anneal_shell_keep_per_band": anneal_shell_keep_per_band,
        "orthogonal_prune_boundary": orthogonal_prune_boundary,
        "orthogonal_alpha_floor": orthogonal_alpha_floor,
        "orthogonal_lb": orthogonal_lb,
        "orthogonal_pruned_candidates": orthogonal_pruned_candidates,
        "orthogonal_boundary_trace": orthogonal_boundary_trace,
        "iterative_rounds_executed": iterative_rounds_executed,
        "iterative_early_stopped": iterative_early_stopped,
        "iterative_trace": iterative_trace,
        "iterative_barrier_trace": iterative_barrier_trace,
        "reverse_rounds_used": reverse_rounds_used,
        "reverse_bad_mass_history": reverse_bad_mass_history,
        "first_sat_stop": first_sat_stop,
        "first_sat_triggered": first_sat_triggered,
        "first_sat_step": first_sat_step,
        "best_by_cost": asdict(by_cost[0]),
        "best_by_effective_score": asdict(by_effective[0]),
        "best_by_root_distance": asdict(by_root[0]),
        "top_k_by_cost": [asdict(c) for c in by_cost[:top_k]],
        "top_k_by_effective_score": [asdict(c) for c in by_effective[:top_k]],
        "spearman_root_vs_cost": rho_root_vs_cost,
        "spearman_effective_vs_cost": rho_eff_vs_cost,
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Directed torus ATSP geometric oracle")
    p.add_argument("--matrix-json", type=str, default=None, help="path to square distance matrix JSON")
    p.add_argument("--demo-cities", type=int, default=9, help="city count for random asymmetric demo")
    p.add_argument("--demo-seed", type=int, default=1234, help="seed for random demo matrix")
    p.add_argument("--max-steps", type=int, default=3000, help="geometric walk step budget")
    p.add_argument("--top-k", type=int, default=7, help="top candidates to report")
    p.add_argument(
        "--assoc-weight",
        type=float,
        default=None,
        help="weight for associator correction (default: dynamic from matrix asymmetry)",
    )
    p.add_argument(
        "--tau-mode",
        choices=("off", "cycle", "mod", "assoc"),
        default="off",
        help="tau-like curvature feature mode for directed manifold ranking",
    )
    p.add_argument("--tau-weight", type=float, default=0.0, help="weight for tau curvature feature")
    p.add_argument(
        "--k-arity",
        type=int,
        default=None,
        help="n-arity level for narrow arc constraint (default: city count)",
    )
    p.add_argument(
        "--arc-scale",
        type=float,
        default=1.0,
        help="multiplier on base arc length pi/(2k); 1.0 follows k-th root arc rule",
    )
    p.add_argument(
        "--first-sat-stop",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="stop at first SAT-like condition (new permutation with nonzero associator)",
    )
    p.add_argument(
        "--optimizer",
        choices=(
            "golden-section",
            "spiral",
            "anchored-spiral",
            "anchored-intercept",
            "recursive-intercept",
            "reverse-flip-prune",
            "iterative-peel-anneal",
        ),
        default="golden-section",
        help="narrow-arc optimizer (default: direct golden-section minimization)",
    )
    p.add_argument("--anchor-city", type=int, default=0, help="anchor source city for anchored-spiral mode")
    p.add_argument("--anchor-next", type=int, default=None, help="fixed anchor target city; default brute-force n-1 targets")
    p.add_argument(
        "--anchor-bruteforce",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="when anchor-next unset, brute-force all n-1 outgoing anchor targets",
    )
    p.add_argument("--intercept-grid", type=int, default=24, help="samples per anchored arc for intercept probing")
    p.add_argument(
        "--intercept-kendall-max",
        type=float,
        default=0.15,
        help="max normalized Kendall distance to treat arc points as intercept-coincident",
    )
    p.add_argument("--intercept-topk", type=int, default=64, help="max intercept candidates retained")
    p.add_argument(
        "--intercept-mismatch-weight",
        type=float,
        default=0.20,
        help="penalty weight for arc-family mismatch at intercepts",
    )
    p.add_argument("--recursive-depth", type=int, default=2, help="levels for recursive intercept pole expansion")
    p.add_argument("--recursive-beam", type=int, default=4, help="max promoted pole seeds per level")
    p.add_argument(
        "--reverse-rounds",
        type=int,
        default=0,
        help="for reverse-flip-prune: prune rounds (0 => n rounds)",
    )
    p.add_argument(
        "--reverse-overlap-keep",
        type=float,
        default=0.55,
        help="for reverse-flip-prune: keep candidate when edge-overlap with worst <= threshold",
    )
    p.add_argument(
        "--rapidity-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="for reverse-flip-prune: prune tours containing rapidity-dominated directed edges",
    )
    p.add_argument(
        "--rapidity-prune-scale",
        type=float,
        default=2.0,
        help="scale for rapidity inequality margin used in edge dominance pruning",
    )
    p.add_argument(
        "--rapidity-prune-scale-mode",
        choices=("fixed", "sqrt-n", "sqrt-n-over-arity", "cosh-arity"),
        default="fixed",
        help="policy for rapidity prune scale (fixed, sqrt(n), sqrt(arity), or catenary-like cosh schedule on arity)",
    )
    p.add_argument(
        "--rapidity-prune-cosh-beta",
        type=float,
        default=2.0,
        help="for scale-mode=cosh-arity: curvature parameter beta",
    )
    p.add_argument(
        "--rapidity-prune-cosh-strength",
        type=float,
        default=0.35,
        help="for scale-mode=cosh-arity: widening strength toward peel side",
    )
    p.add_argument(
        "--orthogonal-prune-boundary",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="enable LB/UB orthogonal soft boundary pruning informed by rapidity alpha",
    )
    p.add_argument(
        "--orthogonal-alpha-floor",
        type=float,
        default=0.25,
        help="minimum alpha for orthogonal boundary interpolation between LB and UB",
    )
    p.add_argument(
        "--binary-prune-boundary",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="for reverse/iterative modes: if matrix is {1,2} and a unit-cycle witness exists, prune candidates with cost > n",
    )
    p.add_argument(
        "--binary-prune-exact-if-at-most",
        type=int,
        default=10,
        help="for binary prune boundary: if witness not sampled and n is small, run exact check up to this n to detect unit-cycle witness",
    )
    p.add_argument(
        "--iterative-rounds",
        type=int,
        default=1,
        help="for iterative-peel-anneal: number of peel+anneal macro rounds",
    )
    p.add_argument(
        "--iterative-arity-start",
        type=int,
        default=2,
        help="for iterative-peel-anneal: starting arity for peel ladder (increments by +1 each step)",
    )
    p.add_argument(
        "--iterative-stage-topk",
        type=int,
        default=24,
        help="for iterative-peel-anneal: top-k candidates retained from each arity stage",
    )
    p.add_argument(
        "--iterative-early-stop-patience",
        type=int,
        default=1,
        help="for iterative-peel-anneal: stop after this many non-improving rounds",
    )
    p.add_argument(
        "--iterative-early-stop-tol",
        type=float,
        default=1e-9,
        help="for iterative-peel-anneal: minimum strict best-cost improvement per round",
    )
    p.add_argument(
        "--anneal-rapidity-barrier",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="for iterative-peel-anneal: prune annealed pool above rapidity-derived peel barrier",
    )
    p.add_argument(
        "--anneal-barrier-strength",
        type=float,
        default=1.0,
        help="for iterative-peel-anneal: margin multiplier on rapidity-derived peel barrier",
    )
    p.add_argument(
        "--anneal-rapidity-window",
        type=int,
        default=4,
        help="for iterative-peel-anneal: subpath window size for rapidity bookkeeping",
    )
    p.add_argument(
        "--anneal-rapidity-weight",
        type=float,
        default=0.25,
        help="for iterative-peel-anneal: blend weight for subpath rapidity in anneal score settling",
    )
    p.add_argument(
        "--anneal-rapidity-jitter-weight",
        type=float,
        default=0.10,
        help="for iterative-peel-anneal: weight for subpath rapidity jitter penalty in anneal score settling",
    )
    p.add_argument(
        "--anneal-shell-width",
        type=float,
        default=0.25,
        help="for iterative-peel-anneal: shell quantization width for rapidity bands",
    )
    p.add_argument(
        "--anneal-shell-keep-per-band",
        type=int,
        default=0,
        help="for iterative-peel-anneal: keep at most this many candidates per rapidity shell band (0 disables)",
    )
    p.add_argument(
        "--hybrid-anchor-refine",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="for recursive-intercept: add anchor-style pair refinement pass",
    )
    p.add_argument(
        "--hybrid-refine-budget",
        type=int,
        default=6,
        help="max directed pairs used in hybrid anchor refinement",
    )
    p.add_argument(
        "--hybrid-refine-samples",
        type=int,
        default=16,
        help="arc samples per pair in hybrid anchor refinement",
    )
    p.add_argument(
        "--hybrid-rerank-top-m",
        type=int,
        default=16,
        help="top-M candidates to rerank with blended effective+cost score",
    )
    p.add_argument(
        "--hybrid-blend-effective",
        type=float,
        default=0.35,
        help="blend weight on geometric effective score in hybrid rerank",
    )
    p.add_argument(
        "--hybrid-blend-cost",
        type=float,
        default=0.65,
        help="blend weight on normalized tour cost in hybrid rerank",
    )
    p.add_argument(
        "--geometry",
        choices=("intrinsic", "oblique"),
        default="oblique",
        help="tour decode geometry (oblique tips city dimensions by edge weights)",
    )
    p.add_argument(
        "--roughness-mode",
        choices=("off", "on"),
        default="off",
        help="add local roughness terms (slope/curvature/permutation jump) to score",
    )
    p.add_argument(
        "--roughness-eps",
        type=float,
        default=0.0,
        help="finite-difference epsilon on arc parameter (0 => arc_length/64)",
    )
    p.add_argument("--rough-slope-weight", type=float, default=0.20, help="weight for slope roughness penalty")
    p.add_argument("--rough-curvature-weight", type=float, default=0.10, help="weight for curvature roughness penalty")
    p.add_argument("--rough-jump-weight", type=float, default=0.25, help="weight for permutation jump roughness penalty")
    p.add_argument(
        "--golden-iters",
        type=int,
        default=40,
        help="golden-section iterations when optimizer=golden-section",
    )
    p.add_argument("--exact-if-at-most", type=int, default=9, help="run exact brute-force if n <= threshold")
    p.add_argument("--json", action="store_true", help="emit JSON payload")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.max_steps <= 0:
        raise SystemExit("--max-steps must be > 0")
    if args.top_k <= 0:
        raise SystemExit("--top-k must be > 0")
    if args.assoc_weight is not None and args.assoc_weight < 0:
        raise SystemExit("--assoc-weight must be >= 0")
    if args.tau_weight < 0:
        raise SystemExit("--tau-weight must be >= 0")
    if args.k_arity is not None and args.k_arity < 1:
        raise SystemExit("--k-arity must be >= 1")
    if args.arc_scale <= 0:
        raise SystemExit("--arc-scale must be > 0")
    if args.golden_iters < 1:
        raise SystemExit("--golden-iters must be >= 1")
    if args.roughness_eps < 0:
        raise SystemExit("--roughness-eps must be >= 0")
    if args.intercept_grid < 2:
        raise SystemExit("--intercept-grid must be >= 2")
    if not (0.0 <= args.intercept_kendall_max <= 1.0):
        raise SystemExit("--intercept-kendall-max must be in [0,1]")
    if args.intercept_topk < 1:
        raise SystemExit("--intercept-topk must be >= 1")
    if args.intercept_mismatch_weight < 0:
        raise SystemExit("--intercept-mismatch-weight must be >= 0")
    if args.recursive_depth < 1:
        raise SystemExit("--recursive-depth must be >= 1")
    if args.recursive_beam < 1:
        raise SystemExit("--recursive-beam must be >= 1")
    if args.reverse_rounds < 0:
        raise SystemExit("--reverse-rounds must be >= 0")
    if not (0.0 <= args.reverse_overlap_keep <= 1.0):
        raise SystemExit("--reverse-overlap-keep must be in [0,1]")
    if args.rapidity_prune_scale <= 0:
        raise SystemExit("--rapidity-prune-scale must be > 0")
    if args.rapidity_prune_cosh_beta < 0:
        raise SystemExit("--rapidity-prune-cosh-beta must be >= 0")
    if args.rapidity_prune_cosh_strength < 0:
        raise SystemExit("--rapidity-prune-cosh-strength must be >= 0")
    if not (0.0 <= args.orthogonal_alpha_floor <= 1.0):
        raise SystemExit("--orthogonal-alpha-floor must be in [0,1]")
    if args.iterative_rounds < 1:
        raise SystemExit("--iterative-rounds must be >= 1")
    if args.iterative_arity_start < 1:
        raise SystemExit("--iterative-arity-start must be >= 1")
    if args.iterative_stage_topk < 1:
        raise SystemExit("--iterative-stage-topk must be >= 1")
    if args.iterative_early_stop_patience < 1:
        raise SystemExit("--iterative-early-stop-patience must be >= 1")
    if args.iterative_early_stop_tol < 0:
        raise SystemExit("--iterative-early-stop-tol must be >= 0")
    if args.anneal_barrier_strength < 0:
        raise SystemExit("--anneal-barrier-strength must be >= 0")
    if args.anneal_rapidity_window < 1:
        raise SystemExit("--anneal-rapidity-window must be >= 1")
    if args.anneal_rapidity_weight < 0:
        raise SystemExit("--anneal-rapidity-weight must be >= 0")
    if args.anneal_rapidity_jitter_weight < 0:
        raise SystemExit("--anneal-rapidity-jitter-weight must be >= 0")
    if args.anneal_shell_width <= 0:
        raise SystemExit("--anneal-shell-width must be > 0")
    if args.anneal_shell_keep_per_band < 0:
        raise SystemExit("--anneal-shell-keep-per-band must be >= 0")
    if args.binary_prune_exact_if_at_most < 0:
        raise SystemExit("--binary-prune-exact-if-at-most must be >= 0")
    if args.hybrid_refine_budget < 1:
        raise SystemExit("--hybrid-refine-budget must be >= 1")
    if args.hybrid_refine_samples < 2:
        raise SystemExit("--hybrid-refine-samples must be >= 2")
    if args.hybrid_rerank_top_m < 1:
        raise SystemExit("--hybrid-rerank-top-m must be >= 1")
    if args.hybrid_blend_effective < 0 or args.hybrid_blend_cost < 0:
        raise SystemExit("--hybrid-blend-effective and --hybrid-blend-cost must be >= 0")
    if args.hybrid_blend_effective + args.hybrid_blend_cost <= 0:
        raise SystemExit("hybrid blend weights cannot both be zero")

    if args.matrix_json:
        with open(args.matrix_json, "r", encoding="utf-8") as fh:
            dist = json.load(fh)
    else:
        dist = random_asymmetric_matrix(args.demo_cities, args.demo_seed)

    payload = directed_torus_atsp_solver(
        dist=dist,
        max_steps=args.max_steps,
        top_k=args.top_k,
        assoc_weight=args.assoc_weight,
        tau_mode=args.tau_mode,
        tau_weight=args.tau_weight,
        k_arity=args.k_arity,
        first_sat_stop=args.first_sat_stop,
        optimizer=args.optimizer,
        golden_iters=args.golden_iters,
        geometry=args.geometry,
        roughness_mode=args.roughness_mode,
        roughness_eps=args.roughness_eps,
        rough_slope_weight=args.rough_slope_weight,
        rough_curvature_weight=args.rough_curvature_weight,
        rough_jump_weight=args.rough_jump_weight,
        arc_scale=args.arc_scale,
        anchor_city=args.anchor_city,
        anchor_next=args.anchor_next,
        anchor_bruteforce=args.anchor_bruteforce,
        intercept_grid=args.intercept_grid,
        intercept_kendall_max=args.intercept_kendall_max,
        intercept_topk=args.intercept_topk,
        intercept_mismatch_weight=args.intercept_mismatch_weight,
        recursive_depth=args.recursive_depth,
        recursive_beam=args.recursive_beam,
        hybrid_anchor_refine=args.hybrid_anchor_refine,
        hybrid_refine_budget=args.hybrid_refine_budget,
        hybrid_refine_samples=args.hybrid_refine_samples,
        hybrid_rerank_top_m=args.hybrid_rerank_top_m,
        hybrid_blend_effective=args.hybrid_blend_effective,
        hybrid_blend_cost=args.hybrid_blend_cost,
        reverse_rounds=args.reverse_rounds,
        reverse_overlap_keep=args.reverse_overlap_keep,
        rapidity_prune=args.rapidity_prune,
        rapidity_prune_scale=args.rapidity_prune_scale,
        rapidity_prune_scale_mode=args.rapidity_prune_scale_mode,
        rapidity_prune_cosh_beta=args.rapidity_prune_cosh_beta,
        rapidity_prune_cosh_strength=args.rapidity_prune_cosh_strength,
        orthogonal_prune_boundary=args.orthogonal_prune_boundary,
        orthogonal_alpha_floor=args.orthogonal_alpha_floor,
        iterative_rounds=args.iterative_rounds,
        iterative_arity_start=args.iterative_arity_start,
        iterative_stage_topk=args.iterative_stage_topk,
        iterative_early_stop_patience=args.iterative_early_stop_patience,
        iterative_early_stop_tol=args.iterative_early_stop_tol,
        anneal_rapidity_barrier=args.anneal_rapidity_barrier,
        anneal_barrier_strength=args.anneal_barrier_strength,
        anneal_rapidity_window=args.anneal_rapidity_window,
        anneal_rapidity_weight=args.anneal_rapidity_weight,
        anneal_rapidity_jitter_weight=args.anneal_rapidity_jitter_weight,
        anneal_shell_width=args.anneal_shell_width,
        anneal_shell_keep_per_band=args.anneal_shell_keep_per_band,
        binary_prune_boundary=args.binary_prune_boundary,
        binary_prune_exact_if_at_most=args.binary_prune_exact_if_at_most,
    )

    n = payload["n_cities"]
    if n <= args.exact_if_at_most:
        exact_cost, exact_tour = exact_atsp_small(dist)
        payload["exact_optimal_cost"] = exact_cost
        payload["exact_optimal_tour"] = exact_tour
        payload["gap_best_cost"] = payload["best_by_cost"]["tour_cost"] - exact_cost
        payload["gap_best_effective"] = payload["best_by_effective_score"]["tour_cost"] - exact_cost
        payload["gap_best_root"] = payload["best_by_root_distance"]["tour_cost"] - exact_cost

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print(
        f"n={payload['n_cities']} sampled={payload['unique_tours_sampled']}/{payload['tour_space_size']} "
        f"coverage={payload['coverage_ratio']:.4f}"
    )
    print(
        f"rho(root,cost)={payload['spearman_root_vs_cost']:.4f} "
        f"rho(effective,cost)={payload['spearman_effective_vs_cost']:.4f} "
        f"tau_mode={payload['tau_mode']} tau_weight={payload['tau_weight']:.3f} "
        f"k={payload['k_arity']} asym={payload['matrix_asymmetry']:.4f} "
        f"assoc_w={payload['assoc_weight']:.3f} "
        f"rapidity=(du:{payload['rapidity_du']:.6f},dv:{payload['rapidity_dv']:.6f}) "
        f"optimizer={payload['optimizer']} geometry={payload['geometry']} arc_scale={payload['arc_scale']:.3f} "
        f"roughness={payload['roughness_mode']}"
    )
    b = payload["best_by_cost"]
    e = payload["best_by_effective_score"]
    r = payload["best_by_root_distance"]
    print(f"best_cost={b['tour_cost']:.6f} tour={b['tour']} step={b['step']}")
    print(f"best_effective_cost={e['tour_cost']:.6f} score={e['effective_score']:.6f} tour={e['tour']}")
    print(
        "best_effective_components: "
        f"root={e['root_distance']:.6f} "
        f"assoc={e['assoc_term']:.6f} "
        f"tau={e['tau_term']:.6f} "
        f"rapidity={e.get('rapidity_term', 0.0):.6f} "
        f"jitter={e.get('rapidity_jitter', 0.0):.6f} "
        f"shell={e.get('rapidity_shell', -1)} "
        f"rough(s,c,j)=({e['rough_slope']:.6f},{e['rough_curvature']:.6f},{e['rough_jump']:.6f})"
    )
    print(f"best_root_cost={r['tour_cost']:.6f} root_distance={r['root_distance']:.6f} tour={r['tour']}")
    print("top_effective_candidates:")
    for i, c in enumerate(payload["top_k_by_effective_score"][: min(5, len(payload["top_k_by_effective_score"]))], start=1):
        print(
            f"  #{i} score={c['effective_score']:.6f} cost={c['tour_cost']:.6f} "
            f"root={c['root_distance']:.6f} assoc={c['assoc_term']:.6f} tau={c['tau_term']:.6f} "
            f"step={c['step']} tour={c['tour']}"
        )
    print(
        f"first_sat_stop={payload['first_sat_stop']} triggered={payload['first_sat_triggered']} "
        f"step={payload['first_sat_step']}"
    )
    if payload["optimizer"] in {
        "anchored-intercept",
        "recursive-intercept",
        "reverse-flip-prune",
        "iterative-peel-anneal",
    }:
        print(
            f"intercept_pairs_tested={payload['intercept_pairs_tested']} "
            f"intercept_hits={payload['intercept_hits']}"
        )
    if payload["optimizer"] in {"recursive-intercept", "reverse-flip-prune", "iterative-peel-anneal"}:
        print(
            f"recursive_levels={payload['recursive_levels_visited']} "
            f"poles_expanded={payload['recursive_poles_expanded']}"
        )
        if payload["hybrid_anchor_refine"]:
            print(
                f"hybrid_pairs_used={payload['hybrid_pairs_used']} "
                f"hybrid_rerank_top_m={payload['hybrid_rerank_top_m']} "
                f"blend=({payload['hybrid_blend_effective']:.2f},{payload['hybrid_blend_cost']:.2f})"
            )
    if payload["optimizer"] in {"reverse-flip-prune", "iterative-peel-anneal"}:
        print(
            f"reverse_rounds_used={payload['reverse_rounds_used']} "
            f"reverse_overlap_keep={payload['reverse_overlap_keep']:.3f}"
        )
        print(
            f"rapidity_prune={payload['rapidity_prune']} "
            f"scale=({payload['rapidity_prune_scale_mode']}:"
            f"{payload['rapidity_prune_scale_effective']:.3f}) "
            f"cosh(beta={payload['rapidity_prune_cosh_beta']:.3f},"
            f"strength={payload['rapidity_prune_cosh_strength']:.3f}) "
            f"dominated_edges={payload['rapidity_dominated_edge_count']} "
            f"candidates_pruned={payload['rapidity_pruned_candidates']}"
        )
        print(
            f"binary_prune_boundary={payload['binary_prune_boundary']} "
            f"exact_check_used={payload['binary_exact_check_used']} "
            f"active={payload['binary_prune_boundary_active']} "
            f"unit_cycle_witness={payload['binary_unit_cycle_witness_found']} "
            f"binary_pruned={payload['binary_pruned_candidates']}"
        )
        print(
            f"orthogonal_prune_boundary={payload['orthogonal_prune_boundary']} "
            f"lb={payload['orthogonal_lb']:.6f} "
            f"alpha_floor={payload['orthogonal_alpha_floor']:.3f} "
            f"orth_pruned={payload['orthogonal_pruned_candidates']}"
        )
        history = payload["reverse_bad_mass_history"]
        if history:
            first_before, _ = history[0]
            _, last_after = history[-1]
            print(f"reverse_bad_mass(before->after)={first_before:.6f}->{last_after:.6f}")
    if payload["optimizer"] == "iterative-peel-anneal":
        print(
            f"iterative(rounds={payload['iterative_rounds']}, "
            f"start_arity={payload['iterative_arity_start']}, "
            f"stage_topk={payload['iterative_stage_topk']}, "
            f"early_stop_patience={payload['iterative_early_stop_patience']}, "
            f"tol={payload['iterative_early_stop_tol']:.2e})"
        )
        print(
            f"anneal_rapidity_barrier={payload['anneal_rapidity_barrier']} "
            f"strength={payload['anneal_barrier_strength']:.3f} "
            f"window={payload['anneal_rapidity_window']} "
            f"weight={payload['anneal_rapidity_weight']:.3f} "
            f"jitter_weight={payload['anneal_rapidity_jitter_weight']:.3f} "
            f"shell_width={payload['anneal_shell_width']:.3f} "
            f"shell_keep={payload['anneal_shell_keep_per_band']}"
        )
        print(
            f"iterative_executed={payload['iterative_rounds_executed']} "
            f"early_stopped={payload['iterative_early_stopped']}"
        )
        trace = payload["iterative_trace"]
        for row in trace[: min(6, len(trace))]:
            print(
                f"  round={row['round']} k={row['k_arity']} scale={row['scale_effective']:.3f} "
                f"sampled={row['sampled']} best_cost={row['best_cost']:.6f}"
            )
        btrace = payload["iterative_barrier_trace"]
        for row in btrace[: min(4, len(btrace))]:
            print(
                f"  barrier_round={row['round']} barrier={row['barrier_cost']:.6f} "
                f"peel_best={row['peel_best_cost']:.6f} peel_scale_mean={row['peel_scale_mean']:.3f} "
                f"pruned={row['pruned']}"
            )
    if "exact_optimal_cost" in payload:
        print(
            f"exact_optimal_cost={payload['exact_optimal_cost']:.6f} "
            f"gap(best/effective/root)=({payload['gap_best_cost']:.6f}, "
            f"{payload['gap_best_effective']:.6f}, {payload['gap_best_root']:.6f})"
        )


if __name__ == "__main__":
    main()

