#!/usr/bin/env python3
"""
Rapidity-first ATSP oracle (research-first prototype).

This script reorganizes the directed-torus ATSP search around a monotone
rapidity ladder inspired by the Lean rapidity / patch-parameter story:

- shells are traversed in monotone rapidity order;
- each shell emits a finite periodic slot family;
- optional neighborhood expansion probes nearby phase slots;
- OSHoracle-style "flip" pruning keeps candidates whose support changed from the
  previous shell snapshot;
- optional lightweight local completion improves top shell seeds.

It is explicitly heuristic and intended for ablation-heavy research work.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Any

from directed_torus_atsp_oracle import (
    DirectedTorusCandidate,
    ScoreContext,
    candidate_from_t,
    closed_tour_cost,
    compute_node_tilts,
    compute_tau_term,
    dedupe_by_code_keep_best,
    dynamic_assoc_weight_from_matrix,
    exact_atsp_small,
    global_lower_bound_atsp,
    keep_top_per_rapidity_shell,
    matrix_asymmetry,
    mean_edge_cost,
    min_subpath_rapidity,
    octonion_associator_like,
    orthogonal_soft_boundary,
    permutation_to_factoradic_code,
    rapidity_alpha_from_scale,
    rapidity_delta,
    rapidity_dominated_edges,
    rapidity_shell_id,
    random_asymmetric_matrix,
    resolve_rapidity_prune_scale,
    subpath_rapidity_jitter,
    validate_distance_matrix,
)

PHI = (1.0 + math.sqrt(5.0)) / 2.0
GOLDEN_ANGLE = 2.0 * math.pi / (PHI**2)


@dataclass
class RapidityResearchCandidate(DirectedTorusCandidate):
    shell_step: int = 0
    slot_index: int = 0
    shell_phase: float = 0.0
    slot_phase: float = 0.0
    research_score: float = 0.0
    flip_changed: bool = False
    local_search_gain: float = 0.0
    local_search_rounds: int = 0


@dataclass(frozen=True)
class LocalSearchCacheEntry:
    tour: tuple[int, ...]
    cost: float
    assoc_term: float
    tau_term: float
    permutation_code: int
    gain: float


def build_score_context(
    dist: list[list[float]],
    *,
    k_arity: int | None,
    assoc_weight: float | None,
    tau_mode: str,
    tau_weight: float,
    arc_scale: float,
    geometry: str,
) -> tuple[ScoreContext, float]:
    n = len(dist)
    k = k_arity if k_arity is not None else n
    k = max(1, k)
    arc_length = (math.pi / (2.0 * float(k))) * arc_scale
    assoc_weight_effective = dynamic_assoc_weight_from_matrix(dist) if assoc_weight is None else assoc_weight
    asymmetry = matrix_asymmetry(dist)
    edge_mean = mean_edge_cost(dist)
    node_skew_norm, node_scale_norm = compute_node_tilts(dist)
    mean_skew = sum(node_skew_norm) / float(max(1, len(node_skew_norm)))
    flow_anchor_u = (0.5 + 0.20 * math.tanh(mean_skew)) % 1.0
    flow_anchor_v = (0.5 + 0.30 * math.tanh(asymmetry)) % 1.0
    ctx = ScoreContext(
        dist=dist,
        n=n,
        k=k,
        arc_length=arc_length,
        perm_space=math.factorial(n),
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
        roughness_mode="off",
        roughness_eps=0.0,
        rough_slope_weight=0.0,
        rough_curvature_weight=0.0,
        rough_jump_weight=0.0,
    )
    return ctx, assoc_weight_effective


def omega_weight(shell_step: int, mode: str, k_arity: int) -> float:
    s = float(shell_step + 1)
    if mode == "unit":
        return 1.0
    if mode == "reciprocal":
        return 1.0 / s
    if mode == "sqrt-reciprocal":
        return 1.0 / math.sqrt(s)
    if mode == "log-reciprocal":
        return 1.0 / max(1.0, math.log(s + 1.0))
    if mode == "one-over-k":
        return 1.0 / float(max(1, k_arity))
    if mode == "root-scale":
        return s ** (-1.0 / float(max(1, k_arity)))
    raise ValueError(f"unknown omega mode: {mode}")


def shell_neighborhood_scale(shell_step: int, mode: str, base_scale: float) -> float:
    s = float(shell_step + 1)
    if mode == "constant":
        return base_scale
    if mode == "reciprocal":
        return base_scale / s
    if mode == "sqrt-reciprocal":
        return base_scale / math.sqrt(s)
    raise ValueError(f"unknown neighborhood mode: {mode}")


def unique_phases(phases: list[float]) -> list[float]:
    out: list[float] = []
    seen: set[float] = set()
    tau = 2.0 * math.pi
    for phase in phases:
        wrapped = phase % tau
        key = round(wrapped, 12)
        if key in seen:
            continue
        seen.add(key)
        out.append(wrapped)
    return out


def shell_slot_phases(
    base_phase: float,
    *,
    slots_per_shell: int,
    slot_family: str,
) -> list[float]:
    tau = 2.0 * math.pi
    k = max(1, slots_per_shell)
    periodic = [base_phase + tau * float(j) / float(k) for j in range(k)]
    one_over_k = [base_phase / float(k) + tau * float(j) / float(k) for j in range(k)]
    reflected = [-base_phase + tau * float(j) / float(k) for j in range(k)]
    if slot_family == "periodic":
        return unique_phases(periodic)
    if slot_family == "one-over-k":
        return unique_phases(one_over_k)
    if slot_family == "reflected":
        return unique_phases(periodic + reflected)
    if slot_family == "hybrid":
        return unique_phases(periodic + reflected + one_over_k)
    raise ValueError(f"unknown slot family: {slot_family}")


def phase_to_t(phase: float, arc_length: float) -> float:
    if arc_length <= 0:
        return 0.0
    frac = ((phase / (2.0 * math.pi)) % 1.0)
    return frac * arc_length


def shell_flip_codes(before_codes: set[int], after_codes: set[int]) -> set[int]:
    return (before_codes - after_codes) | (after_codes - before_codes)


def promote_candidate(
    base: DirectedTorusCandidate,
    *,
    shell_step: int,
    slot_index: int,
    shell_phase: float,
    slot_phase: float,
) -> RapidityResearchCandidate:
    return RapidityResearchCandidate(
        step=base.step,
        seed_idx=base.seed_idx,
        u=base.u,
        v=base.v,
        root_distance=base.root_distance,
        permutation_code=base.permutation_code,
        tour=list(base.tour),
        tour_cost=base.tour_cost,
        assoc_term=base.assoc_term,
        tau_term=base.tau_term,
        rough_slope=base.rough_slope,
        rough_curvature=base.rough_curvature,
        rough_jump=base.rough_jump,
        effective_score=base.effective_score,
        rapidity_term=base.rapidity_term,
        rapidity_jitter=base.rapidity_jitter,
        rapidity_shell=base.rapidity_shell,
        shell_step=shell_step,
        slot_index=slot_index,
        shell_phase=shell_phase,
        slot_phase=slot_phase,
        research_score=0.0,
        flip_changed=False,
        local_search_gain=0.0,
        local_search_rounds=0,
    )


def attach_rapidity_metrics(
    c: RapidityResearchCandidate,
    *,
    dist: list[list[float]],
    shell_width: float,
    rapidity_window: int,
    research_weight_rapidity: float,
    research_weight_jitter: float,
    research_weight_effective: float,
    research_weight_cost: float,
    flip_bonus: float,
    edge_mean: float,
    metric_cache: dict[int, tuple[float, float, int]] | None = None,
) -> RapidityResearchCandidate:
    metric_key = c.permutation_code
    cached = metric_cache.get(metric_key) if metric_cache is not None else None
    if cached is None:
        rapidity_term = min_subpath_rapidity(c.tour, dist, window=rapidity_window)
        rapidity_jitter = subpath_rapidity_jitter(c.tour, dist, window=rapidity_window)
        rapidity_shell = rapidity_shell_id(rapidity_term, shell_width)
        cached = (rapidity_term, rapidity_jitter, rapidity_shell)
        if metric_cache is not None:
            metric_cache[metric_key] = cached
    c.rapidity_term, c.rapidity_jitter, c.rapidity_shell = cached
    rapidity_norm = c.rapidity_term / max(1e-9, edge_mean)
    jitter_norm = c.rapidity_jitter / max(1e-9, edge_mean)
    cost_norm = c.tour_cost / (len(c.tour) * max(1e-9, edge_mean))
    c.research_score = (
        research_weight_rapidity * rapidity_norm
        + research_weight_jitter * jitter_norm
        + research_weight_effective * c.effective_score
        + research_weight_cost * cost_norm
        - (flip_bonus if c.flip_changed else 0.0)
    )
    return c


def candidate_priority(c: RapidityResearchCandidate) -> tuple[float, ...]:
    return (
        float(c.rapidity_shell),
        0.0 if c.flip_changed else 1.0,
        c.rapidity_term,
        c.rapidity_jitter,
        c.research_score,
        c.tour_cost,
    )


def rebuild_after_tour_edit(
    c: RapidityResearchCandidate,
    *,
    tour: list[int],
    ctx: ScoreContext,
    cost: float | None = None,
    assoc_term: float | None = None,
    tau_term: float | None = None,
    permutation_code: int | None = None,
) -> RapidityResearchCandidate:
    if cost is None:
        cost = closed_tour_cost(ctx.dist, tour)
    if assoc_term is None:
        assoc_term = octonion_associator_like(tour, ctx.dist)
    if tau_term is None:
        tau_term = compute_tau_term(ctx.tau_mode, tour, ctx.dist, assoc_term)
    if permutation_code is None:
        permutation_code = permutation_to_factoradic_code(tour)
    cost_norm = cost / (ctx.n * max(1e-9, ctx.mean_edge_cost))
    assoc_norm = assoc_term / (1.0 + abs(assoc_term))
    tau_norm = tau_term / (1.0 + abs(tau_term))
    effective = c.root_distance + cost_norm + ctx.assoc_weight * assoc_norm + ctx.tau_weight * tau_norm
    return RapidityResearchCandidate(
        step=c.step,
        seed_idx=c.seed_idx,
        u=c.u,
        v=c.v,
        root_distance=c.root_distance,
        permutation_code=permutation_code,
        tour=tour,
        tour_cost=cost,
        assoc_term=assoc_term,
        tau_term=tau_term,
        rough_slope=0.0,
        rough_curvature=0.0,
        rough_jump=0.0,
        effective_score=effective,
        rapidity_term=c.rapidity_term,
        rapidity_jitter=c.rapidity_jitter,
        rapidity_shell=c.rapidity_shell,
        shell_step=c.shell_step,
        slot_index=c.slot_index,
        shell_phase=c.shell_phase,
        slot_phase=c.slot_phase,
        research_score=c.research_score,
        flip_changed=c.flip_changed,
        local_search_gain=c.local_search_gain,
        local_search_rounds=c.local_search_rounds,
    )


def directed_two_opt_best(tour: list[int], dist: list[list[float]]) -> tuple[list[int], float]:
    return directed_two_opt_best_bounded(tour, dist, span_cap=0)


def directed_two_opt_best_bounded(
    tour: list[int],
    dist: list[list[float]],
    *,
    span_cap: int = 0,
) -> tuple[list[int], float]:
    best_tour = tour[:]
    best_cost = closed_tour_cost(dist, best_tour)
    n = len(tour)
    if n < 4:
        return best_tour, best_cost
    improved = True
    while improved:
        improved = False
        for i in range(n - 1):
            j_hi = n if span_cap <= 0 else min(n, i + 1 + max(2, span_cap))
            for j in range(i + 2, j_hi):
                if i == 0 and j == n - 1:
                    continue
                cand = best_tour[: i + 1] + list(reversed(best_tour[i + 1 : j + 1])) + best_tour[j + 1 :]
                cost = closed_tour_cost(dist, cand)
                if cost + 1e-12 < best_cost:
                    best_tour = cand
                    best_cost = cost
                    improved = True
                    break
            if improved:
                break
    return best_tour, best_cost


def directed_relocate_best(
    tour: list[int],
    dist: list[list[float]],
    *,
    move_cap: int = 0,
) -> tuple[list[int], float]:
    best_tour = tour[:]
    best_cost = closed_tour_cost(dist, best_tour)
    n = len(tour)
    for i in range(n):
        j_lo = 0 if move_cap <= 0 else max(0, i - move_cap)
        j_hi = n if move_cap <= 0 else min(n, i + move_cap + 1)
        for j in range(j_lo, j_hi):
            if i == j:
                continue
            base = best_tour[:]
            node = base.pop(i)
            base.insert(j, node)
            cost = closed_tour_cost(dist, base)
            if cost + 1e-12 < best_cost:
                best_tour = base
                best_cost = cost
    return best_tour, best_cost


def locally_complete_candidate(
    c: RapidityResearchCandidate,
    *,
    ctx: ScoreContext,
    mode: str,
    rounds: int,
    local_search_cache: dict[tuple[int, str, int], LocalSearchCacheEntry] | None = None,
    two_opt_span_cap: int = 0,
    relocate_move_cap: int = 0,
) -> RapidityResearchCandidate:
    if mode == "off":
        return c
    cache_key = (
        c.permutation_code,
        mode,
        max(1, rounds),
        max(0, two_opt_span_cap),
        max(0, relocate_move_cap),
    )
    cached = local_search_cache.get(cache_key) if local_search_cache is not None else None
    if cached is not None:
        out = rebuild_after_tour_edit(
            c,
            tour=list(cached.tour),
            ctx=ctx,
            cost=cached.cost,
            assoc_term=cached.assoc_term,
            tau_term=cached.tau_term,
            permutation_code=cached.permutation_code,
        )
        out.local_search_gain = cached.gain
        out.local_search_rounds = max(1, rounds)
        return out
    cur = c
    base_cost = c.tour_cost
    for _ in range(max(1, rounds)):
        if mode in {"2opt", "both"}:
            tour_2opt, cost_2opt = directed_two_opt_best_bounded(
                cur.tour,
                ctx.dist,
                span_cap=two_opt_span_cap,
            )
            if cost_2opt + 1e-12 < cur.tour_cost:
                cur = rebuild_after_tour_edit(cur, tour=tour_2opt, ctx=ctx)
        if mode in {"relocate", "both"}:
            tour_reloc, cost_reloc = directed_relocate_best(
                cur.tour,
                ctx.dist,
                move_cap=relocate_move_cap,
            )
            if cost_reloc + 1e-12 < cur.tour_cost:
                cur = rebuild_after_tour_edit(cur, tour=tour_reloc, ctx=ctx)
    cur.local_search_gain = max(0.0, base_cost - cur.tour_cost)
    cur.local_search_rounds = max(1, rounds)
    if local_search_cache is not None:
        local_search_cache[cache_key] = LocalSearchCacheEntry(
            tour=tuple(cur.tour),
            cost=cur.tour_cost,
            assoc_term=cur.assoc_term,
            tau_term=cur.tau_term,
            permutation_code=cur.permutation_code,
            gain=cur.local_search_gain,
        )
    return cur


def spectral_peaks(series: list[float], top_k: int) -> list[dict[str, float]]:
    if len(series) < 4:
        return []
    out: list[dict[str, float]] = []
    n = len(series)
    mean = sum(series) / float(n)
    centered = [x - mean for x in series]
    max_freq = max(1, n // 2)
    for freq in range(1, max_freq + 1):
        re = 0.0
        im = 0.0
        for idx, val in enumerate(centered):
            angle = 2.0 * math.pi * float(freq * idx) / float(n)
            re += val * math.cos(angle)
            im -= val * math.sin(angle)
        amp = math.sqrt(re * re + im * im) / float(n)
        out.append({"frequency": float(freq), "amplitude": amp, "period": float(n) / float(freq)})
    out.sort(key=lambda row: row["amplitude"], reverse=True)
    return out[: max(1, top_k)]


def rapidity_first_solver(
    dist: list[list[float]],
    *,
    top_k: int = 8,
    assoc_weight: float | None = None,
    tau_mode: str = "off",
    tau_weight: float = 0.0,
    k_arity: int | None = None,
    arc_scale: float = 1.0,
    geometry: str = "oblique",
    shell_count: int = 24,
    shell_phase_scale: float = 1.0,
    shell_phase_stride: float = 1.0,
    omega_mode: str = "unit",
    slots_per_shell: int = 8,
    slot_family: str = "hybrid",
    neighborhood_offsets: int = 1,
    neighborhood_mode: str = "reciprocal",
    neighborhood_scale: float = 0.35,
    rapidity_window: int = 4,
    rapidity_shell_width: float = 0.25,
    keep_per_shell: int = 4,
    pool_limit: int = 64,
    pool_keep_per_band: int = 0,
    flip_prune: bool = True,
    local_search_mode: str = "off",
    local_search_topk: int = 2,
    local_search_rounds: int = 1,
    local_search_two_opt_span_cap: int = 0,
    local_search_relocate_move_cap: int = 0,
    rapidity_prune: bool = False,
    rapidity_prune_scale: float = 1.0,
    rapidity_prune_scale_mode: str = "sqrt-n-over-arity",
    rapidity_prune_cosh_beta: float = 2.0,
    rapidity_prune_cosh_strength: float = 0.35,
    orthogonal_boundary: bool = False,
    orthogonal_alpha_floor: float = 0.25,
    research_weight_rapidity: float = 1.0,
    research_weight_jitter: float = 0.30,
    research_weight_effective: float = 0.20,
    research_weight_cost: float = 0.10,
    flip_bonus: float = 0.10,
    spectral_topk: int = 4,
) -> dict[str, Any]:
    validate_distance_matrix(dist)
    ctx, assoc_weight_effective = build_score_context(
        dist,
        k_arity=k_arity,
        assoc_weight=assoc_weight,
        tau_mode=tau_mode,
        tau_weight=tau_weight,
        arc_scale=arc_scale,
        geometry=geometry,
    )
    n = ctx.n
    edge_mean = ctx.mean_edge_cost
    orthogonal_lb = global_lower_bound_atsp(dist)
    rapidity_prune_scale_effective = resolve_rapidity_prune_scale(
        mode=rapidity_prune_scale_mode,
        base_scale=rapidity_prune_scale,
        n=n,
        arity=ctx.k,
        cosh_beta=rapidity_prune_cosh_beta,
        cosh_strength=rapidity_prune_cosh_strength,
    )
    dominated_edges = (
        rapidity_dominated_edges(
            dist=dist,
            rapidity_du=rapidity_delta(n * n),
            rapidity_dv=rapidity_delta(n * n * 2),
            mean_edge=edge_mean,
            scale=rapidity_prune_scale_effective,
        )
        if rapidity_prune
        else set()
    )

    phase_accum = 0.0
    prev_codes: set[int] = set()
    pool: list[RapidityResearchCandidate] = []
    shell_trace: list[dict[str, Any]] = []
    shell_best_cost_series: list[float] = []
    flip_kept_total = 0
    rapidity_pruned_candidates = 0
    metric_cache: dict[int, tuple[float, float, int]] = {}
    local_search_cache: dict[tuple[int, str, int], LocalSearchCacheEntry] = {}

    for shell_step in range(max(1, shell_count)):
        omega = omega_weight(shell_step, omega_mode, ctx.k)
        phase_step = shell_phase_scale * shell_phase_stride * omega * rapidity_delta(n * n)
        phase_accum += phase_step
        slot_phases = shell_slot_phases(
            phase_accum,
            slots_per_shell=slots_per_shell,
            slot_family=slot_family,
        )
        shell_candidates: list[RapidityResearchCandidate] = []
        local_scale = shell_neighborhood_scale(shell_step, neighborhood_mode, neighborhood_scale)

        for slot_index, slot_phase in enumerate(slot_phases):
            probe_phases = [slot_phase]
            for off in range(1, max(0, neighborhood_offsets) + 1):
                delta = local_scale * float(off) * rapidity_delta(n * n)
                probe_phases.append(slot_phase + delta)
                probe_phases.append(slot_phase - delta)
            for probe_phase in unique_phases(probe_phases):
                t = phase_to_t(probe_phase, ctx.arc_length)
                base = candidate_from_t(t, ctx, step=shell_step, seed_idx=slot_index % 3)
                cand = promote_candidate(
                    base,
                    shell_step=shell_step,
                    slot_index=slot_index,
                    shell_phase=phase_accum,
                    slot_phase=probe_phase,
                )
                shell_candidates.append(cand)

        shell_candidates = dedupe_by_code_keep_best(shell_candidates)  # type: ignore[assignment]
        shell_codes = {c.permutation_code for c in shell_candidates}
        flipped_codes = shell_flip_codes(prev_codes, shell_codes)

        enriched: list[RapidityResearchCandidate] = []
        for cand in shell_candidates:
            cand.flip_changed = cand.permutation_code in flipped_codes
            cand = attach_rapidity_metrics(
                cand,
                dist=dist,
                shell_width=rapidity_shell_width,
                rapidity_window=rapidity_window,
                research_weight_rapidity=research_weight_rapidity,
                research_weight_jitter=research_weight_jitter,
                research_weight_effective=research_weight_effective,
                research_weight_cost=research_weight_cost,
                flip_bonus=flip_bonus,
                edge_mean=edge_mean,
                metric_cache=metric_cache,
            )
            enriched.append(cand)
        shell_candidates = sorted(enriched, key=candidate_priority)

        if rapidity_prune and dominated_edges:
            best_shell = shell_candidates[0] if shell_candidates else None
            kept_shell: list[RapidityResearchCandidate] = []
            for cand in shell_candidates:
                uses_dominated = any(
                    (cand.tour[i], cand.tour[(i + 1) % len(cand.tour)]) in dominated_edges
                    for i in range(len(cand.tour))
                )
                if not uses_dominated or (best_shell is not None and cand.permutation_code == best_shell.permutation_code):
                    kept_shell.append(cand)
                else:
                    rapidity_pruned_candidates += 1
            shell_candidates = kept_shell

        if flip_prune and shell_candidates:
            best_shell = shell_candidates[0]
            flip_kept = [c for c in shell_candidates if c.flip_changed]
            if flip_kept:
                shell_candidates = flip_kept
                flip_kept_total += len(flip_kept)
            else:
                shell_candidates = [best_shell]

        shell_candidates = sorted(shell_candidates, key=candidate_priority)

        if local_search_mode != "off" and shell_candidates:
            improved: list[RapidityResearchCandidate] = []
            limit = min(max(1, local_search_topk), len(shell_candidates))
            for idx, cand in enumerate(shell_candidates):
                if idx < limit:
                    cand = locally_complete_candidate(
                        cand,
                        ctx=ctx,
                        mode=local_search_mode,
                        rounds=local_search_rounds,
                        local_search_cache=local_search_cache,
                        two_opt_span_cap=local_search_two_opt_span_cap,
                        relocate_move_cap=local_search_relocate_move_cap,
                    )
                    cand = attach_rapidity_metrics(
                        cand,
                        dist=dist,
                        shell_width=rapidity_shell_width,
                        rapidity_window=rapidity_window,
                        research_weight_rapidity=research_weight_rapidity,
                        research_weight_jitter=research_weight_jitter,
                        research_weight_effective=research_weight_effective,
                        research_weight_cost=research_weight_cost,
                        flip_bonus=flip_bonus,
                        edge_mean=edge_mean,
                        metric_cache=metric_cache,
                    )
                improved.append(cand)
            shell_candidates = sorted(improved, key=candidate_priority)

        if orthogonal_boundary and shell_candidates:
            best_cost = min(c.tour_cost for c in shell_candidates)
            alpha = rapidity_alpha_from_scale(
                rapidity_prune_scale_effective,
                n,
                alpha_floor=orthogonal_alpha_floor,
            )
            bound = orthogonal_soft_boundary(orthogonal_lb, best_cost, alpha)
            best_shell = min(shell_candidates, key=lambda c: c.tour_cost)
            bounded = [c for c in shell_candidates if c.tour_cost <= bound + 1e-9]
            if all(c.permutation_code != best_shell.permutation_code for c in bounded):
                bounded.append(best_shell)
            shell_candidates = sorted(bounded, key=candidate_priority)
        else:
            bound = math.inf
            alpha = 1.0

        if keep_per_shell > 0:
            shell_candidates = shell_candidates[:keep_per_shell]

        pool = dedupe_by_code_keep_best(pool + shell_candidates)  # type: ignore[assignment]
        if pool_keep_per_band > 0:
            pool = keep_top_per_rapidity_shell(pool, pool_keep_per_band)  # type: ignore[assignment]
        pool = sorted(pool, key=candidate_priority)[: max(1, pool_limit)]
        prev_codes = {c.permutation_code for c in shell_candidates}

        shell_best_cost = min((c.tour_cost for c in shell_candidates), default=math.inf)
        shell_best_cost_series.append(shell_best_cost if math.isfinite(shell_best_cost) else 0.0)
        shell_trace.append(
            {
                "shell_step": shell_step,
                "omega": omega,
                "phase_step": phase_step,
                "shell_phase": phase_accum,
                "slot_count": len(slot_phases),
                "candidates_before_prune": len(shell_codes),
                "candidates_after_prune": len(shell_candidates),
                "flipped_codes": len(flipped_codes),
                "best_shell_cost": shell_best_cost,
                "best_shell_rapidity": shell_candidates[0].rapidity_term if shell_candidates else math.inf,
                "best_shell_jitter": shell_candidates[0].rapidity_jitter if shell_candidates else math.inf,
                "orthogonal_alpha": alpha,
                "orthogonal_bound": bound,
            }
        )

    if not pool:
        return {
            "n_cities": n,
            "candidates": [],
            "unique_tours_sampled": 0,
            "tour_space_size": ctx.perm_space,
            "coverage_ratio": 0.0,
            "optimizer": "rapidity-first-shells",
        }

    by_cost = sorted(pool, key=lambda c: (c.tour_cost, c.rapidity_term, c.rapidity_jitter))
    by_research = sorted(pool, key=candidate_priority)
    by_rapidity = sorted(pool, key=lambda c: (c.rapidity_term, c.rapidity_jitter, c.tour_cost))
    return {
        "n_cities": n,
        "optimizer": "rapidity-first-shells",
        "unique_tours_sampled": len(pool),
        "tour_space_size": ctx.perm_space,
        "coverage_ratio": len(pool) / float(ctx.perm_space),
        "assoc_weight": assoc_weight_effective,
        "matrix_asymmetry": ctx.asymmetry,
        "tau_mode": tau_mode,
        "tau_weight": tau_weight,
        "k_arity": ctx.k,
        "narrow_arc_length": ctx.arc_length,
        "arc_scale": arc_scale,
        "geometry": geometry,
        "shell_count": shell_count,
        "shell_phase_scale": shell_phase_scale,
        "shell_phase_stride": shell_phase_stride,
        "omega_mode": omega_mode,
        "slots_per_shell": slots_per_shell,
        "slot_family": slot_family,
        "neighborhood_offsets": neighborhood_offsets,
        "neighborhood_mode": neighborhood_mode,
        "neighborhood_scale": neighborhood_scale,
        "rapidity_window": rapidity_window,
        "rapidity_shell_width": rapidity_shell_width,
        "keep_per_shell": keep_per_shell,
        "pool_limit": pool_limit,
        "pool_keep_per_band": pool_keep_per_band,
        "flip_prune": flip_prune,
        "flip_kept_total": flip_kept_total,
        "local_search_mode": local_search_mode,
        "local_search_topk": local_search_topk,
        "local_search_rounds": local_search_rounds,
        "local_search_two_opt_span_cap": local_search_two_opt_span_cap,
        "local_search_relocate_move_cap": local_search_relocate_move_cap,
        "rapidity_prune": rapidity_prune,
        "rapidity_prune_scale": rapidity_prune_scale,
        "rapidity_prune_scale_mode": rapidity_prune_scale_mode,
        "rapidity_prune_scale_effective": rapidity_prune_scale_effective,
        "rapidity_prune_cosh_beta": rapidity_prune_cosh_beta,
        "rapidity_prune_cosh_strength": rapidity_prune_cosh_strength,
        "rapidity_dominated_edge_count": len(dominated_edges),
        "rapidity_pruned_candidates": rapidity_pruned_candidates,
        "orthogonal_boundary": orthogonal_boundary,
        "orthogonal_alpha_floor": orthogonal_alpha_floor,
        "orthogonal_lb": orthogonal_lb,
        "research_weight_rapidity": research_weight_rapidity,
        "research_weight_jitter": research_weight_jitter,
        "research_weight_effective": research_weight_effective,
        "research_weight_cost": research_weight_cost,
        "flip_bonus": flip_bonus,
        "shell_trace": shell_trace,
        "spectral_peaks": spectral_peaks(shell_best_cost_series, spectral_topk),
        "best_by_cost": asdict(by_cost[0]),
        "best_by_research_score": asdict(by_research[0]),
        "best_by_rapidity": asdict(by_rapidity[0]),
        "top_k_by_cost": [asdict(c) for c in by_cost[:top_k]],
        "top_k_by_research_score": [asdict(c) for c in by_research[:top_k]],
        "top_k_by_rapidity": [asdict(c) for c in by_rapidity[:top_k]],
    }


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Rapidity-first ATSP oracle (research prototype)")
    p.add_argument("--matrix-json", type=str, default=None, help="path to square distance matrix JSON")
    p.add_argument("--demo-cities", type=int, default=9, help="city count for random asymmetric demo")
    p.add_argument("--demo-seed", type=int, default=1234, help="seed for random demo matrix")
    p.add_argument("--top-k", type=int, default=8, help="top candidates to report")
    p.add_argument("--assoc-weight", type=float, default=None, help="weight for associator correction")
    p.add_argument("--tau-mode", choices=("off", "cycle", "mod", "assoc"), default="off", help="tau-like feature mode")
    p.add_argument("--tau-weight", type=float, default=0.0, help="tau feature weight")
    p.add_argument("--k-arity", type=int, default=None, help="arity level for narrow-arc chart (default: n)")
    p.add_argument("--arc-scale", type=float, default=1.0, help="multiplier on base arc length pi/(2k)")
    p.add_argument("--geometry", choices=("intrinsic", "oblique"), default="oblique", help="tour decode geometry")
    p.add_argument("--shell-count", type=int, default=24, help="number of rapidity shells to traverse")
    p.add_argument("--shell-phase-scale", type=float, default=1.0, help="global scale on rapidity phase increments")
    p.add_argument("--shell-phase-stride", type=float, default=1.0, help="extra multiplier on per-shell phase increment")
    p.add_argument(
        "--omega-mode",
        choices=("unit", "reciprocal", "sqrt-reciprocal", "log-reciprocal", "one-over-k", "root-scale"),
        default="unit",
        help="positive shell weight used in the monotone rapidity ladder",
    )
    p.add_argument("--slots-per-shell", type=int, default=8, help="periodic slots emitted per shell")
    p.add_argument(
        "--slot-family",
        choices=("periodic", "one-over-k", "reflected", "hybrid"),
        default="hybrid",
        help="periodic slot family used within each shell",
    )
    p.add_argument("--neighborhood-offsets", type=int, default=1, help="extra probe offsets on each side of every slot")
    p.add_argument(
        "--neighborhood-mode",
        choices=("constant", "reciprocal", "sqrt-reciprocal"),
        default="reciprocal",
        help="how local phase probe radius decays with shell depth",
    )
    p.add_argument("--neighborhood-scale", type=float, default=0.35, help="base local probe radius multiplier")
    p.add_argument("--rapidity-window", type=int, default=4, help="window for rapidity/jitter statistics")
    p.add_argument("--rapidity-shell-width", type=float, default=0.25, help="quantization width for rapidity shell IDs")
    p.add_argument("--keep-per-shell", type=int, default=4, help="retain at most this many candidates per shell")
    p.add_argument("--pool-limit", type=int, default=64, help="global retained candidate pool limit")
    p.add_argument("--pool-keep-per-band", type=int, default=0, help="keep at most this many candidates per rapidity band")
    p.add_argument(
        "--flip-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="keep shell candidates whose permutation support flipped vs previous shell snapshot",
    )
    p.add_argument(
        "--local-search-mode",
        choices=("off", "2opt", "relocate", "both"),
        default="off",
        help="lightweight local completion applied to top shell candidates",
    )
    p.add_argument("--local-search-topk", type=int, default=2, help="top shell candidates sent into local completion")
    p.add_argument("--local-search-rounds", type=int, default=1, help="local completion rounds")
    p.add_argument(
        "--local-search-two-opt-span-cap",
        type=int,
        default=0,
        help="max reversal span tested by 2-opt local completion (0 => full search)",
    )
    p.add_argument(
        "--local-search-relocate-move-cap",
        type=int,
        default=0,
        help="max insertion distance tested by relocate local completion (0 => full search)",
    )
    p.add_argument(
        "--rapidity-prune",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="apply rapidity-dominated-edge prune on shell candidates",
    )
    p.add_argument("--rapidity-prune-scale", type=float, default=1.0, help="base rapidity prune scale")
    p.add_argument(
        "--rapidity-prune-scale-mode",
        choices=("fixed", "sqrt-n", "sqrt-n-over-arity", "cosh-arity"),
        default="sqrt-n-over-arity",
        help="policy for rapidity prune scale",
    )
    p.add_argument("--rapidity-prune-cosh-beta", type=float, default=2.0, help="cosh-arity curvature parameter beta")
    p.add_argument("--rapidity-prune-cosh-strength", type=float, default=0.35, help="cosh-arity widening strength")
    p.add_argument(
        "--orthogonal-boundary",
        action=argparse.BooleanOptionalAction,
        default=False,
        help="apply LB/UB orthogonal shell barrier after shell ranking",
    )
    p.add_argument("--orthogonal-alpha-floor", type=float, default=0.25, help="minimum alpha for orthogonal barrier")
    p.add_argument("--research-weight-rapidity", type=float, default=1.0, help="secondary weight on rapidity term")
    p.add_argument("--research-weight-jitter", type=float, default=0.30, help="secondary weight on rapidity jitter")
    p.add_argument("--research-weight-effective", type=float, default=0.20, help="secondary weight on original effective score")
    p.add_argument("--research-weight-cost", type=float, default=0.10, help="secondary weight on normalized tour cost")
    p.add_argument("--flip-bonus", type=float, default=0.10, help="bonus subtracted from research score when a candidate flips support")
    p.add_argument("--spectral-topk", type=int, default=4, help="number of dominant shell-periodicity peaks to report")
    p.add_argument("--exact-if-at-most", type=int, default=9, help="run exact brute-force if n <= threshold")
    p.add_argument("--json", action="store_true", help="emit JSON payload")
    return p


def main() -> None:
    args = build_parser().parse_args()
    if args.demo_cities < 2:
        raise SystemExit("--demo-cities must be >= 2")
    if args.top_k < 1:
        raise SystemExit("--top-k must be >= 1")
    if args.assoc_weight is not None and args.assoc_weight < 0:
        raise SystemExit("--assoc-weight must be >= 0")
    if args.tau_weight < 0:
        raise SystemExit("--tau-weight must be >= 0")
    if args.k_arity is not None and args.k_arity < 1:
        raise SystemExit("--k-arity must be >= 1")
    if args.arc_scale <= 0:
        raise SystemExit("--arc-scale must be > 0")
    if args.shell_count < 1:
        raise SystemExit("--shell-count must be >= 1")
    if args.shell_phase_scale <= 0:
        raise SystemExit("--shell-phase-scale must be > 0")
    if args.shell_phase_stride <= 0:
        raise SystemExit("--shell-phase-stride must be > 0")
    if args.slots_per_shell < 1:
        raise SystemExit("--slots-per-shell must be >= 1")
    if args.neighborhood_offsets < 0:
        raise SystemExit("--neighborhood-offsets must be >= 0")
    if args.neighborhood_scale < 0:
        raise SystemExit("--neighborhood-scale must be >= 0")
    if args.rapidity_window < 1:
        raise SystemExit("--rapidity-window must be >= 1")
    if args.rapidity_shell_width <= 0:
        raise SystemExit("--rapidity-shell-width must be > 0")
    if args.keep_per_shell < 1:
        raise SystemExit("--keep-per-shell must be >= 1")
    if args.pool_limit < 1:
        raise SystemExit("--pool-limit must be >= 1")
    if args.pool_keep_per_band < 0:
        raise SystemExit("--pool-keep-per-band must be >= 0")
    if args.local_search_topk < 1:
        raise SystemExit("--local-search-topk must be >= 1")
    if args.local_search_rounds < 1:
        raise SystemExit("--local-search-rounds must be >= 1")
    if args.local_search_two_opt_span_cap < 0:
        raise SystemExit("--local-search-two-opt-span-cap must be >= 0")
    if args.local_search_relocate_move_cap < 0:
        raise SystemExit("--local-search-relocate-move-cap must be >= 0")
    if args.rapidity_prune_scale <= 0:
        raise SystemExit("--rapidity-prune-scale must be > 0")
    if args.rapidity_prune_cosh_beta < 0:
        raise SystemExit("--rapidity-prune-cosh-beta must be >= 0")
    if args.rapidity_prune_cosh_strength < 0:
        raise SystemExit("--rapidity-prune-cosh-strength must be >= 0")
    if not (0.0 <= args.orthogonal_alpha_floor <= 1.0):
        raise SystemExit("--orthogonal-alpha-floor must be in [0,1]")
    if args.spectral_topk < 1:
        raise SystemExit("--spectral-topk must be >= 1")
    if args.exact_if_at_most < 0:
        raise SystemExit("--exact-if-at-most must be >= 0")

    if args.matrix_json:
        with open(args.matrix_json, "r", encoding="utf-8") as fh:
            dist = json.load(fh)
    else:
        dist = random_asymmetric_matrix(args.demo_cities, args.demo_seed)

    payload = rapidity_first_solver(
        dist=dist,
        top_k=args.top_k,
        assoc_weight=args.assoc_weight,
        tau_mode=args.tau_mode,
        tau_weight=args.tau_weight,
        k_arity=args.k_arity,
        arc_scale=args.arc_scale,
        geometry=args.geometry,
        shell_count=args.shell_count,
        shell_phase_scale=args.shell_phase_scale,
        shell_phase_stride=args.shell_phase_stride,
        omega_mode=args.omega_mode,
        slots_per_shell=args.slots_per_shell,
        slot_family=args.slot_family,
        neighborhood_offsets=args.neighborhood_offsets,
        neighborhood_mode=args.neighborhood_mode,
        neighborhood_scale=args.neighborhood_scale,
        rapidity_window=args.rapidity_window,
        rapidity_shell_width=args.rapidity_shell_width,
        keep_per_shell=args.keep_per_shell,
        pool_limit=args.pool_limit,
        pool_keep_per_band=args.pool_keep_per_band,
        flip_prune=args.flip_prune,
        local_search_mode=args.local_search_mode,
        local_search_topk=args.local_search_topk,
        local_search_rounds=args.local_search_rounds,
        local_search_two_opt_span_cap=args.local_search_two_opt_span_cap,
        local_search_relocate_move_cap=args.local_search_relocate_move_cap,
        rapidity_prune=args.rapidity_prune,
        rapidity_prune_scale=args.rapidity_prune_scale,
        rapidity_prune_scale_mode=args.rapidity_prune_scale_mode,
        rapidity_prune_cosh_beta=args.rapidity_prune_cosh_beta,
        rapidity_prune_cosh_strength=args.rapidity_prune_cosh_strength,
        orthogonal_boundary=args.orthogonal_boundary,
        orthogonal_alpha_floor=args.orthogonal_alpha_floor,
        research_weight_rapidity=args.research_weight_rapidity,
        research_weight_jitter=args.research_weight_jitter,
        research_weight_effective=args.research_weight_effective,
        research_weight_cost=args.research_weight_cost,
        flip_bonus=args.flip_bonus,
        spectral_topk=args.spectral_topk,
    )

    n = payload["n_cities"]
    if n <= args.exact_if_at_most:
        exact_cost, exact_tour = exact_atsp_small(dist)
        payload["exact_optimal_cost"] = exact_cost
        payload["exact_optimal_tour"] = exact_tour
        payload["gap_best_cost"] = payload["best_by_cost"]["tour_cost"] - exact_cost
        payload["gap_best_research"] = payload["best_by_research_score"]["tour_cost"] - exact_cost
        payload["gap_best_rapidity"] = payload["best_by_rapidity"]["tour_cost"] - exact_cost

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print(
        f"n={payload['n_cities']} sampled={payload['unique_tours_sampled']}/{payload['tour_space_size']} "
        f"coverage={payload['coverage_ratio']:.4f} optimizer={payload['optimizer']}"
    )
    print(
        f"k={payload['k_arity']} geometry={payload['geometry']} asym={payload['matrix_asymmetry']:.4f} "
        f"assoc_w={payload['assoc_weight']:.3f} tau_mode={payload['tau_mode']} tau_weight={payload['tau_weight']:.3f}"
    )
    print(
        f"shells={payload['shell_count']} omega={payload['omega_mode']} slots={payload['slots_per_shell']} "
        f"slot_family={payload['slot_family']} flip_prune={payload['flip_prune']} "
        f"local_search={payload['local_search_mode']}"
    )
    best_cost = payload["best_by_cost"]
    best_research = payload["best_by_research_score"]
    best_rapidity = payload["best_by_rapidity"]
    print(f"best_cost={best_cost['tour_cost']:.6f} tour={best_cost['tour']} shell={best_cost['shell_step']}")
    print(
        f"best_research_cost={best_research['tour_cost']:.6f} "
        f"research_score={best_research['research_score']:.6f} "
        f"rapidity={best_research['rapidity_term']:.6f} jitter={best_research['rapidity_jitter']:.6f} "
        f"flip={best_research['flip_changed']} tour={best_research['tour']}"
    )
    print(
        f"best_rapidity_cost={best_rapidity['tour_cost']:.6f} "
        f"rapidity={best_rapidity['rapidity_term']:.6f} jitter={best_rapidity['rapidity_jitter']:.6f} "
        f"tour={best_rapidity['tour']}"
    )
    print(
        f"rapidity_prune={payload['rapidity_prune']} "
        f"scale=({payload['rapidity_prune_scale_mode']}:{payload['rapidity_prune_scale_effective']:.3f}) "
        f"dominated_edges={payload['rapidity_dominated_edge_count']} "
        f"pruned={payload['rapidity_pruned_candidates']}"
    )
    print(
        f"orthogonal_boundary={payload['orthogonal_boundary']} "
        f"lb={payload['orthogonal_lb']:.6f} alpha_floor={payload['orthogonal_alpha_floor']:.3f} "
        f"flip_kept_total={payload['flip_kept_total']}"
    )
    print("top_research_candidates:")
    for row in payload["top_k_by_research_score"][: min(5, len(payload["top_k_by_research_score"]))]:
        print(
            f"  shell={row['shell_step']} slot={row['slot_index']} "
            f"score={row['research_score']:.6f} cost={row['tour_cost']:.6f} "
            f"rapidity={row['rapidity_term']:.6f} jitter={row['rapidity_jitter']:.6f} "
            f"flip={row['flip_changed']} local_gain={row['local_search_gain']:.6f}"
        )
    peaks = payload["spectral_peaks"]
    if peaks:
        print("shell_periodicity_peaks:")
        for peak in peaks:
            print(
                f"  freq={peak['frequency']:.0f} period={peak['period']:.3f} "
                f"amplitude={peak['amplitude']:.6f}"
            )
    for row in payload["shell_trace"][: min(8, len(payload["shell_trace"]))]:
        print(
            f"  shell={row['shell_step']} phase={row['shell_phase']:.6f} "
            f"omega={row['omega']:.6f} slots={row['slot_count']} "
            f"cands={row['candidates_after_prune']} flips={row['flipped_codes']} "
            f"best_cost={row['best_shell_cost']:.6f}"
        )
    if "exact_optimal_cost" in payload:
        print(
            f"exact_optimal_cost={payload['exact_optimal_cost']:.6f} "
            f"gap(best/research/rapidity)=({payload['gap_best_cost']:.6f}, "
            f"{payload['gap_best_research']:.6f}, {payload['gap_best_rapidity']:.6f})"
        )


if __name__ == "__main__":
    main()
