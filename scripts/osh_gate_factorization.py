#!/usr/bin/env python3
"""
OSHoracle-style geometric factorization prototype.

Pipeline per shell step:
expand -> reconstruct -> evolve -> flip -> prune

Registers live in phase-space, candidates are extracted from angle slots on the #Q shell,
and reflected counterparts are co-generated across the doubled-span reflection line.

Q lookup modes
--------------
``flat-reflector`` (default):
  ``q_span(n) = isqrt(n)``.  A gate code maps to slot ``code % doubled_span`` and its
  reflection; each slot maps to ``2 + slot % (q_span - 1)``.  This is a wrapped line
  segment — gate dynamics live in code space but the final lookup on ``q`` is flat.

``hopf-intersection``:
  Each code lifts to a unit quaternion on S³.  The Hopf map yields a base direction on
  S² and an S¹ fiber phase.  Integrable Hopf windings ``w = 1..S`` are activated with
  ``S = min(3, ⌊∛n⌋)`` (TUFT integrability cap at 3; scale from
  ``MonolithicGeometricFactorizer.floorCbrt``).  Each chart projects a slot; candidates
  with chart agreement (intersection votes) are preferred.  Per-step local fiber budget
  is ``≤ 2 * S`` (Lean ``K_exact ≤ 2 * #Q`` with at-most-two intersections per center).

  With ``--hopf-search``, a systematic phase sweep marches the doubled-span q window
  while the gate pipeline runs — a real search rather than a single-step probe.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict
from typing import Any

import geometric_factorization_solver as base

# TUFT integrable torus sectors (HopfShellComplex.lean): windings 1, 2, 3 only.
HOPF_MAX_INTEGRABLE_WINDING: int = 3

Q_LOOKUP_FLAT = "flat-reflector"
Q_LOOKUP_HOPF = "hopf-intersection"
Q_LOOKUP_MODES = (Q_LOOKUP_FLAT, Q_LOOKUP_HOPF)


def floor_cbrt(n: int) -> int:
    """Greatest r ≥ 0 with r³ ≤ n (matches ``MonolithicGeometricFactorizer.floorCbrt``)."""
    if n < 0:
        raise ValueError("floor_cbrt expects n >= 0")
    if n < 2:
        return 0 if n == 0 else 1
    lo, hi = 1, n
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def hopf_shell_bound(n: int) -> int:
    """
    Count ``S`` of S^n Hopf charts to activate: windings ``1..S`` with
    ``S = min(3, max(1, ⌊∛n⌋))``.
    """
    if n <= 1:
        return 1
    return min(HOPF_MAX_INTEGRABLE_WINDING, max(1, floor_cbrt(n)))


def active_hopf_windings(n: int) -> tuple[int, ...]:
    """Integrable winding labels ``1..S`` for composite ``n``."""
    s = hopf_shell_bound(n)
    return tuple(range(1, s + 1))


def k_exact_per_center_bound(shell_count: int) -> int:
    """Lean ``K_exactUnionCard ≤ 2 * |Q|`` with ≤2 local intersections per center → ``2 * S`` charts."""
    return 2 * max(1, shell_count)


def q_span(n: int) -> int:
    return max(1, math.isqrt(max(1, n)))


def q_window_candidate_values(n: int) -> list[int]:
    """All distinct factor candidates in ``[2, q_span(n)]``."""
    root = q_span(n)
    if root <= 1:
        return [2]
    return list(range(2, root + 1))


# Full q-window exhaustion is only feasible for modest ``q_span`` (medium corpora).
MAX_Q_WINDOW_EXHAUST = 512


def should_exhaust_q_window(n: int) -> bool:
    return q_span(n) <= MAX_Q_WINDOW_EXHAUST


def reflection_slot(slot: int, span: int) -> int:
    m = max(1, span)
    return (m - 1 - (slot % m)) % m


def slot_to_candidate(slot: int, n: int) -> int:
    q = q_span(n)
    if q <= 1:
        return 2
    return 2 + (slot % (q - 1))


def code_to_unit_quaternion(code: int, register_bits: int) -> tuple[float, float, float, float]:
    """
    Deterministic lift of a register code to a unit quaternion (w, x, y, z) on S³.

    Four bit-segments of the masked code are mapped to [-1, 1] and normalized.
    """
    if register_bits <= 0:
        return (1.0, 0.0, 0.0, 0.0)
    mask = (1 << register_bits) - 1
    c = code & mask
    seg = max(1, register_bits // 4)
    comps: list[float] = []
    for i in range(4):
        shift = i * seg
        chunk = (c >> shift) & ((1 << seg) - 1)
        denom = max(1, (1 << seg) - 1)
        comps.append(2.0 * (chunk / float(denom)) - 1.0)
    w, x, y, z = comps
    norm = math.sqrt(w * w + x * x + y * y + z * z)
    if norm <= 0.0:
        return (1.0, 0.0, 0.0, 0.0)
    return (w / norm, x / norm, y / norm, z / norm)


def hopf_map_s3_to_s2(w: float, x: float, y: float, z: float) -> tuple[float, float, float]:
    """
    Standard Hopf fibration S³ → S² for unit quaternion (w, x, y, z).

    Base point on S² (not necessarily normalized to unit length; direction suffices).
    """
    return (
        w * w + x * x - y * y - z * z,
        2.0 * (w * z + x * y),
        2.0 * (y * z - w * x),
    )


def hopf_fiber_phase(w: float, x: float, y: float, z: float) -> float:
    """S¹ fiber coordinate associated with the Hopf lift."""
    return math.atan2(2.0 * (w * y - x * z), w * w + z * z - x * x - y * y)


def hopf_chart_slot_for_winding(
    code: int,
    doubled_span: int,
    winding: int,
    register_bits: int,
) -> int:
    """
    Slot on the doubled-span window from one integrable Hopf chart.

    Winding ``n`` uses Beltrami label ``n+1`` and sector multiplicity ``(n+1)²``
    (Lean: tuftMinimalBeltramiEigenvalue / sphericalHarmonicDimS3).
    """
    w, x, y, z = code_to_unit_quaternion(code, register_bits)
    bx, by, _bz = hopf_map_s3_to_s2(w, x, y, z)
    fiber = hopf_fiber_phase(w, x, y, z)
    theta = math.atan2(by, bx)
    beltrami = float(winding + 1)
    mult = float((winding + 1) ** 2)
    span = max(1, doubled_span)
    phase = (theta * beltrami + fiber * mult) / (2.0 * math.pi)
    return int(round(phase * span)) % span


def hopf_chart_slots(
    code: int,
    n: int,
    doubled_span: int,
    register_bits: int,
    *,
    chart_width: int = 1,
    windings: tuple[int, ...] | None = None,
) -> tuple[list[int], dict[str, Any]]:
    """
    Multi-chart Hopf slot family with intersection voting.

    Uses windings ``1..S`` where ``S = hopf_shell_bound(n)`` unless overridden.
    Returns candidate integers and compact diagnostics.
    """
    charts = windings if windings is not None else active_hopf_windings(n)
    if not charts:
        charts = (1,)

    w, x, y, z = code_to_unit_quaternion(code, register_bits)
    bx, by, bz = hopf_map_s3_to_s2(w, x, y, z)
    fiber = hopf_fiber_phase(w, x, y, z)

    slots_by_winding: dict[int, int] = {}
    for winding in charts:
        slots_by_winding[winding] = hopf_chart_slot_for_winding(
            code, doubled_span, winding, register_bits
        )

    width = max(0, chart_width)
    candidate_votes: dict[int, int] = {}
    for _winding, slot in slots_by_winding.items():
        for delta in range(-width, width + 1):
            s = (slot + delta) % max(1, doubled_span)
            cand = slot_to_candidate(s, n)
            candidate_votes[cand] = candidate_votes.get(cand, 0) + 1

    sorted_votes = sorted(candidate_votes.items(), key=lambda kv: (-kv[1], kv[0]))
    quorum = min(2, len(charts))
    intersection = [c for c, votes in sorted_votes if votes >= quorum]
    if not intersection:
        intersection = [c for c, _ in sorted_votes[: max(2, min(2, len(charts)))]]
    if not intersection:
        intersection = [slot_to_candidate(slots_by_winding[charts[0]], n)]

    max_out = min(2 * len(charts), k_exact_per_center_bound(len(charts)))
    max_out = max(max_out, 2)
    out: list[int] = []
    seen: set[int] = set()
    for cand in intersection:
        if cand not in seen:
            seen.add(cand)
            out.append(cand)
        if len(out) >= max_out:
            break

    diagnostics: dict[str, Any] = {
        "hopf_shell_bound": len(charts),
        "active_windings": list(charts),
        "k_exact_per_center_bound": k_exact_per_center_bound(len(charts)),
        "hopf_base": [round(bx, 6), round(by, 6), round(bz, 6)],
        "fiber_phase": round(fiber, 6),
        "chart_slots": {str(k): v for k, v in slots_by_winding.items()},
        "intersection_size": len(out),
        "intersection_quorum": quorum,
        "chart_votes": {str(k): v for k, v in sorted_votes[:8]},
    }
    return out, diagnostics


def candidate_family_from_code(
    code: int,
    n: int,
    doubled_span: int,
    *,
    q_lookup_mode: str = Q_LOOKUP_FLAT,
    register_bits: int = 0,
    hopf_chart_width: int = 1,
    hopf_windings: tuple[int, ...] | None = None,
) -> tuple[list[int], dict[str, Any] | None]:
    """
    Map one gate code to a small candidate family on the q window.

    Returns ``(candidates, hopf_diagnostics)``; diagnostics is ``None`` in flat mode.
    """
    if q_lookup_mode == Q_LOOKUP_HOPF:
        cands, diag = hopf_chart_slots(
            code,
            n,
            doubled_span,
            register_bits,
            chart_width=hopf_chart_width,
            windings=hopf_windings,
        )
        return cands, diag

    slot = code % doubled_span
    refl = reflection_slot(slot, doubled_span)
    vals = [slot_to_candidate(slot, n), slot_to_candidate(refl, n)]
    out: list[int] = []
    seen: set[int] = set()
    for v in vals:
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out, None


def systematic_hopf_slot_codes(
    step: int,
    doubled_span: int,
    register_bits: int,
    slots_per_shell: int,
) -> list[tuple[int, int]]:
    """
    Real-search phase sweep: march slot indices across the doubled-span window.

    Returns ``(slot_index, seed_code)`` pairs for this shell step.
    """
    span = max(1, doubled_span)
    out: list[tuple[int, int]] = []
    for k in range(slots_per_shell):
        slot = (step * slots_per_shell + k) % span
        frac = slot / float(span)
        code = base._seed_code_from_fraction(register_bits, frac)
        out.append((slot, code))
    return out


def process_code_candidates(
    *,
    n: int,
    code: int,
    step: int,
    seed_idx: int,
    alpha: float,
    doubled_span: int,
    register_bits: int,
    q_lookup_mode: str,
    hopf_chart_width: int,
    hopf_windings: tuple[int, ...],
    coherence_bonus: int,
    hits: set[int],
    candidates: list[base.Candidate],
    tested_candidates: set[int],
    step_scored: list[tuple[tuple[int, int, int, int, int], int, base.Candidate]],
    frontier_scores: dict[int, tuple[int, int, int, int, int]],
) -> tuple[bool, list[int] | None, dict[str, Any] | None]:
    """
    Score one code's candidate family; return ``(early_stop, symmetric_pair, hopf_diag)``.
    """
    best_sc_for_code: tuple[int, int, int, int, int] | None = None
    symmetric_pair: list[int] | None = None
    early_stopped = False
    hopf_diag: dict[str, Any] | None = None

    cand_values, hopf_diag = candidate_family_from_code(
        code,
        n,
        doubled_span,
        q_lookup_mode=q_lookup_mode,
        register_bits=register_bits,
        hopf_chart_width=hopf_chart_width,
        hopf_windings=hopf_windings,
    )

    shell_mod = max(1, len(hopf_windings))
    for cand_value in cand_values:
        tested_candidates.add(cand_value)
        derived = cand_value if (cand_value > 1 and n % cand_value == 0) else None
        row = base.Candidate(
            step=step,
            seed_idx=(seed_idx % shell_mod),
            arc_param=float(alpha),
            derived_divisor=derived,
        )
        candidates.append(row)
        sc = base._candidate_score(n, cand_value, coherence_bonus=coherence_bonus)
        step_scored.append((sc, code, row))
        if best_sc_for_code is None or sc < best_sc_for_code:
            best_sc_for_code = sc
        if derived is not None:
            hits.add(cand_value)
            q = n // cand_value
            if 1 < q < n and cand_value * q == n:
                symmetric_pair = sorted([cand_value, q])
                early_stopped = True
                break

    if best_sc_for_code is not None:
        prev = frontier_scores.get(code)
        if prev is None or best_sc_for_code < prev:
            frontier_scores[code] = best_sc_for_code

    return early_stopped, symmetric_pair, hopf_diag


def test_q_candidates_from_slots(
    *,
    n: int,
    slot_indices: set[int] | list[int],
    step: int,
    alpha: float,
    coherence_bonus: int,
    hits: set[int],
    candidates: list[base.Candidate],
    tested_candidates: set[int],
    step_scored: list[tuple[tuple[int, int, int, int, int], int, base.Candidate]],
    include_reflection: bool = True,
) -> tuple[bool, list[int] | None]:
    """
    Direct q-window probe: map visited slots (and reflections) to candidate integers.

    Ensures hopf-search slot coverage actually exercises the discrete q ladder.
    """
    symmetric_pair: list[int] | None = None
    span = max(1, 2 * q_span(n))
    for slot_idx in sorted(slot_indices):
        slots_to_try = [slot_idx]
        if include_reflection:
            refl = reflection_slot(slot_idx, span)
            if refl not in slots_to_try:
                slots_to_try.append(refl)
        for s in slots_to_try:
            cand_value = slot_to_candidate(s, n)
            if cand_value in tested_candidates:
                continue
            tested_candidates.add(cand_value)
            derived = cand_value if (cand_value > 1 and n % cand_value == 0) else None
            row = base.Candidate(
                step=step,
                seed_idx=0,
                arc_param=float(alpha),
                derived_divisor=derived,
            )
            candidates.append(row)
            sc = base._candidate_score(n, cand_value, coherence_bonus=coherence_bonus)
            step_scored.append((sc, s, row))
            if derived is not None:
                hits.add(cand_value)
                q = n // cand_value
                if 1 < q < n and cand_value * q == n:
                    symmetric_pair = sorted([cand_value, q])
                    return True, symmetric_pair
    return False, symmetric_pair


def test_q_candidates_direct(
    *,
    n: int,
    cand_values: list[int],
    step: int,
    alpha: float,
    hits: set[int],
    candidates: list[base.Candidate],
    tested_candidates: set[int],
    step_scored: list[tuple[tuple[int, int, int, int, int], int, base.Candidate]],
) -> tuple[bool, list[int] | None]:
    """Probe an explicit list of q-window candidate integers."""
    for cand_value in cand_values:
        if cand_value in tested_candidates:
            continue
        tested_candidates.add(cand_value)
        derived = cand_value if (cand_value > 1 and n % cand_value == 0) else None
        row = base.Candidate(
            step=step,
            seed_idx=0,
            arc_param=float(alpha),
            derived_divisor=derived,
        )
        candidates.append(row)
        sc = base._candidate_score(n, cand_value, coherence_bonus=0)
        step_scored.append((sc, cand_value, row))
        if derived is not None:
            hits.add(cand_value)
            q = n // cand_value
            if 1 < q < n and cand_value * q == n:
                return True, sorted([cand_value, q])
    return False, None


def osh_factor_once(
    n: int,
    *,
    max_steps: int | None = 300,
    max_seconds: float | None = None,
    include_trivial_pair: bool = True,
    q_lookup_mode: str = Q_LOOKUP_FLAT,
    hopf_chart_width: int = 1,
    hopf_search: bool = False,
) -> dict[str, Any]:
    if q_lookup_mode not in Q_LOOKUP_MODES:
        raise ValueError(f"q_lookup_mode must be one of: {', '.join(Q_LOOKUP_MODES)}")
    if hopf_chart_width < 0:
        raise ValueError("hopf_chart_width must be >= 0")
    if hopf_search and q_lookup_mode != Q_LOOKUP_HOPF:
        raise ValueError("hopf_search requires q_lookup_mode=hopf-intersection")

    hopf_windings = active_hopf_windings(n)
    shell_s = len(hopf_windings)

    if n <= 1:
        return {
            "n": n,
            "divisors": [1],
            "steps_used": 0,
            "candidates_generated": 0,
            "one_step_pick_certificate": {"kind": "one-step-pick", "picked": False, "n": n},
            "pipeline_mode": "osh-expand-reconstruct-evolve-flip-prune",
            "q_lookup_mode": q_lookup_mode,
            "hopf_shell_bound": shell_s,
        }

    forbidden = base.is_forbidden_form(n)
    symmetric_tip_used = not forbidden
    arc_len = (math.pi / 4.0) if symmetric_tip_used else (2.0 * math.pi)
    delta_phi = base.rapidity_delta(n)

    base_register_bits = max(2, base.register_bit_bound_from_sqrt(n))
    register_bits = 2 * base_register_bits
    mask = (1 << register_bits) - 1
    flip_budget_per_seed = min(96, max(8, 3 * base_register_bits))
    doubled_span = max(2, 2 * q_span(n))
    if q_lookup_mode == Q_LOOKUP_HOPF:
        slots_per_shell = min(
            doubled_span,
            max(8, shell_s * base_register_bits),
        )
        if hopf_search:
            slots_per_shell = min(doubled_span, max(slots_per_shell, shell_s * 4))
    else:
        slots_per_shell = min(32, max(8, base_register_bits))
    frontier_keep_per_step = min(128, max(16, 4 * base_register_bits))
    prune_keep_per_step = min(16, max(6, base_register_bits // 2 + 1))

    hits: set[int] = set()
    candidates: list[base.Candidate] = []
    prune_trace: list[dict[str, Any]] = []
    lag_histogram: dict[int, int] = {}
    code_last_seen_step: dict[int, int] = {}
    hopf_trace: list[dict[str, Any]] = []
    slots_visited: set[int] = set()

    frontier_codes: set[int] = set()
    frontier_scores: dict[int, tuple[int, int, int, int, int]] = {}

    alpha = 0.0
    step = 0
    steps_used = 0
    early_stopped = False
    timed_out = False
    symmetric_pair: list[int] | None = None
    started_at = time.perf_counter()
    tested_candidates: set[int] = set()

    while True:
        if max_steps is not None and step >= max_steps:
            break
        if max_seconds is not None and (time.perf_counter() - started_at) >= max_seconds:
            timed_out = True
            break

        # expand: build seed codes from phase slots + prior frontier
        seed_codes: set[int] = set(frontier_codes)
        frac = (alpha % arc_len) / arc_len if arc_len > 0 else 0.0
        for slot in range(slots_per_shell):
            slot_frac = (frac + (slot / float(slots_per_shell))) % 1.0
            seed_codes.add(base._seed_code_from_fraction(register_bits, slot_frac))

        # reconstruct: local neighborhoods around each seed
        expanded_codes: set[int] = set()
        for s in seed_codes:
            for c in base._flip_codes(s, register_bits, flip_budget_per_seed):
                expanded_codes.add(c & mask)

        # evolve: gate transforms on expanded codes
        evolved_codes: set[int] = set()
        for c in expanded_codes:
            for g in base._gate_frontier_codes(c, register_bits, step):
                evolved_codes.add(g & mask)

        # flip: changed codes between frontier and evolved frontier
        flipped_codes = (frontier_codes - evolved_codes) | (evolved_codes - frontier_codes)
        active_codes = flipped_codes if flipped_codes else evolved_codes

        # hopf real search: systematic slot sweep across doubled-span window
        sweep_codes: list[tuple[int, int]] = []
        if hopf_search:
            sweep_codes = systematic_hopf_slot_codes(
                step, doubled_span, register_bits, slots_per_shell
            )
            for slot_idx, sweep_code in sweep_codes:
                slots_visited.add(slot_idx)
                active_codes.add(sweep_code & mask)

        step_scored: list[tuple[tuple[int, int, int, int, int], int, base.Candidate]] = []
        step_hopf_samples: list[dict[str, Any]] = []
        for seed_idx, code in enumerate(sorted(active_codes)):
            prev_step = code_last_seen_step.get(code)
            coherence_bonus = 0
            if prev_step is not None:
                lag = step - prev_step
                if lag > 0:
                    lag_histogram[lag] = lag_histogram.get(lag, 0) + 1
                    coherence_bonus = min(16, lag_histogram[lag])
            code_last_seen_step[code] = step

            stopped, pair, hopf_diag = process_code_candidates(
                n=n,
                code=code,
                step=step,
                seed_idx=seed_idx,
                alpha=alpha,
                doubled_span=doubled_span,
                register_bits=register_bits,
                q_lookup_mode=q_lookup_mode,
                hopf_chart_width=hopf_chart_width,
                hopf_windings=hopf_windings,
                coherence_bonus=coherence_bonus,
                hits=hits,
                candidates=candidates,
                tested_candidates=tested_candidates,
                step_scored=step_scored,
                frontier_scores=frontier_scores,
            )
            if hopf_diag is not None and len(step_hopf_samples) < 3:
                step_hopf_samples.append({"code": code, **hopf_diag})
            if stopped and pair is not None:
                symmetric_pair = pair
                early_stopped = True
                steps_used = step + 1
                break
        if not early_stopped and hopf_search:
            stopped, pair = test_q_candidates_from_slots(
                n=n,
                slot_indices=slots_visited,
                step=step,
                alpha=alpha,
                coherence_bonus=0,
                hits=hits,
                candidates=candidates,
                tested_candidates=tested_candidates,
                step_scored=step_scored,
            )
            if stopped and pair is not None:
                symmetric_pair = pair
                early_stopped = True
                steps_used = step + 1
        if early_stopped:
            break

        # hopf search: full slot coverage — exhaust q ladder when feasible
        if hopf_search and len(slots_visited) >= doubled_span and not early_stopped:
            if should_exhaust_q_window(n):
                stopped, pair = test_q_candidates_direct(
                    n=n,
                    cand_values=q_window_candidate_values(n),
                    step=step,
                    alpha=alpha,
                    hits=hits,
                    candidates=candidates,
                    tested_candidates=tested_candidates,
                    step_scored=step_scored,
                )
                if stopped and pair is not None:
                    symmetric_pair = pair
                    early_stopped = True
                    steps_used = step + 1
            break

        # prune: keep top frontier for next shell
        if step_scored:
            step_scored.sort(key=lambda x: (x[0], x[1]))
            top = step_scored[:prune_keep_per_step]
            frontier_ranked = sorted(frontier_scores.items(), key=lambda kv: (kv[1], kv[0]))
            frontier_codes = {code for code, _ in frontier_ranked[:frontier_keep_per_step]}
            if len(frontier_ranked) > 8 * frontier_keep_per_step:
                frontier_scores = dict(frontier_ranked[: 8 * frontier_keep_per_step])
            prune_entry: dict[str, Any] = {
                "step": step,
                "expand_seed_count": len(seed_codes),
                "reconstruct_count": len(expanded_codes),
                "evolve_count": len(evolved_codes),
                "flip_count": len(flipped_codes),
                "active_count": len(active_codes),
                "frontier_size": len(frontier_codes),
                "kept": [
                    {
                        "code": code,
                        "score": list(sc),
                        "derived_divisor": c.derived_divisor,
                    }
                    for sc, code, c in top
                ],
            }
            if q_lookup_mode == Q_LOOKUP_HOPF:
                prune_entry["hopf_shell_bound"] = shell_s
                prune_entry["active_windings"] = list(hopf_windings)
                if hopf_search:
                    prune_entry["slots_visited"] = len(slots_visited)
                    prune_entry["slot_coverage_fraction"] = len(slots_visited) / doubled_span
                if step_hopf_samples:
                    prune_entry["hopf_samples"] = step_hopf_samples
            prune_trace.append(prune_entry)
            if q_lookup_mode == Q_LOOKUP_HOPF and step_hopf_samples:
                hopf_trace.append({"step": step, "samples": step_hopf_samples})

        alpha += delta_phi
        step += 1

    if steps_used == 0:
        steps_used = step

    if include_trivial_pair:
        hits.add(1)
        hits.add(n)

    divisors = sorted(hits)
    root = max(2, math.isqrt(n))
    candidate_window_size = max(1, root - 1)
    tested_count = len(tested_candidates)
    one_step_pick_certificate = base.build_one_step_pick_certificate(n, candidates)
    periodicity_trace = [
        {"lag": lag, "count": cnt}
        for lag, cnt in sorted(lag_histogram.items(), key=lambda kv: (-kv[1], kv[0]))[:10]
    ]
    slot_coverage_fraction = (
        len(slots_visited) / doubled_span if hopf_search and doubled_span > 0 else None
    )

    return {
        "n": n,
        "forbidden_form": forbidden,
        "divisors": divisors,
        "steps_used": steps_used,
        "candidates_generated": len(candidates),
        "tested_candidate_count": tested_count,
        "candidate_window_size": candidate_window_size,
        "search_coverage_fraction": tested_count / candidate_window_size,
        "pipeline_mode": "osh-hopf-search" if hopf_search else "osh-expand-reconstruct-evolve-flip-prune",
        "q_lookup_mode": q_lookup_mode,
        "hopf_search": hopf_search,
        "hopf_chart_width": hopf_chart_width,
        "hopf_shell_bound": shell_s,
        "floor_cbrt_n": floor_cbrt(n),
        "active_hopf_windings": list(hopf_windings),
        "k_exact_per_center_bound": k_exact_per_center_bound(shell_s),
        "q_span": q_span(n),
        "doubled_span": doubled_span,
        "base_register_bits": base_register_bits,
        "register_bits": register_bits,
        "flip_budget_per_seed": flip_budget_per_seed,
        "slots_per_shell": slots_per_shell,
        "frontier_keep_per_step": frontier_keep_per_step,
        "prune_keep_per_step": prune_keep_per_step,
        "slot_coverage_fraction": slot_coverage_fraction,
        "prune_trace": prune_trace,
        "hopf_trace": hopf_trace if q_lookup_mode == Q_LOOKUP_HOPF else [],
        "periodicity_trace": periodicity_trace,
        "early_stopped": early_stopped,
        "timed_out": timed_out,
        "elapsed_s": time.perf_counter() - started_at,
        "candidates": [asdict(c) for c in candidates],
        "one_step_pick_certificate": one_step_pick_certificate,
        "symmetric_pair": symmetric_pair,
    }


def recursive_prime_factorization_osh(
    n: int,
    *,
    max_steps_per_node: int | None = 240,
    max_seconds_per_node: float | None = 10.0,
    q_lookup_mode: str = Q_LOOKUP_FLAT,
    hopf_chart_width: int = 1,
    hopf_search: bool = False,
) -> dict[str, Any]:
    if n <= 1:
        return {
            "n": n,
            "prime_factors": [],
            "unresolved": [],
            "trace": [],
            "verified_product": (n == 1),
        }

    pending: list[int] = [n]
    prime_factors: list[int] = []
    unresolved: list[int] = []
    unresolved_primality_checks: list[dict[str, Any]] = []
    trace: list[dict[str, Any]] = []

    while pending:
        x = pending.pop()
        if x <= 1:
            continue
        if base.is_probable_prime(x):
            prime_factors.append(x)
            trace.append({"n": x, "status": "probable-prime", "split": None})
            continue

        node = osh_factor_once(
            x,
            max_steps=max_steps_per_node,
            max_seconds=max_seconds_per_node,
            include_trivial_pair=False,
            q_lookup_mode=q_lookup_mode,
            hopf_chart_width=hopf_chart_width,
            hopf_search=hopf_search,
        )
        cert = node.get("one_step_pick_certificate", {})
        d = int(cert.get("d", 0)) if cert.get("picked", False) else 0
        good = bool(
            cert.get("picked", False)
            and cert.get("is_nontrivial", False)
            and cert.get("divides", False)
            and cert.get("pair_product_ok", False)
            and 1 < d < x
        )
        if not good:
            unresolved.append(x)
            probable = base.is_probable_prime(x)
            unresolved_primality_checks.append(
                {
                    "n": x,
                    "probable_prime": probable,
                    "primality_test": "pass" if probable else "fail",
                }
            )
            trace.append(
                {
                    "n": x,
                    "status": "unresolved",
                    "reason": cert.get("reason", "no nontrivial divisor pick"),
                    "steps_used": node.get("steps_used"),
                    "candidates_generated": node.get("candidates_generated"),
                    "probable_prime": probable,
                    "primality_test": "pass" if probable else "fail",
                }
            )
            continue

        q = x // d
        trace.append(
            {
                "n": x,
                "status": "split",
                "split": [d, q],
                "steps_used": node.get("steps_used"),
                "candidates_generated": node.get("candidates_generated"),
            }
        )
        pending.append(d)
        pending.append(q)

    prime_factors.sort()
    product = 1
    for p in prime_factors:
        product *= p
    verified = (len(unresolved) == 0) and (product == n)
    return {
        "n": n,
        "prime_factors": prime_factors,
        "unresolved": unresolved,
        "unresolved_primality_checks": unresolved_primality_checks,
        "trace": trace,
        "verified_product": verified,
        "pipeline_mode": "osh-expand-reconstruct-evolve-flip-prune",
        "q_lookup_mode": q_lookup_mode,
        "hopf_chart_width": hopf_chart_width,
        "hopf_search": hopf_search,
    }


def compare_q_lookup_modes(
    n: int,
    *,
    max_steps: int = 300,
    max_seconds: float | None = 5.0,
    hopf_chart_width: int = 1,
    hopf_search: bool = False,
) -> dict[str, Any]:
    """Smoke comparison: flat-reflector vs hopf-intersection on the same ``n``."""
    flat = osh_factor_once(
        n,
        max_steps=max_steps,
        max_seconds=max_seconds,
        q_lookup_mode=Q_LOOKUP_FLAT,
    )
    hopf = osh_factor_once(
        n,
        max_steps=max_steps,
        max_seconds=max_seconds,
        q_lookup_mode=Q_LOOKUP_HOPF,
        hopf_chart_width=hopf_chart_width,
        hopf_search=hopf_search,
    )
    return {
        "n": n,
        "hopf_shell_bound": hopf_shell_bound(n),
        "floor_cbrt_n": floor_cbrt(n),
        "active_hopf_windings": list(active_hopf_windings(n)),
        "flat": {
            "early_stopped": flat["early_stopped"],
            "steps_used": flat["steps_used"],
            "tested_candidate_count": flat["tested_candidate_count"],
            "search_coverage_fraction": flat["search_coverage_fraction"],
            "symmetric_pair": flat["symmetric_pair"],
        },
        "hopf": {
            "early_stopped": hopf["early_stopped"],
            "steps_used": hopf["steps_used"],
            "tested_candidate_count": hopf["tested_candidate_count"],
            "search_coverage_fraction": hopf["search_coverage_fraction"],
            "slot_coverage_fraction": hopf.get("slot_coverage_fraction"),
            "symmetric_pair": hopf["symmetric_pair"],
            "hopf_search": hopf.get("hopf_search", False),
        },
        "hopf_finds_factor_when_flat_does": (
            hopf["early_stopped"] and not flat["early_stopped"]
        ),
        "flat_finds_factor_when_hopf_does": (
            flat["early_stopped"] and not hopf["early_stopped"]
        ),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OSHoracle-style gate-frontier factorization")
    parser.add_argument("n", type=int, help="positive integer to probe")
    parser.add_argument("--max-steps", type=int, default=300, help="iteration budget (0 => unbounded)")
    parser.add_argument("--max-seconds", type=float, default=None, help="wall-clock budget in seconds")
    parser.add_argument("--prime-factorization", action="store_true", help="recursive factorization attempt")
    parser.add_argument(
        "--factor-max-seconds-per-node",
        type=float,
        default=10.0,
        help="wall-clock cap per recursive node",
    )
    parser.add_argument(
        "--q-lookup-mode",
        choices=Q_LOOKUP_MODES,
        default=Q_LOOKUP_FLAT,
        help="q candidate lookup: flat-reflector (default) or hopf-intersection",
    )
    parser.add_argument(
        "--hopf-chart-width",
        type=int,
        default=1,
        help="local slot neighborhood half-width for hopf-intersection mode",
    )
    parser.add_argument(
        "--hopf-search",
        action="store_true",
        help="systematic Hopf phase sweep over doubled-span (requires hopf-intersection mode)",
    )
    parser.add_argument(
        "--compare-q-modes",
        action="store_true",
        help="run flat vs hopf smoke comparison and include in output",
    )
    parser.add_argument("--json", action="store_true", help="emit JSON payload")
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.n < 1:
        raise SystemExit("n must be >= 1")
    if args.max_steps < 0:
        raise SystemExit("--max-steps must be >= 0")
    if args.max_seconds is not None and args.max_seconds <= 0:
        raise SystemExit("--max-seconds must be > 0 when provided")
    if args.factor_max_seconds_per_node is not None and args.factor_max_seconds_per_node <= 0:
        raise SystemExit("--factor-max-seconds-per-node must be > 0 when provided")
    if args.hopf_chart_width < 0:
        raise SystemExit("--hopf-chart-width must be >= 0")
    if args.hopf_search and args.q_lookup_mode != Q_LOOKUP_HOPF:
        raise SystemExit("--hopf-search requires --q-lookup-mode hopf-intersection")

    payload = osh_factor_once(
        args.n,
        max_steps=(None if args.max_steps == 0 else args.max_steps),
        max_seconds=args.max_seconds,
        include_trivial_pair=True,
        q_lookup_mode=args.q_lookup_mode,
        hopf_chart_width=args.hopf_chart_width,
        hopf_search=args.hopf_search,
    )
    if args.compare_q_modes:
        payload["q_mode_comparison"] = compare_q_lookup_modes(
            args.n,
            max_steps=(300 if args.max_steps == 0 else args.max_steps),
            max_seconds=args.max_seconds if args.max_seconds is not None else 5.0,
            hopf_chart_width=args.hopf_chart_width,
            hopf_search=args.hopf_search,
        )
    if args.prime_factorization:
        rec = recursive_prime_factorization_osh(
            args.n,
            max_steps_per_node=(None if args.max_steps == 0 else args.max_steps),
            max_seconds_per_node=args.factor_max_seconds_per_node,
            q_lookup_mode=args.q_lookup_mode,
            hopf_chart_width=args.hopf_chart_width,
            hopf_search=args.hopf_search,
        )
        payload["recursive_factorization"] = rec
        payload["factor_export_validation"] = base.validate_factor_export(args.n, rec)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return

    print(
        f"n={payload['n']} steps_used={payload['steps_used']} "
        f"pipeline_mode={payload['pipeline_mode']}"
    )
    print(
        f"q_lookup_mode={payload['q_lookup_mode']} hopf_search={payload.get('hopf_search', False)} "
        f"hopf_shell_bound={payload.get('hopf_shell_bound')} hopf_chart_width={payload['hopf_chart_width']} "
        f"candidates_generated={payload['candidates_generated']} early_stopped={payload['early_stopped']} "
        f"timed_out={payload['timed_out']}"
    )
    print(
        f"q_span={payload['q_span']} doubled_span={payload['doubled_span']} "
        f"register_bits={payload['register_bits']}"
    )
    print(
        f"tested_candidate_count={payload['tested_candidate_count']} "
        f"candidate_window_size={payload['candidate_window_size']} "
        f"search_coverage_fraction={payload['search_coverage_fraction']:.6f}"
    )
    print(f"divisors={payload['divisors']}")
    if payload["symmetric_pair"] is not None:
        print(f"symmetric_pair={payload['symmetric_pair']}")
    print(f"one_step_pick_certificate={payload['one_step_pick_certificate']}")
    print(f"periodicity_trace={payload['periodicity_trace']}")
    if args.compare_q_modes and "q_mode_comparison" in payload:
        print(f"q_mode_comparison={payload['q_mode_comparison']}")
    if args.prime_factorization:
        rec = payload["recursive_factorization"]
        validation = payload["factor_export_validation"]
        print(
            f"recursive_factorization_verified={rec['verified_product']} "
            f"prime_factors={rec['prime_factors']} unresolved={rec['unresolved']}"
        )
        print(
            f"factor_export_validation_status={validation['status']} "
            f"failed_checks={validation['failed_checks']}"
        )


if __name__ == "__main__":
    main()
