#!/usr/bin/env python3
"""
Generalized geometric oracle modes (factor / modular / sat) built on top of the
typed candidate stream from `geometric_factorization_solver.py`.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import time
from dataclasses import dataclass
from typing import Any

from geometric_factorization_solver import (
    Candidate,
    candidate_list_to_csv,
    geometric_factorization_solver,
)


def sat_search_root_scale(n: int) -> float:
    """Lean `satSearchRootScale`: `n^(1/n)` as ℝ (Python float witness for certificates)."""
    if n <= 0:
        return 1.0
    return float(n) ** (1.0 / float(n))


def sat_search_envelope(n: int) -> float:
    """Lean `satSearchEnvelope`: `1 + n^(1/n)`."""
    return 1.0 + sat_search_root_scale(n)


def build_factor_pick_bridge_payload(raw_cert: dict[str, Any] | None) -> dict[str, Any]:
    """
    Normalize one-step factor-pick certificates for cross-mode JSON outputs.

    Target Lean wrapper:
      `Hqiv.Geometry.Bridge.OneStepPickCertificate`
    with theorem consumers:
      `OneStepPickCertificate.sound`, `OneStepPickCertificate.pair_product`.
    """
    cert = raw_cert if isinstance(raw_cert, dict) else {}
    picked = bool(cert.get("picked", False))
    out: dict[str, Any] = {
        "schema": "hqiv.one-step-pick-bridge.v1",
        "lean_namespace": "Hqiv.Geometry.Bridge",
        "lean_certificate_target": "OneStepPickCertificate",
        "lean_theorems": [
            "OneStepPickCertificate.sound",
            "OneStepPickCertificate.pair_product",
        ],
        "picked": picked,
    }
    if not picked:
        out["status"] = "no-pick"
        out["reason"] = cert.get("reason", "no nontrivial divisor found in candidate order")
        return out
    d = int(cert.get("d", 0))
    n = int(cert.get("n", 0))
    cofactor = int(cert.get("cofactor", 0))
    is_nontrivial = bool(cert.get("is_nontrivial", False))
    divides = bool(cert.get("divides", False))
    pair_product_ok = bool(cert.get("pair_product_ok", False))
    out.update(
        {
            "status": "picked",
            "n": n,
            "d": d,
            "cofactor": cofactor,
            "candidate_index": cert.get("candidate_index"),
            "step": cert.get("step"),
            "seed_idx": cert.get("seed_idx"),
            "runtime_checks": {
                "is_nontrivial": is_nontrivial,
                "divides": divides,
                "pair_product_ok": pair_product_ok,
            },
            "theorem_ready": bool(is_nontrivial and divides and pair_product_ok),
        }
    )
    return out


def _assignment_to_dimacs_literals(assignment: list[bool]) -> list[int]:
    return [i if value else -i for i, value in enumerate(assignment, start=1)]


def blocking_clause_from_assignment(assignment: list[bool]) -> list[int]:
    """Clause falsified exactly by the given complete assignment."""
    return [-(i + 1) if value else (i + 1) for i, value in enumerate(assignment)]


def evaluate_assignment_certificate(
    clauses: list[list[int]], assignment: list[bool]
) -> dict[str, Any]:
    """Return a certificate payload for a concrete SAT witness assignment."""
    clause_results: list[dict[str, Any]] = []
    satisfied_count = 0
    for idx, clause in enumerate(clauses):
        sat = clause_satisfied(clause, assignment)
        if sat:
            satisfied_count += 1
        clause_results.append(
            {
                "clause_index": idx,
                "clause": clause,
                "satisfied": sat,
            }
        )
    return {
        "kind": "sat-witness",
        "assignment": assignment,
        "assignment_literals": _assignment_to_dimacs_literals(assignment),
        "satisfied_clause_count": satisfied_count,
        "num_clauses": len(clauses),
        "all_clauses_satisfied": satisfied_count == len(clauses),
        "clause_results": clause_results,
    }


def exhaustive_unsat_certificate(
    clauses: list[list[int]], num_vars: int
) -> dict[str, Any]:
    """Return an explicit exhaustive-search UNSAT certificate payload."""
    total_assignments = 1 << max(0, num_vars)
    checked_assignments: list[dict[str, Any]] = []
    for code in range(total_assignments):
        assignment = assignment_from_code(code, num_vars)
        sat_count = sum(1 for clause in clauses if clause_satisfied(clause, assignment))
        checked_assignments.append(
            {
                "assignment_code": code,
                "assignment_literals": _assignment_to_dimacs_literals(assignment),
                "satisfied_clause_count": sat_count,
                "is_model": sat_count == len(clauses),
            }
        )
    return {
        "kind": "unsat-exhaustive",
        "num_vars": num_vars,
        "num_clauses": len(clauses),
        "total_assignments": total_assignments,
        "checked_assignments": checked_assignments,
        "models_found": 0,
        "survivor_work": total_assignments,
        "baseline_work": total_assignments,
        "survivor_ratio": 1.0,
    }


def build_sat_certificate(
    clauses: list[list[int]],
    num_vars: int,
    status: str,
    assignment: list[bool] | None,
    *,
    exhaustive_limit: int,
    traversal_summary: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Construct a SAT/UNSAT/UNKNOWN certificate payload aligned with the Lean framing."""
    total_assignments = 1 << max(0, num_vars)
    if status == "SAT" and assignment is not None:
        cert = evaluate_assignment_certificate(clauses, assignment)
        cert.update(
            {
                "status": "SAT",
                "num_vars": num_vars,
                "search_space_size": total_assignments,
                "certified": True,
            }
        )
        return cert
    if status == "UNSAT" and num_vars <= exhaustive_limit:
        cert = exhaustive_unsat_certificate(clauses, num_vars)
        cert.update(
            {
                "status": "UNSAT",
                "certified": True,
            }
        )
        return cert
    if status == "UNSAT" and traversal_summary is not None and traversal_summary.get("exhausted"):
        cert = {
            "kind": "unsat-exhausted-pool",
            "status": "UNSAT",
            "num_vars": num_vars,
            "num_clauses": len(clauses),
            "search_space_size": 1 << max(0, num_vars),
            "certified": True,
            "visited_codes": int(traversal_summary.get("visited_codes", 0)),
            "edges_examined": int(traversal_summary.get("edges_examined", 0)),
            "frontier_remaining": int(traversal_summary.get("frontier_remaining", 0)),
            "baseline_work": int(traversal_summary.get("baseline_work", 0)),
            "survivor_work": int(traversal_summary.get("survivor_work", 0)),
            "survivor_ratio": float(traversal_summary.get("survivor_ratio", 1.0)),
        }
        if traversal_summary.get("drat_lines"):
            cert["drat_like_proof"] = traversal_summary.get("drat_lines")
        return cert
    if status == "UNKNOWN" and traversal_summary is not None:
        return {
            "kind": "unknown-timeout",
            "status": "UNKNOWN",
            "num_vars": num_vars,
            "num_clauses": len(clauses),
            "search_space_size": 1 << max(0, num_vars),
            "certified": False,
            "reason": str(traversal_summary.get("reason", "timeout")),
            "visited_codes": int(traversal_summary.get("visited_codes", 0)),
            "edges_examined": int(traversal_summary.get("edges_examined", 0)),
            "frontier_remaining": int(traversal_summary.get("frontier_remaining", 0)),
        }
    return {
        "kind": "unknown",
        "status": "UNKNOWN",
        "num_vars": num_vars,
        "num_clauses": len(clauses),
        "search_space_size": total_assignments,
        "certified": False,
        "reason": "no SAT witness found and exhaustive UNSAT certificate unavailable within configured limit",
    }


def traverse_candidate_pool_exhaustively(
    num_vars: int,
    clauses: list[list[int]],
    seed_codes: list[int],
    *,
    max_seconds: float | None,
    started_at: float | None = None,
    emit_drat: bool = False,
) -> dict[str, Any]:
    """
    Traverse the reachable assignment pool induced by seed codes and single-bit flips.

    Returns SAT on first witness, UNSAT if the reachable pool is exhausted with no model,
    and UNKNOWN if timeout occurs before exhaustion.
    """
    started = time.perf_counter() if started_at is None else started_at
    mask = (1 << max(0, num_vars)) - 1
    seen: set[int] = set()
    frontier: list[int] = []
    drat_lines: list[str] = []
    for code in seed_codes:
        norm = int(code) & mask
        if norm not in seen:
            seen.add(norm)
            frontier.append(norm)
    if not frontier:
        frontier.append(0)
        seen.add(0)

    edges_examined = 0
    while frontier:
        if max_seconds is not None and (time.perf_counter() - started) >= max_seconds:
            return {
                "status": "UNKNOWN",
                "reason": "timeout",
                "visited_codes": len(seen),
                "frontier_remaining": len(frontier),
                "edges_examined": edges_examined,
                "exhausted": False,
            }
        code = frontier.pop()
        assignment = assignment_from_code(code, num_vars)
        if cnf_satisfied(clauses, assignment):
            return {
                "status": "SAT",
                "assignment": assignment,
                "assignment_code": code,
                "visited_codes": len(seen),
                "frontier_remaining": len(frontier),
                "edges_examined": edges_examined,
                "exhausted": False,
                "drat_lines": drat_lines,
            }
        if emit_drat:
            block = blocking_clause_from_assignment(assignment)
            drat_lines.append(" ".join(str(lit) for lit in block) + " 0")
        for bit in range(num_vars):
            nxt = code ^ (1 << bit)
            edges_examined += 1
            if nxt not in seen:
                seen.add(nxt)
                frontier.append(nxt)

    return {
        "status": "UNSAT",
        "visited_codes": len(seen),
        "frontier_remaining": 0,
        "edges_examined": edges_examined,
        "exhausted": True,
        "baseline_work": len(seen),
        "survivor_work": len(seen),
        "survivor_ratio": 1.0,
        "drat_lines": drat_lines + (["0"] if emit_drat else []),
    }


def parse_dimacs_cnf(path: str) -> tuple[int, list[list[int]]]:
    """Parse a DIMACS CNF file and return (num_vars, clauses)."""
    num_vars = 0
    clauses: list[list[int]] = []
    pending: list[int] = []
    with open(path, "r", encoding="utf-8") as fh:
        for raw in fh:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                parts = line.split()
                if len(parts) >= 4 and parts[1].lower() == "cnf":
                    num_vars = int(parts[2])
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    if pending:
                        clauses.append(pending)
                    pending = []
                else:
                    pending.append(lit)
    if pending:
        clauses.append(pending)
    if num_vars <= 0:
        max_var = 0
        for clause in clauses:
            for lit in clause:
                max_var = max(max_var, abs(lit))
        num_vars = max_var
    return num_vars, clauses


def assignment_from_code(code: int, num_vars: int) -> list[bool]:
    """Decode integer assignment code into variable truth values (1-indexed vars)."""
    return [bool((code >> i) & 1) for i in range(num_vars)]


def clause_satisfied(clause: list[int], assignment: list[bool]) -> bool:
    for lit in clause:
        idx = abs(lit) - 1
        if idx < 0 or idx >= len(assignment):
            continue
        value = assignment[idx]
        if (lit > 0 and value) or (lit < 0 and not value):
            return True
    return False


def cnf_satisfied(clauses: list[list[int]], assignment: list[bool]) -> bool:
    return all(clause_satisfied(clause, assignment) for clause in clauses)


def write_sat_competition_output(path: str, status: str, sat_assignment: list[bool] | None = None) -> None:
    with open(path, "w", encoding="utf-8") as fh:
        if status == "UNSAT":
            fh.write("s UNSATISFIABLE\n")
            return
        if status == "UNKNOWN":
            fh.write("s UNKNOWN\n")
            return
        if sat_assignment is None:
            fh.write("s UNKNOWN\n")
            return
        lits = []
        for i, value in enumerate(sat_assignment, start=1):
            lits.append(str(i if value else -i))
        fh.write("s SATISFIABLE\n")
        fh.write(f"v {' '.join(lits)} 0\n")


def exhaustive_cnf_status(
    clauses: list[list[int]], num_vars: int, max_vars: int = 20
) -> tuple[str, list[bool] | None]:
    """Small-instance proof channel: return SAT/UNSAT exactly up to max_vars, else UNKNOWN."""
    if num_vars > max_vars:
        return "UNKNOWN", None
    for code in range(1 << num_vars):
        assignment = assignment_from_code(code, num_vars)
        if cnf_satisfied(clauses, assignment):
            return "SAT", assignment
    return "UNSAT", None


def modular_projection(n: int, candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for c in candidates:
        rows.append(
            {
                "step": c["step"],
                "seed_idx": c["seed_idx"],
                "arc_param": c["arc_param"],
                "tau_re": c["arc_param"],
                "tau_im": 1.0,
                "fourier_mode": n * c["step"] + c["seed_idx"],
                "l_value": None,
            }
        )
    return rows


def assignment_code_from_candidate(
    c: dict[str, Any],
    num_vars: int,
    *,
    mix_mode: str = "legacy",
) -> int:
    """Map a geometric candidate triple to a Boolean assignment bit-code."""
    if num_vars <= 0:
        return 0
    mask = (1 << num_vars) - 1
    if mix_mode == "legacy":
        return (int(c["step"]) + int(c["seed_idx"])) & mask
    tau = 2.0 * math.pi
    arc = float(c["arc_param"])
    frac = (arc % tau) / tau if tau > 0 else 0.0
    spread = int(frac * float(mask + 1))
    if spread > mask:
        spread = mask
    mix = ((int(c["step"]) * 1103515245 + int(c["seed_idx"]) * 12345) ^ int(abs(arc) * 1_000_000.0)) & mask
    return (spread ^ mix) & mask


def _omega_weight(shell_step: int, mode: str, k_arity: int) -> float:
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


def _shell_neighborhood_scale(shell_step: int, mode: str, base_scale: float) -> float:
    s = float(shell_step + 1)
    if mode == "constant":
        return base_scale
    if mode == "reciprocal":
        return base_scale / s
    if mode == "sqrt-reciprocal":
        return base_scale / math.sqrt(s)
    raise ValueError(f"unknown neighborhood mode: {mode}")


def _unique_phases(phases: list[float]) -> list[float]:
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


def _shell_slot_phases(
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
        return _unique_phases(periodic)
    if slot_family == "one-over-k":
        return _unique_phases(one_over_k)
    if slot_family == "reflected":
        return _unique_phases(periodic + reflected)
    if slot_family == "hybrid":
        return _unique_phases(periodic + reflected + one_over_k)
    raise ValueError(f"unknown slot family: {slot_family}")


def _rapidity_delta_scale(n: int) -> float:
    return math.pi / (4.0 * math.log(float(max(2, n))))


def _shell_flip_codes(before_codes: set[int], after_codes: set[int]) -> set[int]:
    return (before_codes - after_codes) | (after_codes - before_codes)


def greedy_flip_completion(
    assignment: list[bool],
    clauses: list[list[int]],
    *,
    max_rounds: int,
) -> list[bool]:
    """Hill-climb by single-variable flips (greedy GSAT-style completion for shell seeds)."""
    if max_rounds <= 0 or not clauses:
        return assignment
    cur = assignment[:]
    for _ in range(max_rounds):
        base_score = sum(1 for cl in clauses if clause_satisfied(cl, cur))
        if base_score == len(clauses):
            return cur
        best_score = base_score
        best_assign = cur
        improved = False
        for i in range(len(cur)):
            trial = cur[:]
            trial[i] = not trial[i]
            sc = sum(1 for cl in clauses if clause_satisfied(cl, trial))
            if sc > best_score:
                best_score = sc
                best_assign = trial
                improved = True
        cur = best_assign
        if not improved:
            break
    return cur


def walksat_completion(
    assignment: list[bool],
    clauses: list[list[int]],
    *,
    max_rounds: int,
    rng: random.Random,
) -> list[bool]:
    """Pick a random unsatisfied clause and flip a random literal in it (WalkSAT-style)."""
    if max_rounds <= 0 or not clauses:
        return assignment
    cur = assignment[:]
    ncl = len(clauses)
    for _ in range(max_rounds):
        unsat_idx = [i for i, cl in enumerate(clauses) if not clause_satisfied(cl, cur)]
        if not unsat_idx:
            return cur
        ci = rng.choice(unsat_idx)
        clause = clauses[ci]
        if not clause:
            continue
        lit = rng.choice(clause)
        var = abs(lit) - 1
        if 0 <= var < len(cur):
            cur[var] = not cur[var]
    return cur


@dataclass(frozen=True)
class _LocalSearchSatCacheKey:
    code: int
    mode: str
    rounds: int


def local_search_sat(
    assignment: list[bool],
    clauses: list[list[int]],
    *,
    mode: str,
    rounds: int,
    rng: random.Random,
    cache: dict[_LocalSearchSatCacheKey, list[bool]] | None = None,
) -> list[bool]:
    """
    ATSP-style local completion: greedy, WalkSAT, or both (half rounds each).
    Optional cache keyed by (assignment_code, mode, rounds).
    """
    if rounds <= 0 or not clauses:
        return assignment
    code = sum((1 << i) for i, b in enumerate(assignment) if b)
    key = _LocalSearchSatCacheKey(code, mode, max(1, rounds))
    if cache is not None and key in cache:
        return cache[key][:]

    g_rounds = rounds
    w_rounds = rounds
    if mode == "both":
        g_rounds = max(1, rounds // 2)
        w_rounds = max(1, rounds - g_rounds)

    cur = assignment
    if mode in {"greedy", "both"}:
        cur = greedy_flip_completion(cur, clauses, max_rounds=g_rounds)
    if mode in {"walksat", "both"}:
        cur = walksat_completion(cur, clauses, max_rounds=w_rounds, rng=rng)

    if cache is not None:
        cache[key] = cur[:]
    return cur


def _compute_sat_research_score(
    sat_count: int,
    num_cl: int,
    shell_step: int,
    shell_count: int,
    flip_changed: bool,
    *,
    w_r: float,
    w_j: float,
    w_e: float,
    w_c: float,
    flip_bonus: float,
) -> float:
    """ATSP `attach_rapidity_metrics`-style scalar for SAT rows."""
    rapidity_norm = shell_step / max(1.0, float(shell_count))
    eff = sat_count / max(1, num_cl)
    jitter_norm = abs(0.5 - eff)
    cost_norm = 1.0 - eff
    return (
        w_r * rapidity_norm
        + w_j * jitter_norm
        + w_e * eff
        + w_c * cost_norm
        - (flip_bonus if flip_changed else 0.0)
    )


def sat_projection(
    candidates: list[dict[str, Any]],
    num_vars: int,
    num_clauses: int,
    clauses: list[list[int]] | None = None,
    *,
    mix_mode: str = "legacy",
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for c in candidates:
        code = assignment_code_from_candidate(c, num_vars, mix_mode=mix_mode)
        exact_scoring = clauses is not None
        if exact_scoring:
            assignment = assignment_from_code(code, num_vars)
            sat_count = sum(1 for clause in clauses if clause_satisfied(clause, assignment))
            witness = sat_count == len(clauses)
        else:
            # Fallback scaffold score when no CNF clauses are provided.
            sat_count = min(num_clauses, bin(code).count("1"))
            witness = sat_count == num_clauses
        row: dict[str, Any] = {
            "step": c["step"],
            "seed_idx": c["seed_idx"],
            "arc_param": c["arc_param"],
            "assignment_code": code,
            "satisfied_clause_count": sat_count,
            "is_witness": witness,
            "exact_scoring": exact_scoring,
        }
        for k in ("shell_step", "flip_changed", "research_score", "rapidity_shell"):
            if k in c:
                row[k] = c[k]
        rows.append(row)
    return rows


def rapidity_first_sat_payload(
    num_vars: int,
    clauses: list[list[int]],
    *,
    shell_count: int = 48,
    shell_phase_scale: float = 1.0,
    shell_phase_stride: float = 1.0,
    omega_mode: str = "sqrt-reciprocal",
    slots_per_shell: int = 8,
    slot_family: str = "hybrid",
    neighborhood_offsets: int = 1,
    neighborhood_mode: str = "reciprocal",
    neighborhood_scale: float = 0.35,
    k_arity: int | None = None,
    keep_per_shell: int = 12,
    pool_limit: int = 384,
    flip_prune: bool = True,
    max_seconds: float | None = None,
    max_candidates: int | None = None,
    local_flip_rounds: int = 2,
    local_search_mode: str = "greedy",
    mix_mode: str = "arc",
    research_weight_rapidity: float = 1.0,
    research_weight_jitter: float = 0.30,
    research_weight_effective: float = 0.20,
    research_weight_cost: float = 0.10,
    flip_bonus: float = 0.10,
    local_search_rng_seed: int = 42,
) -> dict[str, Any]:
    """
    Rapidity-first SAT candidate stream aligned with the ATSP shell/slot/flip story:
    monotone phase ladder, periodic slot families, local phase probes, optional flip pruning,
    research_score ranking (ATSP-style), cached local completion, global pool cap.
    """
    if local_search_mode not in {"off", "greedy", "walksat", "both"}:
        raise ValueError(f"unknown local_search_mode: {local_search_mode!r}")
    started = time.perf_counter()
    k = k_arity if k_arity is not None else max(1, num_vars)
    num_cl = len(clauses)
    shell_scale = max(210, num_vars * max(2, num_cl))
    phase_accum = 0.0
    prev_codes: set[int] = set()
    pool_by_code: dict[int, dict[str, Any]] = {}
    emitted: list[dict[str, Any]] = []
    total_emitted = 0
    shell_trace: list[dict[str, Any]] = []
    arity_gate_trace: list[dict[str, Any]] = []
    witness_assignment: list[bool] | None = None
    ls_rng = random.Random(local_search_rng_seed)
    ls_cache: dict[_LocalSearchSatCacheKey, list[bool]] = {}

    def budget_exhausted() -> bool:
        if max_seconds is not None and (time.perf_counter() - started) >= max_seconds:
            return True
        if max_candidates is not None and total_emitted >= max_candidates:
            return True
        return False

    def ingest_shell_candidates(shell_cands: list[dict[str, Any]], shell_step: int) -> None:
        nonlocal witness_assignment, total_emitted
        rows: list[dict[str, Any]] = []
        codes_now: set[int] = set()
        for cand in shell_cands:
            if budget_exhausted() or witness_assignment is not None:
                break
            code = assignment_code_from_candidate(cand, num_vars, mix_mode=mix_mode)
            codes_now.add(code)
            assignment = assignment_from_code(code, num_vars)
            sat_count = sum(1 for cl in clauses if clause_satisfied(cl, assignment))
            if (
                local_flip_rounds > 0
                and local_search_mode != "off"
                and sat_count > 0
                and sat_count < num_cl
            ):
                improved = local_search_sat(
                    assignment,
                    clauses,
                    mode=local_search_mode,
                    rounds=local_flip_rounds,
                    rng=ls_rng,
                    cache=ls_cache,
                )
                if improved != assignment:
                    assignment = improved
                    code = sum((1 << i) for i, bit in enumerate(improved) if bit)
                    sat_count = sum(1 for cl in clauses if clause_satisfied(cl, improved))
            total_emitted += 1
            cand_out = {
                "step": cand["step"],
                "seed_idx": cand["seed_idx"],
                "arc_param": cand["arc_param"],
                "derived_divisor": cand.get("derived_divisor"),
                "shell_step": shell_step,
                "rapidity_shell": shell_step,
            }
            rows.append({"cand": cand_out, "code": int(code), "sat_count": int(sat_count)})
            if num_cl == 0 or sat_count == num_cl:
                witness_assignment = assignment

        flipped: set[int] = set()
        if rows:
            flipped = _shell_flip_codes(prev_codes, codes_now)
            for row in rows:
                row["flip_changed"] = int(row["code"]) in flipped
                row["research_score"] = _compute_sat_research_score(
                    int(row["sat_count"]),
                    num_cl,
                    shell_step,
                    max(1, shell_count),
                    bool(row["flip_changed"]),
                    w_r=research_weight_rapidity,
                    w_j=research_weight_jitter,
                    w_e=research_weight_effective,
                    w_c=research_weight_cost,
                    flip_bonus=flip_bonus,
                )

        rows.sort(
            key=lambda r: (
                -int(r["sat_count"]),
                int(r["cand"]["shell_step"]),
                0 if r.get("flip_changed") else 1,
                -float(r.get("research_score", 0.0)),
                int(r["code"]),
            )
        )
        if flip_prune and prev_codes and rows:
            flip_rows = [row for row in rows if row.get("flip_changed")]
            if flip_rows:
                rows = flip_rows
            else:
                rows = rows[:1]

        for row in rows[: max(1, keep_per_shell)]:
            code = int(row["code"])
            sat_c = int(row["sat_count"])
            cand_out = row["cand"]
            cand_out["flip_changed"] = bool(row.get("flip_changed", False))
            cand_out["research_score"] = float(row.get("research_score", 0.0))
            prev_best = pool_by_code.get(code)
            prev_sc = int(prev_best["_sat_count"]) if prev_best and "_sat_count" in prev_best else -1
            if prev_best is None or sat_c >= prev_sc:
                cand_copy = dict(cand_out)
                cand_copy["_sat_count"] = sat_c
                pool_by_code[code] = cand_copy
            emitted.append(dict(cand_out))

        if len(pool_by_code) > pool_limit:
            ranked = sorted(
                pool_by_code.items(),
                key=lambda kv: int(kv[1].get("_sat_count", 0)),
                reverse=True,
            )
            pool_by_code.clear()
            for code, payload in ranked[:pool_limit]:
                pool_by_code[int(code)] = payload

        shell_trace.append(
            {
                "shell_step": shell_step,
                "shell_phase": phase_accum,
                "candidates_scored": len(shell_cands),
                "pool_size": len(pool_by_code),
                "flipped_codes": len(flipped),
            }
        )

    for shell_step in range(max(1, shell_count)):
        if budget_exhausted() or witness_assignment is not None:
            break
        omega = _omega_weight(shell_step, omega_mode, k)
        phase_step = (
            shell_phase_scale * shell_phase_stride * omega * _rapidity_delta_scale(shell_scale + shell_step * max(1, k))
        )
        phase_accum += phase_step
        slot_phases = _shell_slot_phases(
            phase_accum,
            slots_per_shell=slots_per_shell,
            slot_family=slot_family,
        )
        local_scale = _shell_neighborhood_scale(shell_step, neighborhood_mode, neighborhood_scale)
        shell_cands: list[dict[str, Any]] = []
        for slot_index, slot_phase in enumerate(slot_phases):
            if budget_exhausted():
                break
            probe_phases = [slot_phase]
            for off in range(1, max(0, neighborhood_offsets) + 1):
                delta = local_scale * float(off) * _rapidity_delta_scale(shell_scale + shell_step + off)
                probe_phases.append(slot_phase + delta)
                probe_phases.append(slot_phase - delta)
            for probe_phase in _unique_phases(probe_phases):
                arc_param = float(probe_phase)
                shell_cands.append(
                    {
                        "step": shell_step,
                        "seed_idx": int(slot_index) % 3,
                        "arc_param": arc_param,
                        "derived_divisor": None,
                    }
                )
        pool_before = len(pool_by_code)
        ingest_shell_candidates(shell_cands, shell_step)
        pool_after = len(pool_by_code)
        st_tail = shell_trace[-1] if shell_trace else {}
        arity_gate_trace.append(
            {
                "shell_step": shell_step,
                "k_arity": k,
                "pool_before": pool_before,
                "pool_after": pool_after,
                "epsilon_step_proxy": max(0.0, float(pool_before - pool_after)),
                "candidates_scored": int(st_tail.get("candidates_scored", len(shell_cands))),
                "flipped_codes": int(st_tail.get("flipped_codes", 0)),
            }
        )
        prev_codes = {assignment_code_from_candidate(c, num_vars, mix_mode=mix_mode) for c in shell_cands}

    pool_list = [dict(c) for c in pool_by_code.values()]
    for c in pool_list:
        c.pop("_sat_count", None)

    sat_arity_residual_sum = sum(float(g.get("epsilon_step_proxy", 0.0)) for g in arity_gate_trace)
    return {
        "optimizer": "rapidity-first-sat-shells-v2",
        "num_vars": num_vars,
        "num_clauses": num_cl,
        "shell_count": shell_count,
        "k_arity": k,
        "candidates": pool_list,
        "candidates_generated": len(emitted),
        "shell_trace": shell_trace,
        "arity_gate_trace": arity_gate_trace,
        "sat_arity_residual_sum": float(sat_arity_residual_sum),
        "sat_search_n": num_vars,
        "sat_search_root_scale": sat_search_root_scale(num_vars),
        "sat_search_envelope": sat_search_envelope(num_vars),
        "elapsed_s": time.perf_counter() - started,
        "witness_assignment": witness_assignment,
        "mix_mode": mix_mode,
        "local_search_mode": local_search_mode,
        "local_search_cache_size": len(ls_cache),
    }


def rapidity_first_sat_payload_by_arity(
    num_vars: int,
    clauses: list[list[int]],
    *,
    min_arity: int = 1,
    max_arity: int | None = None,
    max_seconds: float | None = None,
    mix_mode: str = "arc",
    **kwargs: Any,
) -> dict[str, Any]:
    """
    Run the geometric gate/prune pipeline incrementally, one arity at a time.

    This mirrors the rest of the geometric story more closely than a single fixed-arity run:
    arity 1, then 2, then 3, ... with pruning and witness checks after each stage.
    """
    started = time.perf_counter()
    k_lo = max(1, min_arity)
    k_hi = max(1, max_arity if max_arity is not None else num_vars)
    arity_runs: list[dict[str, Any]] = []
    combined_candidates: list[dict[str, Any]] = []
    witness_assignment: list[bool] | None = None

    for k in range(k_lo, k_hi + 1):
        remaining: float | None = None
        if max_seconds is not None:
            remaining = max(0.0, max_seconds - (time.perf_counter() - started))
            if remaining <= 0:
                break
        payload = rapidity_first_sat_payload(
            num_vars,
            clauses,
            k_arity=k,
            max_seconds=remaining,
            mix_mode=mix_mode,
            **kwargs,
        )
        arity_runs.append(
            {
                "arity": k,
                "candidates_generated": int(payload.get("candidates_generated", 0)),
                "pool_size": len(payload.get("candidates", [])),
                "elapsed_s": float(payload.get("elapsed_s", 0.0)),
                "witness_found": payload.get("witness_assignment") is not None,
                "shell_trace": payload.get("shell_trace", []),
                "arity_gate_trace": payload.get("arity_gate_trace", []),
                "sat_arity_residual_sum": float(payload.get("sat_arity_residual_sum", 0.0)),
            }
        )
        combined_candidates.extend(payload.get("candidates", []))
        if payload.get("witness_assignment") is not None:
            witness_assignment = payload["witness_assignment"]
            break

    dedup: dict[int, dict[str, Any]] = {}
    for cand in combined_candidates:
        code = assignment_code_from_candidate(cand, num_vars, mix_mode=mix_mode)
        prev = dedup.get(code)
        prev_score = float(prev.get("research_score", float("-inf"))) if prev is not None else float("-inf")
        cur_score = float(cand.get("research_score", 0.0))
        if prev is None or cur_score >= prev_score:
            dedup[code] = dict(cand)

    combined_residual = sum(float(r.get("sat_arity_residual_sum", 0.0)) for r in arity_runs)
    return {
        "optimizer": "rapidity-first-sat-by-arity",
        "num_vars": num_vars,
        "num_clauses": len(clauses),
        "arity_runs": arity_runs,
        "candidates": list(dedup.values()),
        "candidates_generated": sum(int(r["candidates_generated"]) for r in arity_runs),
        "sat_arity_residual_sum": float(combined_residual),
        "sat_search_n": num_vars,
        "sat_search_root_scale": sat_search_root_scale(num_vars),
        "sat_search_envelope": sat_search_envelope(num_vars),
        "elapsed_s": time.perf_counter() - started,
        "witness_assignment": witness_assignment,
        "max_arity_reached": arity_runs[-1]["arity"] if arity_runs else 0,
        "mix_mode": mix_mode,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Generalized geometric oracle projections")
    parser.add_argument("n", nargs="?", type=int, default=1, help="shell/input scale parameter")
    parser.add_argument(
        "--mode",
        choices=("factor", "symmetric-tip", "modular", "sat", "sat-competition"),
        default="factor",
    )
    parser.add_argument("--max-steps", type=int, default=120, help="step budget (0 => unbounded)")
    parser.add_argument("--max-seconds", type=float, default=None, help="wall-clock budget in seconds")
    parser.add_argument(
        "--search-mode",
        choices=("standard", "symmetric-tip", "auto"),
        default="auto",
        help="factor candidate walk mode",
    )
    parser.add_argument("--num-vars", type=int, default=8, help="SAT mode variable count")
    parser.add_argument("--num-clauses", type=int, default=16, help="SAT mode clause count")
    parser.add_argument("--dimacs", type=str, default=None, help="DIMACS CNF input file (sat-competition mode)")
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="SAT competition output file (sat-competition mode)",
    )
    parser.add_argument(
        "--export-csv",
        type=str,
        default=None,
        help="write canonical candidate CSV to this path",
    )
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--rigorous-sat",
        action="store_true",
        help="require DIMACS-backed exact SAT scoring/certification in sat mode",
    )
    parser.add_argument(
        "--sat-proof-max-vars",
        type=int,
        default=20,
        help="max vars for exhaustive SAT/UNSAT certification",
    )
    parser.add_argument(
        "--sat-mix",
        choices=("legacy", "arc"),
        default="legacy",
        help="SAT projection: legacy (step+seed) or arc phase mix (ATSP torus style)",
    )
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.n < 1:
        raise SystemExit("n must be >= 1")
    if args.max_steps < 0:
        raise SystemExit("--max-steps must be >= 0")
    if args.max_seconds is not None and args.max_seconds <= 0:
        raise SystemExit("--max-seconds must be > 0 when provided")
    clauses: list[list[int]] | None = None
    if args.mode == "sat":
        if args.rigorous_sat and not args.dimacs:
            raise SystemExit("--rigorous-sat requires --dimacs in --mode sat")
        if args.dimacs:
            num_vars, clauses = parse_dimacs_cnf(args.dimacs)
            args.num_vars = num_vars
            args.num_clauses = len(clauses)
    elif args.mode == "sat-competition":
        if not args.dimacs:
            raise SystemExit("--dimacs is required for --mode sat-competition")
        if not args.output:
            raise SystemExit("--output is required for --mode sat-competition")
        num_vars, clauses = parse_dimacs_cnf(args.dimacs)
        # For SAT competition mode, use a richer shell scale so candidate generation
        # does not terminate immediately on tiny `n`.
        args.n = max(210, num_vars * max(2, len(clauses)))
        args.num_vars = num_vars
        args.num_clauses = len(clauses)

    max_steps = None if args.max_steps == 0 else args.max_steps
    search_mode = args.search_mode
    if args.mode == "symmetric-tip":
        search_mode = "symmetric-tip"
    if args.mode in {"sat", "sat-competition"} and args.n < 2:
        args.n = max(2, args.num_vars * max(2, args.num_clauses))
    payload = geometric_factorization_solver(
        args.n,
        max_steps=max_steps,
        include_trivial_pair=True,
        max_seconds=args.max_seconds,
        search_mode=search_mode,
    )
    payload["factor_pick_bridge"] = build_factor_pick_bridge_payload(
        payload.get("one_step_pick_certificate")
    )
    if args.mode == "sat-competition":
        # Guard against early-stop behavior inherited from factor mode.
        attempts = 0
        shell_n = args.n
        while max_steps is not None and payload.get("steps_used", 0) < max_steps and attempts < 3:
            shell_n *= 10
            payload = geometric_factorization_solver(
                shell_n,
                max_steps=max_steps,
                include_trivial_pair=True,
                max_seconds=args.max_seconds,
                search_mode=search_mode,
            )
            payload["factor_pick_bridge"] = build_factor_pick_bridge_payload(
                payload.get("one_step_pick_certificate")
            )
            attempts += 1
        payload["sat_shell_n"] = shell_n
    candidates = payload.get("candidates", [])

    if args.mode == "modular":
        payload["modular_candidates"] = modular_projection(args.n, candidates)
    elif args.mode == "sat":
        sat_rows = sat_projection(
            candidates, args.num_vars, args.num_clauses, clauses=clauses, mix_mode=args.sat_mix
        )
        payload["sat_candidates"] = sat_rows
        payload["sat_exact_scoring"] = clauses is not None
        if clauses is not None:
            winning_assignment: list[bool] | None = None
            for row in sat_rows:
                assignment = assignment_from_code(row["assignment_code"], args.num_vars)
                if cnf_satisfied(clauses, assignment):
                    winning_assignment = assignment
                    break
            if winning_assignment is not None:
                sat_status = "SAT"
            else:
                sat_status, winning_assignment = exhaustive_cnf_status(
                    clauses, args.num_vars, max_vars=args.sat_proof_max_vars
                )
            payload["sat_status"] = sat_status
            payload["sat_witness_assignment"] = winning_assignment
            payload["sat_certified_by_exhaustive"] = args.num_vars <= args.sat_proof_max_vars
        payload["sat_bridge_certificates"] = {
            "one_step_pick": payload["factor_pick_bridge"],
        }
    elif args.mode == "sat-competition":
        sat_rows = sat_projection(
            candidates, args.num_vars, args.num_clauses, clauses=clauses, mix_mode=args.sat_mix
        )
        payload["sat_candidates"] = sat_rows
        winning_assignment: list[bool] | None = None
        for row in sat_rows:
            assignment = assignment_from_code(row["assignment_code"], args.num_vars)
            if cnf_satisfied(clauses, assignment):
                winning_assignment = assignment
                break
        if winning_assignment is not None:
            solver_result = "SAT"
        else:
            solver_result, winning_assignment = exhaustive_cnf_status(clauses, args.num_vars, max_vars=20)
        write_sat_competition_output(args.output, solver_result, winning_assignment)
        payload["dimacs"] = args.dimacs
        payload["output"] = args.output
        payload["solver_result"] = solver_result
        payload["num_vars"] = args.num_vars
        payload["num_clauses"] = args.num_clauses
        payload["sat_bridge_certificates"] = {
            "one_step_pick": payload["factor_pick_bridge"],
        }

    # Canonical CSV export on normalized candidate slots.
    csv_candidates: list[Candidate] = []
    for c in candidates:
        csv_candidates.append(
            Candidate(
                step=c["step"],
                seed_idx=c["seed_idx"],
                arc_param=float(c.get("arc_param", c["step"])),
                derived_divisor=c.get("derived_divisor"),
            )
        )
    payload["candidate_csv"] = candidate_list_to_csv(csv_candidates)
    if args.export_csv:
        with open(args.export_csv, "w", encoding="utf-8") as fh:
            fh.write(payload["candidate_csv"])
        payload["exported_csv_path"] = args.export_csv
        payload["exported_candidates"] = len(csv_candidates)

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            f"mode={args.mode} n={payload['n']} steps_used={payload['steps_used']} "
            f"candidates_generated={payload['candidates_generated']} search_mode={payload['search_mode']}"
        )
        print(f"divisors={payload['divisors']}")
        if payload["symmetric_pair"] is not None:
            print(f"symmetric_pair={payload['symmetric_pair']}")
        if args.mode == "modular":
            print(f"modular_rows={len(payload['modular_candidates'])}")
        elif args.mode == "sat":
            witnesses = [r for r in payload["sat_candidates"] if r["is_witness"]]
            print(
                f"sat_rows={len(payload['sat_candidates'])} sat_witnesses={len(witnesses)} "
                f"exact_scoring={payload.get('sat_exact_scoring', False)}"
            )
            if "sat_status" in payload:
                print(
                    f"sat_status={payload['sat_status']} "
                    f"certified_by_exhaustive={payload.get('sat_certified_by_exhaustive', False)}"
                )
            print(
                "one_step_pick_bridge="
                f"{payload.get('sat_bridge_certificates', {}).get('one_step_pick', {}).get('status', 'unknown')}"
            )
        elif args.mode == "sat-competition":
            print(
                f"sat_rows={len(payload['sat_candidates'])} "
                f"vars={payload['num_vars']} clauses={payload['num_clauses']} "
                f"result={payload['solver_result']}"
            )
            print(
                "one_step_pick_bridge="
                f"{payload.get('sat_bridge_certificates', {}).get('one_step_pick', {}).get('status', 'unknown')}"
            )
            print(f"Wrote SAT competition output to {payload['output']}")
        print("candidate_csv_preview:")
        for line in payload["candidate_csv"].splitlines()[:5]:
            print(f"  {line}")
        if args.export_csv:
            print(f"Exported {len(csv_candidates)} candidates to {args.export_csv}")


if __name__ == "__main__":
    main()

