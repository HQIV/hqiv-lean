#!/usr/bin/env python3
"""
Minimal SAT competition entrypoint for the geometric oracle.

This script intentionally keeps output silent on success and only writes the
required SAT competition result lines to the output file.

**Lean contract (mirrors `Hqiv.Geometry.SATWorstCaseCertified` /
`ATSPWorstCaseCertified`):** sound pruning never removes a satisfying
assignment; if the reachable survivor/candidate pool is fully exhausted with no
model, that certifies UNSAT. This solver therefore uses the competition timeout
as the main stop condition and returns exactly one of:

- `SAT` when a witness assignment is found,
- `UNSAT` when the traversed candidate pool is exhausted with no witness,
- `UNKNOWN` when time runs out before exhaustion.

Important complexity note: the rapidity/arity machinery currently certifies only
an envelope/budget contract on survivor work and additive residuals. It does not
by itself establish a polynomial-time algorithm for SAT. In particular,
candidate generation can still be factorial/exponential in the worst case unless
an additional proof shows that the generated frontier and every residual budget
remain polynomially bounded as a function of the instance size.
"""

from __future__ import annotations

import argparse
import json
import random
from typing import Any

from generalized_geometric_oracle import (
    assignment_from_code,
    build_sat_certificate,
    cnf_satisfied,
    greedy_flip_completion,
    local_search_sat,
    parse_dimacs_cnf,
    rapidity_first_sat_payload_by_arity,
    rapidity_first_sat_payload,
    sat_projection,
    traverse_candidate_pool_exhaustively,
    write_sat_competition_output,
)
from geometric_factorization_solver import Candidate, candidate_list_to_csv, geometric_factorization_solver


def _sat_row_sort_key(row: dict[str, Any]) -> tuple:
    """Prefer clause score, then ATSP-style research ordering when present."""
    sc = -int(row["satisfied_clause_count"])
    code = int(row["assignment_code"])
    if "research_score" not in row:
        return (sc, code)
    return (
        sc,
        int(row.get("shell_step", 0)),
        0 if row.get("flip_changed") else 1,
        -float(row["research_score"]),
        code,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Geometric SAT competition solver")
    parser.add_argument("dimacs_pos", nargs="?", help="DIMACS CNF input path")
    parser.add_argument("output_pos", nargs="?", help="SAT result output path")
    parser.add_argument("--dimacs", type=str, default=None, help="DIMACS CNF input path")
    parser.add_argument("--output", type=str, default=None, help="SAT result output path")
    parser.add_argument("--max-steps", type=int, default=0, help="candidate walk step budget (0 => unbounded)")
    parser.add_argument(
        "--max-seconds",
        type=float,
        default=1800.0,
        help="wall-clock budget in seconds (default 1800 = 30 minutes; competition-style cap)",
    )
    parser.add_argument(
        "--export-csv",
        type=str,
        default=None,
        help="optional canonical candidate CSV export path",
    )
    parser.add_argument(
        "--sat-search",
        choices=("both", "rapidity-first", "rapidity-by-arity", "legacy"),
        default="both",
        help="candidate stream: rapidity SAT shells, rapidity stepped by arity, legacy factor walk, or merged variants",
    )
    parser.add_argument("--min-arity", type=int, default=1, help="starting arity for arity-by-arity rapidity SAT")
    parser.add_argument("--max-arity", type=int, default=0, help="final arity for arity-by-arity rapidity SAT (0 => num_vars)")
    parser.add_argument(
        "--sat-mix",
        choices=("legacy", "arc"),
        default="arc",
        help="how geometric triples map to Boolean assignments (arc mixes phase like the ATSP torus)",
    )
    parser.add_argument("--rapidity-shells", type=int, default=48, help="rapidity-first SAT shell count")
    parser.add_argument("--shell-phase-scale", type=float, default=1.0, help="global scale on rapidity phase increments")
    parser.add_argument("--shell-phase-stride", type=float, default=1.0, help="extra multiplier on per-shell phase increment")
    parser.add_argument(
        "--omega-mode",
        choices=("unit", "reciprocal", "sqrt-reciprocal", "log-reciprocal", "one-over-k", "root-scale"),
        default="sqrt-reciprocal",
        help="monotone shell weight (ATSP rapidity_first ladder)",
    )
    parser.add_argument("--slots-per-shell", type=int, default=8, help="periodic slots emitted per shell")
    parser.add_argument(
        "--slot-family",
        choices=("periodic", "one-over-k", "reflected", "hybrid"),
        default="hybrid",
        help="slot family within each shell",
    )
    parser.add_argument("--neighborhood-offsets", type=int, default=1, help="extra phase probes on each side of every slot")
    parser.add_argument(
        "--neighborhood-mode",
        choices=("constant", "reciprocal", "sqrt-reciprocal"),
        default="reciprocal",
        help="how local phase probe radius decays with shell depth",
    )
    parser.add_argument("--neighborhood-scale", type=float, default=0.35, help="base local probe radius multiplier")
    parser.add_argument("--keep-per-shell", type=int, default=12, help="retain at most this many candidates per shell")
    parser.add_argument("--pool-limit", type=int, default=384, help="global pool cap inside rapidity-first SAT")
    parser.add_argument(
        "--flip-prune",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="keep shell candidates whose assignment code flipped vs previous shell (ATSP-style)",
    )
    parser.add_argument(
        "--rapidity-local-flips",
        type=int,
        default=2,
        help="local completion rounds per rapidity shell candidate (greedy/walksat/both)",
    )
    parser.add_argument(
        "--local-search-mode",
        choices=("off", "greedy", "walksat", "both"),
        default="greedy",
        help="local completion inside each shell (cached; mirrors ATSP local completion)",
    )
    parser.add_argument("--local-search-seed", type=int, default=42, help="RNG seed for walksat/both local search")
    parser.add_argument("--research-weight-rapidity", type=float, default=1.0, help="research_score weight on shell depth")
    parser.add_argument("--research-weight-jitter", type=float, default=0.30, help="research_score weight on detuning")
    parser.add_argument("--research-weight-effective", type=float, default=0.20, help="research_score weight on clause fraction")
    parser.add_argument("--research-weight-cost", type=float, default=0.10, help="research_score weight on unsat fraction")
    parser.add_argument("--flip-bonus", type=float, default=0.10, help="subtract from research_score when flip_changed")
    parser.add_argument(
        "--post-local-search-mode",
        choices=("off", "greedy", "walksat", "both"),
        default="greedy",
        help="local search on merged projected rows before exhaustive fallback",
    )
    parser.add_argument("--post-local-search-rounds", type=int, default=8, help="round budget for post-merge local search")
    parser.add_argument(
        "--max-merged-candidates",
        type=int,
        default=16384,
        help="cap merged heuristic candidates before sat_projection (0 = no cap)",
    )
    parser.add_argument(
        "--certificate-out",
        type=str,
        default=None,
        help="optional JSON file to write SAT/UNSAT/UNKNOWN certificate payload",
    )
    parser.add_argument(
        "--drat-out",
        type=str,
        default=None,
        help="optional file to write a DRAT-like UNSAT trace generated during pool traversal",
    )
    return parser


def resolve_paths(args: argparse.Namespace) -> tuple[str, str]:
    dimacs_path = args.dimacs or args.dimacs_pos
    output_path = args.output or args.output_pos
    if not dimacs_path:
        raise SystemExit("missing DIMACS input path (positional or --dimacs)")
    if not output_path:
        raise SystemExit("missing output path (positional or --output)")
    return dimacs_path, output_path


def main() -> None:
    args = build_parser().parse_args()
    if args.max_steps < 0:
        raise SystemExit("--max-steps must be >= 0")
    if args.max_seconds is not None and args.max_seconds <= 0:
        raise SystemExit("--max-seconds must be > 0 when provided")
    if args.max_merged_candidates < 0:
        raise SystemExit("--max-merged-candidates must be >= 0")
    if args.shell_phase_scale <= 0 or args.shell_phase_stride <= 0:
        raise SystemExit("--shell-phase-scale and --shell-phase-stride must be > 0")
    if args.slots_per_shell < 1 or args.keep_per_shell < 1 or args.pool_limit < 1:
        raise SystemExit("--slots-per-shell, --keep-per-shell, --pool-limit must be >= 1")
    if args.neighborhood_offsets < 0 or args.neighborhood_scale < 0:
        raise SystemExit("--neighborhood-offsets must be >= 0 and --neighborhood-scale >= 0")
    if args.post_local_search_rounds < 0:
        raise SystemExit("--post-local-search-rounds must be >= 0")

    dimacs_path, output_path = resolve_paths(args)
    num_vars, clauses = parse_dimacs_cnf(dimacs_path)

    shell_n = max(210, num_vars * max(2, len(clauses)))
    max_steps = None if args.max_steps == 0 else args.max_steps
    mix_mode = args.sat_mix

    winning_assignment: list[bool] | None = None
    merged: list[dict[str, Any]] = []
    rap_elapsed_s = 0.0
    traversal_summary: dict[str, Any] | None = None
    rap_payload: dict[str, Any] | None = None

    if args.sat_search in {"both", "rapidity-first", "rapidity-by-arity"}:
        rapidity_budget = args.max_seconds
        rapidity_kwargs = dict(
            shell_count=max(4, args.rapidity_shells),
            shell_phase_scale=args.shell_phase_scale,
            shell_phase_stride=args.shell_phase_stride,
            omega_mode=args.omega_mode,
            slots_per_shell=args.slots_per_shell,
            slot_family=args.slot_family,
            neighborhood_offsets=args.neighborhood_offsets,
            neighborhood_mode=args.neighborhood_mode,
            neighborhood_scale=args.neighborhood_scale,
            keep_per_shell=args.keep_per_shell,
            pool_limit=args.pool_limit,
            flip_prune=args.flip_prune,
            max_seconds=rapidity_budget,
            max_candidates=None if max_steps is None else max(2000, max_steps * 64),
            local_flip_rounds=max(0, args.rapidity_local_flips),
            local_search_mode=args.local_search_mode,
            mix_mode=mix_mode,
            research_weight_rapidity=args.research_weight_rapidity,
            research_weight_jitter=args.research_weight_jitter,
            research_weight_effective=args.research_weight_effective,
            research_weight_cost=args.research_weight_cost,
            flip_bonus=args.flip_bonus,
            local_search_rng_seed=args.local_search_seed,
        )
        if args.sat_search == "rapidity-by-arity":
            rap = rapidity_first_sat_payload_by_arity(
                num_vars,
                clauses,
                min_arity=max(1, args.min_arity),
                max_arity=(num_vars if args.max_arity <= 0 else max(1, args.max_arity)),
                **rapidity_kwargs,
            )
        else:
            rap = rapidity_first_sat_payload(num_vars, clauses, **rapidity_kwargs)
        rap_payload = rap
        rap_elapsed_s = float(rap.get("elapsed_s", 0.0))
        if rap.get("witness_assignment") is not None:
            winning_assignment = rap["witness_assignment"]
        merged.extend(rap.get("candidates", []))

    if args.sat_search in {"both", "legacy"}:
        legacy_seconds = args.max_seconds
        if args.max_seconds is not None and args.sat_search == "both":
            legacy_seconds = max(0.0, float(args.max_seconds) - rap_elapsed_s)
        payload = geometric_factorization_solver(
            shell_n,
            max_steps=max_steps,
            include_trivial_pair=True,
            max_seconds=legacy_seconds,
        )

        # Guard against early-stop inherited from factor-mode internals.
        attempts = 0
        while max_steps is not None and payload.get("steps_used", 0) < max_steps and attempts < 3:
            shell_n *= 10
            payload = geometric_factorization_solver(
                shell_n,
                max_steps=max_steps,
                include_trivial_pair=True,
                max_seconds=legacy_seconds,
            )
            attempts += 1
        merged.extend(payload.get("candidates", []))

    if args.max_merged_candidates > 0 and len(merged) > args.max_merged_candidates:
        merged = merged[-args.max_merged_candidates :]

    sat_rows = sat_projection(merged, num_vars, len(clauses), clauses=clauses, mix_mode=mix_mode)
    if winning_assignment is None:
        sat_rows.sort(key=_sat_row_sort_key)
        post_rng = random.Random(args.local_search_seed)
        post_cache: dict = {}
        for row in sat_rows:
            assignment = assignment_from_code(row["assignment_code"], num_vars)
            if cnf_satisfied(clauses, assignment):
                winning_assignment = assignment
                break
            if row["satisfied_clause_count"] > 0 and args.post_local_search_mode != "off":
                improved = local_search_sat(
                    assignment,
                    clauses,
                    mode=args.post_local_search_mode,
                    rounds=max(1, args.post_local_search_rounds),
                    rng=post_rng,
                    cache=post_cache,
                )
                if cnf_satisfied(clauses, improved):
                    winning_assignment = improved
                    break
            elif row["satisfied_clause_count"] > 0:
                improved = greedy_flip_completion(
                    assignment,
                    clauses,
                    max_rounds=max(4, args.rapidity_local_flips * 2),
                )
                if cnf_satisfied(clauses, improved):
                    winning_assignment = improved
                    break

    if winning_assignment is not None:
        status = "SAT"
    else:
        seed_codes = [int(row["assignment_code"]) for row in sat_rows]
        traversal_summary = traverse_candidate_pool_exhaustively(
            num_vars,
            clauses,
            seed_codes,
            max_seconds=args.max_seconds,
            emit_drat=args.drat_out is not None,
        )
        status = str(traversal_summary.get("status", "UNKNOWN"))
        if status == "SAT":
            winning_assignment = traversal_summary.get("assignment")
    write_sat_competition_output(output_path, status, winning_assignment)

    if args.drat_out and traversal_summary is not None and traversal_summary.get("drat_lines"):
        with open(args.drat_out, "w", encoding="utf-8") as fh:
            for line in traversal_summary.get("drat_lines", []):
                fh.write(f"{line}\n")

    if args.certificate_out:
        certificate = build_sat_certificate(
            clauses,
            num_vars,
            status,
            winning_assignment,
            exhaustive_limit=0,
            traversal_summary=traversal_summary,
        )
        certificate.update(
            {
                "dimacs_path": dimacs_path,
                "output_path": output_path,
                "sat_search": args.sat_search,
                "sat_mix": mix_mode,
                "heuristic_candidates": len(merged),
            }
        )
        if rap_payload is not None:
            certificate["lean_certificate_refs"] = [
                "Hqiv.Geometry.SATWorstCaseCertified (SoundRemovalChain, sat_cumulative_arity_residuals_le_envelope)",
            ]
            certificate["rapidity_optimizer"] = rap_payload.get("optimizer")
            certificate["sat_search_n"] = rap_payload.get("sat_search_n", num_vars)
            certificate["sat_search_root_scale"] = rap_payload.get("sat_search_root_scale")
            certificate["sat_search_envelope"] = rap_payload.get("sat_search_envelope")
            certificate["sat_arity_residual_sum"] = rap_payload.get("sat_arity_residual_sum")
            if rap_payload.get("optimizer") == "rapidity-first-sat-by-arity":
                certificate["arity_runs"] = rap_payload.get("arity_runs", [])
            else:
                certificate["arity_gate_trace"] = rap_payload.get("arity_gate_trace", [])
        if args.sat_search == "rapidity-by-arity":
            certificate["arity_schedule"] = {
                "min_arity": max(1, args.min_arity),
                "max_arity": (num_vars if args.max_arity <= 0 else max(1, args.max_arity)),
            }
        if sat_rows:
            best_row = max(sat_rows, key=lambda row: int(row.get("satisfied_clause_count", 0)))
            certificate["best_heuristic_row"] = {
                "assignment_code": int(best_row["assignment_code"]),
                "satisfied_clause_count": int(best_row["satisfied_clause_count"]),
                "shell_step": int(best_row.get("shell_step", 0)),
                "flip_changed": bool(best_row.get("flip_changed", False)),
                "research_score": float(best_row.get("research_score", 0.0)),
            }
        with open(args.certificate_out, "w", encoding="utf-8") as fh:
            json.dump(certificate, fh, indent=2)

    if args.export_csv:
        csv_candidates: list[Candidate] = []
        for c in merged:
            csv_candidates.append(
                Candidate(
                    step=c["step"],
                    seed_idx=c["seed_idx"],
                    arc_param=float(c.get("arc_param", c["step"])),
                    derived_divisor=c.get("derived_divisor"),
                )
            )
        with open(args.export_csv, "w", encoding="utf-8") as fh:
            fh.write(candidate_list_to_csv(csv_candidates))


if __name__ == "__main__":
    main()

