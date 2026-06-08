#!/usr/bin/env python3
"""
Batch benchmark for OSH gate / Hopf-intersection factorization search.

Corpus tiers:
  tiny     — hand-picked KNOWN_FACTOR_VECTORS semiprimes
  small    — all semiprimes p*q with primes p <= q, q < 100   (~ hundreds)
  medium   — q < 300                                          (~ thousands)
  u64      — rows from data/semiprimes_u64.json               (49 large cases)

Usage:
  python3 osh_hopf_benchmark.py --tier small --mode hopf-search
  python3 osh_hopf_benchmark.py --tier medium --mode all --json-out /tmp/osh_bench.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

_SCRIPTS = Path(__file__).resolve().parent
_REPO = _SCRIPTS.parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import geometric_factorization_solver as gfs
import osh_gate_factorization as osh

DEFAULT_U64_PATH = _REPO / "data" / "semiprimes_u64.json"


@dataclass(frozen=True)
class SemiprimeCase:
    n: int
    p: int
    q: int

    @property
    def expected_pair(self) -> list[int]:
        return sorted([self.p, self.q])

    @property
    def bits(self) -> int:
        return self.n.bit_length()


def primes_below(limit: int) -> list[int]:
    if limit <= 2:
        return []
    sieve = bytearray(b"\x01") * limit
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            start = p * p
            sieve[start:limit:p] = b"\x00" * ((limit - start - 1) // p + 1)
    return [i for i in range(2, limit) if sieve[i]]


def semiprimes_q_below(q_max: int) -> list[SemiprimeCase]:
    ps = primes_below(q_max)
    out: list[SemiprimeCase] = []
    for i, p in enumerate(ps):
        for q in ps[i:]:
            out.append(SemiprimeCase(n=p * q, p=p, q=q))
    return out


def tiny_corpus() -> list[SemiprimeCase]:
    out: list[SemiprimeCase] = []
    for n, factors in gfs.KNOWN_FACTOR_VECTORS.items():
        if len(factors) != 2:
            continue
        p, q = sorted(factors)
        if p * q != n:
            continue
        out.append(SemiprimeCase(n=n, p=p, q=q))
    return sorted(out, key=lambda c: c.n)


def load_u64_corpus(path: Path = DEFAULT_U64_PATH) -> list[SemiprimeCase]:
    if not path.is_file():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data.get("rows", [])
    out: list[SemiprimeCase] = []
    for row in rows:
        p = int(row["p"])
        q = int(row["q"])
        n = int(row["n"])
        if p * q != n:
            continue
        out.append(SemiprimeCase(n=n, p=min(p, q), q=max(p, q)))
    return out


def corpus_for_tier(tier: str, *, u64_path: Path = DEFAULT_U64_PATH) -> list[SemiprimeCase]:
    tier = tier.lower()
    if tier == "tiny":
        return tiny_corpus()
    if tier == "small":
        return semiprimes_q_below(100)
    if tier == "medium":
        return semiprimes_q_below(300)
    if tier == "large":
        return semiprimes_q_below(1000)
    if tier == "u64":
        return load_u64_corpus(u64_path)
    raise ValueError(f"unknown tier: {tier}")


def budget_for_case(case: SemiprimeCase) -> tuple[int, float]:
    bits = case.bits
    if bits <= 16:
        return 800, 3.0
    if bits <= 24:
        return 1200, 8.0
    if bits <= 32:
        return 2000, 20.0
    return 3000, 45.0


def run_one(
    case: SemiprimeCase,
    *,
    q_lookup_mode: str,
    hopf_search: bool,
    hopf_chart_width: int = 1,
    max_steps: int | None = None,
    max_seconds: float | None = None,
) -> dict[str, Any]:
    ms = max_steps
    sec = max_seconds
    if ms is None or sec is None:
        default_steps, default_sec = budget_for_case(case)
        if ms is None:
            ms = default_steps
        if sec is None:
            sec = default_sec

    t0 = time.perf_counter()
    payload = osh.osh_factor_once(
        case.n,
        max_steps=ms,
        max_seconds=sec,
        include_trivial_pair=False,
        q_lookup_mode=q_lookup_mode,
        hopf_chart_width=hopf_chart_width,
        hopf_search=hopf_search,
    )
    elapsed = time.perf_counter() - t0
    pair = payload.get("symmetric_pair")
    hit = bool(payload.get("early_stopped") and pair == case.expected_pair)
    return {
        "n": case.n,
        "p": case.p,
        "q": case.q,
        "bits": case.bits,
        "hit": hit,
        "early_stopped": payload.get("early_stopped"),
        "symmetric_pair": pair,
        "expected_pair": case.expected_pair,
        "steps_used": payload.get("steps_used"),
        "tested_candidate_count": payload.get("tested_candidate_count"),
        "search_coverage_fraction": payload.get("search_coverage_fraction"),
        "slot_coverage_fraction": payload.get("slot_coverage_fraction"),
        "hopf_shell_bound": payload.get("hopf_shell_bound"),
        "timed_out": payload.get("timed_out"),
        "elapsed_s": elapsed,
        "q_lookup_mode": q_lookup_mode,
        "hopf_search": hopf_search,
    }


def run_batch(
    cases: list[SemiprimeCase],
    *,
    q_lookup_mode: str,
    hopf_search: bool,
    hopf_chart_width: int = 1,
    limit: int | None = None,
    progress_every: int = 50,
) -> dict[str, Any]:
    subset = cases[:limit] if limit is not None else cases
    results: list[dict[str, Any]] = []
    misses: list[dict[str, Any]] = []
    t0 = time.perf_counter()

    for i, case in enumerate(subset):
        row = run_one(
            case,
            q_lookup_mode=q_lookup_mode,
            hopf_search=hopf_search,
            hopf_chart_width=hopf_chart_width,
        )
        results.append(row)
        if not row["hit"]:
            misses.append(row)
        if progress_every > 0 and (i + 1) % progress_every == 0:
            hits = sum(1 for r in results if r["hit"])
            print(
                f"  progress {i + 1}/{len(subset)} hits={hits} "
                f"rate={hits / (i + 1):.3f}",
                file=sys.stderr,
            )

    hits = sum(1 for r in results if r["hit"])
    elapsed = time.perf_counter() - t0
    return {
        "tier_count": len(subset),
        "hits": hits,
        "misses": len(misses),
        "hit_rate": hits / max(1, len(subset)),
        "elapsed_s": elapsed,
        "q_lookup_mode": q_lookup_mode,
        "hopf_search": hopf_search,
        "miss_samples": misses[:20],
        "results": results,
    }


def run_mode_suite(
    cases: list[SemiprimeCase],
    mode: str,
    *,
    limit: int | None = None,
    hopf_chart_width: int = 1,
) -> dict[str, Any]:
    suites: dict[str, dict[str, Any]] = {}
    if mode in ("flat", "all"):
        suites["flat"] = run_batch(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_FLAT,
            hopf_search=False,
            hopf_chart_width=hopf_chart_width,
            limit=limit,
        )
    if mode in ("hopf", "all"):
        suites["hopf"] = run_batch(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=False,
            hopf_chart_width=hopf_chart_width,
            limit=limit,
        )
    if mode in ("hopf-search", "all"):
        suites["hopf_search"] = run_batch(
            cases,
            q_lookup_mode=osh.Q_LOOKUP_HOPF,
            hopf_search=True,
            hopf_chart_width=hopf_chart_width,
            limit=limit,
        )
    return suites


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Batch OSH / Hopf factorization benchmark")
    p.add_argument(
        "--tier",
        choices=("tiny", "small", "medium", "large", "u64"),
        default="small",
        help="semiprime corpus size",
    )
    p.add_argument(
        "--mode",
        choices=("flat", "hopf", "hopf-search", "all"),
        default="hopf-search",
        help="lookup mode(s) to run",
    )
    p.add_argument("--limit", type=int, default=None, help="cap number of cases")
    p.add_argument("--hopf-chart-width", type=int, default=1)
    p.add_argument("--json-out", type=Path, default=None, help="write full results JSON")
    p.add_argument("--u64-path", type=Path, default=DEFAULT_U64_PATH)
    return p


def main() -> None:
    args = build_parser().parse_args()
    cases = corpus_for_tier(args.tier, u64_path=args.u64_path)
    if not cases:
        raise SystemExit(f"empty corpus for tier={args.tier}")

    print(
        f"tier={args.tier} cases={len(cases)} mode={args.mode} "
        f"limit={args.limit or 'all'}",
        file=sys.stderr,
    )
    suites = run_mode_suite(
        cases,
        args.mode,
        limit=args.limit,
        hopf_chart_width=args.hopf_chart_width,
    )

    summary: dict[str, Any] = {
        "tier": args.tier,
        "corpus_size": len(cases),
        "limit": args.limit,
        "suites": {
            name: {
                "hits": s["hits"],
                "misses": s["misses"],
                "hit_rate": s["hit_rate"],
                "elapsed_s": s["elapsed_s"],
                "miss_samples": s["miss_samples"],
            }
            for name, s in suites.items()
        },
    }

    print(json.dumps(summary, indent=2, sort_keys=True))

    if args.json_out is not None:
        args.json_out.write_text(
            json.dumps({"summary": summary, "suites": suites}, indent=2, sort_keys=True),
            encoding="utf-8",
        )
        print(f"wrote {args.json_out}", file=sys.stderr)


if __name__ == "__main__":
    main()
