#!/usr/bin/env python3
"""Benchmark reverse-Shor period selector: range, success rate, timing."""

from __future__ import annotations

import json
import math
import statistics
import sys
import time
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

import hqiv_reverse_shor_period_selector as rss


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def _semiprime(p: int, q: int) -> int:
    return p * q


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def benchmark_one(n: int, *, max_steps: int, max_seconds: float) -> dict:
    t0 = time.perf_counter()
    r = rss.reverse_shor_factor(n, max_steps=max_steps, max_seconds=max_seconds)
    elapsed = time.perf_counter() - t0
    ok = r["success"] and _prod(r["factors"]) == n
    trace = r.get("odd_node", r).get("trace", r.get("trace", []))
    last = trace[-1] if trace else {}
    return {
        "n": n,
        "bits": n.bit_length(),
        "success": ok,
        "factors": r["factors"],
        "steps_used": r.get("odd_node", r).get("steps_used", r.get("steps_used")),
        "elapsed_s": elapsed,
        "L": r.get("odd_node", r).get("L"),
        "basis_card": r.get("odd_node", r).get("basis_card"),
        "last_carrier_support": last.get("carrier_support_size"),
        "last_candidates_tried": last.get("candidates_tried"),
        "last_mirror_witnesses": last.get("mirror_witness_count"),
    }


def run_suite() -> dict:
    max_steps = 240
    max_seconds = 3.0

    # Small composites / semiprimes (product form)
    small_semiprimes = [
        _semiprime(p, q)
        for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
        for q in (p, p + 2, p + 4, p + 6)
        if p < q and p * q < 2000
    ]
    small_semiprimes = sorted(set(small_semiprimes))

    # Medium semiprimes (two ~sqrt(n) primes)
    medium = [
        _semiprime(101, 103),
        _semiprime(1009, 1013),
        _semiprime(9973, 997),
        15,
        143,
        899,
        3599,
        10403 * 10499,  # ~1e8
    ]

    # Powers of two and evens
    specials = [16, 32, 64, 100, 2 * 3 * 5 * 7]

    # Primes (expect fail unless lucky)
    primes = [17, 101, 1009, 9973, 65537]

    rows: list[dict] = []
    for n in small_semiprimes:
        rows.append(benchmark_one(n, max_steps=max_steps, max_seconds=max_seconds))
    for n in medium:
        if n not in {r["n"] for r in rows}:
            rows.append(benchmark_one(n, max_steps=max_steps, max_seconds=max_seconds))
    for n in specials + primes:
        rows.append(benchmark_one(n, max_steps=max_steps, max_seconds=max_seconds))

    # Size sweep: random semiprimes by bit length
    import random

    random.seed(42)
    bit_sweep: list[dict] = []
    for bits in range(8, 33, 4):
        hits = 0
        trials = 8
        times: list[float] = []
        for _ in range(trials):
            # random odd factors ~2^(bits/2)
            half = max(2, bits // 2)
            lo = 1 << (half - 1)
            hi = min((1 << half) - 1, 50000)
            if lo >= hi:
                continue
            p = random.randrange(lo | 1, hi, 2)
            while _is_prime(p) is False and p < hi:
                p += 2
            q = random.randrange(lo | 1, hi, 2)
            while _is_prime(q) is False and q < hi:
                q += 2
            if p == q:
                q += 2
            n = p * q
            row = benchmark_one(n, max_steps=max_steps, max_seconds=max_seconds)
            times.append(row["elapsed_s"])
            if row["success"]:
                hits += 1
        bit_sweep.append(
            {
                "target_bits": bits,
                "trials": trials,
                "hits": hits,
                "hit_rate": hits / trials,
                "median_elapsed_s": statistics.median(times) if times else None,
                "max_elapsed_s": max(times) if times else None,
            }
        )

    semiprime_rows = [r for r in rows if not _is_prime(r["n"]) and r["n"] > 1]
    sp_hits = sum(1 for r in semiprime_rows if r["success"])
    prime_rows = [r for r in rows if _is_prime(r["n"])]
    false_pos = sum(1 for r in prime_rows if r["success"])

    return {
        "config": {"max_steps": max_steps, "max_seconds": max_seconds},
        "summary": {
            "semiprime_count": len(semiprime_rows),
            "semiprime_hits": sp_hits,
            "semiprime_hit_rate": sp_hits / max(1, len(semiprime_rows)),
            "prime_count": len(prime_rows),
            "prime_false_factorizations": false_pos,
            "max_n_tested": max(r["n"] for r in rows),
            "max_bits_tested": max(r["bits"] for r in rows),
        },
        "bit_sweep": bit_sweep,
        "rows": rows,
    }


def main() -> None:
    report = run_suite()
    out = Path(__file__).resolve().parent.parent / "data" / "reverse_shor_benchmark.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2))
    s = report["summary"]
    print("Reverse-Shor period selector benchmark")
    print("=" * 40)
    print(f"config: max_steps={report['config']['max_steps']} max_seconds={report['config']['max_seconds']}")
    print(
        f"semiprimes: {s['semiprime_hits']}/{s['semiprime_count']} "
        f"({100 * s['semiprime_hit_rate']:.1f}% hit rate)"
    )
    print(f"primes: {s['prime_false_factorizations']} false splits on {s['prime_count']} primes")
    print(f"max n tested: {s['max_n_tested']} ({s['max_bits_tested']} bits)")
    print("\nBit-length sweep (random semiprimes, 8 trials each):")
    for row in report["bit_sweep"]:
        print(
            f"  ~{row['target_bits']:2d} bits: {row['hits']}/{row['trials']} hits, "
            f"median {row['median_elapsed_s']:.4f}s, max {row['max_elapsed_s']:.4f}s"
        )
    failures = [r for r in report["rows"] if not _is_prime(r["n"]) and r["n"] > 1 and not r["success"]]
    if failures:
        print(f"\nSample failures ({min(10, len(failures))} of {len(failures)}):")
        for r in failures[:10]:
            print(f"  n={r['n']} bits={r['bits']} steps={r['steps_used']} L={r['L']}")
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()
