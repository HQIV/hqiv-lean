#!/usr/bin/env python3
"""
Benchmark `factor_grok.octonion_factor` on semiprimes n = p*q.

Usage:
  python3 bench_factor_grok_semiprimes.py
  python3 bench_factor_grok_semiprimes.py --quick   # only small n (default)

Heuristic may return [n] when no split is found (both primes can exceed trial bound).
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent


def _load():
    spec = importlib.util.spec_from_file_location("factor_grok", _SCRIPTS / "factor_grok.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _prod(xs: list[int]) -> int:
    p = 1
    for x in xs:
        p *= x
    return p


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--full",
        action="store_true",
        help="include slower cases (n up to ~1.5e5 semiprimes)",
    )
    args = p.parse_args()

    mod = _load()
    f = mod.octonion_factor

    cases: list[tuple[str, int, int]] = [
        ("tiny", 17, 19),
        ("small", 101, 103),
        ("mid-A", 257, 263),
        ("mid-B", 307, 311),
        ("~1e6 semiprime", 1009, 1013),
    ]
    if args.full:
        cases.extend(
            [
                ("larger (slow rep loops)", 379, 397),
                ("~1e8 scale", 10007, 10009),
            ]
        )

    print("factor_grok semiprime bench")
    print(f"_dynamic_p_max(10**6) = {mod._dynamic_p_max(10**6)}")
    print()

    for label, a, b in cases:
        n = a * b
        t0 = time.perf_counter()
        out = f(n)
        dt = time.perf_counter() - t0
        want = sorted([a, b])
        got_sorted = sorted(out)
        splits = _prod(out) == n and got_sorted == want
        status = "SPLIT_OK" if splits else "NO_SPLIT_OR_PARTIAL"
        print(f"{label:28}  n={n}  bits={n.bit_length()}  {dt:8.4f}s  {status}")
        print(f"{'':28}  want {want}")
        print(f"{'':28}  got  {got_sorted}")
        print()


if __name__ == "__main__":
    main()
