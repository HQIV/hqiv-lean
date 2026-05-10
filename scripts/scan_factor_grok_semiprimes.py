#!/usr/bin/env python3
"""
Scan all semiprimes n = p * q with primes p <= q and q < 10000.
Run factor_grok.octonion_factor(n); log every case that does not return the full prime factorization.

Usage:
  python3 scan_factor_grok_semiprimes.py
  python3 scan_factor_grok_semiprimes.py --limit 5000   # first N pairs only (debug)
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
_REPO = _SCRIPTS.parent
_OUT_DEFAULT = _REPO / "data" / "factor_grok_semiprime_misses.log"


def _primes_below(limit: int) -> list[int]:
    """Primes p with 2 <= p < limit."""
    if limit <= 2:
        return []
    sieve = bytearray(b"\x01") * limit
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start:limit:step] = b"\x00" * ((limit - start - 1) // step + 1)
    return [i for i in range(2, limit) if sieve[i]]


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--limit",
        type=int,
        default=None,
        help="stop after this many pairs (i<=j enumeration order)",
    )
    p.add_argument(
        "-o",
        "--output",
        type=Path,
        default=_OUT_DEFAULT,
        help=f"log file for misses (default: {_OUT_DEFAULT})",
    )
    args = p.parse_args()

    spec = importlib.util.spec_from_file_location("factor_grok", _SCRIPTS / "factor_grok.py")
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader
    spec.loader.exec_module(mod)
    factor_fn = mod.octonion_factor

    primes = _primes_below(10000)
    total_pairs = len(primes) * (len(primes) + 1) // 2

    args.output.parent.mkdir(parents=True, exist_ok=True)

    misses = 0
    checked = 0
    t0 = time.perf_counter()

    with args.output.open("w", encoding="utf-8") as log:
        log.write(
            f"# factor_grok semiprime scan: p <= q, primes q < 10000\n"
            f"# primes count: {len(primes)}  total_pairs: {total_pairs}\n"
            f"# n  p  q  got(sorted)  expected\n"
        )

        for i, pi in enumerate(primes):
            for j in range(i, len(primes)):
                pj = primes[j]
                n = pi * pj
                checked += 1
                want = sorted([pi, pj])
                got = sorted(factor_fn(n))
                if got != want:
                    misses += 1
                    line = f"{n}\t{pi}\t{pj}\t{got}\t{want}\n"
                    log.write(line)
                    log.flush()

                if args.limit is not None and checked >= args.limit:
                    break
            if args.limit is not None and checked >= args.limit:
                break

            if checked % 50_000 == 0:
                elapsed = time.perf_counter() - t0
                print(f"progress {checked}/{total_pairs}  misses={misses}  {elapsed:.1f}s", flush=True)

    elapsed = time.perf_counter() - t0
    print(
        f"done: checked={checked}  misses={misses}  "
        f"hit_rate={(checked-misses)/max(1,checked)*100:.4f}%  time={elapsed:.2f}s",
        file=sys.stderr,
    )
    print(f"miss log: {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
