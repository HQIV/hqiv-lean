#!/usr/bin/env python3
"""
Build a deterministic semiprime corpus up to 64 bits.

Produces JSON rows:
  { "target_bits", "bits", "p", "q", "n" }
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def is_probable_prime_u64(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
    for p in small:
        if n == p:
            return True
        if n % p == 0 and n != p:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    # Deterministic Miller-Rabin bases for 64-bit unsigned range.
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        witness = True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                witness = False
                break
        if witness:
            return False
    return True


def next_prime(n: int) -> int:
    if n <= 2:
        return 2
    x = n if n % 2 == 1 else n + 1
    while not is_probable_prime_u64(x):
        x += 2
    return x


def build_prime_cache(max_factor_bits: int) -> dict[int, int]:
    out: dict[int, int] = {}
    for k in range(2, max_factor_bits + 1):
        # Start near upper edge of k-bit interval for fast target-bit coverage.
        start = (1 << k) - 4096
        if start < (1 << (k - 1)):
            start = (1 << (k - 1)) + 3
        out[k] = next_prime(start)
    return out


def build_one(target_bits: int, prime_cache: dict[int, int]) -> dict[str, int]:
    # Split target bits across two prime factors.
    a = max(2, target_bits // 2)
    b = max(2, target_bits - a)
    p = prime_cache[a]
    q = prime_cache[b]
    n = p * q

    # If still below target, gently advance q.
    guard = 0
    while n.bit_length() < target_bits and guard < 128:
        q = next_prime(q + 2)
        n = p * q
        guard += 1
    return {
        "target_bits": target_bits,
        "bits": n.bit_length(),
        "p": p,
        "q": q,
        "n": n,
    }


def build_corpus(bits_min: int, bits_max: int) -> list[dict[str, int]]:
    max_factor_bits = max(2, bits_max)
    prime_cache = build_prime_cache(max_factor_bits)
    out: list[dict[str, int]] = []
    for b in range(bits_min, bits_max + 1):
        out.append(build_one(b, prime_cache))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Build semiprime corpus up to 64 bits")
    ap.add_argument("--bits-min", type=int, default=16, help="minimum target bit-length")
    ap.add_argument("--bits-max", type=int, default=64, help="maximum target bit-length")
    ap.add_argument(
        "--output-json",
        type=str,
        default="data/semiprimes_u64.json",
        help="output JSON path",
    )
    args = ap.parse_args()
    if args.bits_min < 4:
        raise SystemExit("--bits-min must be >= 4")
    if args.bits_max < args.bits_min:
        raise SystemExit("--bits-max must be >= --bits-min")

    rows = build_corpus(args.bits_min, args.bits_max)
    out = {
        "meta": {
            "bits_min": args.bits_min,
            "bits_max": args.bits_max,
            "count": len(rows),
            "note": "deterministic semiprime corpus for benchmark harness",
        },
        "rows": rows,
    }
    path = Path(args.output_json)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"wrote {path} rows={len(rows)}")


if __name__ == "__main__":
    main()

