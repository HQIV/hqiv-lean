#!/usr/bin/env python3
"""
Exercise monolithic_geometric_factorizer3.factor() on random balanced semiprimes.

Uses sympy for prime generation. Optional ``--max-steps`` caps the main loop
(``0`` = unlimited).
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

from sympy import randprime


def load_factorizer():
    path = Path(__file__).resolve().parent / "monolithic_geometric_factorizer3.py"
    spec = importlib.util.spec_from_file_location("mgf3", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["mgf3"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def make_balanced_semiprime(total_bits: int) -> tuple[int, int, int]:
    """Return (N, p, q) with p, q prime and N = p * q having ``total_bits`` bits."""
    if total_bits < 4:
        raise ValueError("total_bits too small")
    hi_sz = (total_bits + 1) // 2
    lo_sz = total_bits // 2
    lo_big, hi_big = 2 ** (hi_sz - 1), 2**hi_sz
    lo_small, hi_small = 2 ** (lo_sz - 1), 2**lo_sz
    for _ in range(50_000):
        p = randprime(lo_big, hi_big)
        q = randprime(lo_small, hi_small)
        n = p * q
        if n.bit_length() == total_bits:
            return n, p, q
    raise RuntimeError(f"could not build a {total_bits}-bit semiprime after many tries")


def main() -> None:
    parser = argparse.ArgumentParser(description="Test mgf3 on semiprimes (e.g. 80–100 bits)")
    parser.add_argument("--bits-min", type=int, default=80)
    parser.add_argument("--bits-max", type=int, default=100)
    parser.add_argument(
        "--bits-step",
        type=int,
        default=1,
        help="Stride across bit widths (default 1 = every width)",
    )
    parser.add_argument("--samples-per-width", type=int, default=1)
    parser.add_argument(
        "--max-steps",
        type=int,
        default=500_000,
        metavar="N",
        help="Main-loop step cap per factor() (default 500k; 0 = unlimited)",
    )
    args = parser.parse_args()
    mgf3 = load_factorizer()

    max_steps = None if args.max_steps == 0 else args.max_steps

    print(
        f"Testing monolithic_geometric_factorizer3: "
        f"bits {args.bits_min}..{args.bits_max} step {args.bits_step}, "
        f"{args.samples_per_width} sample(s)/width, max_steps={max_steps}\n",
        flush=True,
    )

    for bits in range(args.bits_min, args.bits_max + 1, args.bits_step):
        for _ in range(args.samples_per_width):
            n, p_true, q_true = make_balanced_semiprime(bits)
            bl = n.bit_length()
            t0 = time.perf_counter()
            result = mgf3.factor(n, max_steps=max_steps)
            elapsed = time.perf_counter() - t0
            ok = result["success"] and sorted(result["prime_factors"]) == sorted(
                [p_true, q_true]
            )
            status = "OK" if ok else "FAIL"
            print(
                f"  bits_request={bits}  N_bits={bl}  status={status}  "
                f"success={result['success']}  steps={result['steps']}  "
                f"time_s={elapsed:.3f}",
                flush=True,
            )
            if not ok:
                print(f"    N={n}", flush=True)
                print(f"    expect factors {p_true}, {q_true}", flush=True)
                print(f"    got {result.get('prime_factors')}", flush=True)


if __name__ == "__main__":
    main()
