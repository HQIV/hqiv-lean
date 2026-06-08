#!/usr/bin/env python3
"""
Exercise monolithic_geometric_factorizer4.factor() on random balanced semiprimes
whose product has bit length in [110, 120].

Uses sympy for prime generation. No shell timeout — optional ``--max-steps`` caps
the main search loop so each case always terminates (default: 8_000_000).
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
import time
from pathlib import Path

from sympy import randprime


def load_factorizer():
    path = Path(__file__).resolve().parent / "monolithic_geometric_factorizer4.py"
    spec = importlib.util.spec_from_file_location("mgf4", path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["mgf4"] = mod
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def make_balanced_semiprime(total_bits: int) -> tuple[int, int, int]:
    """Return (N, p, q) with p, q prime and N = p * q having ``total_bits`` bits."""
    if total_bits < 4:
        raise ValueError("total_bits too small")
    # Balanced RSA-style: factor bit sizes ⌈b/2⌉ and ⌊b/2⌋; retry until product has exact width
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
    parser = argparse.ArgumentParser(description="Test mgf4 on 110–120 bit semiprimes")
    parser.add_argument(
        "--bits-min",
        type=int,
        default=110,
        help="Minimum product bit length (default 110)",
    )
    parser.add_argument(
        "--bits-max",
        type=int,
        default=120,
        help="Maximum product bit length inclusive (default 120)",
    )
    parser.add_argument(
        "--samples-per-width",
        type=int,
        default=1,
        help="How many random semiprimes per bit width (default 1)",
    )
    parser.add_argument(
        "--max-steps",
        type=int,
        default=8_000_000,
        metavar="N",
        help="Main-loop step cap per factor() call (default 8e6; 0 = unlimited)",
    )
    args = parser.parse_args()
    mgf4 = load_factorizer()

    max_steps = None if args.max_steps == 0 else args.max_steps

    print(
        f"Testing monolithic_geometric_factorizer4: "
        f"bits [{args.bits_min}, {args.bits_max}], "
        f"{args.samples_per_width} sample(s)/width, "
        f"max_steps={max_steps}\n",
        flush=True,
    )

    for bits in range(args.bits_min, args.bits_max + 1):
        for s in range(args.samples_per_width):
            n, p_true, q_true = make_balanced_semiprime(bits)
            bl = n.bit_length()
            t0 = time.perf_counter()
            result = mgf4.factor(n, max_steps=max_steps)
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
