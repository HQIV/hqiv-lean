#!/usr/bin/env python3
"""Brute-force check for `r8(m)` (integer vectors in Z^8 with sum of squares = m).

Must match `Hqiv.Algebra.r8` / `latticeShell8Finset` for small m (see `r8_zero`, `r8_one` in Lean).
"""

from __future__ import annotations

import itertools
import math


def sum_sq_int8(z: tuple[int, ...]) -> int:
    return sum(x * x for x in z)


def r8_bruteforce(m: int) -> int:
    b = int(math.isqrt(m))
    rng = range(-b, b + 1)
    count = 0
    for z in itertools.product(rng, repeat=8):
        if sum_sq_int8(z) == m:
            count += 1
    return count


def main() -> None:
    for m in range(0, 6):
        c = r8_bruteforce(m)
        print(f"m={m}  r8={c}")
    assert r8_bruteforce(0) == 1
    assert r8_bruteforce(1) == 16


if __name__ == "__main__":
    main()
