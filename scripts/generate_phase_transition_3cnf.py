#!/usr/bin/env python3
"""
Generate random 3-CNF instances near the satisfiability phase transition (α ≈ 4.26).

Seeds are derived from odd primes (HQIV / moiré encoding style) so runs are reproducible
and distinct per instance id. Not a SAT solver — instance construction only.

Typical use:
  python3 scripts/generate_phase_transition_3cnf.py --out-dir data/sat_benchmarks/phase_transition --count 20
"""

from __future__ import annotations

import argparse
import math
import random
from pathlib import Path

# Odd primes from 3 upward (same spirit as hqiv_geometric_3sat_demo: no factor 2).
_ODD_PRIMES: tuple[int, ...] = (
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
)


def _prime_mix_seed(instance_id: int, n: int, m: int) -> int:
    """Deterministic 32-bit-ish seed from primes and shape parameters."""
    p = _ODD_PRIMES[instance_id % len(_ODD_PRIMES)]
    q = _ODD_PRIMES[(n + instance_id) % len(_ODD_PRIMES)]
    r = _ODD_PRIMES[(m + 2 * instance_id) % len(_ODD_PRIMES)]
    x = (instance_id + 1) * p * q * r + n * 17 + m * 31 + (n ^ m) * 7
    return (x % (2**31 - 1)) + 1


def _alpha_for_instance(instance_id: int) -> float:
    """
    Clause-to-variable ratio in the empirical hard band (~4.2–4.35 for large random 3-SAT).
    Slight deterministic wobble from primes so instances are not identical densities.
    """
    base = 4.26  # near phase transition
    p = _ODD_PRIMES[instance_id % len(_ODD_PRIMES)]
    q = _ODD_PRIMES[(instance_id // 3) % len(_ODD_PRIMES)]
    wobble = ((p * q) % 200) / 2000.0  # ~0 to 0.1
    return base - 0.05 + wobble  # roughly [4.21, 4.31]


def _n_vars_for_instance(instance_id: int) -> int:
    """Diverse but modest n (hard enough, still brute-checkable for small-solver regression)."""
    # Spread 14..48 with prime residue so we don't get only multiples of 5.
    base = 14 + (instance_id * 37) % 35
    bump = _ODD_PRIMES[instance_id % len(_ODD_PRIMES)] % 7
    return max(12, min(55, base + bump))


def generate_3cnf(
    n: int,
    m: int,
    rng: random.Random,
    *,
    max_attempts: int = 200_000,
) -> list[list[int]]:
    """Uniform random 3-CNF: three distinct variables per clause; no duplicate signed clauses."""
    clauses: list[list[int]] = []
    seen: set[frozenset[int]] = set()
    attempts = 0
    while len(clauses) < m and attempts < max_attempts:
        attempts += 1
        vs = rng.sample(range(1, n + 1), 3)
        lits = [v if rng.random() < 0.5 else -v for v in vs]
        key = frozenset(lits)
        if key in seen:
            continue
        seen.add(key)
        clauses.append(lits)
    if len(clauses) < m:
        raise RuntimeError(
            f"could only sample {len(clauses)}/{m} distinct clauses (n={n}); try larger n or smaller alpha"
        )
    return clauses


def write_dimacs(path: Path, n: int, clauses: list[list[int]], comments: list[str]) -> None:
    lines = [f"c {line}" for line in comments]
    lines.append(f"p cnf {n} {len(clauses)}")
    for cl in clauses:
        lines.append(" ".join(str(x) for x in cl) + " 0")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    p = argparse.ArgumentParser(description="Generate prime-seeded phase-transition 3-CNF instances")
    p.add_argument("--out-dir", type=Path, required=True, help="output directory for .cnf files")
    p.add_argument("--count", type=int, default=20, help="number of instances")
    p.add_argument("--start-id", type=int, default=0, help="first instance id (for filenames/seeds)")
    args = p.parse_args()
    if args.count < 1:
        raise SystemExit("--count must be >= 1")
    args.out_dir.mkdir(parents=True, exist_ok=True)

    for k in range(args.count):
        i = args.start_id + k
        n = _n_vars_for_instance(i)
        alpha = _alpha_for_instance(i)
        m = max(1, int(round(alpha * n)))
        seed = _prime_mix_seed(i, n, m)
        rng = random.Random(seed)
        clauses = generate_3cnf(n, m, rng)
        name = f"hqiv_pt3_id{i:02d}_n{n}_m{m}_a{alpha:.3f}_s{seed}.cnf"
        path = args.out_dir / name
        comments = [
            f"HQIV phase-transition random 3-CNF instance {k + 1}/{args.count}",
            f"vars={n} clauses={m} alpha={alpha:.4f} (target band ~4.2-4.3)",
            f"prime-mix seed={seed} (reproducible)",
        ]
        write_dimacs(path, n, clauses, comments)
        print(f"wrote {path}  (n={n} m={m} alpha≈{alpha:.3f})")


if __name__ == "__main__":
    main()
