#!/usr/bin/env python3
"""
HQIV geometric pipeline vs **SAT Competition 2026** workflow (probe / harness — not a competing solver).

Official event: https://satcompetition.github.io/2026/

This script does **not** register a solver. It:

* loads **DIMACS CNF** instances restricted to **3-CNF** (exactly three literals per clause);
* runs the repo’s prime encoding + :func:`hqiv_geometric_3sat_demo.patch_search_score_driven` etc.;
* optionally runs **brute-force SAT** only when ``n_vars`` is small enough;
* prints **timings** (parse, encode, moiré patch, optional brute force).

Competition benchmarks are distributed via ``benchmarks2026.csv`` and the benchmark compilation script
(see the 2026 news page). Place downloaded ``.cnf`` files locally and pass ``--cnf`` or ``--dir``.

Example::

  python3 scripts/hqiv_satcomp_benchmark.py --cnf path/to/instance.cnf --bruteforce-max-vars 22
  python3 scripts/hqiv_satcomp_benchmark.py --dir ./cnf --glob '*.cnf' --json
  python3 scripts/hqiv_satcomp_benchmark.py --dir data/sat_benchmarks --glob '**/*.cnf' --recursive --skip-non-3cnf --max-files 100 --json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# Import demo from same directory
import importlib.util

_scripts = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("hqiv_geometric_3sat_demo", _scripts / "hqiv_geometric_3sat_demo.py")
_g3 = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
sys.modules["hqiv_geometric_3sat_demo"] = _g3
_spec.loader.exec_module(_g3)


def parse_dimacs_3cnf(path: Path) -> _g3.Formula3SAT:
    """Parse DIMACS CNF; every clause must have exactly three literals (3-CNF)."""

    nvars = 0
    clauses: list[tuple[_g3.Literal, _g3.Literal, _g3.Literal]] = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) < 4 or parts[1] != "cnf":
                raise ValueError(f"bad preamble: {line!r}")
            nvars = int(parts[2])
            continue
        nums = [int(x) for x in line.split()]
        if nums and nums[-1] == 0:
            nums = nums[:-1]
        if len(nums) != 3:
            raise ValueError(f"{path}: expected 3 literals per clause, got {len(nums)}: {line!r}")
        lit = []
        for x in nums:
            v = abs(x) - 1
            if v < 0 or v >= nvars:
                raise ValueError(f"literal {x} out of range for nvars={nvars}")
            lit.append(_g3.Literal(v, neg=(x < 0)))
        clauses.append((lit[0], lit[1], lit[2]))
    if nvars < 1:
        raise ValueError("no problem line or nvars < 1")
    return _g3.Formula3SAT(num_vars=nvars, clauses=tuple(clauses))


def _bench_one(path: Path, bruteforce_max_vars: int) -> dict[str, object]:
    t0 = time.perf_counter()
    fm = parse_dimacs_3cnf(path)
    t_parse = time.perf_counter() - t0

    t1 = time.perf_counter()
    M, _primes, _cprods = _g3.encode_formula_to_M(fm)
    k = _g3.omega_M_exact(fm)
    t_enc = time.perf_counter() - t1

    c = len(fm.clauses)
    n_patch = _g3.patch_window_length(c)
    t2 = time.perf_counter()
    ps = _g3.patch_search_score_driven(M, k, c, n_patch)
    t_patch = time.perf_counter() - t2

    t_bf = 0.0
    sat: bool | None = None
    witness: list[bool] | None = None
    if fm.num_vars <= bruteforce_max_vars:
        t3 = time.perf_counter()
        sat, w = _g3.is_satisfiable_bruteforce(fm)
        t_bf = time.perf_counter() - t3
        witness = list(w) if w is not None else None
    else:
        sat = None

    return {
        "path": str(path),
        "ok": True,
        "n_vars": fm.num_vars,
        "n_clauses": c,
        "M_bit_length": M.bit_length(),
        "seconds_parse": t_parse,
        "seconds_encode": t_enc,
        "seconds_patch_search": t_patch,
        "seconds_bruteforce": t_bf,
        "seconds_total": t_parse + t_enc + t_patch + t_bf,
        "sat_bruteforce": sat,
        "witness": witness,
        "patch_cum_total": ps.cum_total,
        "patch_j_first": ps.j_first_ge_threshold,
        "mp_dps_shell": _g3.mp_dps_for_shell_M(M),
    }


def _bench_one_safe(path: Path, bruteforce_max_vars: int) -> dict[str, object]:
    try:
        return _bench_one(path, bruteforce_max_vars)
    except (ValueError, OSError) as e:
        return {
            "path": str(path),
            "ok": False,
            "error": f"{type(e).__name__}: {e}",
        }


def _collect_paths(cnf: Path | None, directory: Path | None, glob_pat: str, recursive: bool) -> list[Path]:
    paths: list[Path] = []
    if cnf is not None:
        paths.append(cnf)
    if directory is not None:
        if recursive:
            paths.extend(sorted(directory.rglob(glob_pat)))
        else:
            paths.extend(sorted(directory.glob(glob_pat)))
    return paths


def main() -> None:
    p = argparse.ArgumentParser(description="Time HQIV 3-SAT geometry vs DIMACS 3-CNF (SAT Competition 2026 probe)")
    p.add_argument("--cnf", type=Path, help="single .cnf file")
    p.add_argument("--dir", type=Path, help="directory of .cnf files")
    p.add_argument("--glob", default="*.cnf", help="glob under --dir (default *.cnf)")
    p.add_argument(
        "--recursive",
        action="store_true",
        help="use rglob so --glob can match subdirs (e.g. **/*.cnf)",
    )
    p.add_argument(
        "--skip-non-3cnf",
        action="store_true",
        help="on parse failure, emit row with ok=false instead of aborting",
    )
    p.add_argument("--max-files", type=int, default=0, metavar="N", help="process at most N files after sorting (0 = no limit)")
    p.add_argument("--bruteforce-max-vars", type=int, default=22, metavar="N", help="run brute SAT if n_vars ≤ N (default 22)")
    p.add_argument("--json", action="store_true", help="JSON array to stdout")
    args = p.parse_args()

    paths = _collect_paths(args.cnf, args.dir, args.glob, args.recursive)
    if not paths:
        p.error("need --cnf and/or --dir")

    if args.max_files and args.max_files > 0:
        paths = paths[: args.max_files]

    bench = _bench_one_safe if args.skip_non_3cnf else _bench_one
    rows = [bench(path, args.bruteforce_max_vars) for path in paths]
    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        for r in rows:
            if not r.get("ok", True):
                print(f"{r['path']}: SKIP  {r.get('error', '')}")
                continue
            print(f"{r['path']}: total={r['seconds_total']*1000:.2f}ms  parse={r['seconds_parse']*1000:.2f}ms  "
                  f"encode={r['seconds_encode']*1000:.2f}ms  patch={r['seconds_patch_search']*1000:.2f}ms  "
                  f"bf={r['seconds_bruteforce']*1000:.2f}ms  sat={r['sat_bruteforce']}  "
                  f"M_bits={r['M_bit_length']}  mp_dps={r['mp_dps_shell']}")


if __name__ == "__main__":
    main()
