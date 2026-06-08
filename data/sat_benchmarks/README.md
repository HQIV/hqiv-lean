# SAT-style DIMACS (3-CNF) for HQIV scripts

The geometric pipeline in `scripts/hqiv_geometric_3sat_demo.py` expects **3-CNF** (exactly three literals per clause). General SAT Competition CNFs are often mixed width — those are **skipped** by `hqiv_satcomp_benchmark.py` unless you convert to 3-CNF elsewhere.

## Shipped samples

See `samples/` — tiny instances you can regression-test without downloading anything.

## Larger / competition sets

1. **SAT Competition** — [2026 site](https://satcompetition.github.io/2026/), `benchmarks2026.csv`, compilation script (see news on that page).
2. **SATLIB / previous years** — e.g. [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html), UF/UF-S / similar; filter or convert to 3-CNF as needed.
3. Place `.cnf` files under this directory (any layout), then:

```bash
python3 scripts/hqiv_satcomp_benchmark.py --dir data/sat_benchmarks/my_downloads --glob '**/*.cnf' --recursive --skip-non-3cnf --json
```

Use `--max-files 50` while iterating. Brute-force SAT is only run for small `n_vars` (`--bruteforce-max-vars`, default 22).
