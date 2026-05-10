# SATLIB large graph-colouring DIMACS instances

These are the **large SAT-encoded graph colouring** benchmarks from SATLIB
([description](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/GCP/descr.html)):
all listed instances are **satisfiable**.

| File        | Colours | Vars | Clauses |
| ----------- | ------- | ---- | ------- |
| g125.18.cnf | 18      | 2250 | 70163   |
| g125.17.cnf | 17      | 2125 | 66272   |
| g250.15.cnf | 15      | 3750 | 233965  |
| g250.29.cnf | 29      | 7250 | 454622  |

## Download

The UBC SATLIB tree no longer serves raw `.cnf` at the old paths (404). Use the
**DIMACS challenge archive** (compressed `.cnf.Z`):

- Index: <http://archive.dimacs.rutgers.edu/pub/challenge/sat/benchmarks/volume/Cnf/>

From the repo root:

```bash
scripts/benchmarks/satlib_gcp/fetch_satlib_gcp.sh
```

Or manually: fetch each `g*.cnf.Z`, then `uncompress` / `zcat` to `.cnf`.

## Run (HQIV rapidity-frontier solver)

```bash
python3 scripts/hqiv_rapidity_frontier_sat_solver.py \
  --cnf scripts/benchmarks/satlib_gcp/g125.18.cnf \
  --backend pysat --json
```

Use `--backend dpll` for instrumented search; large instances need **PySAT** (or long runs).

Large `.cnf` files are **not** committed by default (see root `.gitignore` under `scripts/`).
