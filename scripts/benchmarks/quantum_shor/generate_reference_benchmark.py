#!/usr/bin/env python3
"""
Generate reference Shor layout benchmark (15–32 bit semiprimes).

Writes unified reference artifacts with **structural** and **gate-expanded** depths:
  - shor_layout_benchmark.csv
  - shor_layout_benchmark.md
  - shor_layout_benchmark.json

Structural: ``decompose_reps=0``, ``opt_level=1`` (fast, high-level ops).
Gate-expanded: ``decompose_reps=1``, ``opt_level=3`` (tb_gate_depth / co_gate_depth).

Mod-exp blocks are disk-cached under ``HQIV_LEAN/scripts/.cache/modexp/``.

```bash
python3 benchmarks/quantum_shor/generate_reference_benchmark.py \\
  --min-bits 15 --max-bits 25

# Gate pass only (merge into existing JSON):
python3 benchmarks/quantum_shor/generate_reference_benchmark.py \\
  --gate-only --max-bits 25
```
"""

from __future__ import annotations

import argparse
import csv
import json
import random
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from orthogonal_diagonal_qiskit_poc import compare_one  # noqa: E402

OUT_DIR = Path(__file__).resolve().parent

SMALL_DEMO_SEMIPRIMES = [15, 143, 899, 10403]
LARGE_ANCHOR_SEMIPRIMES = [1022117]

STRUCTURAL_DECOMPOSE = 0
STRUCTURAL_OPT = 1
GATE_DECOMPOSE = 1
GATE_OPT = 3


def semiprime_for_bit_length(bits: int, *, seed: int) -> int:
    if bits < 4:
        raise ValueError("bits must be ≥ 4")
    rng = random.Random(seed + bits * 10007)
    half = bits // 2
    other = bits - half
    for _ in range(5000):
        p = rng.getrandbits(half) | (1 << (half - 1)) | 1
        q = rng.getrandbits(other) | (1 << (other - 1)) | 1
        if p < 2 or q < 2:
            continue
        n = p * q
        if n.bit_length() == bits:
            return n
    raise RuntimeError(f"could not sample semiprime for {bits} bits")


def benchmark_case_list(
    *,
    min_bits: int,
    max_bits: int,
    include_small_demos: bool = True,
) -> list[int]:
    cases: set[int] = set()
    if include_small_demos:
        cases.update(SMALL_DEMO_SEMIPRIMES)
    for n in LARGE_ANCHOR_SEMIPRIMES:
        if min_bits <= n.bit_length() <= max_bits:
            cases.add(n)
    for bits in range(min_bits, max_bits + 1):
        cases.add(semiprime_for_bit_length(bits, seed=42))
    return sorted(cases)


CSV_FIELDS = [
    "n",
    "bits",
    "L",
    "B",
    "base",
    "textbook_physical_qubits",
    "coarse_physical_qubits",
    "refined_physical_qubits",
    "textbook_depth",
    "coarse_depth",
    "refined_depth",
    "coarse_depth_ratio",
    "refined_depth_ratio",
    "coarse_qubit_delta",
    "refined_qubit_delta",
    "tb_gate_depth",
    "co_gate_depth",
    "gate_depth_ratio",
    "build_seconds",
]


def _row_from_compare(n: int, row: Any, *, elapsed: float, gate_only: bool) -> dict[str, Any]:
    d = row.__dict__.copy()
    d["build_seconds"] = round(elapsed, 2)
    if gate_only:
        for k in (
            "textbook_depth",
            "coarse_depth",
            "refined_depth",
            "coarse_depth_ratio",
            "refined_depth_ratio",
        ):
            d.pop(k, None)
    return d


def run_benchmark(
    *,
    min_bits: int,
    max_bits: int,
    include_small_demos: bool,
    run_structural: bool,
    run_gate: bool,
    existing_rows: dict[int, dict[str, Any]] | None = None,
) -> dict[str, Any]:
    cases = benchmark_case_list(
        min_bits=min_bits, max_bits=max_bits, include_small_demos=include_small_demos
    )
    by_n: dict[int, dict[str, Any]] = dict(existing_rows or {})
    failures: list[dict[str, Any]] = []

    for n in cases:
        t0 = time.perf_counter()
        try:
            prev = by_n.get(n, {})
            if run_structural and run_gate:
                row = compare_one(
                    n,
                    decompose_reps=STRUCTURAL_DECOMPOSE,
                    opt_level=STRUCTURAL_OPT,
                    compare_layouts=True,
                    gate_decompose_reps=GATE_DECOMPOSE,
                    gate_opt_level=GATE_OPT,
                )
                merged = {**prev, **_row_from_compare(n, row, elapsed=time.perf_counter() - t0, gate_only=False)}
            elif run_structural:
                row = compare_one(
                    n,
                    decompose_reps=STRUCTURAL_DECOMPOSE,
                    opt_level=STRUCTURAL_OPT,
                    compare_layouts=True,
                )
                merged = {**prev, **_row_from_compare(n, row, elapsed=time.perf_counter() - t0, gate_only=False)}
            elif run_gate:
                row = compare_one(
                    n,
                    decompose_reps=STRUCTURAL_DECOMPOSE,
                    opt_level=STRUCTURAL_OPT,
                    compare_layouts=True,
                    gate_decompose_reps=GATE_DECOMPOSE,
                    gate_opt_level=GATE_OPT,
                )
                merged = {
                    **prev,
                    "n": n,
                    "bits": row.bits,
                    "L": row.L,
                    "B": row.B,
                    "base": row.base,
                    "tb_gate_depth": row.tb_gate_depth,
                    "co_gate_depth": row.co_gate_depth,
                    "gate_depth_ratio": row.gate_depth_ratio,
                    "build_seconds": round(time.perf_counter() - t0, 2),
                }
            else:
                continue
            by_n[n] = merged
            elapsed = time.perf_counter() - t0
            if elapsed > 15:
                print(f"info: n={n} ({n.bit_length()} bits) in {elapsed:.1f}s", flush=True)
        except Exception as exc:  # noqa: BLE001
            failures.append({"n": n, "bits": n.bit_length(), "error": str(exc)})
            print(f"warn: n={n} failed: {exc}", flush=True)

    rows = [by_n[k] for k in sorted(by_n)]
    return {
        "protocol": "orthogonal_diagonal_qiskit_poc/v3_unified",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "min_bits": min_bits,
        "max_bits": max_bits,
        "structural": {"decompose_reps": STRUCTURAL_DECOMPOSE, "opt_level": STRUCTURAL_OPT},
        "gate_expanded": {"decompose_reps": GATE_DECOMPOSE, "opt_level": GATE_OPT},
        "compare_layouts": True,
        "note": (
            "Real Fourier mod-exp with disk cache. "
            "textbook_depth/coarse_depth: structural (decompose_reps=0). "
            "tb_gate_depth/co_gate_depth: gate-expanded (decompose_reps=1, opt_level=3)."
        ),
        "rows": rows,
        "failures": failures,
    }


def write_csv(result: dict[str, Any], path: Path) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDS, extrasaction="ignore")
        w.writeheader()
        for row in result["rows"]:
            w.writerow(row)


def write_markdown(result: dict[str, Any], path: Path) -> None:
    meta = result
    s = meta["structural"]
    g = meta["gate_expanded"]
    lines = [
        "# Shor layout benchmark (reference data)",
        "",
        f"Generated: `{meta['generated_at']}` (UTC)",
        "",
        "| Parameter | Value |",
        "|-----------|-------|",
        f"| Bit range | {meta['min_bits']}–{meta['max_bits']} |",
        f"| Structural | `decompose_reps={s['decompose_reps']}`, `opt_level={s['opt_level']}` |",
        f"| Gate-expanded | `decompose_reps={g['decompose_reps']}`, `opt_level={g['opt_level']}` |",
        "",
        meta["note"],
        "",
        "## Results",
        "",
        "| n | bits | tb_q | co_q | rf_q | struct tb/co | gate tb/co | gate× | co Δq | rf Δq |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for r in meta["rows"]:
        struct_ratio = r.get("coarse_depth_ratio", 0)
        gate_tb = r.get("tb_gate_depth", -1)
        gate_co = r.get("co_gate_depth", -1)
        gate_ratio = r.get("gate_depth_ratio", 0)
        lines.append(
            f"| {r['n']} | {r['bits']} | {r['textbook_physical_qubits']} | "
            f"{r['coarse_physical_qubits']} | {r.get('refined_physical_qubits', -1)} | "
            f"{r.get('textbook_depth', '-')} / {r.get('coarse_depth', '-')} ({struct_ratio:.2f}×) | "
            f"{gate_tb} / {gate_co} | {gate_ratio:.3f}× | "
            f"{r.get('coarse_qubit_delta', '')} | {r.get('refined_qubit_delta', '')} |"
        )

    grid = [r for r in meta["rows"] if r["bits"] >= meta["min_bits"]]
    if grid and all(r.get("gate_depth_ratio", 0) > 0 for r in grid):
        avg_struct = sum(r["coarse_depth_ratio"] for r in grid) / len(grid)
        avg_gate = sum(r["gate_depth_ratio"] for r in grid) / len(grid)
        lines.extend(
            [
                "",
                "## Summary",
                "",
                f"- Grid cases: **{len(grid)}** ({meta['min_bits']}–{meta['max_bits']} bits)",
                f"- Mean structural depth ratio: **{avg_struct:.3f}×**",
                f"- Mean gate-expanded depth ratio: **{avg_gate:.3f}×**",
                "",
            ]
        )

    demos = [r for r in meta["rows"] if r["bits"] < meta["min_bits"]]
    if demos:
        lines.extend(["## Small demos", "", "| n | bits | struct× | gate× |", "|---:|---:|---:|---:|"])
        for r in demos:
            lines.append(
                f"| {r['n']} | {r['bits']} | {r.get('coarse_depth_ratio', 0):.3f} | "
                f"{r.get('gate_depth_ratio', 0):.3f} |"
            )
        lines.append("")

    if meta.get("failures"):
        lines.extend(["## Failures", ""])
        for f in meta["failures"]:
            lines.append(f"- n={f['n']}: {f['error']}")

    lines.extend(
        [
            "## Legend",
            "",
            "- **struct tb/co**: transpiled depth at `decompose_reps=0`.",
            "- **gate tb/co**: transpiled depth at `decompose_reps=1`, `opt_level=3`.",
            "- **gate×**: `tb_gate_depth / co_gate_depth`.",
            "",
            "```bash",
            "python3 HQIV_LEAN/scripts/benchmarks/quantum_shor/generate_reference_benchmark.py \\",
            f"  --min-bits {meta['min_bits']} --max-bits {meta['max_bits']}",
            "```",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate unified Shor layout benchmark")
    parser.add_argument("--min-bits", type=int, default=15)
    parser.add_argument("--max-bits", type=int, default=25)
    parser.add_argument("--output-dir", type=Path, default=OUT_DIR)
    parser.add_argument("--no-small-demos", action="store_true")
    parser.add_argument(
        "--gate-only",
        action="store_true",
        help="only run gate-expanded pass (merge into existing JSON if present)",
    )
    parser.add_argument(
        "--structural-only",
        action="store_true",
        help="only run structural pass",
    )
    args = parser.parse_args()

    try:
        import qiskit  # noqa: F401
    except ImportError as exc:
        raise SystemExit("Install qiskit: pip install qiskit") from exc

    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    json_path = out / "shor_layout_benchmark.json"

    existing: dict[int, dict[str, Any]] | None = None
    if args.gate_only and json_path.is_file():
        data = json.loads(json_path.read_text(encoding="utf-8"))
        existing = {r["n"]: r for r in data.get("rows", [])}

    run_structural = not args.gate_only
    run_gate = not args.structural_only
    if args.structural_only:
        run_gate = False

    print(
        f"benchmark: bits {args.min_bits}-{args.max_bits} "
        f"structural={run_structural} gate={run_gate}",
        flush=True,
    )
    t0 = time.perf_counter()
    result = run_benchmark(
        min_bits=args.min_bits,
        max_bits=args.max_bits,
        include_small_demos=not args.no_small_demos,
        run_structural=run_structural,
        run_gate=run_gate,
        existing_rows=existing,
    )
    result["total_seconds"] = round(time.perf_counter() - t0, 1)

    write_csv(result, out / "shor_layout_benchmark.csv")
    write_markdown(result, out / "shor_layout_benchmark.md")
    json_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"wrote {len(result['rows'])} rows to {out} in {result['total_seconds']}s", flush=True)


if __name__ == "__main__":
    main()
