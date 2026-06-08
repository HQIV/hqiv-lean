#!/usr/bin/env python3
"""
Run euclidean_factor_peel on a semiprime corpus until first timeout.

Default behavior:
- read `data/semiprimes_u64.json`
- run each input with timeout=5s
- stop on first timeout
- print per-case timings and a concise summary
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path
from typing import Any

_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from euclidean_factor_peel import factor_peel_geometric


def _worker(n: int, kwargs: dict[str, Any], q: mp.Queue) -> None:
    t0 = time.perf_counter()
    try:
        factors, unresolved = factor_peel_geometric(n, **kwargs)
        dt = time.perf_counter() - t0
        q.put(
            {
                "ok": True,
                "elapsed_s": dt,
                "factor_count": len(factors),
                "unresolved_count": len(unresolved),
                "unresolved": unresolved[:5],
            }
        )
    except Exception as e:  # pragma: no cover
        q.put({"ok": False, "error": repr(e)})


def run_one_with_timeout(n: int, kwargs: dict[str, Any], timeout_s: float) -> dict[str, Any]:
    q: mp.Queue = mp.Queue()
    p = mp.Process(target=_worker, args=(n, kwargs, q))
    p.start()
    p.join(timeout_s)
    if p.is_alive():
        p.terminate()
        p.join()
        return {"timeout": True}
    if q.empty():
        return {"timeout": False, "ok": False, "error": "no_result"}
    return {"timeout": False, **q.get()}


def load_rows(path: Path) -> list[dict[str, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise SystemExit("invalid corpus: missing rows")
    out: list[dict[str, int]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        n = int(row.get("n", 0))
        bits = int(row.get("bits", n.bit_length()))
        out.append({"n": n, "bits": bits, "target_bits": int(row.get("target_bits", bits))})
    out.sort(key=lambda r: (r["bits"], r["n"]))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Benchmark euclidean factor peel on semiprimes until timeout")
    ap.add_argument(
        "--input-json",
        type=str,
        default="data/semiprimes_u64.json",
        help="semiprime corpus JSON path",
    )
    ap.add_argument("--timeout-s", type=float, default=5.0, help="per-input timeout seconds")
    ap.add_argument("--start-index", type=int, default=0, help="start row index in corpus")
    ap.add_argument("--max-cases", type=int, default=0, help="max cases to run (0 => no cap)")
    ap.add_argument("--sqrt-arity", type=float, default=2.0)
    ap.add_argument("--no-sqrt-arity-prune", action="store_true")
    ap.add_argument("--no-tensor-field", action="store_true")
    ap.add_argument("--tensor-chi-base", type=int, default=4)
    ap.add_argument("--tensor-chi-max", type=int, default=8)
    ap.add_argument("--tensor-residual-gate", type=float, default=0.25)
    ap.add_argument("--tensor-single-probe-margin", type=float, default=0.35)
    ap.add_argument("--no-tensor-gates", action="store_true")
    ap.add_argument("--tensor-gate-span", type=float, default=0.08)
    ap.add_argument("--tensor-gate-max-candidates", type=int, default=4)
    ap.add_argument("--khinchin-gate", action="store_true")
    ap.add_argument("--khinchin-terms", type=int, default=10)
    ap.add_argument("--khinchin-gate-span", type=float, default=0.06)
    ap.add_argument("--khinchin-single-probe-threshold", type=float, default=0.10)
    ap.add_argument("--no-small-prime-peel", action="store_true")
    ap.add_argument("--small-prime-limit", type=int, default=257)
    ap.add_argument("--no-fermat-lehman", action="store_true")
    ap.add_argument("--fermat-max-steps", type=int, default=0, help="0 => auto budget")
    ap.add_argument("--lehman-k-max", type=int, default=0, help="0 => auto budget")
    ap.add_argument("--no-residue-gate", action="store_true")
    ap.add_argument("--residue-gate-prime-limit", type=int, default=97)
    ap.add_argument("--max-probes-per-step", type=int, default=12)
    args = ap.parse_args()

    corpus_path = Path(args.input_json)
    if not corpus_path.exists():
        raise SystemExit(f"missing corpus file: {corpus_path}")
    if args.timeout_s <= 0:
        raise SystemExit("--timeout-s must be > 0")
    if args.start_index < 0:
        raise SystemExit("--start-index must be >= 0")
    if args.max_cases < 0:
        raise SystemExit("--max-cases must be >= 0")

    rows = load_rows(corpus_path)
    rows = rows[args.start_index :]
    if args.max_cases > 0:
        rows = rows[: args.max_cases]

    kwargs = {
        "fermat_lehman": not args.no_fermat_lehman,
        "fermat_max_steps": None if args.fermat_max_steps <= 0 else args.fermat_max_steps,
        "lehman_k_max": None if args.lehman_k_max <= 0 else args.lehman_k_max,
        "sqrt_arity_prune": not args.no_sqrt_arity_prune,
        "sqrt_arity": args.sqrt_arity,
        "tensor_field": not args.no_tensor_field,
        "tensor_chi_base": args.tensor_chi_base,
        "tensor_chi_max": args.tensor_chi_max,
        "tensor_residual_gate": args.tensor_residual_gate,
        "tensor_single_probe_margin": args.tensor_single_probe_margin,
        "tensor_gate_driven": not args.no_tensor_gates,
        "tensor_gate_span": args.tensor_gate_span,
        "tensor_gate_max_candidates": args.tensor_gate_max_candidates,
        "khinchin_gate": args.khinchin_gate,
        "khinchin_terms": args.khinchin_terms,
        "khinchin_gate_span": args.khinchin_gate_span,
        "khinchin_single_probe_threshold": args.khinchin_single_probe_threshold,
        "residue_gate": not args.no_residue_gate,
        "residue_gate_prime_limit": args.residue_gate_prime_limit,
        "max_probes_per_step": args.max_probes_per_step,
        "small_prime_peel": not args.no_small_prime_peel,
        "small_prime_limit": args.small_prime_limit,
    }

    print(
        "mode:"
        f" fermat_lehman={kwargs['fermat_lehman']} residue_gate={kwargs['residue_gate']}"
        f" sqrt_prune={kwargs['sqrt_arity_prune']} sqrt_arity={kwargs['sqrt_arity']}"
        f" tensor={kwargs['tensor_field']} tensor_gates={kwargs['tensor_gate_driven']}"
        f" small_prime_peel={kwargs['small_prime_peel']} timeout_s={args.timeout_s}"
    )
    print("idx,bits,elapsed_s,status,unresolved_count")

    elapsed_total = 0.0
    completed = 0
    timeout_row: dict[str, int] | None = None
    for i, row in enumerate(rows):
        n = row["n"]
        bits = row["bits"]
        r = run_one_with_timeout(n, kwargs, args.timeout_s)
        if r.get("timeout"):
            print(f"{i},{bits},,TIMEOUT,")
            timeout_row = row
            break
        if not r.get("ok", False):
            print(f"{i},{bits},,ERROR,")
            print(f"error={r.get('error')}")
            break
        elapsed = float(r["elapsed_s"])
        elapsed_total += elapsed
        completed += 1
        status = "OK" if int(r.get("unresolved_count", 0)) == 0 else "PARTIAL"
        print(f"{i},{bits},{elapsed:.6f},{status},{int(r.get('unresolved_count', 0))}")

    print()
    print(f"completed={completed}")
    print(f"elapsed_total_s={elapsed_total:.6f}")
    if completed > 0:
        print(f"elapsed_mean_s={elapsed_total / completed:.6f}")
    if timeout_row is not None:
        print(f"first_timeout_bits={timeout_row['bits']}")
        print(f"first_timeout_n={timeout_row['n']}")
    else:
        print("first_timeout_bits=none")


if __name__ == "__main__":
    main()

