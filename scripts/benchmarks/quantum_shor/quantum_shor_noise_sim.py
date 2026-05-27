#!/usr/bin/env python3
"""
Noisy Aer simulation for coarse sparse Shor circuits (representative 20- and 25-bit cases).

Compares textbook vs coarse sparse success proxy under depolarizing + readout noise.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from orthogonal_diagonal_qiskit_poc import (  # noqa: E402
    build_orthogonal_diagonal_circuit,
    build_textbook_shor_circuit,
    choose_coprime_base,
)

# Representative cases from reference benchmark grid
DEFAULT_CASES = {
    20: 1022117,
    25: 17958675,
}


def _noise_model(p_depol: float = 0.001, p_readout: float = 0.02):
    from qiskit_aer.noise import NoiseModel, ReadoutError, depolarizing_error

    nm = NoiseModel()
    er1 = depolarizing_error(p_depol, 1)
    er2 = depolarizing_error(p_depol, 2)
    nm.add_all_qubit_quantum_error(er1, ["u", "h", "p", "t", "tdg", "s", "sdg", "x", "y", "z", "rx", "ry", "rz"])
    nm.add_all_qubit_quantum_error(er2, ["cx", "cz", "cp", "rzz", "rxx", "swap"])
    ro = ReadoutError([[1 - p_readout, p_readout], [p_readout, 1 - p_readout]])
    nm.add_all_qubit_readout_error(ro)
    return nm


def _peak_probability(counts: dict[str, int], shots: int) -> float:
    if not counts:
        return 0.0
    return max(counts.values()) / shots


def simulate_one(
    n: int,
    *,
    layout: str,
    shots: int,
    decompose_reps: int,
    opt_level: int,
    p_depol: float,
    p_readout: float,
) -> dict[str, Any]:
    from qiskit import transpile
    from qiskit_aer import AerSimulator

    base = choose_coprime_base(n)
    if layout == "textbook":
        qc = build_textbook_shor_circuit(n, base, decompose_reps=decompose_reps)
    elif layout == "coarse":
        qc = build_orthogonal_diagonal_circuit(n, base, refined=False, decompose_reps=decompose_reps)
    else:
        raise ValueError(layout)

    # Aer requires ISA basis gates; expand boxed mod-exp if structural build used.
    basis = ["cx", "cz", "id", "rz", "sx", "x", "h", "swap", "cp"]
    prep = qc.decompose(reps=max(1, decompose_reps)) if decompose_reps == 0 else qc
    tqc = transpile(
        prep,
        optimization_level=opt_level,
        basis_gates=basis,
        seed_transpiler=0,
    )
    nm = _noise_model(p_depol, p_readout)
    # Statevector is infeasible beyond ~18 qubits after expansion; use MPS for large n.
    method = "matrix_product_state" if tqc.num_qubits > 18 else "automatic"
    sim = AerSimulator(noise_model=nm, method=method, max_memory_mb=32_000)
    job = sim.run(tqc, shots=shots)
    counts = job.result().get_counts()
    return {
        "n": n,
        "bits": n.bit_length(),
        "layout": layout,
        "base": base,
        "shots": shots,
        "depth": tqc.depth(),
        "qubits": tqc.num_qubits,
        "peak_probability": _peak_probability(counts, shots),
        "top_counts": dict(sorted(counts.items(), key=lambda kv: -kv[1])[:5]),
        "p_depol": p_depol,
        "p_readout": p_readout,
        "decompose_reps": decompose_reps,
        "opt_level": opt_level,
    }


def run_noise_suite(
    *,
    cases: dict[int, int],
    shots: int,
    decompose_reps: int,
    opt_level: int,
    p_depol: float,
    p_readout: float,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for bits, n in sorted(cases.items()):
        for layout in ("textbook", "coarse"):
            print(f"sim: n={n} ({bits}b) {layout} ...", flush=True)
            rows.append(
                simulate_one(
                    n,
                    layout=layout,
                    shots=shots,
                    decompose_reps=decompose_reps,
                    opt_level=opt_level,
                    p_depol=p_depol,
                    p_readout=p_readout,
                )
            )
    return {
        "protocol": "quantum_shor_noise_sim/v1",
        "cases": cases,
        "shots": shots,
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Noisy Aer Shor layout comparison")
    parser.add_argument("--shots", type=int, default=512)
    parser.add_argument("--decompose-reps", type=int, default=0, help="0=fast structural")
    parser.add_argument("--opt-level", type=int, default=1)
    parser.add_argument("--p-depol", type=float, default=0.001)
    parser.add_argument("--p-readout", type=float, default=0.02)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    result = run_noise_suite(
        cases=DEFAULT_CASES,
        shots=args.shots,
        decompose_reps=args.decompose_reps,
        opt_level=args.opt_level,
        p_depol=args.p_depol,
        p_readout=args.p_readout,
    )

    out_path = args.output or Path(__file__).resolve().parent / "shor_noise_sim.json"
    out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"wrote {out_path}")
        for row in result["rows"]:
            print(
                f"  {row['layout']:8} n={row['n']:>9} depth={row['depth']:>6} "
                f"peak_prob={row['peak_probability']:.3f}"
            )


if __name__ == "__main__":
    main()
