#!/usr/bin/env python3
"""
Qiskit proof-of-concept: textbook Shor vs orthogonal-diagonal sparse schedule.

Uses **real** Fourier-space modular exponentiation (``shor_modexp.py``) for both
schedules so depth and width reflect arithmetic cost, not placeholders.

Run:
  python3 orthogonal_diagonal_qiskit_poc.py --max-bits 20
  python3 orthogonal_diagonal_qiskit_poc.py --refined --max-bits 20
  python3 orthogonal_diagonal_qiskit_poc.py --compare-layouts --max-bits 18
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from shor_modexp import build_modular_exponentiation, choose_coprime_base, num_bits_for_modulus

# Lean: shorBitLength
def shor_bit_length(n: int) -> int:
    return max(1, (max(2, n) - 1).bit_length() or 1)


def diagonal_ancilla_budget(L: int) -> int:
    return 3 * max(1, (max(2, L) - 1).bit_length()) + 10


def textbook_qubit_budget(n: int) -> int:
    """Lean coarse analytic budget (no aux slack)."""
    return 3 * shor_bit_length(n)


def coarse_orthogonal_qubit_budget(n: int) -> int:
    return 3 * shor_bit_length(n)


def refined_orthogonal_qubit_budget(n: int) -> int:
    L = shor_bit_length(n)
    return 2 * L + diagonal_ancilla_budget(L)


def _apply_h(qc, qubits: list[int]) -> None:
    for q in qubits:
        qc.h(q)


def _inverse_qft(qc, qubits: list[int]) -> None:
    from qiskit.synthesis import synth_qft_full

    n = len(qubits)
    if n == 0:
        return
    iqft = synth_qft_full(n, do_swaps=False).inverse()
    qc.compose(iqft, qubits=qubits, inplace=True)


def _diagonal_reflection_carrier(qc, phase_regs: list[int], ancilla: list[int], period_r: int = 4) -> None:
    from qiskit.circuit.library import PhaseGate

    for k, q in enumerate(phase_regs):
        theta = 2 * math.pi * k / max(period_r, 1)
        w_a = math.cos(theta) ** 2
        if w_a > 1e-12:
            qc.append(PhaseGate(math.pi * w_a), [q])
        if len(ancilla) > 1 and k < len(ancilla) - 1:
            qc.cx(q, ancilla[1])


def _init_work_register_one(qc, work_regs: list[int]) -> None:
    if work_regs:
        qc.x(work_regs[0])


def build_textbook_shor_circuit(
    n: int,
    a: int | None = None,
    *,
    decompose_reps: int = 2,
) -> Any:
    """
    Textbook layout: ``2·B`` counting + ``B`` work + ``B+2`` aux (Beauregard-style core).
    """
    from qiskit import QuantumCircuit

    base = a if a is not None else choose_coprime_base(n)
    n_bits = num_bits_for_modulus(n)
    count = 2 * n_bits

    modexp = build_modular_exponentiation(
        n, base, num_counting_qubits=count, decompose_reps=decompose_reps, use_cache=True
    )
    # modexp qubits: count | work | aux
    n_qubits = modexp.num_qubits
    measure_bits = min(shor_bit_length(n), count)
    qc = QuantumCircuit(n_qubits, measure_bits)

    count_regs = list(range(count))
    work_regs = list(range(count, count + n_bits))
    aux_regs = list(range(count + n_bits, n_qubits))

    _apply_h(qc, count_regs)
    _init_work_register_one(qc, work_regs)
    qc.compose(modexp, list(range(n_qubits)), inplace=True)
    _inverse_qft(qc, count_regs)
    qc.measure(count_regs[:measure_bits], list(range(measure_bits)))
    qc.name = f"textbook_shor_n{n}"
    return qc


def build_orthogonal_diagonal_circuit(
    n: int,
    a: int | None = None,
    *,
    refined: bool = False,
    period_r: int = 4,
    decompose_reps: int = 2,
) -> Any:
    """
    Orthogonal-diagonal layout: ``L`` counting + ``B`` work + ``B+2`` aux [+ diagonal ancilla].

    ``refined=False``: coarse 3-register schedule (L counting; mirror register omitted).
    ``refined=True``: adds explicit diagonal-reflection ancilla budget from Lean.
    """
    from qiskit import QuantumCircuit

    base = a if a is not None else choose_coprime_base(n)
    L = shor_bit_length(n)
    n_bits = num_bits_for_modulus(n)
    count = L

    modexp = build_modular_exponentiation(
        n, base, num_counting_qubits=count, decompose_reps=decompose_reps, use_cache=True
    )
    arith_qubits = modexp.num_qubits
    di_anc = diagonal_ancilla_budget(L) if refined else 0
    n_qubits = arith_qubits + di_anc

    measure_bits = min(L, count)
    qc = QuantumCircuit(n_qubits, measure_bits)

    count_regs = list(range(count))
    work_regs = list(range(count, count + n_bits))
    aux_regs = list(range(count + n_bits, arith_qubits))
    di_regs = list(range(arith_qubits, n_qubits))

    _apply_h(qc, count_regs)
    _init_work_register_one(qc, work_regs)
    qc.compose(modexp, list(range(arith_qubits)), inplace=True)
    _diagonal_reflection_carrier(qc, count_regs, di_regs, period_r=period_r)
    qc.measure(count_regs[:measure_bits], list(range(measure_bits)))
    qc.name = f"sparse_shor_n{n}_refined={refined}"
    return qc


@dataclass
class CircuitComparisonRow:
    n: int
    bits: int
    L: int
    B: int
    base: int
    textbook_analytic_qubits: int
    coarse_analytic_qubits: int
    refined_analytic_qubits: int
    textbook_physical_qubits: int
    coarse_physical_qubits: int
    refined_physical_qubits: int
    textbook_depth: int
    coarse_depth: int
    refined_depth: int
    coarse_depth_ratio: float
    refined_depth_ratio: float
    coarse_qubit_delta: int
    refined_qubit_delta: int
    tb_gate_depth: int = -1
    co_gate_depth: int = -1
    gate_depth_ratio: float = 0.0


def _transpile_depth(qc: Any, *, opt_level: int) -> tuple[int, int]:
    from qiskit import transpile

    t = transpile(qc, optimization_level=opt_level, seed_transpiler=0)
    return t.num_qubits, t.depth()


def compare_one(
    n: int,
    *,
    opt_level: int = 1,
    decompose_reps: int = 0,
    compare_layouts: bool = False,
    sparse_refined: bool = False,
    gate_decompose_reps: int | None = None,
    gate_opt_level: int | None = None,
) -> CircuitComparisonRow:
    base = choose_coprime_base(n)
    L = shor_bit_length(n)
    B = num_bits_for_modulus(n)

    tb = build_textbook_shor_circuit(n, base, decompose_reps=decompose_reps)
    tb_q, tb_d = _transpile_depth(tb, opt_level=opt_level)

    use_refined_sparse = sparse_refined and not compare_layouts
    sp_primary = build_orthogonal_diagonal_circuit(
        n, base, refined=use_refined_sparse, decompose_reps=decompose_reps
    )
    pr_q, pr_d = _transpile_depth(sp_primary, opt_level=opt_level)

    co_q, co_d = pr_q, pr_d
    rf_q, rf_d = -1, -1
    if compare_layouts:
        sp_coarse = build_orthogonal_diagonal_circuit(
            n, base, refined=False, decompose_reps=decompose_reps
        )
        co_q, co_d = _transpile_depth(sp_coarse, opt_level=opt_level)
        sp_refined = build_orthogonal_diagonal_circuit(
            n, base, refined=True, decompose_reps=decompose_reps
        )
        rf_q, rf_d = _transpile_depth(sp_refined, opt_level=opt_level)

    tb_gate_d = -1
    co_gate_d = -1
    if gate_decompose_reps is not None:
        g_opt = gate_opt_level if gate_opt_level is not None else 3
        g_dec = gate_decompose_reps
        tb_g = build_textbook_shor_circuit(n, base, decompose_reps=g_dec)
        _, tb_gate_d = _transpile_depth(tb_g, opt_level=g_opt)
        sp_g = build_orthogonal_diagonal_circuit(n, base, refined=False, decompose_reps=g_dec)
        _, co_gate_d = _transpile_depth(sp_g, opt_level=g_opt)

    tb_an = textbook_qubit_budget(n)
    co_an = coarse_orthogonal_qubit_budget(n)
    rf_an = refined_orthogonal_qubit_budget(n)

    return CircuitComparisonRow(
        n=n,
        bits=n.bit_length(),
        L=L,
        B=B,
        base=base,
        textbook_analytic_qubits=tb_an,
        coarse_analytic_qubits=co_an,
        refined_analytic_qubits=rf_an,
        textbook_physical_qubits=tb_q,
        coarse_physical_qubits=co_q,
        refined_physical_qubits=rf_q,
        textbook_depth=tb_d,
        coarse_depth=co_d,
        refined_depth=rf_d,
        coarse_depth_ratio=tb_d / max(1, co_d),
        refined_depth_ratio=(
            tb_d / max(1, rf_d) if rf_d > 0 else tb_d / max(1, pr_d) if use_refined_sparse else 0.0
        ),
        coarse_qubit_delta=tb_q - co_q,
        refined_qubit_delta=tb_q - (rf_q if rf_q > 0 else pr_q),
        tb_gate_depth=tb_gate_d,
        co_gate_depth=co_gate_d,
        gate_depth_ratio=tb_gate_d / max(1, co_gate_d) if tb_gate_d > 0 and co_gate_d > 0 else 0.0,
    )


def run_suite(
    *,
    max_bits: int = 20,
    opt_level: int = 1,
    decompose_reps: int = 2,
    compare_layouts: bool = False,
    sparse_refined: bool = False,
) -> dict[str, Any]:
    cases = [
        15,
        143,
        899,
        10403,
        101 * 103,
        1022117,
    ]
    import random

    random.seed(42)
    for _ in range(6):
        half = max(2, max_bits // 2)
        p = random.randint(1 << (half - 1), (1 << half) - 1) | 1
        q = random.randint(1 << (half - 1), (1 << half) - 1) | 1
        cases.append(p * q)
    cases = sorted(set(cases))

    rows: list[CircuitComparisonRow] = []
    for n in cases:
        if n.bit_length() > max_bits:
            continue
        t0 = time.perf_counter()
        try:
            rows.append(
                compare_one(
                    n,
                    opt_level=opt_level,
                    decompose_reps=decompose_reps,
                    compare_layouts=compare_layouts,
                    sparse_refined=sparse_refined,
                )
            )
        except Exception as exc:  # noqa: BLE001
            print(f"warn: n={n} failed: {exc}", flush=True)
        else:
            elapsed = time.perf_counter() - t0
            if elapsed > 5:
                print(f"info: n={n} built in {elapsed:.1f}s", flush=True)

    return {
        "protocol": "orthogonal_diagonal_qiskit_poc/v2_modexp",
        "opt_level": opt_level,
        "decompose_reps": decompose_reps,
        "max_bits": max_bits,
        "compare_layouts": compare_layouts,
        "sparse_refined": sparse_refined,
        "rows": [asdict(r) for r in rows],
    }


def _print_table(result: dict[str, Any], *, compare_layouts: bool) -> None:
    print(f"protocol: {result['protocol']} (decompose_reps={result['decompose_reps']})")
    sparse_refined = result.get("sparse_refined", False)
    if compare_layouts:
        print(
            "n       L  B  | tb_q co_q rf_q | tb_d  co_d  rf_d | co_ratio rf_ratio | co_Δq rf_Δq"
        )
        for row in result["rows"]:
            print(
                f"{row['n']:>7} {row['L']:>2} {row['B']:>2} | "
                f"{row['textbook_physical_qubits']:>3} {row['coarse_physical_qubits']:>3} "
                f"{row['refined_physical_qubits']:>3} | "
                f"{row['textbook_depth']:>5} {row['coarse_depth']:>5} {row['refined_depth']:>5} | "
                f"{row['coarse_depth_ratio']:>6.2f} {row['refined_depth_ratio']:>6.2f} | "
                f"{row['coarse_qubit_delta']:>4} {row['refined_qubit_delta']:>4}"
            )
    else:
        sp_label = "rf_q" if sparse_refined else "co_q"
        print(f"n       L  B  | tb_q {sp_label} | tb_d  sp_d | depth_ratio | Δqubits")
        for row in result["rows"]:
            sp_q = row["refined_physical_qubits"] if sparse_refined else row["coarse_physical_qubits"]
            sp_d = row["refined_depth"] if sparse_refined else row["coarse_depth"]
            ratio = row["refined_depth_ratio"] if sparse_refined else row["coarse_depth_ratio"]
            dq = row["refined_qubit_delta"] if sparse_refined else row["coarse_qubit_delta"]
            print(
                f"{row['n']:>7} {row['L']:>2} {row['B']:>2} | "
                f"{row['textbook_physical_qubits']:>3} {sp_q:>3} | "
                f"{row['textbook_depth']:>5} {sp_d:>5} | "
                f"{ratio:>6.2f} | {dq:>4}"
            )


def main() -> None:
    parser = argparse.ArgumentParser(description="Qiskit Shor vs orthogonal-diagonal PoC (real mod-exp)")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--max-bits", type=int, default=20)
    parser.add_argument("--opt-level", type=int, default=1)
    parser.add_argument(
        "--decompose-reps",
        type=int,
        default=2,
        help="mod-exp internal decompose depth (lower = faster build, larger = smaller circuit)",
    )
    parser.add_argument(
        "--refined",
        action="store_true",
        help="sparse schedule uses refined layout (L counting + diagonal ancilla)",
    )
    parser.add_argument(
        "--compare-layouts",
        action="store_true",
        help="build coarse and refined sparse circuits side-by-side",
    )
    args = parser.parse_args()

    try:
        import qiskit  # noqa: F401
    except ImportError as exc:
        raise SystemExit("Install qiskit: pip install qiskit") from exc

    result = run_suite(
        max_bits=args.max_bits,
        opt_level=args.opt_level,
        decompose_reps=args.decompose_reps,
        compare_layouts=args.compare_layouts,
        sparse_refined=args.refined and not args.compare_layouts,
    )

    if args.json:
        print(json.dumps(result, indent=2))
        return
    _print_table(result, compare_layouts=args.compare_layouts)


if __name__ == "__main__":
    main()
