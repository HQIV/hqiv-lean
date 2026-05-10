#!/usr/bin/env python3
"""
Convert a SHA256-style logic gate map into an equivalent quantum circuit.

The expected input format is:
1) "<num_gates> <num_wires>"
2) "<input_wires> <maybe_unused> <output_wires>" (compact variant used here)
3+) Gate lines in Bristol style:
     - Binary gate: "2 1 <in_a> <in_b> <out> XOR|AND"
     - Unary gate:  "1 1 <in> <out> INV"

The generated circuit uses one qubit per wire and maps operations as:
 - XOR(a,b)->out  as CX(a,out); CX(b,out)
 - AND(a,b)->out  as CCX(a,b,out)
 - INV(a)->out    as X(out); CX(a,out)

This realizes out ^= f(inputs), which is exact when out starts at |0>.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional


@dataclass(frozen=True)
class Gate:
    op: str
    inputs: List[int]
    output: int


@dataclass(frozen=True)
class GateMap:
    num_gates_declared: int
    num_wires: int
    input_wires: int
    output_wires: int
    gates: List[Gate]


def _parse_ints(line: str) -> List[int]:
    return [int(tok) for tok in line.split()]


def parse_gate_map(path: Path) -> GateMap:
    lines = [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()]
    if len(lines) < 3:
        raise ValueError("Gate map file is too short.")

    header = _parse_ints(lines[0])
    if len(header) != 2:
        raise ValueError("First line must have exactly two integers: '<num_gates> <num_wires>'.")
    num_gates_declared, num_wires = header

    io_header = _parse_ints(lines[1])
    if len(io_header) < 2:
        raise ValueError("Second line must provide at least input and output wire counts.")
    input_wires = io_header[0]
    output_wires = io_header[-1]

    gates: List[Gate] = []
    for idx, line in enumerate(lines[2:], start=3):
        parts = line.split()
        if len(parts) < 5:
            raise ValueError(f"Malformed gate line {idx}: '{line}'")

        fanin = int(parts[0])
        fanout = int(parts[1])
        if fanout != 1:
            raise ValueError(f"Only fanout=1 is supported (line {idx}).")

        op = parts[-1].upper()
        payload = [int(x) for x in parts[2:-1]]
        if op in {"XOR", "AND"}:
            if fanin != 2 or len(payload) != 3:
                raise ValueError(f"Expected '2 1 a b out {op}' on line {idx}.")
            in_a, in_b, out = payload
            gates.append(Gate(op=op, inputs=[in_a, in_b], output=out))
        elif op in {"INV", "NOT"}:
            if fanin != 1 or len(payload) != 2:
                raise ValueError(f"Expected '1 1 a out {op}' on line {idx}.")
            in_a, out = payload
            gates.append(Gate(op="INV", inputs=[in_a], output=out))
        else:
            raise ValueError(f"Unsupported op '{op}' on line {idx}.")

    if len(gates) != num_gates_declared:
        raise ValueError(
            f"Declared {num_gates_declared} gates but parsed {len(gates)}."
        )

    return GateMap(
        num_gates_declared=num_gates_declared,
        num_wires=num_wires,
        input_wires=input_wires,
        output_wires=output_wires,
        gates=gates,
    )


def build_quantum_circuit(gmap: GateMap) -> QuantumCircuit:
    try:
        from qiskit import QuantumCircuit
    except ImportError as exc:  # pragma: no cover - runtime dependency check
        raise SystemExit(
            "qiskit is required. Install with: pip install qiskit"
        ) from exc

    qc = QuantumCircuit(gmap.num_wires, name="logic_map_equivalent")
    for gate in gmap.gates:
        if gate.op == "XOR":
            a, b = gate.inputs
            out = gate.output
            qc.cx(a, out)
            qc.cx(b, out)
        elif gate.op == "AND":
            a, b = gate.inputs
            out = gate.output
            qc.ccx(a, b, out)
        elif gate.op == "INV":
            a = gate.inputs[0]
            out = gate.output
            qc.x(out)
            qc.cx(a, out)
        else:  # pragma: no cover - parser already enforces this
            raise ValueError(f"Unsupported op during build: {gate.op}")
    return qc


def summarize(gmap: GateMap) -> str:
    counts = {"XOR": 0, "AND": 0, "INV": 0}
    for gate in gmap.gates:
        counts[gate.op] = counts.get(gate.op, 0) + 1
    return (
        f"Parsed {len(gmap.gates)} gates across {gmap.num_wires} wires\n"
        f"Inputs: {gmap.input_wires} wires, Outputs: {gmap.output_wires} wires\n"
        f"Gate counts: XOR={counts.get('XOR', 0)}, "
        f"AND={counts.get('AND', 0)}, INV={counts.get('INV', 0)}"
    )


def write_qasm(circuit: QuantumCircuit, out_path: Path) -> None:
    qasm = circuit.qasm()
    out_path.write_text(qasm, encoding="utf-8")


def parse_args(argv: Optional[Iterable[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Convert a gate map file to a Qiskit quantum circuit."
    )
    parser.add_argument("input", type=Path, help="Path to logic gate map text file")
    parser.add_argument(
        "--qasm-out",
        type=Path,
        default=None,
        help="Optional output path for OpenQASM 2.0 text",
    )
    parser.add_argument(
        "--print-circuit",
        action="store_true",
        help="Print text diagram of the resulting quantum circuit",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Iterable[str]] = None) -> int:
    args = parse_args(argv)
    gmap = parse_gate_map(args.input)
    qc = build_quantum_circuit(gmap)

    print(summarize(gmap))
    print(f"Quantum ops in circuit: {sum(qc.count_ops().values())}")

    if args.qasm_out is not None:
        write_qasm(qc, args.qasm_out)
        print(f"Wrote QASM to: {args.qasm_out}")

    if args.print_circuit:
        print(qc)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
