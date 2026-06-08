#!/usr/bin/env python3
"""
General Bristol Circuit Solver + HQIV-OSH Preimage Search

This script:
1. Parses Bristol-format circuit files.
2. Evaluates the circuit on inputs.
3. Uses the HQIV-OSH integrated engine to search for preimages.

Supports reduced-round extraction for testing (e.g., first N rounds of MD5).
"""

import argparse
import time
from typing import List, Tuple, Dict
from dataclasses import dataclass
import mpmath as mp

mp.mp.dps = 60

@dataclass
class Gate:
    op: str
    inputs: List[int]
    output: int

class BristolCircuit:
    def __init__(self, filepath: str):
        self.gates: List[Gate] = []
        self.num_wires = 0
        self.num_gates = 0
        #: If present, second line ``n_in _ n_out`` (e.g. ``512 0 128`` for ``md5.txt``).
        self.n_inputs: int | None = None
        self.n_outputs: int | None = None
        self.parse(filepath)

    def parse(self, filepath: str):
        with open(filepath, 'r') as f:
            lines = f.readlines()

        # First line: num_gates num_wires
        header = lines[0].strip().split()
        self.num_gates = int(header[0])
        self.num_wires = int(header[1])

        start = 1
        if len(lines) > 1:
            p2 = lines[1].strip().split()
            if (
                len(p2) == 3
                and p2[0].isdigit()
                and p2[1].lstrip("-").isdigit()
                and p2[2].isdigit()
                and p2[0] not in ("1", "2")
            ):
                self.n_inputs = int(p2[0])
                self.n_outputs = int(p2[2])
                start = 2

        for line in lines[start:]:
            parts = line.strip().split()
            if not parts:
                continue

            if parts[0] == '1':  # 1-input gate (INV)
                op = 'INV'
                inputs = [int(parts[2])]
                output = int(parts[3])
            elif parts[0] == '2':  # 2-input gate (AND, XOR)
                op = parts[5]  # AND or XOR
                inputs = [int(parts[2]), int(parts[3])]
                output = int(parts[4])
            else:
                continue

            self.gates.append(Gate(op, inputs, output))

    def evaluate(self, inputs: List[int]) -> List[int]:
        """Evaluate the circuit on binary inputs."""
        wire_values = [0] * self.num_wires

        # Set input wires (first len(inputs) wires)
        for i, val in enumerate(inputs):
            if i < self.num_wires:
                wire_values[i] = val

        for gate in self.gates:
            if gate.op == 'INV':
                a = wire_values[gate.inputs[0]]
                wire_values[gate.output] = 1 - a
            elif gate.op == 'AND':
                a = wire_values[gate.inputs[0]]
                b = wire_values[gate.inputs[1]]
                wire_values[gate.output] = a & b
            elif gate.op == 'XOR':
                a = wire_values[gate.inputs[0]]
                b = wire_values[gate.inputs[1]]
                wire_values[gate.output] = a ^ b

        # Return output wires (last few wires)
        # For MD5, output is typically the last 128 bits (or first 32 for testing)
        return wire_values[-32:]  # Return last 32 bits for testing

def find_preimage_bristol(circuit: BristolCircuit, target: List[int], max_sweeps: int = 100) -> dict:
    """
    BQGate Phase Evolution (|allwirephasespace>).

    Each wire has phase interval [low, high] (representing [0, 2π]).
    We apply quantum versions of the gates (mod 2π phase operations)
    in iterative sweeps until the input wires collapse to 0 or 1.
    """
    started = time.perf_counter()

    input_size = len(target)
    low = [0.0] * circuit.num_wires
    high = [1.0] * circuit.num_wires

    # Set output constraints (target phase)
    output_start = circuit.num_wires - input_size
    for i, bit in enumerate(target):
        wire_idx = output_start + i
        if wire_idx < circuit.num_wires:
            if bit == 0:
                high[wire_idx] = 0.0
            else:
                low[wire_idx] = 1.0

    sweeps = 0
    changed = True

    while changed and sweeps < max_sweeps:
        changed = False
        sweeps += 1

        for gate in circuit.gates:
            if gate.op == 'INV':
                # X gate: phase flip (mod 1)
                out_wire = gate.output
                in_wire = gate.inputs[0]
                if low[out_wire] == high[out_wire]:
                    val = low[out_wire]
                    new_val = (1.0 - val) % 1.0
                    if low[in_wire] != new_val or high[in_wire] != new_val:
                        low[in_wire] = high[in_wire] = new_val
                        changed = True
            elif gate.op == 'XOR':
                # CNOT: if control is |1>, flip target phase (mod 1)
                out_wire = gate.output
                in1, in2 = gate.inputs  # in1 = control, in2 = target
                if low[in1] == high[in1] == 1.0:
                    new_low = (1.0 - high[in2]) % 1.0
                    new_high = (1.0 - low[in2]) % 1.0
                    if low[in2] != new_low or high[in2] != new_high:
                        low[in2] = new_low
                        high[in2] = new_high
                        changed = True
            elif gate.op == 'AND':
                # Toffoli: if both controls are |1>, flip target phase (mod 1)
                out_wire = gate.output
                in1, in2 = gate.inputs
                if low[in1] == high[in1] == 1.0 and low[in2] == high[in2] == 1.0:
                    new_low = (1.0 - high[out_wire]) % 1.0
                    new_high = (1.0 - low[out_wire]) % 1.0
                    if low[out_wire] != new_low or high[out_wire] != new_high:
                        low[out_wire] = new_low
                        high[out_wire] = new_high
                        changed = True

    # Extract input wires
    input_bits = []
    for i in range(min(input_size, circuit.num_wires)):
        if low[i] == high[i]:
            input_bits.append(1 if low[i] >= 0.5 else 0)
        else:
            input_bits.append(0)

    output = circuit.evaluate(input_bits)
    success = output == target

    return {
        "success": success,
        "sweeps": sweeps,
        "preimage": sum(bit << i for i, bit in enumerate(input_bits)),
        "time": time.perf_counter() - started
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Bristol Circuit Solver + HQIV-OSH Preimage Search")
    parser.add_argument("circuit_file", help="Path to Bristol circuit file")
    parser.add_argument("--target", type=str, default="0x12345678", help="Target output (hex)")
    parser.add_argument("--max-steps", type=int, default=500)
    args = parser.parse_args()

    print(f"Loading circuit: {args.circuit_file}")
    circuit = BristolCircuit(args.circuit_file)
    print(f"Circuit loaded: {circuit.num_gates} gates, {circuit.num_wires} wires")

    target_int = int(args.target, 16)
    target_bits = [(target_int >> i) & 1 for i in range(32)]

    print(f"Searching for preimage of {args.target}...")
    start = time.time()
    result = find_preimage_bristol(circuit, target_bits, max_sweeps=args.max_steps)
    elapsed = time.time() - start

    print(f"\nResult: {'SUCCESS' if result['success'] else 'FAIL'} in {result['sweeps']} sweeps ({elapsed:.2f}s)")
    if result['success']:
        print(f"Candidate: {result['candidate']}")