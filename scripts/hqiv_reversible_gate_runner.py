#!/usr/bin/env python3
"""
Run a Bristol-style gate map as a reversible gate system.

Lean alignment (DigitalGates.lean):
- Gates are treated as bijections/permutations on discrete basis states (`HQIVGate`).
- CNOT-like behavior is permutation-based (`cnotPerm` / `applyPermFour`).

This runner uses the reversible update form:
  target_bit ^= f(control_bits)
which is an involution (self-inverse) when controls are read-only for that gate.
Applying the same gate list in reverse order therefore inverts the circuit.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional

try:
    from gate_map_to_quantum import GateMap, parse_gate_map
except ImportError:
    from scripts.gate_map_to_quantum import GateMap, parse_gate_map


@dataclass(frozen=True)
class BitState:
    """Little-endian bit state over `num_wires` wires."""

    num_wires: int
    value: int

    @classmethod
    def from_bitstring(cls, bits: str, num_wires: int) -> "BitState":
        cleaned = bits.strip().replace("_", "")
        if cleaned.startswith("0b"):
            cleaned = cleaned[2:]
        if len(cleaned) > num_wires:
            raise ValueError(
                f"Bitstring length {len(cleaned)} exceeds wire count {num_wires}."
            )
        v = int(cleaned, 2) if cleaned else 0
        return cls(num_wires=num_wires, value=v)

    def bit(self, i: int) -> int:
        return (self.value >> i) & 1

    def with_toggled(self, i: int, flip: int) -> "BitState":
        if flip & 1:
            return BitState(self.num_wires, self.value ^ (1 << i))
        return self

    def to_bitstring(self) -> str:
        return format(self.value, f"0{self.num_wires}b")


def _gate_flip(gate_op: str, controls: List[int], state: BitState) -> int:
    if gate_op == "XOR":
        a, b = controls
        return state.bit(a) ^ state.bit(b)
    if gate_op == "AND":
        a, b = controls
        return state.bit(a) & state.bit(b)
    if gate_op == "INV":
        a = controls[0]
        return 1 ^ state.bit(a)
    raise ValueError(f"Unsupported op '{gate_op}'.")


def apply_gate(state: BitState, gate_op: str, controls: List[int], target: int) -> BitState:
    flip = _gate_flip(gate_op, controls, state)
    return state.with_toggled(target, flip)


def run_forward(gmap: GateMap, initial: BitState) -> BitState:
    s = initial
    for g in gmap.gates:
        s = apply_gate(s, g.op, g.inputs, g.output)
    return s


def run_reverse(gmap: GateMap, final_state: BitState) -> BitState:
    s = final_state
    for g in reversed(gmap.gates):
        # Same update because each out ^= f(...) gate is self-inverse.
        s = apply_gate(s, g.op, g.inputs, g.output)
    return s


def validate_reversible_shape(gmap: GateMap) -> List[str]:
    warnings: List[str] = []
    for idx, g in enumerate(gmap.gates):
        if g.output in g.inputs:
            warnings.append(
                f"gate#{idx} ({g.op}) writes to one of its controls; "
                "reversibility can fail unless this is intentional."
            )
    return warnings


def parse_args(argv: Optional[Iterable[str]] = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Execute and reverse a gate map with reversible out^=f semantics."
    )
    p.add_argument("input", type=Path, help="Gate map file")
    p.add_argument(
        "--initial",
        type=str,
        default=None,
        help=(
            "Initial full-wire bitstring (MSB..LSB). "
            "If omitted, uses input wires from --inputs and sets other wires to 0."
        ),
    )
    p.add_argument(
        "--inputs",
        type=str,
        default=None,
        help=(
            "Input-wire bitstring (MSB..LSB) for the first 'input_wires' wires. "
            "Ignored when --initial is provided."
        ),
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="Verify reverse(forward(state)) == state and print result.",
    )
    return p.parse_args(argv)


def _compose_initial_from_input_bits(gmap: GateMap, input_bits: Optional[str]) -> BitState:
    if input_bits is None:
        input_bits = "0" * gmap.input_wires
    cleaned = input_bits.strip().replace("_", "")
    if cleaned.startswith("0b"):
        cleaned = cleaned[2:]
    if len(cleaned) != gmap.input_wires:
        raise ValueError(
            f"--inputs must be exactly {gmap.input_wires} bits for this gate map."
        )
    input_val = int(cleaned, 2) if cleaned else 0
    # Input wires are assumed to be the first [0, input_wires) in little-endian wire indexing.
    # We place parsed MSB..LSB bits directly into the low-order region.
    return BitState(num_wires=gmap.num_wires, value=input_val)


def main(argv: Optional[Iterable[str]] = None) -> int:
    args = parse_args(argv)
    gmap = parse_gate_map(args.input)
    warnings = validate_reversible_shape(gmap)
    for w in warnings[:20]:
        print(f"warning: {w}")
    if len(warnings) > 20:
        print(f"warning: {len(warnings) - 20} additional warnings omitted")

    if args.initial is not None:
        initial = BitState.from_bitstring(args.initial, gmap.num_wires)
    else:
        initial = _compose_initial_from_input_bits(gmap, args.inputs)

    forward = run_forward(gmap, initial)
    recovered = run_reverse(gmap, forward)

    print(f"wires: {gmap.num_wires}, gates: {len(gmap.gates)}")
    print(f"initial : {initial.to_bitstring()}")
    print(f"forward : {forward.to_bitstring()}")
    print(f"reverse : {recovered.to_bitstring()}")

    if args.check:
        ok = recovered.value == initial.value
        print(f"roundtrip_ok: {ok}")
        return 0 if ok else 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
