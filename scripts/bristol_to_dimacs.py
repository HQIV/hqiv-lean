#!/usr/bin/env python3
"""
Bristol combinational circuit → DIMACS CNF (Tseitin-style, without extra helper variables).

Each wire `w` (0 .. num_wires-1) maps to DIMACS variable ``w + 1``. For each gate we add
clauses that force the output wire to be the correct Boolean function of its inputs.

Supported gates (same as ``bristol_solver.BristolCircuit``): ``INV``, ``AND``, ``XOR``.

Optional: fix the **output** slice (last ``n`` wires), e.g. for preimage / equation solving.
For ``scripts/md5.txt`` (Bristol line ``512 0 128``), use ``--n-output-bits 128`` (or omit it:
defaults to ``n_outputs`` from the file) and a 128-bit digest via ``--fix-output-hex`` or
``--fix-output-md5``.

Examples::

  python3 scripts/bristol_to_dimacs.py path/to/circuit.bristol -o /tmp/c.cnf
  python3 scripts/bristol_to_dimacs.py circuit.bristol --fix-output-hex 0xdeadbeef --n-output-bits 32 -o preimage.cnf
  python3 scripts/bristol_to_dimacs.py scripts/md5.txt --fix-output-md5 d41d8cd98f00b204e9800998ecf8427e -o /tmp/md5_preimage.cnf
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import List

# Run as ``python3 scripts/bristol_to_dimacs.py`` from repo root
_SCRIPTS = Path(__file__).resolve().parent
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from bristol_solver import BristolCircuit, Gate  # noqa: E402


def wire_lit(w: int) -> int:
    """DIMACS literal for wire ``w`` true (1-based variable index)."""
    return w + 1


def wire_neg(w: int) -> int:
    """DIMACS literal for wire ``w`` false."""
    return -(w + 1)


def clauses_inv(out_w: int, in_w: int) -> List[List[int]]:
    """out = NOT in  →  (out ∨ in) ∧ (¬out ∨ ¬in)"""
    o, a = wire_lit(out_w), wire_lit(in_w)
    return [[o, a], [-o, -a]]


def clauses_and(out_w: int, a_w: int, b_w: int) -> List[List[int]]:
    """out = a AND b  →  standard 3-CNF (3 clauses)."""
    o, a, b = wire_lit(out_w), wire_lit(a_w), wire_lit(b_w)
    return [[-o, a], [-o, b], [o, -a, -b]]


def clauses_xor(out_w: int, a_w: int, b_w: int) -> List[List[int]]:
    """out = a XOR b  →  four 3-literal clauses."""
    o, a, b = wire_lit(out_w), wire_lit(a_w), wire_lit(b_w)
    return [[o, a, b], [o, -a, -b], [-o, a, -b], [-o, -a, b]]


def gate_to_clauses(g: Gate) -> List[List[int]]:
    if g.op == "INV":
        return clauses_inv(g.output, g.inputs[0])
    if g.op == "AND":
        return clauses_and(g.output, g.inputs[0], g.inputs[1])
    if g.op == "XOR":
        return clauses_xor(g.output, g.inputs[0], g.inputs[1])
    raise ValueError(f"unsupported gate op: {g.op!r}")


def bristol_to_clauses(circuit: BristolCircuit) -> List[List[int]]:
    out: List[List[int]] = []
    for g in circuit.gates:
        out.extend(gate_to_clauses(g))
    return out


def fix_output_clauses(circuit: BristolCircuit, bits: List[int]) -> List[List[int]]:
    """Unit clauses forcing last ``len(bits)`` wires to ``bits`` (LSB = last wire in slice)."""
    n = len(bits)
    if n > circuit.num_wires:
        raise ValueError(f"more output bits ({n}) than wires ({circuit.num_wires})")
    start = circuit.num_wires - n
    cls: List[List[int]] = []
    for i, bit in enumerate(bits):
        w = start + i
        if bit:
            cls.append([wire_lit(w)])
        else:
            cls.append([wire_neg(w)])
    return cls


def int_to_output_bits(value: int, n_bits: int) -> List[int]:
    """LSB maps to ``circuit.num_wires - n_bits`` (first wire in the output slice)."""
    return [(value >> i) & 1 for i in range(n_bits)]


def parse_md5_digest_hex(s: str) -> int:
    """32 hex characters → 128-bit integer (same bit order as ``--fix-output-hex``)."""
    t = s.strip().replace(" ", "").replace("0x", "")
    if len(t) != 32:
        raise ValueError(f"MD5 digest must be 32 hex characters, got {len(t)}")
    return int(t, 16)


def write_dimacs(
    path: Path | None,
    num_vars: int,
    clauses: List[List[int]],
    comments: List[str] | None = None,
) -> None:
    lines: List[str] = []
    for c in comments or []:
        for line in c.splitlines():
            lines.append("c " + line if not line.startswith("c ") else line)
    lines.append(f"p cnf {num_vars} {len(clauses)}")
    for cl in clauses:
        lines.append(" ".join(str(x) for x in cl) + " 0")
    text = "\n".join(lines) + "\n"
    if path is None:
        sys.stdout.write(text)
    else:
        path.write_text(text, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Bristol circuit → DIMACS CNF")
    p.add_argument("bristol", type=Path, help="Bristol-format circuit file")
    p.add_argument(
        "-o",
        "--output",
        type=Path,
        default=None,
        help="Write DIMACS here (default: stdout)",
    )
    p.add_argument(
        "--fix-output-hex",
        type=str,
        default=None,
        help="Add unit clauses fixing the last --n-output-bits wires to this integer (hex, any width).",
    )
    p.add_argument(
        "--fix-output-md5",
        type=str,
        default=None,
        help="Same as --fix-output-hex for a 128-bit MD5 digest: exactly 32 hex chars (optional spaces).",
    )
    p.add_argument(
        "--n-output-bits",
        type=int,
        default=None,
        help=(
            "How many low bits of the digest are pinned to the last N wires (LSB → lowest-index wire "
            "in that slice). Default: Bristol n_outputs from the file if present (e.g. 128 for md5.txt), "
            "else 32 when --fix-output-hex is set."
        ),
    )
    args = p.parse_args(argv)

    if args.fix_output_hex is not None and args.fix_output_md5 is not None:
        p.error("use only one of --fix-output-hex and --fix-output-md5")

    circuit = BristolCircuit(str(args.bristol))
    clauses = bristol_to_clauses(circuit)

    comments = [
        f"source {args.bristol}",
        f"gates={circuit.num_gates} wires={circuit.num_wires}",
    ]
    if circuit.n_inputs is not None and circuit.n_outputs is not None:
        comments.append(f"Bristol I/O line: n_inputs={circuit.n_inputs} n_outputs={circuit.n_outputs}")

    n_out_bits = args.n_output_bits
    if args.fix_output_hex is not None or args.fix_output_md5 is not None:
        if n_out_bits is None:
            if circuit.n_outputs is not None:
                n_out_bits = circuit.n_outputs
            else:
                n_out_bits = 32
        if args.fix_output_md5 is not None:
            value = parse_md5_digest_hex(args.fix_output_md5)
            digest_label = args.fix_output_md5.strip()
        else:
            assert args.fix_output_hex is not None
            value = int(args.fix_output_hex.strip().replace("0x", ""), 16)
            digest_label = args.fix_output_hex.strip()
        bits = int_to_output_bits(value, n_out_bits)
        clauses.extend(fix_output_clauses(circuit, bits))
        comments.append(f"fixed last {n_out_bits} output wires (digest {digest_label})")

    write_dimacs(args.output, circuit.num_wires, clauses, comments=comments)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
