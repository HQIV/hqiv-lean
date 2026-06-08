#!/usr/bin/env python3
"""
Generate an exact rational toy-model certificate for so(4) closure from
so(3) + Delta4, where Delta4 = J14.

Output:
  artifacts/so4_symbolic_certificate.json
"""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


def j(a: int, b: int, n: int = 4) -> sp.Matrix:
    """Standard antisymmetric generator J_ab (1-indexed)."""
    m = sp.zeros(n, n)
    m[a - 1, b - 1] = 1
    m[b - 1, a - 1] = -1
    return m


def pack_antisym(m: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([m[i, k] for i in range(4) for k in range(i + 1, 4)])


def rat_pair(x: sp.Rational) -> list[int]:
    q = sp.Rational(x)
    return [int(q.p), int(q.q)]


def main() -> None:
    out = Path(__file__).resolve().parent.parent / "artifacts" / "so4_symbolic_certificate.json"
    out.parent.mkdir(parents=True, exist_ok=True)

    basis = [j(1, 2), j(1, 3), j(1, 4), j(2, 3), j(2, 4), j(3, 4)]
    basis_names = ["J12", "J13", "J14", "J23", "J24", "J34"]
    B = sp.Matrix.hstack(*[pack_antisym(x) for x in basis])  # 6x6

    # Seed: so(3) on first 3 coords plus Delta4 = J14
    seed = [j(1, 2), j(1, 3), j(2, 3), j(1, 4)]
    seed_rank = sp.Matrix.hstack(*[pack_antisym(x) for x in seed]).rank()

    coeff = []
    for i in range(6):
        row = []
        for k in range(6):
            br = basis[i] * basis[k] - basis[k] * basis[i]
            v = pack_antisym(br)
            c = B.LUsolve(v)
            row.append([rat_pair(c[t]) for t in range(6)])
        coeff.append(row)

    payload = {
        "description": "Exact rational toy certificate for so(3)+Delta4 -> so(4)",
        "basis_names": basis_names,
        "seed_names": ["J12", "J13", "J23", "Delta4=J14"],
        "seed_linear_rank": int(seed_rank),
        "so4_dimension": 6,
        "witness_brackets": {
            "[J12,J14]": "J24",
            "[J13,J14]": "J34",
        },
        "structure_coeff_q": coeff,
    }

    with open(out, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
