#!/usr/bin/env python3
"""
Generate an exact (symbolic/rational) Lie-closure certificate for so(8)
from the HQIV seed generators g2 union {Delta}, without modifying existing
floating-point certificate files.

Output:
  - JSON certificate with:
      * exact basis (packed 28-vectors over Q)
      * exact structure coefficients c_{ij}^k over Q
      * denominator statistics

Usage:
  cd ~/Repos/HQIV_LEAN
  PYTHONPATH=~/Repos/HQIV python3 scripts/generate_symbolic_lie_closure_certificate.py
  PYTHONPATH=~/Repos/HQIV python3 scripts/generate_symbolic_lie_closure_certificate.py \
      --output artifacts/so8_symbolic_certificate.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Iterable

import sympy as sp

_REPO_LEAN = Path(__file__).resolve().parent.parent
_REPO_HQIV = _REPO_LEAN.parent / "HQIV"
if _REPO_HQIV.exists():
    sys.path.insert(0, str(_REPO_HQIV))


def _to_sympy_matrix(m) -> sp.Matrix:
    """Convert numpy-like matrix with numeric entries to exact sympy Matrix."""
    rows = []
    for i in range(8):
        row = []
        for j in range(8):
            # Current HQVM seed entries are integral / sign values.
            row.append(sp.Rational(int(round(float(m[i][j]))), 1))
        rows.append(row)
    return sp.Matrix(rows)


def _pack_antisym(m: sp.Matrix) -> sp.Matrix:
    """Pack 8x8 antisymmetric matrix to 28x1 vector (upper triangle i<j)."""
    return sp.Matrix([m[i, j] for i in range(8) for j in range(i + 1, 8)])


def _is_zero_matrix(m: sp.Matrix) -> bool:
    return all(v == 0 for v in m)


def _commutator(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    return a * b - b * a


def _rank_of_columns(cols: Iterable[sp.Matrix]) -> int:
    cols = list(cols)
    if not cols:
        return 0
    return sp.Matrix.hstack(*cols).rank()


def build_exact_basis(max_iter: int = 80) -> list[sp.Matrix]:
    """Build a rank-28 Lie-closure basis over Q from g2 union {Delta}."""
    from HQVM.matrices import OctonionHQIVAlgebra

    alg = OctonionHQIVAlgebra(verbose=False)
    seed = [_to_sympy_matrix(g) for g in (alg.g2_basis + [alg.Delta])]
    basis: list[sp.Matrix] = []
    basis_cols: list[sp.Matrix] = []

    # Keep seed order, add only rank-increasing directions.
    for m in seed:
        col = _pack_antisym(m)
        if _rank_of_columns(basis_cols + [col]) > len(basis_cols):
            basis.append(m)
            basis_cols.append(col)

    if len(basis_cols) == 28:
        return basis

    # Lie-closure growth by commutators, exact rank tests over Q.
    for _ in range(max_iter):
        grew = False
        n = len(basis)
        for i in range(n):
            for j in range(i + 1, n):
                c = _commutator(basis[i], basis[j])
                if _is_zero_matrix(c):
                    continue
                col = _pack_antisym(c)
                if _rank_of_columns(basis_cols + [col]) > len(basis_cols):
                    basis.append(c)
                    basis_cols.append(col)
                    grew = True
                    if len(basis_cols) == 28:
                        return basis
        if not grew:
            break

    raise RuntimeError(f"Failed to reach rank 28; got rank {len(basis_cols)}")


def coeff_tensor_exact(basis: list[sp.Matrix]) -> list[list[list[sp.Rational]]]:
    """Compute exact structure constants c_{ij}^k in the chosen basis."""
    cols = [_pack_antisym(m) for m in basis]
    B = sp.Matrix.hstack(*cols)  # 28x28
    if B.rank() != 28:
        raise RuntimeError("Basis matrix is not full rank.")

    coeff: list[list[list[sp.Rational]]] = []
    for i in range(28):
        row = []
        for j in range(28):
            br = _commutator(basis[i], basis[j])
            v = _pack_antisym(br)
            c = B.LUsolve(v)  # exact rational vector
            # Ensure exact identity in packed coordinates.
            if B * c != v:
                raise RuntimeError(f"Symbolic solve verification failed at ({i}, {j}).")
            row.append([sp.Rational(c[k]) for k in range(28)])
        coeff.append(row)
    return coeff


def _rat_to_pair(q: sp.Rational) -> tuple[int, int]:
    return int(q.p), int(q.q)


def _matrix_to_pairs(m: sp.Matrix) -> list[list[list[int]]]:
    out = []
    for i in range(m.rows):
        row = []
        for j in range(m.cols):
            p, q = _rat_to_pair(sp.Rational(m[i, j]))
            row.append([p, q])
        out.append(row)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate exact symbolic so(8) closure certificate.")
    parser.add_argument(
        "--output",
        default=str(_REPO_LEAN / "artifacts" / "so8_symbolic_certificate.json"),
        help="Output JSON path (default: artifacts/so8_symbolic_certificate.json)",
    )
    parser.add_argument("--max-iter", type=int, default=80, help="Max closure growth iterations.")
    args = parser.parse_args()

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    basis = build_exact_basis(max_iter=args.max_iter)
    coeff = coeff_tensor_exact(basis)

    denoms = [int(c.q) for i in range(28) for j in range(28) for c in coeff[i][j]]
    max_denom = max(denoms) if denoms else 1

    payload = {
        "description": "Exact symbolic Lie-closure certificate over Q for HQIV g2 + Delta in so(8)",
        "basis_count": len(basis),
        "basis_packed_q": [_matrix_to_pairs(_pack_antisym(m)) for m in basis],
        "coeff_q": [
            [[list(_rat_to_pair(c)) for c in coeff[i][j]] for j in range(28)]
            for i in range(28)
        ],
        "stats": {
            "max_denominator": max_denom,
            "nonzero_coeff_count": sum(
                1 for i in range(28) for j in range(28) for c in coeff[i][j] if c != 0
            ),
        },
    }

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    print(f"Wrote symbolic certificate: {out_path}")
    print(f"Basis size: {len(basis)} (expected 28)")
    print(f"Max coefficient denominator: {max_denom}")


if __name__ == "__main__":
    main()
