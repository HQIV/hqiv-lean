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

By default the script prints the 14 concrete ``\\mathfrak{g}_2`` seed matrices and ``Delta``
(8×8, exact integers after rounding floats from HQVM) to stdout for manuscript / appendix
listings. Use ``--no-print-matrices`` to suppress.
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


def load_seed_g2_and_delta() -> tuple[list[sp.Matrix], sp.Matrix]:
    """Return exact SymPy 8×8 matrices for the 14-element ``g2`` basis and ``Delta``."""
    from HQVM.matrices import OctonionHQIVAlgebra

    alg = OctonionHQIVAlgebra(verbose=False)
    g2 = [_to_sympy_matrix(g) for g in alg.g2_basis]
    delta = _to_sympy_matrix(alg.Delta)
    return g2, delta


def format_matrix_8x8(m: sp.Matrix, *, col_width: int = 4) -> str:
    """Human-readable 8×8 block (entries as exact rationals / integers)."""
    lines = []
    for i in range(8):
        cells = [str(sp.Rational(m[i, j])).rjust(col_width) for j in range(8)]
        lines.append(" ".join(cells))
    return "\n".join(lines)


def print_proof_seed_matrices(
    g2: list[sp.Matrix],
    delta: sp.Matrix,
    *,
    stream=sys.stdout,
) -> None:
    """Print the concrete matrices cited in the Lie-closure proof (seed before bracket closure)."""
    stream.write(
        "\n# === Proof seed: 14 × \\mathfrak{g}_2 generators + \\Delta (8×8 each) ===\n"
    )
    for i, mat in enumerate(g2):
        stream.write(f"\n## g2_basis[{i}]\n")
        stream.write(format_matrix_8x8(mat))
        stream.write("\n")
    stream.write("\n## Delta (phase-lift generator on the chosen plane)\n")
    stream.write(format_matrix_8x8(delta))
    stream.write("\n")


def build_exact_basis(max_iter: int = 80, seed: list[sp.Matrix] | None = None) -> list[sp.Matrix]:
    """Build a rank-28 Lie-closure basis over Q from g2 union {Delta}.

    If ``seed`` is omitted, matrices are loaded from ``OctonionHQIVAlgebra`` once.
    """
    if seed is None:
        g2, delta = load_seed_g2_and_delta()
        seed = g2 + [delta]
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
    parser.add_argument(
        "--print-matrices",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Print 14 g2 + Delta 8×8 matrices to stdout (default: on).",
    )
    parser.add_argument(
        "--print-full-basis",
        action="store_true",
        help="After closure, also print all 28 basis 8×8 matrices (large).",
    )
    args = parser.parse_args()

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    g2, delta = load_seed_g2_and_delta()
    if args.print_matrices:
        print_proof_seed_matrices(g2, delta)

    basis = build_exact_basis(max_iter=args.max_iter, seed=g2 + [delta])
    if args.print_full_basis:
        print("\n# === Full Lie-closure basis (28 matrices) ===\n", file=sys.stdout)
        for k, mat in enumerate(basis):
            print(f"\n## closure_basis[{k}]\n{format_matrix_8x8(mat)}\n", file=sys.stdout)
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
