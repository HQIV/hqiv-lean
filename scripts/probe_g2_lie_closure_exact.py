#!/usr/bin/env python3
"""
Exact Lie-closure probe for HQIV octonion left-multiplication data (SymPy, ℚ).

Motivation
----------
The float classifier ``classify_g2_so8_good_generators.py`` can mis-read 𝔤₂ seeds because
``numpy.linalg`` rank / SVD thresholds are not exact.  Older ``HQVM/matrices.py`` builds
had a **transcription bug in ``L(e₆)``** (two rows duplicated); that breaks skew-adjointness
and contaminates float probes.  The tables here match ``Hqiv/OctonionLeftMultiplication.lean``.

This script still builds **skew-symmetrized** matrices ``L′ᵢ := (Lᵢ − Lᵢᵀ)/2`` so the probe
stays honest if a table regresses; with the corrected ``L₆``, ``L′ = L``.

It reports, over ℚ:

* linear ``rank`` of the packed 28-vector span of each seed list;
* **Lie-saturation dimension**: iterative adjoining of commutators until the packed rank stabilizes.

No dependency on the HQIV Python tree: integer tables are inlined (same literals as ``HQVM/matrices.py``).

Run::

  cd ~/Repos/HQIV_LEAN
  python3 scripts/probe_g2_lie_closure_exact.py
  python3 scripts/probe_g2_lie_closure_exact.py --pairs hqvm14 lean14 all21
"""

from __future__ import annotations

import argparse
from itertools import combinations
from typing import Iterable

import sympy as sp

Int = sp.Integer


def _L_tables() -> list[list[list[int]]]:
    """Same 8×8 integer tables as ``HQVM/matrices.py::_build_left_multiplications`` (L₁…L₇)."""
    L7 = [
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
    ]
    L1 = [
        [0, -1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
    ]
    L2 = [
        [0, 0, -1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
    ]
    L3 = [
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0, 0],
    ]
    L4 = [
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
        [0, 0, -1, 0, 0, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
    ]
    L5 = [
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, -1],
        [0, 0, 0, 0, 0, 0, 1, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
    ]
    L6 = [
        [0, 0, 0, 0, 0, 0, -1, 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, 0, -1, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0, 0],
    ]
    return [L1, L2, L3, L4, L5, L6, L7]


def matrix_from_table(rows: list[list[int]]) -> sp.Matrix:
    return sp.Matrix([[Int(x) for x in row] for row in rows])


def skew_part(M: sp.Matrix) -> sp.Matrix:
    """Return (M − Mᵀ)/2 (exact skew-symmetric part)."""
    return (M - M.transpose()) / 2


def pack_upper(M: sp.Matrix) -> sp.Matrix:
    """28×1 column vector: entries M[i,j] for i < j (antisymmetric degrees of freedom)."""
    return sp.Matrix([M[i, j] for i in range(8) for j in range(i + 1, 8)])


def unpack_upper(v: sp.Matrix) -> sp.Matrix:
    M = sp.zeros(8, 8)
    idx = 0
    for i in range(8):
        for j in range(i + 1, 8):
            M[i, j] = v[idx]
            M[j, i] = -v[idx]
            idx += 1
    return M


def comm(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def packed_rank(cols: list[sp.Matrix]) -> int:
    if not cols:
        return 0
    M = sp.Matrix.hstack(*cols)
    return int(M.rank())


def lie_closure_packed_rank_exact(
    seed: list[sp.Matrix],
    *,
    max_rounds: int = 200,
) -> tuple[int, int]:
    """
    Return (final packed ℚ-rank, number of matrices in the saturated list).

    Saturation: repeatedly append any commutator whose packed vector increases ℚ-rank
    of the current matrix list; stop when one full pass adds nothing.
    """
    ms = [M.copy() for M in seed]
    for _ in range(max_rounds):
        cols = [pack_upper(M) for M in ms]
        r0 = packed_rank(cols)
        n = len(ms)
        added = False
        for i in range(n):
            for j in range(i + 1, n):
                C = comm(ms[i], ms[j])
                if C.is_zero_matrix:
                    continue
                trial = cols + [pack_upper(C)]
                if packed_rank(trial) > r0:
                    ms.append(C)
                    added = True
                    break
            if added:
                break
        if not added:
            break
    return packed_rank([pack_upper(M) for M in ms]), len(ms)


def build_L_prime_skew() -> list[sp.Matrix]:
    """Skew-symmetrized HQIV ``L(e₁)…L(e₇)`` as exact SymPy matrices."""
    return [skew_part(matrix_from_table(T)) for T in _L_tables()]


def delta_matrix() -> sp.Matrix:
    D = sp.zeros(8, 8)
    D[1, 7] = -1
    D[7, 1] = 1
    return D


def g2_commutators(Lp: list[sp.Matrix], pairs: Iterable[tuple[int, int]]) -> list[sp.Matrix]:
    out: list[sp.Matrix] = []
    for i, j in pairs:
        C = comm(Lp[i], Lp[j])
        if not C.is_zero_matrix:
            out.append(C)
    return out


# ``Hqiv.Algebra.g2Generator`` lex pairs (indices into L′ with 0 = e₁, …, 6 = e₇).
LEAN_G2_PAIRS = [
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 6),
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (1, 6),
    (2, 3),
    (2, 4),
    (2, 5),
]


def hqvm_first14_pairs() -> list[tuple[int, int]]:
    """First 14 pairs in ``combinations(range(7),2)`` order (matches ``_build_g2_basis``)."""
    return list(combinations(range(7), 2))[:14]


def all_nontrivial_pairs() -> list[tuple[int, int]]:
    return list(combinations(range(7), 2))


def so7_bivectors() -> list[sp.Matrix]:
    mats: list[sp.Matrix] = []
    for i in range(7):
        for j in range(i + 1, 7):
            M = sp.zeros(8, 8)
            M[i, j] = 1
            M[j, i] = -1
            mats.append(M)
    return mats


def main() -> int:
    parser = argparse.ArgumentParser(description="Exact ℚ Lie-closure rank probe (SymPy).")
    parser.add_argument(
        "--pairs",
        nargs="*",
        choices=("hqvm14", "lean14", "all21"),
        default=["hqvm14", "lean14", "all21"],
    )
    args = parser.parse_args()

    L_raw = [matrix_from_table(T) for T in _L_tables()]
    Lp = build_L_prime_skew()

    print("# Exact Lie-closure probe (SymPy, ℚ)")
    print("# HQVM L tables: raw skew check max |M+Mᵀ| entries (should be 0 after skew-part for L′).")
    for k, M in enumerate(L_raw):
        S = M + M.transpose()
        mx = max(abs(S[i, j]) for i in range(8) for j in range(8))
        print(f"#   L_raw[{k}] (e_{k+1}) max|M+Mᵀ| = {mx}")
    print()

    if "hqvm14" in args.pairs:
        g2 = g2_commutators(Lp, hqvm_first14_pairs())
        lin = packed_rank([pack_upper(M) for M in g2])
        sat, nm = lie_closure_packed_rank_exact(g2)
        print(f"hqvm14_commutators_of_Lprime:  count={len(g2)}  packed_Q_rank={lin}  lie_saturated_rank={sat}  n_matrices={nm}")

    if "lean14" in args.pairs:
        g2 = g2_commutators(Lp, LEAN_G2_PAIRS)
        lin = packed_rank([pack_upper(M) for M in g2])
        sat, nm = lie_closure_packed_rank_exact(g2)
        print(f"lean14_commutators_of_Lprime:   count={len(g2)}  packed_Q_rank={lin}  lie_saturated_rank={sat}  n_matrices={nm}")

    if "all21" in args.pairs:
        g2 = g2_commutators(Lp, all_nontrivial_pairs())
        lin = packed_rank([pack_upper(M) for M in g2])
        sat, nm = lie_closure_packed_rank_exact(g2)
        print(f"all21_commutators_of_Lprime:    count={len(g2)}  packed_Q_rank={lin}  lie_saturated_rank={sat}  n_matrices={nm}")

    # Reference: Δ + lean14 (matches certificate story)
    if "lean14" in args.pairs:
        g2 = g2_commutators(Lp, LEAN_G2_PAIRS)
        seed = g2 + [delta_matrix()]
        lin = packed_rank([pack_upper(M) for M in seed])
        sat, nm = lie_closure_packed_rank_exact(seed)
        print(f"lean14_plus_Delta:              packed_Q_rank={lin}  lie_saturated_rank={sat}  n_matrices={nm}")

    # Sanity: true subalgebra
    s7 = so7_bivectors()
    lin7 = packed_rank([pack_upper(M) for M in s7])
    sat7, n7 = lie_closure_packed_rank_exact(s7)
    print(f"so7_bivectors_coords0..6:      count={len(s7)}  packed_Q_rank={lin7}  lie_saturated_rank={sat7}  n_matrices={n7}")
    seed = s7 + [delta_matrix()]
    lin = packed_rank([pack_upper(M) for M in seed])
    sat, nm = lie_closure_packed_rank_exact(seed)
    print(f"so7_plus_Delta:                 packed_Q_rank={lin}  lie_saturated_rank={sat}  n_matrices={nm}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
