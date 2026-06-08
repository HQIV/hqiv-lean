#!/usr/bin/env python3
"""
Recomputable certificate for `spinorMonomialGramColumnsZMod101_det` in
`Hqiv/Algebra/CliffordCl06SixSpinorMonomialMatrixCert.lean`.

Builds the **normalized Frobenius Gram** `W` over `ℤ` from the same Kronecker `γ` model as Lean
(`CliffordCl06SixSpinorGammaMatInt` / `spinorGammaMonomialMatZ`):

`Wᵢⱼ = (1/8) * ∑_{a,b} (Mᵢ)ₐᵦ (Mⱼ)ₐᵦ` with `Mᵢ` the ordered `γ` monomial for bitmask `i`.

Computes `det (W mod 101)` in `F₁₀₁` via Gaussian elimination (no SymPy).

Expected: `det W ≡ 1 (mod 101)` (matches the Lean axiom).

Usage (from repo root):

    python3 scripts/spinor_monomial_gram_det_mod101.py
"""

from __future__ import annotations

import sys
from pathlib import Path

P = 101
N = 64

Ix = ((1, 0), (0, 1))
X = ((0, 1), (1, 0))
Z = ((1, 0), (0, -1))
A = ((0, 1), (-1, 0))


def fin8_lo(i: int) -> int:
    return i % 2


def fin8_mid(i: int) -> int:
    return (i // 2) % 2


def fin8_hi(i: int) -> int:
    return i // 4


def mat_get(M: tuple[tuple[int, int], tuple[int, int]], r: int, c: int) -> int:
    return M[r][c]


def kron3(
    A: tuple[tuple[int, int], tuple[int, int]],
    B: tuple[tuple[int, int], tuple[int, int]],
    C: tuple[tuple[int, int], tuple[int, int]],
) -> list[list[int]]:
    out = [[0] * 8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            out[i][j] = (
                mat_get(A, fin8_lo(i), fin8_lo(j))
                * mat_get(B, fin8_mid(i), fin8_mid(j))
                * mat_get(C, fin8_hi(i), fin8_hi(j))
            )
    return out


def mat_mul(A: list[list[int]], B: list[list[int]]) -> list[list[int]]:
    return [[sum(A[i][k] * B[k][j] for k in range(8)) for j in range(8)] for i in range(8)]


GAMMAS = [
    kron3(A, Ix, X),
    kron3(A, Ix, Z),
    kron3(A, A, A),
    kron3(Ix, X, A),
    kron3(Ix, Z, A),
    kron3(X, A, Ix),
]


def mask_indices(m: int) -> list[int]:
    return [i for i in range(6) if (m >> i) & 1]


def monomial_mat(m: int) -> list[list[int]]:
    idx = sorted(mask_indices(m))
    M = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
    for t in idx:
        M = mat_mul(M, GAMMAS[t])
    return M


def frob_sum(A: list[list[int]], B: list[list[int]]) -> int:
    return sum(A[i][j] * B[i][j] for i in range(8) for j in range(8))


def gram_W() -> list[list[int]]:
    mats = [monomial_mat(m) for m in range(N)]
    W = [[0] * N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            s = frob_sum(mats[i], mats[j])
            if s % 8 != 0:
                raise ValueError(f"Frob sum not divisible by 8 at ({i},{j}): {s}")
            W[i][j] = s // 8
    return W


def mod_inv(a: int, p: int) -> int:
    return pow(a % p, p - 2, p)


def determinant_mod_p(mat: list[list[int]], p: int) -> int:
    n = len(mat)
    a = [[mat[i][j] % p for j in range(n)] for i in range(n)]
    det_sign = 1
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if int(a[r][col]) % p != 0:
                pivot = r
                break
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det_sign = (-det_sign) % p
        piv = int(a[col][col]) % p
        inv = mod_inv(piv, p)
        det_sign = (det_sign * piv) % p
        for r in range(col + 1, n):
            if int(a[r][col]) % p == 0:
                continue
            fac = int(a[r][col]) * inv % p
            for c in range(col, n):
                a[r][c] = (a[r][c] - fac * a[col][c]) % p
    return det_sign % p


def main() -> int:
    W = gram_W()
    d = determinant_mod_p(W, P)
    print(f"spinorMonomialGramColumns (Frobenius/8): det mod {P} = {d}")
    if d != 1:
        print(
            f"error: expected 1 (Lean axiom spinorMonomialGramColumnsZMod101_det)",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
