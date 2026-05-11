#!/usr/bin/env python3
"""Verify `8 ∣` every Frobenius sum for the closed-form spinor monomial Gram (see `spinor_monomial_gram_det_mod101.py`)."""

from __future__ import annotations

import sys

# Inline copy of the Kronecker model (keep in sync with `spinor_monomial_gram_det_mod101.py`).
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


def main() -> int:
    mats = [monomial_mat(m) for m in range(64)]
    for i in range(64):
        for j in range(64):
            s = frob_sum(mats[i], mats[j])
            if s % 8 != 0:
                print(f"error: not divisible by 8 at ({i},{j}): {s}", file=sys.stderr)
                return 1
    print("ok: all 64×64 Frobenius sums divisible by 8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
