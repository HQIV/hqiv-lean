#!/usr/bin/env python3
"""Symbolic check: [T^a,T^b] = i * sum_c f^{abc} T^c for HQIV chart (half Gell-Mann + f table)."""

import itertools
from fractions import Fraction

try:
    import sympy as sp
except ImportError:
    raise SystemExit("need sympy")

I = sp.I
sqrt3 = sp.sqrt(3)


def lam(a: int) -> sp.Matrix:
    assert 0 <= a <= 7
    Z = sp.zeros(3, 3)
    if a == 0:
        return sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    if a == 1:
        return sp.Matrix([[0, -I, 0], [I, 0, 0], [0, 0, 0]])
    if a == 2:
        return sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
    if a == 3:
        return sp.Matrix([[0, 0, 1], [0, 0, 0], [1, 0, 0]])
    if a == 4:
        return sp.Matrix([[0, 0, -I], [0, 0, 0], [I, 0, 0]])
    if a == 5:
        return sp.Matrix([[0, 0, 0], [0, 0, 1], [0, 1, 0]])
    if a == 6:
        return sp.Matrix([[0, 0, 0], [0, 0, -I], [0, I, 0]])
    if a == 7:
        return (1 / sqrt3) * sp.Matrix([[1, 0, 0], [0, 1, 0], [0, 0, -2]])
    return Z


def T(a: int) -> sp.Matrix:
    return sp.Rational(1, 2) * lam(a)


def min3(a, b, c):
    return min(a, b, c)


def max3(a, b, c):
    return max(a, b, c)


def mid3(a, b, c):
    i = min3(a, b, c)
    k = max3(a, b, c)
    if a != i and a != k:
        return a
    if b != i and b != k:
        return b
    return c


def perm_sign(a, b, c) -> int:
    if a == b or b == c or c == a:
        return 0
    i, j, k = min3(a, b, c), mid3(a, b, c), max3(a, b, c)
    if (a, b, c) == (i, j, k):
        return 1
    if (a, b, c) == (i, k, j):
        return -1
    if (a, b, c) == (j, i, k):
        return -1
    if (a, b, c) == (j, k, i):
        return 1
    if (a, b, c) == (k, i, j):
        return 1
    if (a, b, c) == (k, j, i):
        return -1
    return 0


def f_sorted(i, j, k) -> sp.Expr:
    assert i < j < k
    key = (i, j, k)
    if key == (0, 1, 2):
        return sp.Integer(1)
    if key == (0, 3, 6):
        return sp.Rational(1, 2)
    if key == (0, 4, 5):
        return sp.Rational(-1, 2)
    if key == (1, 3, 5):
        return sp.Rational(1, 2)
    if key == (1, 4, 6):
        return sp.Rational(1, 2)
    if key == (2, 3, 4):
        return sp.Rational(1, 2)
    if key == (2, 5, 6):
        return sp.Rational(-1, 2)
    if key == (3, 4, 7):
        return sqrt3 / 2
    if key == (5, 6, 7):
        return sqrt3 / 2
    return sp.Integer(0)


def f_abc(a: int, b: int, c: int) -> sp.Expr:
    if a == b or b == c or c == a:
        return sp.Integer(0)
    i, j, k = min3(a, b, c), mid3(a, b, c), max3(a, b, c)
    if not (i < j < k):
        return sp.Integer(0)
    return perm_sign(a, b, c) * f_sorted(i, j, k)


def main() -> None:
    ok = True
    for a, b in itertools.product(range(8), repeat=2):
        lhs = T(a) * T(b) - T(b) * T(a)
        acc = sp.zeros(3, 3)
        for c in range(8):
            acc += f_abc(a, b, c) * T(c)
        rhs = I * acc
        d = sp.simplify(lhs - rhs)
        if d != sp.zeros(3, 3):
            print("FAIL", a, b, d)
            ok = False
    print("all_ok" if ok else "some_fail")


if __name__ == "__main__":
    main()
