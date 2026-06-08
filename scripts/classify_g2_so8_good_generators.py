#!/usr/bin/env python3
"""
Explore Lie-closure dimensions for ``⟨seed, X⟩`` inside the 28-dimensional real model of 𝔰𝔬(8)
(antisymmetric 8×8 matrices, upper-triangle packing).

**Primary experiment (default):** ``seed = 𝔰𝔬(7)`` embedded on coordinates 0..6 (21 generators).
This is a **proper** 21-dimensional Lie subalgebra of 𝔰𝔬(8); random ``X`` in the 7-dimensional
orthogonal complement of its packed span typically drives closure to dimension 28. This matches
the intended “small subalgebra + one extra direction” stratification story.

**HQIV note:** ``HQVM.matrices.OctonionHQIVAlgebra.g2_basis`` filters 21 commutators and keeps the
first 14 **nonzero** in lex order — that list is **not** slot-aligned with Lean ``g2Generator``.
Use ``--mode lean_g2`` for the 14 commutator pairs matching ``Hqiv/GeneratorsFromAxioms`` /
``G2Embedding`` (same ``L(e_i)`` tables as ``Hqiv/OctonionLeftMultiplication.lean``).

Run:

  cd ~/Repos/HQIV_LEAN
  python3 scripts/classify_g2_so8_good_generators.py --mode lean_g2 --random-samples 40
  PYTHONPATH=~/Repos/HQIV python3 scripts/classify_g2_so8_good_generators.py --mode hqvm_g2
  python3 scripts/classify_g2_so8_good_generators.py --mode so7 --random-samples 60 --seed 1
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import numpy as np

_REPO_LEAN = Path(__file__).resolve().parent.parent
_REPO_HQIV = _REPO_LEAN.parent / "HQIV"
if _REPO_HQIV.exists():
    sys.path.insert(0, str(_REPO_HQIV))


def pack(M: np.ndarray) -> np.ndarray:
    return np.array([M[i, j] for i in range(8) for j in range(i + 1, 8)], dtype=np.float64)


def unpack(v: np.ndarray) -> np.ndarray:
    M = np.zeros((8, 8), dtype=np.float64)
    idx = 0
    for i in range(8):
        for j in range(i + 1, 8):
            M[i, j] = v[idx]
            M[j, i] = -v[idx]
            idx += 1
    return M


def comm(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    return A @ B - B @ A


def lie_closure_packed_dim(
    seed: list[np.ndarray],
    *,
    tol: float = 1e-10,
    max_rounds: int = 500,
) -> tuple[int, int]:
    """
    Saturate under matrix commutators; return (dim of packed linear span, number of matrices kept).
    """
    ms = [np.array(m, dtype=np.float64).copy() for m in seed]
    for _ in range(max_rounds):
        n = len(ms)
        if n == 0:
            return 0, 0
        V = np.stack([pack(m) for m in ms], axis=1)
        U, S, _ = np.linalg.svd(V, full_matrices=False)
        r = int(np.sum(S > tol))
        if r == 0:
            return 0, len(ms)
        Uo = U[:, :r]
        added = False
        for i in range(n):
            for j in range(i + 1, n):
                C = comm(ms[i], ms[j])
                if np.max(np.abs(C)) < tol:
                    continue
                v = pack(C)
                res = v - Uo @ (Uo.T @ v)
                if np.linalg.norm(res) > tol * max(1.0, np.linalg.norm(v)):
                    ms.append(C)
                    added = True
                    break
            if added:
                break
        if not added:
            break
    V = np.stack([pack(m) for m in ms], axis=1)
    dim = int(np.linalg.matrix_rank(V, tol=tol * 1e4))
    return dim, len(ms)


def complement_columns(packed_cols: np.ndarray, tol: float) -> np.ndarray:
    """Orthonormal complement of columns of packed_cols in ℝ²⁸ (full SVD)."""
    U, s, _ = np.linalg.svd(packed_cols, full_matrices=True)
    smax = float(s[0]) if s.size else 1.0
    rank = int(np.sum(s > max(tol, 1e-12 * smax)))
    return U[:, rank:]


def so7_generators() -> list[np.ndarray]:
    """Standard 𝔰𝔬(7) as bivectors on coordinates 0..6 (embedded in 8×8)."""
    mats: list[np.ndarray] = []
    for i in range(7):
        for j in range(i + 1, 7):
            M = np.zeros((8, 8), dtype=np.float64)
            M[i, j] = 1.0
            M[j, i] = -1.0
            mats.append(M)
    return mats


def so3_generators() -> list[np.ndarray]:
    mats: list[np.ndarray] = []
    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
        M = np.zeros((8, 8), dtype=np.float64)
        M[i, j] = 1.0
        M[j, i] = -1.0
        mats.append(M)
    return mats


def simple_bivector(i: int, j: int) -> np.ndarray:
    M = np.zeros((8, 8), dtype=np.float64)
    M[i, j] = -1.0
    M[j, i] = 1.0
    return M


# Same 7 tables as ``Hqiv/OctonionLeftMultiplication.lean`` / fixed ``HQVM/matrices.py``.
def octonion_L_numpy() -> list[np.ndarray]:
    L7 = np.array(
        [
            [0, 0, 0, 0, 0, 0, 0, -1],
            [0, 0, 0, 0, 0, 0, -1, 0],
            [0, 0, 0, 0, 0, -1, 0, 0],
            [0, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 1, 0, 0, 0, 0],
            [0, 0, 1, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0, 0, 0],
            [1, 0, 0, 0, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L1 = np.array(
        [
            [0, -1, 0, 0, 0, 0, 0, 0],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, -1],
            [0, 0, 0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, -1, 0, 0],
            [0, 0, 0, 0, 1, 0, 0, 0],
            [0, 0, 0, -1, 0, 0, 0, 0],
            [0, 0, 1, 0, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L2 = np.array(
        [
            [0, 0, -1, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, 1],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, -1, 0],
            [0, 0, 0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 1, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L3 = np.array(
        [
            [0, 0, 0, -1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, -1, 0, 0],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, -1],
            [0, 0, 1, 0, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L4 = np.array(
        [
            [0, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, 0, 0, 1],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 0, 0],
            [0, 0, -1, 0, 0, 0, 0, 0],
            [0, 0, 0, -1, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L5 = np.array(
        [
            [0, 0, 0, 0, 0, -1, 0, 0],
            [0, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 0, 0, 0, 0, -1],
            [0, 0, 0, 0, 0, 0, 1, 0],
            [0, 1, 0, 0, 0, 0, 0, 0],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, 0, 0, -1, 0, 0, 0, 0],
            [0, 0, 1, 0, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    L6 = np.array(
        [
            [0, 0, 0, 0, 0, 0, -1, 0],
            [0, 0, 0, 0, 0, 0, 0, 1],
            [0, 0, 0, 0, -1, 0, 0, 0],
            [0, 0, 0, 0, 0, -1, 0, 0],
            [0, 0, 1, 0, 0, 0, 0, 0],
            [0, 0, 0, 1, 0, 0, 0, 0],
            [1, 0, 0, 0, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0, 0, 0],
        ],
        dtype=np.float64,
    )
    return [L1, L2, L3, L4, L5, L6, L7]


# Lex order of (i,j) with i<j in 0..6 matching ``g2_comm_*`` in ``GeneratorsFromAxioms``.
LEAN_G2_PAIRS: tuple[tuple[int, int], ...] = (
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
)


def lean_g2_commutator_matrices() -> list[np.ndarray]:
    """All 14 matrices ``[L(e_{i+1}), L(e_{j+1})]`` in Lean ``g2_comm_*`` order (one pair is zero)."""
    L = octonion_L_numpy()
    return [comm(L[i], L[j]) for i, j in LEAN_G2_PAIRS]


def is_simple_plane_bivector(M: np.ndarray, *, tol: float = 1e-8) -> bool:
    """
    True if M is (numerically) a single-plane rotation generator: skew, rank 2, and M² is
    a negative rank-2 projector on that plane (e.g. HQIV ``Δ`` on (e₁,e₇)).
    """
    S = 0.5 * (M - M.T)
    if np.max(np.abs(S - M)) > tol * 1e3:
        return False
    r = int(np.linalg.matrix_rank(S, tol=max(tol, 1e-10)))
    if r != 2:
        return False
    T = S @ S
    rt = int(np.linalg.matrix_rank(T, tol=max(tol, 1e-9)))
    if rt != 2:
        return False
    eig = np.linalg.eigvalsh(T)
    if np.max(eig) > tol:
        return False
    return True


def delta_hqiv() -> np.ndarray:
    D = np.zeros((8, 8), dtype=np.float64)
    D[1, 7] = -1.0
    D[7, 1] = 1.0
    return D


def packed_residual_to_span(v: np.ndarray, cols: np.ndarray, *, tol: float) -> float:
    """‖v - G α‖₂ / ‖v‖₂ for least-squares α (diagnostic: Δ in linear span of packed columns)."""
    nv = float(np.linalg.norm(v))
    if nv < tol:
        return 0.0
    smax = float(np.linalg.norm(cols, ord=2)) or 1.0
    alpha, _, rank, _ = np.linalg.lstsq(cols, v, rcond=max(tol, 1e-14 * smax))
    if rank == 0:
        return 1.0
    res = v - cols @ alpha
    return float(np.linalg.norm(res) / nv)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lie-closure dimension scans: ⟨seed, X⟩ in packed 𝔰𝔬(8)."
    )
    parser.add_argument(
        "--mode",
        choices=("so7", "hqvm_g2", "lean_g2"),
        default="so7",
        help="so7: 𝔰𝔬(7)+X. lean_g2: Lean 14 commutator pairs + X (no PYTHONPATH). hqvm_g2: HQVM g2_basis + X.",
    )
    parser.add_argument("--random-samples", type=int, default=40)
    parser.add_argument("--seed", type=int, default=0, help="RNG seed.")
    parser.add_argument("--tol", type=float, default=1e-10)
    args = parser.parse_args()

    rows: list[tuple[str, int, int, str, str]] = []

    def record(name: str, seed: list[np.ndarray], note: str = "", simple: str = "-") -> None:
        dim, nmat = lie_closure_packed_dim(seed, tol=args.tol)
        rows.append((name, dim, nmat, note, simple))

    print("# Lie-closure packed dimension (antisymmetric 8×8 model)")
    print(f"# mode={args.mode}, tol={args.tol}, random_samples={args.random_samples}, rng_seed={args.seed}")
    print()

    # Sanity checks (always meaningful)
    record("control_so3_only", so3_generators(), "expect 3", "-")
    record("control_so7_only", so7_generators(), "expect 21", "-")

    rng = np.random.default_rng(args.seed)

    if args.mode == "so7":
        s7 = so7_generators()
        G = np.stack([pack(m) for m in s7], axis=1)
        W = complement_columns(G, args.tol)
        assert W.shape == (28, 7), W.shape

        try:
            from HQVM.matrices import OctonionHQIVAlgebra

            Delta = OctonionHQIVAlgebra(verbose=False).Delta
        except ImportError:
            Delta = delta_hqiv()

        record(
            "so7_plus_HQIV_Delta",
            s7 + [Delta],
            "phase-lift reference",
            "yes" if is_simple_plane_bivector(Delta, tol=args.tol) else "?",
        )
        record("so7_plus_zero", s7 + [np.zeros((8, 8))], "degenerate X", "-")

        for (i, j) in [(0, 7), (1, 7), (3, 7), (5, 7)]:
            B = simple_bivector(i, j)
            record(
                f"so7_plus_bivector_{i}_{j}",
                s7 + [B],
                "single extra plane",
                "yes" if is_simple_plane_bivector(B, tol=args.tol) else "no",
            )

        for k in range(W.shape[1]):
            Xk = unpack(W[:, k])
            record(
                f"so7_plus_W_axis_{k}",
                s7 + [Xk],
                "complement axis",
                "yes" if is_simple_plane_bivector(Xk, tol=args.tol) else "no",
            )

        for t in range(args.random_samples):
            c = rng.standard_normal(W.shape[1])
            c /= np.linalg.norm(c) + 1e-30
            Xt = unpack(W @ c)
            record(
                f"so7_plus_random_complement_{t}",
                s7 + [Xt],
                "",
                "yes" if is_simple_plane_bivector(Xt, tol=args.tol) else "no",
            )

    elif args.mode == "lean_g2":
        g2_all = lean_g2_commutator_matrices()
        g2_nz = [M for M in g2_all if np.max(np.abs(M)) > args.tol]
        G = np.stack([pack(m) for m in g2_all], axis=1)
        rlin = int(np.linalg.matrix_rank(G, tol=args.tol * 1e4))
        print(f"# lean_g2: 14 named commutators, packed linear rank = {rlin} (nonzero count = {len(g2_nz)})")
        d_g2, n_g2 = lie_closure_packed_dim(g2_nz, tol=args.tol)
        print(f"# Lie closure with lean nonzero commutators only: dim={d_g2}, #mats={n_g2}")
        Delta = delta_hqiv()
        res_d = packed_residual_to_span(pack(Delta), G, tol=args.tol)
        print(
            f"# ‖pack(Δ) − span(pack([L_i,L_j]))‖ / ‖pack(Δ)‖ ≈ {res_d:.4e} (≈0 ⇒ Δ in linear span of named seeds)"
        )
        print()

        W = complement_columns(G, args.tol)
        print(f"# complement W to span(14 packed seeds): shape {W.shape}")
        print()

        record("lean_g2_only_nonzero", g2_nz, "Lie saturate commutators only", "-")
        record(
            "lean_g2_plus_Delta",
            g2_nz + [Delta],
            "certificate-style seed",
            "yes" if is_simple_plane_bivector(Delta, tol=args.tol) else "?",
        )
        record("lean_g2_plus_zero", g2_nz + [np.zeros((8, 8))], "degenerate X", "-")

        for (i, j) in [(0, 7), (1, 7), (3, 7)]:
            B = simple_bivector(i, j)
            record(
                f"lean_g2_plus_bivector_{i}_{j}",
                g2_nz + [B],
                "extra plane",
                "yes" if is_simple_plane_bivector(B, tol=args.tol) else "no",
            )

        for k in range(min(W.shape[1], 7)):
            Xk = unpack(W[:, k])
            record(
                f"lean_g2_plus_W_axis_{k}",
                g2_nz + [Xk],
                "complement axis",
                "yes" if is_simple_plane_bivector(Xk, tol=args.tol) else "no",
            )

        for t in range(args.random_samples):
            c = rng.standard_normal(W.shape[1])
            c /= np.linalg.norm(c) + 1e-30
            Xt = unpack(W @ c)
            record(
                f"lean_g2_plus_random_W_{t}",
                g2_nz + [Xt],
                "",
                "yes" if is_simple_plane_bivector(Xt, tol=args.tol) else "no",
            )

    else:
        try:
            from HQVM.matrices import OctonionHQIVAlgebra
        except ImportError:
            print("ERROR: hqvm_g2 mode needs HQIV on PYTHONPATH.", file=sys.stderr)
            return 1
        alg = OctonionHQIVAlgebra(verbose=False)
        g2 = alg.g2_basis
        Delta = alg.Delta
        G = np.stack([pack(m) for m in g2], axis=1)
        print("# hqvm_g2_basis: packed column rank =", int(np.linalg.matrix_rank(G, tol=args.tol * 1e4)))
        d0, n0 = lie_closure_packed_dim([m.copy() for m in g2], tol=args.tol)
        print(f"# Lie closure dimension with **g2_basis only** (no X): dim={d0}, #mats={n0}")
        print(
            "# If dim=28, the 14 commutator seeds already Lie-saturate to full 𝔰𝔬(8) in this model;",
            "use --mode so7 for a proper proper-subalgebra stratification.",
        )
        print()
        W = complement_columns(G, args.tol)
        record(
            "hqvm_g2_plus_Delta",
            g2 + [Delta],
            "",
            "yes" if is_simple_plane_bivector(Delta, tol=args.tol) else "?",
        )
        record("hqvm_g2_plus_zero", g2 + [np.zeros((8, 8))], "", "-")
        for t in range(min(args.random_samples, 20)):
            c = rng.standard_normal(W.shape[1])
            c /= np.linalg.norm(c) + 1e-30
            Xt = unpack(W @ c)
            record(
                f"hqvm_g2_plus_random_W_{t}",
                g2 + [Xt],
                "",
                "yes" if is_simple_plane_bivector(Xt, tol=args.tol) else "no",
            )

    from collections import Counter

    cnt = Counter(r[1] for r in rows)
    print("# counts by dim:", dict(sorted(cnt.items())))
    print()
    print(f"{'name':<44} {'simple?':>8} {'dim':>4} {'#mats':>6}  note")
    for name, dim, nmat, note, simple in sorted(rows, key=lambda r: (r[1], r[0])):
        print(f"{name:<44} {simple:>8} {dim:4d} {nmat:6d}  {note}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
