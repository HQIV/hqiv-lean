#!/usr/bin/env python3
"""
Hopf + Δ + left-mul dynamics on the 𝕆 carrier — does the flow land on shell 4?

Hypothesis (exploratory, not Lean):
  • Linear left multiplication alone is norm-preserving and too flat for a lock-in.
  • Hopf fiber–base coupling + phase-lift Δ on the (e₁,e₇) weak plane inject nonlinearity.
  • The discrete mode deficit ``C − N(m)`` with ``C=40``, ``N(m)=8(m+1)`` pulls the shell
    index toward ``referenceM=4`` where the sector closes (``LockIn.lean``).

This script evolves coupled (v, m) with:
  • skew generators from 𝔤₂ commutators ``[L′ᵢ,L′ⱼ]`` + ``Δ`` (14+1 seed → so(8) closure);
  • Hopf-style fiber phase on the (e₁,e₇) plane (Δ plane);
  • shell restoring drive ``−γ·mode_deficit(m)``;
  • optional associator torque from ``(xy)z − x(yz)`` in the left-regular 8×8 representation.

Run:
  cd ~/Repos/HQIV_LEAN
  python3 scripts/hqiv_hopf_delta_shell4_probe.py
  python3 scripts/hqiv_hopf_delta_shell4_probe.py --trials 500 --steps 400 --plot
"""

from __future__ import annotations

import argparse
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

# Lean-aligned pins
REFERENCE_M = 4
SECTOR_CLOSURE_CAPACITY = 40  # dim so(8) + carrier + base = 28+8+4
ALPHA = 3.0 / 5.0
GAMMA_HQIV = 2.0 / 5.0


def new_modes(m: int) -> int:
    return 8 * (m + 1)


def mode_deficit_continuous(m: float) -> float:
    """Real shell coordinate: C − N(m) with N(m)=8(m+1). Zero only at m=referenceM."""
    return float(SECTOR_CLOSURE_CAPACITY) - 8.0 * (m + 1.0)


def mode_deficit(m: int) -> int:
    return SECTOR_CLOSURE_CAPACITY - new_modes(m)


def phi_shell(m: float) -> float:
    return 2.0 * (m + 1.0)


def phase_lift_coeff(m: float) -> float:
    return phi_shell(m) / 6.0


def hopf_fibration_shape(winding: int) -> float:
    return winding / (winding + 2.0)


# ---------------------------------------------------------------------------
# Octonion left-mul tables (match Hqiv/OctonionLeftMultiplication.lean)
# ---------------------------------------------------------------------------


def _L_tables() -> list[np.ndarray]:
    raw = [
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
    ]
    return [np.array(t, dtype=np.float64) for t in raw]


def skew_part(M: np.ndarray) -> np.ndarray:
    return 0.5 * (M - M.T)


def delta_matrix() -> np.ndarray:
    D = np.zeros((8, 8), dtype=np.float64)
    D[1, 7] = -1.0
    D[7, 1] = 1.0
    return D


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


def build_g2_delta_basis() -> tuple[list[np.ndarray], np.ndarray]:
    Lp = [skew_part(L) for L in _L_tables()]
    gens: list[np.ndarray] = []
    for i, j in LEAN_G2_PAIRS:
        C = Lp[i] @ Lp[j] - Lp[j] @ Lp[i]
        if np.max(np.abs(C)) > 1e-12:
            gens.append(C)
    D = delta_matrix()
    return gens, D


def left_mul_matrix(x: np.ndarray) -> np.ndarray:
    """L(x) for octonion components x."""
    Lp = [skew_part(L) for L in _L_tables()]
    M = x[0] * np.eye(8)
    for k in range(7):
        M = M + x[k + 1] * Lp[k]
    return M


def left_mul_vec(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    return left_mul_matrix(x) @ y


def associator(x: np.ndarray, y: np.ndarray, z: np.ndarray) -> np.ndarray:
    return left_mul_vec(left_mul_vec(x, y), z) - left_mul_vec(x, left_mul_vec(y, z))


# ---------------------------------------------------------------------------
# Hopf coordinates on the carrier (fiber S⁷ / weak plane S¹ ⊂ S⁷)
# ---------------------------------------------------------------------------


def hopf_fiber_phase(v: np.ndarray) -> float:
    """Phase in the Δ plane (e₁,e₇)."""
    return math.atan2(v[7], v[1] + 1e-15)


def fiber_imag_norm(v: np.ndarray) -> float:
    return float(np.linalg.norm(v[1:]))


def base_energy(v: np.ndarray) -> float:
    return float(np.dot(v, v))


def hopf_coupling_torque(v: np.ndarray, winding: int) -> np.ndarray:
    """
    Nonlinear Hopf torque: fiber phase gradient × base intensity × hopf shape.
    Returns an ℝ⁸ pseudo-force (not necessarily skew — contracted into generator field).
    """
    r2 = base_energy(v)
    theta = hopf_fiber_phase(v)
    shape = hopf_fibration_shape(winding)
    # Fiber–base cross drive in imaginary slots
    torque = np.zeros(8, dtype=np.float64)
    torque[1] = shape * r2 * math.sin(theta)
    torque[7] = -shape * r2 * math.cos(theta)
    # Spread to other imaginaries via smallest Fano hop (e₁,e₂,e₃ cycle proxy)
    torque[2] = 0.25 * shape * r2 * math.sin(2.0 * theta)
    torque[3] = -0.25 * shape * r2 * math.cos(2.0 * theta)
    return torque


def generator_field(
    v: np.ndarray,
    m: float,
    g2_gens: list[np.ndarray],
    delta: np.ndarray,
    *,
    winding: int,
    associator_gain: float,
) -> np.ndarray:
    """
    Skew operator X(v,m) ∈ so(8) assembled from 𝔤₂ directions weighted by v,
    plus Δ with phase-lift coefficient, plus Hopf torque projected into so(8).
    """
    weights = np.abs(v[1:8])
    wsum = float(np.sum(weights)) + 1e-12
    X = np.zeros((8, 8), dtype=np.float64)
    for w, G in zip(weights, g2_gens[: len(weights)]):
        X += (w / wsum) * G
    coeff = phase_lift_coeff(m)
    X += coeff * delta

    # Hopf nonlinear torque → skew projection
    tau = hopf_coupling_torque(v, winding)
    T = np.outer(tau, v) - np.outer(v, tau)
    X += 0.5 * hopf_fibration_shape(winding) * T

    if associator_gain > 0.0:
        e1 = np.zeros(8)
        e1[1] = 1.0
        e7 = np.zeros(8)
        e7[7] = 1.0
        assoc = associator(v, e1, e7)
        A = np.outer(assoc, v) - np.outer(v, assoc)
        X += associator_gain * 0.5 * A

    return 0.5 * (X - X.T)


def lie_closure_dim_from_state(
    v: np.ndarray, g2_gens: list[np.ndarray], delta: np.ndarray, tol: float = 1e-8
) -> int:
    """Packed rank of {weighted g2, Δ, [g2,Δ]} — proxy for active algebra dimension."""
    mats = [delta]
    w = np.abs(v[1:8])
    for wi, G in zip(w, g2_gens):
        if wi > 1e-6:
            mats.append(wi * G)
    if len(mats) < 2:
        mats.append(g2_gens[0])
    vecs = []
    for M in mats:
        for i in range(8):
            for j in range(i + 1, 8):
                vecs.append(M[i, j])
    V = np.array(vecs, dtype=np.float64).reshape(len(mats), -1).T
    return int(np.linalg.matrix_rank(V, tol=tol))


@dataclass
class TrajectorySummary:
    m0: float
    m_final: float
    m_min: float
    m_max: float
    crossed_lockin: bool
    settled_near_lockin: bool
    mean_deficit_abs: float
    closure_dim_mean: float
    hopf_phase_range: float


def evolve(
    v0: np.ndarray,
    m0: float,
    g2_gens: list[np.ndarray],
    delta: np.ndarray,
    *,
    steps: int,
    dt: float,
    shell_gain: float,
    winding: int,
    associator_gain: float,
    spring: float = 0.0,
) -> TrajectorySummary:
    v = v0.astype(np.float64).copy()
    nrm = np.linalg.norm(v)
    if nrm > 0:
        v /= nrm
    m = float(m0)
    phases: list[float] = []
    deficits: list[float] = []
    closure_dims: list[float] = []

    for _ in range(steps):
        X = generator_field(
            v,
            m,
            g2_gens,
            delta,
            winding=winding,
            associator_gain=associator_gain,
        )
        dv = X @ v
        v = v + dt * dv
        nrm = np.linalg.norm(v)
        if nrm > 0:
            v /= nrm

        deficit = mode_deficit_continuous(m)
        # Positive deficit below lock-in → expand shell; negative above → contract.
        dm = shell_gain * deficit / SECTOR_CLOSURE_CAPACITY
        # Optional weak pinning (set --spring 0 to use pure deficit drive)
        dm -= spring * shell_gain * (m - REFERENCE_M)
        # Hopf winding nudges shell when fiber phase wraps (small)
        phases.append(hopf_fiber_phase(v))
        if len(phases) >= 2:
            dphi = phases[-1] - phases[-2]
            if dphi > math.pi:
                dphi -= 2 * math.pi
            if dphi < -math.pi:
                dphi += 2 * math.pi
            dm += 0.02 * hopf_fibration_shape(winding) * dphi

        m = m + dt * dm
        m = max(0.0, min(m, 12.0))  # cap runaway for probe
        deficits.append(abs(mode_deficit_continuous(m)))
        closure_dims.append(float(lie_closure_dim_from_state(v, g2_gens, delta)))

    m_hist = [m]
    # record not stored per-step m history for speed; re-derive spread from m0, m_final
    settled = abs(m - REFERENCE_M) < 0.35
    return TrajectorySummary(
        m0=m0,
        m_final=m,
        m_min=min(m0, m),
        m_max=max(m0, m),
        crossed_lockin=(m0 - REFERENCE_M) * (m - REFERENCE_M) <= 0.0,
        settled_near_lockin=settled,
        mean_deficit_abs=float(np.mean(deficits)) if deficits else abs(mode_deficit_continuous(m)),
        closure_dim_mean=float(np.mean(closure_dims)) if closure_dims else 0.0,
        hopf_phase_range=(max(phases) - min(phases)) if phases else 0.0,
    )


def random_unit_octonion(rng: random.Random) -> np.ndarray:
    x = np.array([rng.gauss(0, 1) for _ in range(8)], dtype=np.float64)
    x /= np.linalg.norm(x) + 1e-15
    return x


def run_ensemble(args: argparse.Namespace) -> list[TrajectorySummary]:
    g2, delta = build_g2_delta_basis()
    print(f"# 𝔤₂ seed generators: {len(g2)}  (Lean 14-pair commutators)")
    print(f"# Δ antisymmetric check max|D+Dᵀ| = {np.max(np.abs(delta + delta.T)):.2e}")
    sat_rank = lie_closure_dim_from_state(
        np.array([0, 1, 0, 0, 0, 0, 0, 1], dtype=np.float64) / math.sqrt(2),
        g2,
        delta,
    )
    print(f"# Active-dim proxy at e₁+e₇ state: {sat_rank}")
    print()
    print("mode_deficit ladder:")
    for m in range(8):
        print(f"  m={m}  N(m)={new_modes(m):3d}  deficit={mode_deficit(m):+4d}")
    print()

    rng = random.Random(args.seed)
    out: list[TrajectorySummary] = []
    for t in range(args.trials):
        v0 = random_unit_octonion(rng)
        m0 = rng.uniform(0.0, float(args.m_max))
        out.append(
            evolve(
                v0,
                m0,
                g2,
                delta,
                steps=args.steps,
                dt=args.dt,
                shell_gain=args.shell_gain,
                winding=args.winding,
                associator_gain=args.assoc_gain,
                spring=args.spring,
            )
        )
    return out


def summarize(results: list[TrajectorySummary], *, spring: float, steps: int) -> None:
    n = len(results)
    near = sum(1 for r in results if r.settled_near_lockin)
    crossed = sum(1 for r in results if r.crossed_lockin)
    finals = [r.m_final for r in results]
    mean_m = sum(finals) / n
    var_m = sum((x - mean_m) ** 2 for x in finals) / max(1, n - 1)
    hist: dict[int, int] = {}
    for r in results:
        b = int(round(r.m_final))
        hist[b] = hist.get(b, 0) + 1

    print(f"spring toward m={REFERENCE_M}: {spring}")
    print(f"trials: {n}")
    print(f"settled near m={REFERENCE_M} (|m−4|<0.35): {near}/{n} ({100*near/n:.1f}%)")
    print(f"crossed lock-in shell during run: {crossed}/{n} ({100*crossed/n:.1f}%)")
    print(f"mean m_final = {mean_m:.3f}  std = {math.sqrt(var_m):.3f}")
    print(f"mean |mode_deficit| = {sum(r.mean_deficit_abs for r in results)/n:.2f}")
    print(f"mean closure-dim proxy = {sum(r.closure_dim_mean for r in results)/n:.1f}")
    print()
    print("histogram round(m_final):")
    for m in sorted(hist):
        bar = "#" * int(40 * hist[m] / n)
        mark = "  <-- referenceM" if m == REFERENCE_M else ""
        print(f"  m={m:2d}  {hist[m]:4d}  {bar}{mark}")
    print()

    # deterministic grid along m0
    print("m0 sweep (fixed v = e₁+e₇ normalized):")
    g2, delta = build_g2_delta_basis()
    v_fix = np.zeros(8)
    v_fix[1] = 1.0
    v_fix[7] = 1.0
    v_fix /= np.linalg.norm(v_fix)
    for m0 in range(0, 8):
        r = evolve(
            v_fix,
            float(m0),
            g2,
            delta,
            steps=steps,
            dt=0.02,
            shell_gain=1.0,
            winding=1,
            associator_gain=0.15,
            spring=spring,
        )
        print(
            f"  m0={m0} -> m_final={r.m_final:5.2f}  "
            f"deficit_mean={r.mean_deficit_abs:5.1f}  "
            f"closure_dim~{r.closure_dim_mean:4.1f}  "
            f"Δθ_range={r.hopf_phase_range:.2f}"
        )


def maybe_plot(results: list[TrajectorySummary], path: Path) -> None:
    try:
        import matplotlib.pyplot as plt
    except ImportError:
        print("matplotlib not installed; skip --plot", file=sys.stderr)
        return

    finals = [r.m_final for r in results]
    m0s = [r.m0 for r in results]
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    axes[0].hist(finals, bins=32, color="#336699", edgecolor="white")
    axes[0].axvline(REFERENCE_M, color="#cc3333", ls="--", label=f"referenceM={REFERENCE_M}")
    axes[0].set_xlabel("m_final")
    axes[0].set_ylabel("count")
    axes[0].legend()
    axes[0].set_title("Final shell index")

    axes[1].scatter(m0s, finals, s=8, alpha=0.5, c="#336699")
    axes[1].plot([0, 7], [0, 7], "k:", alpha=0.3)
    axes[1].axhline(REFERENCE_M, color="#cc3333", ls="--")
    axes[1].axvline(REFERENCE_M, color="#cc3333", ls="--", alpha=0.4)
    axes[1].set_xlabel("m0")
    axes[1].set_ylabel("m_final")
    axes[1].set_title("Basin map")
    fig.tight_layout()
    fig.savefig(path, dpi=120)
    print(f"wrote {path}")


def main() -> int:
    p = argparse.ArgumentParser(description="Hopf+Δ shell-4 attraction probe")
    p.add_argument("--trials", type=int, default=300)
    p.add_argument("--steps", type=int, default=500)
    p.add_argument("--dt", type=float, default=0.02)
    p.add_argument("--shell-gain", type=float, default=1.0, dest="shell_gain")
    p.add_argument("--winding", type=int, default=1)
    p.add_argument("--assoc-gain", type=float, default=0.15, dest="assoc_gain")
    p.add_argument("--m-max", type=int, default=7)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--spring", type=float, default=0.0, help="optional pinning toward referenceM")
    p.add_argument("--plot", action="store_true")
    p.add_argument("--plot-path", type=Path, default=Path("scripts/out/hopf_delta_shell4_probe.png"))
    args = p.parse_args()

    print("HQIV Hopf + Δ + left-mul shell-4 probe")
    print(f"referenceM={REFERENCE_M}  capacity={SECTOR_CLOSURE_CAPACITY}")
    print(
        f"trials={args.trials} steps={args.steps} dt={args.dt} "
        f"shell_gain={args.shell_gain} winding={args.winding} assoc={args.assoc_gain} spring={args.spring}"
    )
    print()

    results = run_ensemble(args)
    summarize(results, spring=args.spring, steps=args.steps)

    if args.plot:
        args.plot_path.parent.mkdir(parents=True, exist_ok=True)
        maybe_plot(results, args.plot_path)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
