#!/usr/bin/env python3
"""
Hopf + Δ shell lock-in from a discrete HQIV action — no smuggled referenceM spring.

Action (exploratory Python mirror of spine axioms):

  S = ∫ L(v, ṁ, m) dt

with

  L = T_carrier + T_shell + L_gauge + V_assoc + V_hopf + V_budget

Terms are fixed by spine definitions only:

  • φ(m) = 2(m+1)           — Shell.lean
  • phase lift φ(m)/6 on Δ  — PhaseLiftDelta.lean
  • N(m) = 8(m+1)           — LockIn.newModes
  • C = 40 = 28+8+4         — LockIn.sectorClosureCapacity
  • V_budget = (N(m)−C)²/(2C) — quadratic closure penalty; ∂V/∂m = −8·modeDeficit/C
  • 𝔤₂ seed + Δ on 𝕆 carrier — G₂∪{Δ}⇒𝔰𝔬(8) scaffold
  • Hopf fiber–base + associator — octonion nonlinearity (non-associativity axiom route)

Shell evolution: gradient flow ṁ = −∂V_budget/∂m (closure sector). The φ(m)/6
coupling enters the **carrier** generator only — same shell ladder, not a second
potential. No referenceM spring.

Run:
  python3 scripts/hqiv_hopf_delta_action.py
  python3 scripts/hqiv_hopf_delta_action.py --trials 300 --steps 800 --plot
"""

from __future__ import annotations

import argparse
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

# Spine pins (reporting / validation only for referenceM)
REFERENCE_M = 4
CARRIER = 8
SPACETIME = 4
SO8_DIM = 28
SECTOR_CLOSURE_CAPACITY = SO8_DIM + CARRIER + SPACETIME  # 40, LockIn.lean
ALPHA = 3.0 / 5.0
GAMMA_HQIV = 2.0 / 5.0


def new_modes(m: float) -> float:
    return float(CARRIER) * (m + 1.0)


def mode_deficit(m: float) -> float:
    return float(SECTOR_CLOSURE_CAPACITY) - new_modes(m)


def phi_shell(m: float) -> float:
    return 2.0 * (m + 1.0)


def phase_lift_coeff(m: float) -> float:
    return phi_shell(m) / 6.0


def hopf_fibration_shape(winding: int) -> float:
    return winding / (winding + 2.0)


# ---------------------------------------------------------------------------
# Octonion algebra (Lean tables)
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
    return gens, delta_matrix()


def left_mul_vec(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    Lp = [skew_part(L) for L in _L_tables()]
    out = x[0] * y
    for k in range(7):
        out = out + x[k + 1] * (Lp[k] @ y)
    return out


def associator(x: np.ndarray, y: np.ndarray, z: np.ndarray) -> np.ndarray:
    return left_mul_vec(left_mul_vec(x, y), z) - left_mul_vec(x, left_mul_vec(y, z))


def hopf_fiber_phase(v: np.ndarray) -> float:
    return math.atan2(v[7], v[1] + 1e-15)


# ---------------------------------------------------------------------------
# Lagrangian / potential terms
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ActionCoeffs:
    """All coefficients are spine ratios — no referenceM."""

    shell_mass: float = 1.0
    carrier_damping: float = 0.05
    shell_damping: float = 0.08
    assoc_weight: float = GAMMA_HQIV  # informational monogamy complement
    hopf_weight: float = ALPHA  # curvature imprint on fiber–base
    g2_weight: float = 1.0 / 14.0  # normalize by g2Dim
    winding: int = 3  # Hopf S³→S²; tuftHeavyChartShell = n+1 = 4 at lock-in chart


def V_budget(m: float) -> float:
    """Closure budget penalty: (N(m)−C)²/(2C). Zero iff N(m)=C (unique m=4)."""
    delta = new_modes(m) - float(SECTOR_CLOSURE_CAPACITY)
    return 0.5 * delta * delta / float(SECTOR_CLOSURE_CAPACITY)


def dV_budget_dm(m: float) -> float:
    """Analytic ∂V_budget/∂m = 8·(N(m)−C)/C = −8·modeDeficit/C."""
    return float(CARRIER) * (new_modes(m) - float(SECTOR_CLOSURE_CAPACITY)) / float(
        SECTOR_CLOSURE_CAPACITY
    )


def V_associator(v: np.ndarray, coeffs: ActionCoeffs) -> float:
    e1 = np.zeros(8)
    e1[1] = 1.0
    e7 = np.zeros(8)
    e7[7] = 1.0
    a = associator(v, e1, e7)
    return 0.5 * coeffs.assoc_weight * float(np.dot(a, a))


def V_hopf(v: np.ndarray, coeffs: ActionCoeffs) -> float:
    """Fiber–base mismatch: shape·|v|²·(1 − cos 2θ) in the Δ plane."""
    r2 = float(np.dot(v, v))
    theta = hopf_fiber_phase(v)
    shape = hopf_fibration_shape(coeffs.winding)
    return 0.5 * coeffs.hopf_weight * shape * r2 * (1.0 - math.cos(2.0 * theta))


def L_gauge_energy(v: np.ndarray, m: float, g2_gens: list[np.ndarray], delta: np.ndarray, coeffs: ActionCoeffs) -> float:
    """‖X(v,m) v‖²/2 with X = weighted 𝔤₂ + (φ/6)Δ."""
    weights = np.abs(v[1:8])
    wsum = float(np.sum(weights)) + 1e-12
    X = np.zeros((8, 8), dtype=np.float64)
    for w, G in zip(weights, g2_gens[: len(weights)]):
        X += coeffs.g2_weight * (w / wsum) * G
    X += phase_lift_coeff(m) * delta
    X = 0.5 * (X - X.T)
    Xv = X @ v
    return 0.5 * float(np.dot(Xv, Xv))


def dL_gauge_dm(v: np.ndarray, m: float, delta: np.ndarray) -> float:
    """∂/∂m [½‖(φ/6)Δ v‖²] = (φ/6)·(2/6)·⟨Δv,Δv⟩ = (φ/3)·‖Δv‖²/6 ..."""
    coeff = phase_lift_coeff(m)
    Dv = delta @ v
    # ∂/∂m (coeff²/2 · ‖Δv‖²) with coeff = (m+1)/3
    d_coeff = 2.0 / 6.0  # d(2(m+1)/6)/dm = 1/3 = 2/6
    return coeff * d_coeff * float(np.dot(Dv, Dv))


def lagrangian(
    v: np.ndarray,
    m: float,
    mdot: float,
    g2_gens: list[np.ndarray],
    delta: np.ndarray,
    coeffs: ActionCoeffs,
) -> float:
    T_shell = 0.5 * coeffs.shell_mass * mdot * mdot
    return (
        T_shell
        + L_gauge_energy(v, m, g2_gens, delta, coeffs)
        + V_associator(v, coeffs)
        + V_hopf(v, coeffs)
        + V_budget(m)
    )


def carrier_generator(
    v: np.ndarray,
    m: float,
    g2_gens: list[np.ndarray],
    delta: np.ndarray,
    coeffs: ActionCoeffs,
) -> np.ndarray:
    """Skew generator from δ(L_gauge + V_hopf + V_assoc)/δv (structure-preserving flow)."""
    weights = np.abs(v[1:8])
    wsum = float(np.sum(weights)) + 1e-12
    X = np.zeros((8, 8), dtype=np.float64)
    for w, G in zip(weights, g2_gens[: len(weights)]):
        X += coeffs.g2_weight * (w / wsum) * G
    X += phase_lift_coeff(m) * delta

    # Hopf torque in Δ plane
    r2 = float(np.dot(v, v))
    theta = hopf_fiber_phase(v)
    shape = hopf_fibration_shape(coeffs.winding)
    tau = np.zeros(8, dtype=np.float64)
    tau[1] = coeffs.hopf_weight * shape * r2 * math.sin(2.0 * theta)
    tau[7] = -coeffs.hopf_weight * shape * r2 * math.cos(2.0 * theta)
    T = np.outer(tau, v) - np.outer(v, tau)
    X += 0.5 * T

    # Associator gradient proxy
    e1 = np.zeros(8)
    e1[1] = 1.0
    e7 = np.zeros(8)
    e7[7] = 1.0
    assoc = associator(v, e1, e7)
    A = np.outer(assoc, v) - np.outer(v, assoc)
    X += coeffs.assoc_weight * 0.5 * A

    return 0.5 * (X - X.T)


def shell_potential_dm(v: np.ndarray, m: float, delta: np.ndarray, *, closure_only: bool) -> float:
    """
    Shell-sector gradient.

    ``closure_only=True`` (default): only ``∂V_budget/∂m``. The ``φ(m)/6`` factor
    already belongs to the same shell ladder as ``N(m)=8(m+1)``; it parametrizes the
    carrier generator but is not a second copy of shell energy (avoids double-counting).
    """
    if closure_only:
        return dV_budget_dm(m)
    return dV_budget_dm(m) + dL_gauge_dm(v, m, delta)



def project_tangent(v: np.ndarray, dv: np.ndarray) -> np.ndarray:
    return dv - float(np.dot(dv, v)) * v


@dataclass
class TrajectorySummary:
    m0: float
    m_final: float
    mdot_final: float
    settled_near_lockin: bool
    V_budget_final: float
    mean_V_budget: float
    hopf_phase_range: float


def evolve_action(
    v0: np.ndarray,
    m0: float,
    g2_gens: list[np.ndarray],
    delta: np.ndarray,
    coeffs: ActionCoeffs,
    *,
    steps: int,
    dt: float,
    first_order: bool,
    closure_only_shell: bool,
) -> TrajectorySummary:
    v = v0.astype(np.float64).copy()
    nrm = np.linalg.norm(v)
    if nrm > 0:
        v /= nrm
    m = float(m0)
    mdot = 0.0
    phases: list[float] = []
    v_budgets: list[float] = []

    for _ in range(steps):
        X = carrier_generator(v, m, g2_gens, delta, coeffs)
        dv = X @ v
        dv = project_tangent(v, dv)
        v = v + dt * dv
        nrm = np.linalg.norm(v)
        if nrm > 0:
            v /= nrm
        v = v * (1.0 - coeffs.carrier_damping * dt)  # light dissipation on S⁷
        nrm = np.linalg.norm(v)
        if nrm > 0:
            v /= nrm

        if first_order:
            d_pot = shell_potential_dm(v, m, delta, closure_only=closure_only_shell)
            mdot = -d_pot / max(coeffs.shell_mass, 1e-12)
            m = m + dt * mdot
        else:
            d_pot = shell_potential_dm(v, m, delta, closure_only=closure_only_shell)
            mddot = (-d_pot - coeffs.shell_damping * mdot) / coeffs.shell_mass
            mdot = mdot + dt * mddot
            m = m + dt * mdot
        m = max(0.0, min(m, 12.0))

        phases.append(hopf_fiber_phase(v))
        v_budgets.append(V_budget(m))

    settled = abs(m - REFERENCE_M) < 0.35
    return TrajectorySummary(
        m0=m0,
        m_final=m,
        mdot_final=mdot,
        settled_near_lockin=settled,
        V_budget_final=V_budget(m),
        mean_V_budget=float(np.mean(v_budgets)) if v_budgets else V_budget(m),
        hopf_phase_range=(max(phases) - min(phases)) if phases else 0.0,
    )


def verify_el_budget() -> None:
    """Finite-difference check: ∂V_budget/∂m matches analytic."""
    for m in np.linspace(0.0, 8.0, 17):
        h = 1e-5
        fd = (V_budget(m + h) - V_budget(m - h)) / (2.0 * h)
        an = dV_budget_dm(m)
        if abs(fd - an) > 1e-4:
            raise AssertionError(f"EL mismatch at m={m}: fd={fd} an={an}")
    print("# EL check: ∂V_budget/∂m finite-diff OK")


def print_action_spec(coeffs: ActionCoeffs) -> None:
    print("HQIV Hopf+Δ action (variational shell lock-in)")
    print()
    print("L = T_shell + L_gauge + V_assoc + V_hopf + V_budget")
    print()
    print(f"  N(m) = {CARRIER}(m+1)          [LockIn.newModes]")
    print(f"  C    = {SO8_DIM}+{CARRIER}+{SPACETIME} = {SECTOR_CLOSURE_CAPACITY}  [sectorClosureCapacity]")
    print(f"  V_budget = (N(m)−C)²/(2C)     zero ⟺ N(m)=C ⟺ m={REFERENCE_M} [derived]")
    print(f"  φ(m)/6 on Δ                   [PhaseLiftDelta]")
    print(f"  Hopf shape n/(n+2), n={coeffs.winding}  [fiber–base nonlinearity]")
    print(f"  associator weight γ={coeffs.assoc_weight:.2f}   [monogamy complement]")
    print()
    print("mode_deficit ladder (validation):")
    for mi in range(8):
        print(f"  m={mi}  N={int(new_modes(mi)):3d}  deficit={int(mode_deficit(mi)):+4d}  V={V_budget(mi):.2f}")
    print()


def random_unit_octonion(rng: random.Random) -> np.ndarray:
    x = np.array([rng.gauss(0, 1) for _ in range(8)], dtype=np.float64)
    x /= np.linalg.norm(x) + 1e-15
    return x


def run_ensemble(args: argparse.Namespace) -> list[TrajectorySummary]:
    coeffs = ActionCoeffs(
        shell_mass=args.shell_mass,
        carrier_damping=args.carrier_damping,
        shell_damping=args.shell_damping,
        assoc_weight=args.assoc_weight,
        hopf_weight=args.hopf_weight,
        winding=args.winding,
    )
    g2, delta = build_g2_delta_basis()
    print_action_spec(coeffs)
    verify_el_budget()
    print(f"𝔤₂ generators: {len(g2)}")
    print()

    rng = random.Random(args.seed)
    out: list[TrajectorySummary] = []
    for _ in range(args.trials):
        v0 = random_unit_octonion(rng)
        m0 = rng.uniform(0.0, float(args.m_max))
        out.append(
            evolve_action(
                v0,
                m0,
                g2,
                delta,
                coeffs,
                steps=args.steps,
                dt=args.dt,
                first_order=not args.second_order,
                closure_only_shell=not args.full_shell_potential,
            )
        )
    return out


def summarize(results: list[TrajectorySummary], *, steps: int) -> None:
    n = len(results)
    near = sum(1 for r in results if r.settled_near_lockin)
    finals = [r.m_final for r in results]
    mean_m = sum(finals) / n
    var_m = sum((x - mean_m) ** 2 for x in finals) / max(1, n - 1)
    hist: dict[int, int] = {}
    for r in results:
        b = int(round(r.m_final))
        hist[b] = hist.get(b, 0) + 1

    print(f"trials: {n}  (no referenceM spring — pure action EL)")
    print(f"settled near m={REFERENCE_M} (|m−4|<0.35): {near}/{n} ({100*near/n:.1f}%)")
    print(f"mean m_final = {mean_m:.3f}  std = {math.sqrt(var_m):.3f}")
    print(f"mean V_budget final = {sum(r.V_budget_final for r in results)/n:.4f}")
    print()
    print("histogram round(m_final):")
    for m in sorted(hist):
        bar = "#" * int(40 * hist[m] / n)
        mark = "  <-- unique N(m)=C zero" if m == REFERENCE_M else ""
        print(f"  m={m:2d}  {hist[m]:4d}  {bar}{mark}")
    print()

    g2, delta = build_g2_delta_basis()
    v_fix = np.zeros(8)
    v_fix[1] = 1.0
    v_fix[7] = 1.0
    v_fix /= np.linalg.norm(v_fix)
    coeffs = ActionCoeffs()
    print("m0 sweep (v = (e₁+e₇)/√2):")
    for m0 in range(0, 8):
        r = evolve_action(
            v_fix,
            float(m0),
            g2,
            delta,
            coeffs,
            steps=steps,
            dt=0.02,
            first_order=True,
            closure_only_shell=True,
        )
        print(
            f"  m0={m0} -> m={r.m_final:5.2f}  "
            f"V_budget={r.V_budget_final:7.4f}  "
            f"mdot={r.mdot_final:+.4f}  "
            f"Δθ={r.hopf_phase_range:.2f}"
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
    axes[0].hist(finals, bins=32, color="#2d6a4f", edgecolor="white")
    axes[0].axvline(REFERENCE_M, color="#cc3333", ls="--", label=f"N(m)=C at m={REFERENCE_M}")
    axes[0].set_xlabel("m_final")
    axes[0].set_ylabel("count")
    axes[0].legend()
    axes[0].set_title("Action EL: final shell")

    axes[1].scatter(m0s, finals, s=8, alpha=0.5, c="#2d6a4f")
    axes[1].axhline(REFERENCE_M, color="#cc3333", ls="--")
    axes[1].set_xlabel("m0")
    axes[1].set_ylabel("m_final")
    axes[1].set_title("Basin from V_budget + Hopf+Δ")
    fig.tight_layout()
    fig.savefig(path, dpi=120)
    print(f"wrote {path}")


def main() -> int:
    p = argparse.ArgumentParser(description="Variational Hopf+Δ shell lock-in from HQIV action")
    p.add_argument("--trials", type=int, default=300)
    p.add_argument("--steps", type=int, default=600)
    p.add_argument("--dt", type=float, default=0.02)
    p.add_argument("--m-max", type=int, default=7)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--shell-mass", type=float, default=1.0)
    p.add_argument("--shell-damping", type=float, default=0.08)
    p.add_argument("--carrier-damping", type=float, default=0.05)
    p.add_argument("--assoc-weight", type=float, default=GAMMA_HQIV)
    p.add_argument("--hopf-weight", type=float, default=ALPHA)
    p.add_argument("--winding", type=int, default=3)
    p.add_argument("--second-order", action="store_true", help="inertial shell (default: gradient flow)")
    p.add_argument(
        "--full-shell-potential",
        action="store_true",
        help="add ∂L_gauge/∂m to shell flow (double-counts φ ladder; demo only)",
    )
    p.add_argument("--plot", action="store_true")
    p.add_argument("--plot-path", type=Path, default=Path("scripts/out/hopf_delta_action.png"))
    args = p.parse_args()

    results = run_ensemble(args)
    summarize(results, steps=args.steps)

    if args.plot:
        args.plot_path.parent.mkdir(parents=True, exist_ok=True)
        maybe_plot(results, args.plot_path)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
