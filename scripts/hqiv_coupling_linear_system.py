#!/usr/bin/env python3
"""
HQIV Fano coupling linear system (horizon-first).

Unknowns: c_v for v = 0..6 (Fano O–Maxwell normalization per imaginary vertex).

Closed structural equations (Lean-aligned):
  • O–Maxwell: 1/α_v = 42·(1 + c_v·(3/5)·ln(φ(m_v)+1))
  • Fano line incidence (7 lines, PG(2,2))
  • Holonomy quarter-turn budget: (π/2)·k_v·c_v shares one 2π phase per shell step
    (Conservations / ComptonHorizonPhase: horizonQuarterPeriod = 2π/4, full turn 2π)
  • Exactly one PDG/CODATA scale setter in the solve; success = all other readouts agree.

Target inverse coupling: CODATA 1/α ≈ 137.036 (not the paper 127.9 witness).

Run:
  python3 scripts/hqiv_coupling_linear_system.py --coherence
  python3 scripts/hqiv_coupling_linear_system.py --coherence --continuous-xi
  python3 scripts/hqiv_coupling_linear_system.py --coherence --continuous-xi --compare-holonomy
  python3 scripts/hqiv_coupling_linear_system.py --half-step-scan
  python3 scripts/hqiv_coupling_linear_system.py --coherence --continuous-xi --mass-row
  python3 scripts/hqiv_coupling_linear_system.py --coherence --continuous-xi --mass-row --mass-row-kind informational
  python3 scripts/hqiv_coupling_linear_system.py --coherence --continuous-xi --mixing-rows
  python3 scripts/hqiv_coupling_linear_system.py --plot-xi-residual
  python3 scripts/hqiv_sm_constants_explorer.py --continuous-xi --mixing-rows
  python3 scripts/hqiv_coupling_linear_system.py --json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

import numpy as np

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import cubic_phase_relax_probe as cpr  # noqa: E402
import hqiv_scale_witness as sw  # noqa: E402
import hqiv_shell_shape_geometry as ssg  # noqa: E402

# ---------------------------------------------------------------------------
# Lean mirrors

ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
C_RINDLER = cpr.C_RINDLER_SHARED
INV_ALPHA_GUT = 42.0
PHI_COEFF = cpr.PHI_TEMPERATURE_COEFF
REFERENCE_M = cpr.REFERENCE_M
EM_GAUSS_SHELL = REFERENCE_M - 1
EW_PHI_SHELL = REFERENCE_M + 1
# Continuous horizon coordinate ξ = m+1 = φ/2 (Lean curvatureDensity / shell_shape)
XI_EW = float(EW_PHI_SHELL + 1)
XI_GAUSS_INTEGER = float(EM_GAUSS_SHELL + 1)
XI_LOCKIN = float(REFERENCE_M + 1)  # Lean: omega_k_partial referenceM = 1 at ξ_lock
XI_G_BRACE_DEFAULT = 3.4743752754774695  # brace @ c=1, ξ_EW=6 → CODATA (geometry probe)
XI_HALF_STEP = 3.5

FANO_LINES: tuple[frozenset[int], ...] = (
    frozenset({0, 1, 2}),
    frozenset({0, 3, 4}),
    frozenset({0, 5, 6}),
    frozenset({1, 3, 5}),
    frozenset({1, 4, 6}),
    frozenset({2, 3, 6}),
    frozenset({2, 4, 5}),
)

VERTEX_NAMES = (
    "EM/lepton (0)",
    "up g0 (1)",
    "up g1 (2)",
    "up g2 (3)",
    "down g0 (4)",
    "down g1 (5)",
    "down/Higgs (6)",
)

CODATA_INV_ALPHA = 137.035999177
PAPER_INV_ALPHA = 127.9  # legacy witness only; CODATA is the physical target
# PDG comparison only (not used as solve inputs when mixing rows are geometric)
PDG_SIN2_THETA_W = 0.23122
PDG_ALPHA_S_MZ = 0.1180

TRIALITY_ORDER = 3
FANO_LINE_EM_UP = 0
FANO_LINE_WEAK = 1
FANO_LINE_SCALAR = 2

TWO_PI = 2.0 * math.pi
HORIZON_QUARTER = TWO_PI / 4.0  # horizonQuarterPeriod = π/2

ShellChart = Literal["uniform", "residue", "lockin", "sector"]
RhsMode = Literal["bare_gut", "spectral_detuning", "anchor_em", "anchor_em_line0"]
SystemKind = Literal[
    "vertex_diagonal",
    "line_incidence",
    "line_incidence_monogamy",
    "line_plus_holonomy",
    "holonomy_only",
]
ScaleSetter = Literal[
    "codata_vertex0_gauss",  # v=0, m=referenceM-1
    "codata_vertex0_ew",  # v=0, m=referenceM+1
    "codata_line0",  # Fano line 0 (vertices 0,1,2) average coupling
    "codata_weighted_mean",  # Σ w_v 1/α_v = CODATA
    "codata_triality_vector",  # rep 8v slot v=0 only, same as gauss
]
HolonomyKMode = Literal["log_phi", "sigma", "phase", "log_phi_xi"]
HolonomyXiMode = Literal["sector", "global"]
MassRowKind = Literal["omega_k", "informational"]
ScaleWitness = sw.ScaleWitness


def phi_of_shell(m: int) -> float:
    return PHI_COEFF * float(m + 1)


def log_phi_slot(m: int) -> float:
    return ALPHA * math.log(phi_of_shell(m) + 1.0)


def log_phi_slot_xi(xi: float) -> float:
    """α ln(φ+1) with φ = 2ξ — Lean Action L_O_phi_coupling / AuxiliaryField."""
    return ALPHA * math.log(2.0 * xi + 1.0)


def shell_shape_at_xi(xi: float) -> float:
    return ssg.shell_shape_at_xi(xi)


def sigma_ratio(xi_g: float, xi_ew: float = XI_EW) -> float:
    return shell_shape_at_xi(xi_g) / shell_shape_at_xi(xi_ew)


def omega_k_at_xi(xi: float, xi_lock: float = XI_LOCKIN) -> float:
    """Ω_k(ξ) = I(ξ)/I(ξ_lock); Lean omega_k_at_horizon / omega_k_partial calibration."""
    return ssg.omega_k_continuous(xi, xi_lock)


def curvature_integral_discrete(n: int) -> float:
    """Lean curvature_integral n = Σ_{m<n} shell_shape(m)."""
    return sum(cpr.shell_shape(m) for m in range(n))


def one_over_alpha_eff_xi(xi: float, c: float) -> float:
    return INV_ALPHA_GUT * (1.0 + c * log_phi_slot_xi(xi))


def rindler_1jet(m: int) -> float:
    return 1.0 + C_RINDLER * float(m)


def one_over_alpha_eff(m: int, c: float) -> float:
    return INV_ALPHA_GUT * (1.0 + c * log_phi_slot(m))


def fano_line_weight(v: int) -> float:
    return float((v % 7) % 3 + 1)


def fano_weight_vector() -> np.ndarray:
    w = np.array([fano_line_weight(v) for v in range(7)], dtype=float)
    return w / w.sum()


def holonomy_vertex_rhs(v: int) -> float:
    """Share of one 2π horizon turn per shell step on vertex v (weight-normalized)."""
    w = fano_weight_vector()
    return TWO_PI * w[v]


def holonomy_k_at_xi(xi: float, k_mode: HolonomyKMode) -> float:
    """Holonomy coefficient k_v(ξ): ties phase budget to σ(ξ) or local clock density."""
    if k_mode == "log_phi":
        m = max(0, int(round(xi - 1.0)))
        return log_phi_slot(m)
    if k_mode == "sigma":
        return shell_shape_at_xi(xi)
    if k_mode == "phase":
        return ssg.holonomy_phase_density_xi(xi)
    if k_mode == "log_phi_xi":
        return log_phi_slot_xi(xi)
    raise ValueError(k_mode)


def vertex_xi_list(
    chart: ShellChart,
    m_global: int,
    *,
    xi_g_ref: float | None = None,
    xi_vertex_mode: HolonomyXiMode = "sector",
) -> tuple[list[float], list[int]]:
    """
    Horizon coordinates ξ_v = m+1 per Fano vertex.

    sector: v=0 uses ξ_G when given; other vertices use sector shell chart.
    global: all vertices share ξ_G (or referenceM+1 if ξ_G unset).
    """
    shells = [shell_for_vertex(v, chart, m_global) for v in range(7)]
    if xi_vertex_mode == "global":
        xi = xi_g_ref if xi_g_ref is not None else float(REFERENCE_M + 1)
        return [xi] * 7, shells
    xis = [float(m + 1) for m in shells]
    if xi_g_ref is not None:
        xis[0] = xi_g_ref
    return xis, shells


def holonomy_row_rhs(v: int) -> float:
    """(4/7)·12·w_v — Fano share of one 2π turn (dimensionless, π/2 cancelled)."""
    w = fano_weight_vector()
    return (4.0 / 7.0) * (w[v] * 12.0)


def build_holonomy_vertex(
    chart: ShellChart,
    m_global: int,
    *,
    k_mode: HolonomyKMode = "log_phi",
    xi_g_ref: float | None = None,
    xi_vertex_mode: HolonomyXiMode = "sector",
) -> tuple[np.ndarray, np.ndarray, list[int], list[float]]:
    """
    Seven holonomy rows: k_v(ξ_v)·c_v = (4/7)·12·w_v.

    Legacy k_mode=log_phi uses α ln(φ+1) at integer shells.
    Density modes use σ(ξ)=curvatureDensity or quarter-phase density π/(2ξ).
    """
    xis, shells = vertex_xi_list(
        chart, m_global, xi_g_ref=xi_g_ref, xi_vertex_mode=xi_vertex_mode
    )
    A = np.zeros((7, 7))
    b = np.zeros(7)
    for v, xi in enumerate(xis):
        k = holonomy_k_at_xi(xi, k_mode)
        if abs(k) < 1e-15:
            A[v, v] = 1.0
            b[v] = 0.0
        else:
            A[v, v] = k
            b[v] = holonomy_row_rhs(v)
    return A, b, shells, xis


def build_global_holonomy_closure(
    chart: ShellChart,
    m_global: int,
    *,
    k_mode: HolonomyKMode = "log_phi",
    xi_g_ref: float | None = None,
    xi_vertex_mode: HolonomyXiMode = "sector",
) -> tuple[np.ndarray, np.ndarray, list[int]]:
    """Single row: Σ_v w_v·(π/2)·k_v·c_v = 2π (full turn, no GUT prefactor)."""
    xis, shells = vertex_xi_list(
        chart, m_global, xi_g_ref=xi_g_ref, xi_vertex_mode=xi_vertex_mode
    )
    w = fano_weight_vector()
    A = np.zeros((1, 7))
    b = np.zeros(1)
    for v, xi in enumerate(xis):
        A[0, v] = w[v] * HORIZON_QUARTER * holonomy_k_at_xi(xi, k_mode)
    b[0] = TWO_PI
    return A, b, shells


def shell_for_vertex(v: int, chart: ShellChart, m_global: int) -> int:
    if chart == "uniform":
        return m_global
    if chart == "residue":
        return max(0, m_global + v)
    if chart == "lockin":
        # Spread readouts around referenceM using incident-line tick mod 3
        j = m_global % 3
        lines = sorted(i for i in range(7) if v in FANO_LINES[i])
        line = lines[j % len(lines)]
        verts = sorted(FANO_LINES[line])
        return REFERENCE_M + (verts.index(v) - 1)
    if chart == "sector":
        table = {
            0: EM_GAUSS_SHELL,
            1: REFERENCE_M,
            2: REFERENCE_M + 1,
            3: EW_PHI_SHELL,
            4: EM_GAUSS_SHELL,
            5: REFERENCE_M,
            6: EW_PHI_SHELL,
        }
        return table[v]
    raise ValueError(chart)


def double_axis_inv_alpha(c_fano: float = 1.0) -> float:
    inv_em = one_over_alpha_eff(EM_GAUSS_SHELL, c_fano)
    ratio = cpr.shell_shape(EM_GAUSS_SHELL) / cpr.shell_shape(EW_PHI_SHELL)
    return inv_em * ratio


def shell_brace_inv_alpha(c_em: float, m_gauss: int = EM_GAUSS_SHELL, m_ew: int = EW_PHI_SHELL) -> float:
    """Discrete shell-shape ratio between Gauss and electroweak readouts (double-axis brace)."""
    return one_over_alpha_eff(m_gauss, c_em) * (
        cpr.shell_shape(m_gauss) / cpr.shell_shape(m_ew)
    )


def shell_brace_inv_alpha_continuous(
    c_em: float, xi_g: float, xi_ew: float = XI_EW
) -> float:
    """Continuous brace: 1/α(ξ_G)·σ(ξ_G)/σ(ξ_EW) with σ = curvatureDensity."""
    return one_over_alpha_eff_xi(xi_g, c_em) * sigma_ratio(xi_g, xi_ew)


def xi_g_from_brace(c0: float, xi_ew: float = XI_EW) -> float:
    """ξ_G such that shell_brace_inv_alpha_continuous(c0, ξ_G) = CODATA (bisection)."""
    target = CODATA_INV_ALPHA

    def braced(xi: float) -> float:
        return shell_brace_inv_alpha_continuous(c0, xi, xi_ew)

    lo, hi = 1.05, xi_ew - 1e-3
    if braced(lo) < target:
        return lo
    if braced(hi) > target:
        return hi
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if braced(mid) > target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def line_sector_spectral_with_brace() -> dict[str, float]:
    """Best structural combo: 7×7 line incidence (sector shells) + EM shell brace."""
    run = run_one("line_incidence", "sector", REFERENCE_M, "spectral_detuning")
    inv_braced = shell_brace_inv_alpha(run.c[0], EM_GAUSS_SHELL, EW_PHI_SHELL)
    return {
        "c_v": run.c,
        "inv_alpha_vertex": run.inv_alpha_vertex,
        "inv_alpha_em_braced": inv_braced,
        "double_axis": double_axis_inv_alpha(),
    }


def rhs_vertex(v: int, m: int, mode: RhsMode) -> float:
    if mode == "bare_gut":
        return INV_ALPHA_GUT
    if mode == "spectral_detuning":
        return INV_ALPHA_GUT * rindler_1jet(m)
    if mode == "anchor_em":
        return CODATA_INV_ALPHA if v == 0 else INV_ALPHA_GUT * rindler_1jet(m)
    if mode == "anchor_em_line0":
        return CODATA_INV_ALPHA if 0 in FANO_LINES[v] else INV_ALPHA_GUT * rindler_1jet(m)
    raise ValueError(mode)


def build_vertex_diagonal(
    chart: ShellChart, m_global: int, rhs_mode: RhsMode
) -> tuple[np.ndarray, np.ndarray, list[int]]:
    shells = [shell_for_vertex(v, chart, m_global) for v in range(7)]
    A = np.zeros((7, 7))
    b = np.zeros(7)
    for v, m in enumerate(shells):
        k = log_phi_slot(m)
        A[v, v] = INV_ALPHA_GUT * k
        b[v] = rhs_vertex(v, m, rhs_mode) - INV_ALPHA_GUT
    return A, b, shells


def line_coupling_k(
    v: int,
    shells: list[int],
    vertex_xis: list[float] | None,
    line_k_mode: HolonomyKMode | None,
) -> float:
    """O–Maxwell slot in line rows; optional density alignment with holonomy."""
    if line_k_mode is not None and vertex_xis is not None:
        return holonomy_k_at_xi(vertex_xis[v], line_k_mode)
    return log_phi_slot(shells[v])


def build_line_incidence(
    chart: ShellChart,
    m_global: int,
    rhs_mode: RhsMode,
    line_weighted: bool,
    *,
    vertex_xis: list[float] | None = None,
    line_k_mode: HolonomyKMode | None = None,
) -> tuple[np.ndarray, np.ndarray, list[int]]:
    shells = [shell_for_vertex(v, chart, m_global) for v in range(7)]
    A = np.zeros((7, 7))
    b = np.zeros(7)
    for i, pts in enumerate(FANO_LINES):
        weights = []
        for v in pts:
            w = fano_line_weight(v) if line_weighted else 1.0
            weights.append((v, w))
        wsum = sum(w for _, w in weights)
        for v, w in weights:
            m = shells[v]
            k = line_coupling_k(v, shells, vertex_xis, line_k_mode)
            A[i, v] = INV_ALPHA_GUT * k * (w / wsum)
        const = INV_ALPHA_GUT * len(pts) / wsum if line_weighted else INV_ALPHA_GUT
        if rhs_mode == "anchor_em" and 0 in pts:
            b[i] = CODATA_INV_ALPHA - const
        elif rhs_mode == "anchor_em_line0" and i == 0:
            b[i] = CODATA_INV_ALPHA - const
        elif rhs_mode == "bare_gut":
            b[i] = 0.0
        else:
            m_line = int(round(sum(shells[v] for v in pts) / len(pts)))
            b[i] = INV_ALPHA_GUT * rindler_1jet(m_line) - const
    return A, b, shells


def build_line_incidence_monogamy(
    chart: ShellChart, m_global: int, rhs_mode: RhsMode
) -> tuple[np.ndarray, np.ndarray, list[int]]:
    """Six Fano line rows + monogamy row Σ_v w_v c_v = 1 (weights normalized)."""
    shells = [shell_for_vertex(v, chart, m_global) for v in range(7)]
    A = np.zeros((7, 7))
    b = np.zeros(7)
    for i in range(6):
        pts = FANO_LINES[i]
        weights = [(v, fano_line_weight(v)) for v in pts]
        wsum = sum(w for _, w in weights)
        for v, w in weights:
            A[i, v] = INV_ALPHA_GUT * log_phi_slot(shells[v]) * (w / wsum)
        const = INV_ALPHA_GUT
        if rhs_mode == "anchor_em" and 0 in pts:
            b[i] = CODATA_INV_ALPHA - const
        elif rhs_mode == "anchor_em_line0" and i == 0:
            b[i] = CODATA_INV_ALPHA - const
        elif rhs_mode == "bare_gut":
            b[i] = 0.0
        else:
            m_line = int(round(sum(shells[v] for v in pts) / len(pts)))
            b[i] = INV_ALPHA_GUT * rindler_1jet(m_line) - const
    w = np.array([fano_line_weight(v) for v in range(7)], dtype=float)
    w /= w.sum()
    A[6, :] = w
    b[6] = 1.0
    return A, b, shells


def solve_linear(A: np.ndarray, b: np.ndarray) -> tuple[np.ndarray, float]:
    if A.shape[0] == A.shape[1]:
        try:
            c = np.linalg.solve(A, b)
            resid = float(np.linalg.norm(A @ c - b))
            return c, resid
        except np.linalg.LinAlgError:
            pass
    c, resid, _, _ = np.linalg.lstsq(A, b, rcond=None)
    return c, float(np.asarray(resid).ravel()[0])


def stack_system(
    parts: list[tuple[np.ndarray, np.ndarray]]
) -> tuple[np.ndarray, np.ndarray]:
    return np.vstack([p[0] for p in parts]), np.concatenate([p[1] for p in parts])


def build_em_shell_brace_row(
    shells: list[int], weight: float = 1.0
) -> tuple[np.ndarray, np.ndarray]:
    """
    Discrete electroweak readout (legacy integer shells m_G, m_EW).
    Prefer build_continuous_brace_row for --continuous-xi.
    """
    m_g, m_e = EM_GAUSS_SHELL, EW_PHI_SHELL
    ratio = cpr.shell_shape(m_g) / cpr.shell_shape(m_e)
    k = log_phi_slot(m_g)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = INV_ALPHA_GUT * k * ratio * weight
    b[0] = (CODATA_INV_ALPHA - INV_ALPHA_GUT * ratio) * weight
    return A, b


def build_omega_k_mass_row(
    xi_g: float,
    xi_lock: float = XI_LOCKIN,
    weight: float = 1.0,
    holonomy_k_mode: HolonomyKMode = "sigma",
) -> tuple[np.ndarray, np.ndarray]:
    """
    Mass-sector geometric row (no PDG): Ω_k(ξ_lock)=1 calibrates I at ξ_lock=5.

    Scales EM holonomy budget onto lockin density slot:
      k(ξ_lock)·c_0 = holonomy_rhs(0)·Ω_k(ξ_G),  Ω_k(ξ)=I(ξ)/I(ξ_lock).
    """
    om = omega_k_at_xi(xi_g, xi_lock)
    k_lock = holonomy_k_at_xi(xi_lock, holonomy_k_mode)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = k_lock * weight
    b[0] = holonomy_row_rhs(0) * om * weight
    return A, b


def localization_energy_xi(xi: float) -> float:
    """1/Θ_local(ξ) with Θ = T_Pl/ξ and T_Pl = 1 (Lean `localizationEnergyXi`)."""
    if xi == 0.0:
        return float("nan")
    return xi


def build_informational_energy_mass_row(
    xi_g: float,
    xi_lock: float = XI_LOCKIN,
    weight: float = 1.0,
    holonomy_k_mode: HolonomyKMode = "sigma",
    phi: float = 0.0,
    t: float = 0.0,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Lean `informationalEnergyMassRow`: c₀ + loc(ξ_G) = 2π·Ω_k(ξ_G).

    Linear form on vertex 0: c₀ = 2π·Ω_k − loc(ξ_G)  (coefficient 1 on c₀).
    `m_rest = c₀` in the additive informational-energy convention.
    """
    _ = holonomy_k_mode, phi, t  # reserved for lapse-extended rows
    om = omega_k_at_xi(xi_g, xi_lock)
    loc = localization_energy_xi(xi_g)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = 1.0 * weight
    b[0] = (TWO_PI * om - loc) * weight
    return A, b


def build_informational_energy_mass_row_legacy(
    xi_g: float,
    xi_lock: float = XI_LOCKIN,
    weight: float = 1.0,
) -> tuple[np.ndarray, np.ndarray]:
    """Lean `informationalEnergyMassRowLegacy`: c₀ + loc = holonomy_rhs(0)·Ω_k."""
    om = omega_k_at_xi(xi_g, xi_lock)
    loc = localization_energy_xi(xi_g)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = 1.0 * weight
    b[0] = (holonomy_row_rhs(0) * om - loc) * weight
    return A, b


def append_mass_row(
    parts: list[tuple[np.ndarray, np.ndarray]],
    *,
    mass_row: bool,
    mass_row_kind: MassRowKind,
    xi_g: float,
    weight: float,
    holonomy_k_mode: HolonomyKMode,
    phi: float = 0.0,
    t: float = 0.0,
) -> None:
    if not mass_row:
        return
    if mass_row_kind == "omega_k":
        parts.append(
            build_omega_k_mass_row(xi_g, XI_LOCKIN, weight, holonomy_k_mode)
        )
    else:
        parts.append(
            build_informational_energy_mass_row(
                xi_g, XI_LOCKIN, weight, holonomy_k_mode, phi, t
            )
        )


def xi_g_for_mass_row(
    xi_ref: float | None,
    xis_used: list[float] | None,
    shells: list[int],
) -> float:
    if xi_ref is not None:
        return xi_ref
    if xis_used is not None and len(xis_used) > 0:
        return xis_used[0]
    return float(shells[0] + 1)


@dataclass(frozen=True)
class InformationalMassRowReport:
    """Post-solve check of the informational-energy mass row at ξ_G."""

    mass_row_kind: MassRowKind
    xi_g: float
    localization: float
    omega_k: float
    holonomy_rhs0: float
    row_target_c0: float
    row_lhs_e_tot: float
    row_rhs_budget: float
    row_residual: float
    mass_additive: float
    mass_mult_rest: float


def build_informational_mass_report(
    c: np.ndarray,
    xi_g: float,
    *,
    mass_row_kind: MassRowKind,
    phi: float = 0.0,
    t: float = 0.0,
    holonomy_k_mode: HolonomyKMode = "sigma",
) -> InformationalMassRowReport:
    c0 = float(c[0])
    loc = localization_energy_xi(xi_g)
    om = omega_k_at_xi(xi_g, XI_LOCKIN)
    rhs = holonomy_row_rhs(0)
    phi_xi = PHI_COEFF * xi_g if xi_g != 0 else float("nan")
    lapse = 1.0 + phi + phi_xi * t
    e_tot = c0 + loc
    if mass_row_kind == "omega_k":
        k_lock = holonomy_k_at_xi(XI_LOCKIN, holonomy_k_mode)
        target = rhs * om / k_lock if k_lock != 0 else float("nan")
        row_lhs = k_lock * c0
        budget = rhs * om
        residual = row_lhs - budget
    else:
        target = TWO_PI * om - loc
        row_lhs = e_tot
        budget = TWO_PI * om
        residual = e_tot - budget
    return InformationalMassRowReport(
        mass_row_kind=mass_row_kind,
        xi_g=xi_g,
        localization=loc,
        omega_k=om,
        holonomy_rhs0=rhs,
        row_target_c0=target,
        row_lhs_e_tot=row_lhs,
        row_rhs_budget=budget,
        row_residual=residual,
        mass_additive=e_tot,
        mass_mult_rest=c0 / lapse if lapse != 0 else float("nan"),
    )


def shell_surface(m: int) -> float:
    """Lean `shellSurface m = (m+1)(m+2)`."""
    return float(m + 1) * float(m + 2)


def detuned_shell_surface(m: int) -> float:
    """Lean `detunedShellSurface` with `c_rindler_shared = γ/2`."""
    return shell_surface(m) / (1.0 + C_RINDLER * float(m))


def geometric_resonance_step(m_from: int, m_to: int) -> float:
    """Lean `geometricResonanceStep` — detuned surface ratio."""
    return detuned_shell_surface(m_from) / detuned_shell_surface(m_to)


def line_mean_shell(shells: list[int], line_idx: int) -> float:
    pts = FANO_LINES[line_idx]
    return sum(shells[v] for v in pts) / float(len(pts))


def line_mean_xi(xis: list[float], line_idx: int) -> float:
    pts = FANO_LINES[line_idx]
    return sum(xis[v] for v in pts) / float(len(pts))


def sin2_theta_w_triality() -> float:
    """g₁²/(g₁²+g₂²) with g₂=1/3, g₁=γ/3 (`DerivedGaugeAndLeptonSector`)."""
    g2 = 1.0 / TRIALITY_ORDER
    g1 = GAMMA / TRIALITY_ORDER
    return (g1 * g1) / (g1 * g1 + g2 * g2)


def sin2_theta_w_geometric(shells: list[int], xis: list[float]) -> float:
    """
    Triality Weinberg × detuned imprint between weak vertex (v3) and EM vertex (v0),
    corrected by σ(ξ) along the weak vs EM-up Fano lines.
    """
    base = sin2_theta_w_triality() * geometric_resonance_step(shells[3], shells[0])
    xi_em = line_mean_xi(xis, FANO_LINE_EM_UP)
    xi_weak = line_mean_xi(xis, FANO_LINE_WEAK)
    sigma_corr = sigma_ratio(xi_weak, xi_em)
    return base * sigma_corr / (1.0 + ALPHA * max(0.0, sigma_corr - 1.0))


def alpha_s_geometric(xi_strong: float, xi_ew: float = XI_EW) -> float:
    """
    Strong coupling from φ-ladder slope ratio (no PDG input).

    `α_s ≈ (α²/3) · ln(φ(ξ_s)+1) / ln(φ(ξ_EW)+1)` mirrors monogamy/triality split.
    """
    log_s = log_phi_slot_xi(xi_strong)
    log_ew = log_phi_slot_xi(xi_ew)
    if abs(log_ew) < 1e-15:
        return float("nan")
    return (ALPHA * ALPHA / TRIALITY_ORDER) * (log_s / log_ew)


def build_monogamy_row(weight: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """Σ_v w_v c_v = 1 with normalized Fano weights (Lean monogamy normalization)."""
    w = fano_weight_vector()
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, :] = w * weight
    b[0] = weight
    return A, b


def build_coeff_ratio_row(
    v_num: int,
    v_den: int,
    ratio: float,
    weight: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Linear row: c_num − ratio·c_den = 0."""
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, v_num] = weight
    A[0, v_den] = -ratio * weight
    return A, b


def build_inv_alpha_slot_row(
    v: int,
    xi: float,
    inv_target: float,
    weight: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Pin 1/α_eff(ξ) at vertex v: 42·(1 + c_v·α ln(2ξ+1)) = inv_target."""
    k = log_phi_slot_xi(xi)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, v] = INV_ALPHA_GUT * k * weight
    b[0] = (inv_target - INV_ALPHA_GUT) * weight
    return A, b


def build_sin2_coupling_row(
    v_weak: int,
    v_em: int,
    xis: list[float],
    sin2_target: float,
    weight: float,
    k_mode: HolonomyKMode = "sigma",
) -> tuple[np.ndarray, np.ndarray]:
    """Holonomy-aligned weak/EM slot ratio: k_weak·c_weak = sin²·k_em·c_em."""
    k_w = holonomy_k_at_xi(xis[v_weak], k_mode)
    k_e = holonomy_k_at_xi(xis[v_em], k_mode)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, v_weak] = k_w * weight
    A[0, v_em] = -sin2_target * k_e * weight
    return A, b


def build_mixing_geometry_rows(
    shells: list[int],
    xis: list[float],
    *,
    weight: float = 10.0,
    pin_alpha_s: bool = True,
    holonomy_k_mode: HolonomyKMode = "sigma",
) -> list[tuple[np.ndarray, np.ndarray]]:
    """
    Extra rows from Fano / detuning geometry (no PDG in the solve).

    * monogamy: Σ w_v c_v = 1
    * up/down generation ladders on vertices 1–6
    * weak/EM coefficient ratio on line {0,3,4} vs vertex 0
    * optional strong-sector 1/α slot at down-g0 ξ
    """
    parts: list[tuple[np.ndarray, np.ndarray]] = []
    parts.append(build_monogamy_row(weight))

    up_pairs = ((1, 2), (2, 3))
    down_pairs = ((4, 5), (5, 6))
    w_gen = weight * 0.6
    for v_hi, v_lo in up_pairs:
        r = geometric_resonance_step(shells[v_hi], shells[v_lo])
        parts.append(build_coeff_ratio_row(v_hi, v_lo, r, w_gen))
    for v_hi, v_lo in down_pairs:
        r = geometric_resonance_step(shells[v_hi], shells[v_lo])
        parts.append(build_coeff_ratio_row(v_hi, v_lo, r, w_gen))

    sin2_geom = sin2_theta_w_geometric(shells, xis)
    parts.append(
        build_sin2_coupling_row(3, 0, xis, sin2_geom, weight * 0.8, holonomy_k_mode)
    )

    if pin_alpha_s:
        inv_as = 1.0 / alpha_s_geometric(xis[4], XI_EW)
        parts.append(build_inv_alpha_slot_row(4, xis[4], inv_as, weight * 0.5))

    return parts


def build_continuous_brace_row(
    xi_g: float,
    xi_ew: float = XI_EW,
    weight: float = 1.0,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Continuous Gauss→EW brace (one CODATA input, geometry only):
      42·(1 + c_0·α ln(2ξ_G+1)) · σ(ξ_G)/σ(ξ_EW) = CODATA
    Linearized at reference ξ_G for the 7-vector solve; exact ξ_G recovered post-solve.
    """
    ratio = sigma_ratio(xi_g, xi_ew)
    k = log_phi_slot_xi(xi_g)
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = INV_ALPHA_GUT * k * ratio * weight
    b[0] = (CODATA_INV_ALPHA - INV_ALPHA_GUT * ratio) * weight
    return A, b


def build_unit_c0_anchor_row(weight: float = 1.0) -> tuple[np.ndarray, np.ndarray]:
    """Normalize EM vertex coefficient c₀ = 1 (proton_lockin / cmb_now; no CODATA in solve)."""
    A = np.zeros((1, 7))
    b = np.zeros(1)
    A[0, 0] = 1.0 * weight
    b[0] = 1.0 * weight
    return A, b


def anchor_row(
    setter: ScaleSetter, shells: list[int], weight: float = 1.0
) -> tuple[np.ndarray, np.ndarray]:
    """One CODATA scale row (codata_alpha witness mode)."""
    A = np.zeros((1, 7))
    b = np.zeros(1)
    if setter == "codata_vertex0_gauss":
        v, m = 0, EM_GAUSS_SHELL
        k = log_phi_slot(m)
        A[0, v] = INV_ALPHA_GUT * k * weight
        b[0] = (CODATA_INV_ALPHA - INV_ALPHA_GUT) * weight
    elif setter == "codata_vertex0_ew":
        v, m = 0, EW_PHI_SHELL
        k = log_phi_slot(m)
        A[0, v] = INV_ALPHA_GUT * k * weight
        b[0] = (CODATA_INV_ALPHA - INV_ALPHA_GUT) * weight
    elif setter == "codata_line0":
        pts = sorted(FANO_LINES[0])
        wsum = sum(fano_line_weight(v) for v in pts)
        const = 0.0
        for v in pts:
            k = log_phi_slot(shells[v])
            w = fano_line_weight(v) / wsum
            A[0, v] = INV_ALPHA_GUT * k * w * weight
            const += INV_ALPHA_GUT * w
        b[0] = (CODATA_INV_ALPHA - const) * weight
    elif setter == "codata_weighted_mean":
        w = fano_weight_vector()
        for v in range(7):
            k = log_phi_slot(shells[v])
            A[0, v] = w[v] * INV_ALPHA_GUT * k * weight
        mean_const = sum(w[v] * INV_ALPHA_GUT for v in range(7))
        b[0] = (CODATA_INV_ALPHA - mean_const) * weight
    elif setter == "codata_triality_vector":
        return anchor_row("codata_vertex0_gauss", shells, weight)
    else:
        raise ValueError(setter)
    return A, b


@dataclass(frozen=True)
class ScaleReadout:
    name: str
    vertex: int
    shell: int
    inv_alpha_predicted: float


@dataclass(frozen=True)
class TwoObjectiveWitness:
    """Normalization (c₀≈1 brace root) vs structure (min ||Ac-b||) on the same ρ(ξ)."""

    xi_normalization: float
    m_normalization: float
    c0_normalization: float
    residual_normalization: float
    omega_k_normalization: float
    inv_alpha_braced_norm: float

    xi_structure: float
    m_structure: float
    c0_structure: float
    residual_structure: float
    omega_k_structure: float
    inv_alpha_braced_struct: float

    xi_half_step: float
    c0_half_step: float
    residual_half_step: float
    omega_k_half_step: float

    xi_lockin: float
    omega_k_lockin: float  # = 1 by calibration
    curvature_integral_lockin: float


@dataclass(frozen=True)
class MixingGeometryReport:
    """Post-solve mixing readouts from geometric rows (compare to PDG offline)."""

    sin2_triality: float
    sin2_geometric_target: float
    sin2_solved_c3_over_c0: float
    alpha_s_geometric: float
    inv_alpha_s_geometric: float
    inv_alpha_s_solved: float
    monogamy_sum_wc: float
    generation_ratio_up_12: float
    generation_ratio_up_23: float
    generation_ratio_down_45: float
    generation_ratio_down_56: float
    mixing_rows_in_solve: bool


@dataclass
class ContinuousXiReport:
    """Post-solve geometry on the continuous σ(ξ) curve."""

    xi_g: float
    xi_ew: float
    xi_g_brace_row_ref: float
    m_continuous: float
    inv_alpha_direct_at_xi_g: float
    inv_alpha_braced_at_xi_g: float
    inv_alpha_integer_gauss: float
    residual_direct_vs_integer_gauss: float
    residual_brace_vs_codata: float
    sigma_ratio_at_xi_g: float


@dataclass
class CoherenceReport:
    scale_witness: ScaleWitness
    scale_setter_used: str
    c: list[float]
    residual: float
    holonomy_k_mode: str
    holonomy_xi_mode: str
    holonomy_xi_vertices: list[float] | None
    shells: list[int]
    readouts: list[ScaleReadout]
    max_rel_spread_vs_codata: float
    max_abs_delta_among_readouts: float
    factor_alpha: float
    factor_gamma: float
    factor_inv_alpha_gut: float
    factor_g_su2: float
    factor_g_u1: float
    setter_cross_check: dict[str, float]
    continuous_xi: ContinuousXiReport | None = None
    two_objective: TwoObjectiveWitness | None = None
    mass_row_used: bool = False
    mass_row_kind: MassRowKind | None = None
    informational_mass: InformationalMassRowReport | None = None
    mixing_geometry: MixingGeometryReport | None = None


def predict_readouts(c: np.ndarray, shells: list[int]) -> list[ScaleReadout]:
    points: list[tuple[str, int, int]] = [
        ("EM Gauss v0", 0, EM_GAUSS_SHELL),
        ("EM EW v0", 0, EW_PHI_SHELL),
        ("up g0 v1", 1, shells[1]),
        ("up g2 v3", 3, shells[3]),
        ("down g0 v4", 4, shells[4]),
        ("Higgs v6", 6, shells[6]),
        ("lock-in v0", 0, REFERENCE_M),
        ("line0 avg", -1, -1),
    ]
    out: list[ScaleReadout] = []
    for name, v, m in points:
        if v < 0:
            pts = sorted(FANO_LINES[0])
            wsum = sum(fano_line_weight(x) for x in pts)
            inv = sum(
                one_over_alpha_eff(shells[x], float(c[x])) * fano_line_weight(x) / wsum
                for x in pts
            )
            out.append(ScaleReadout(name=name, vertex=0, shell=EM_GAUSS_SHELL, inv_alpha_predicted=inv))
        else:
            out.append(
                ScaleReadout(
                    name=name,
                    vertex=v,
                    shell=m,
                    inv_alpha_predicted=one_over_alpha_eff(m, float(c[v])),
                )
            )
    return out


def _append_mixing_rows(
    parts: list[tuple[np.ndarray, np.ndarray]],
    shells: list[int],
    xis: list[float],
    *,
    mixing_rows: bool,
    mixing_weight: float,
    holonomy_k_mode: HolonomyKMode = "sigma",
) -> None:
    if mixing_rows:
        parts.extend(
            build_mixing_geometry_rows(
                shells,
                xis,
                weight=mixing_weight,
                holonomy_k_mode=holonomy_k_mode,
            )
        )


def solve_line_holonomy_anchor(
    chart: ShellChart,
    m_global: int,
    scale_setter: ScaleSetter | None,
    anchor_weight: float,
    *,
    scale_witness: ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
    use_brace_instead_of_setter: bool = False,
    continuous_xi: bool = False,
    xi_g_brace_ref: float | None = None,
    density_holonomy: bool = False,
    holonomy_k_mode: HolonomyKMode = "log_phi",
    holonomy_xi_mode: HolonomyXiMode = "sector",
    mass_row: bool = False,
    mass_row_kind: MassRowKind = "informational",
    mass_row_weight: float = 1.0,
    mass_row_phi: float = 0.0,
    mass_row_t: float = 0.0,
    mixing_rows: bool = False,
    mixing_weight: float = 10.0,
) -> tuple[np.ndarray, float, list[int], float | None, list[float] | None]:
    k_mode: HolonomyKMode = holonomy_k_mode if density_holonomy else "log_phi"
    xi_ref: float | None = None
    xis_used: list[float] | None = None

    def holonomy_block(xi_g: float | None) -> tuple[np.ndarray, np.ndarray, list[int], list[float]]:
        return build_holonomy_vertex(
            chart,
            m_global,
            k_mode=k_mode,
            xi_g_ref=xi_g,
            xi_vertex_mode=holonomy_xi_mode,
        )

    use_codata_brace = sw.coupling_uses_codata_brace(
        scale_witness, continuous_xi=continuous_xi
    ) and use_brace_instead_of_setter

    if use_codata_brace and continuous_xi:
        xi_ref = xi_g_brace_ref if xi_g_brace_ref is not None else XI_G_BRACE_DEFAULT
        c = np.zeros(7)
        resid = 0.0
        shells: list[int] = []
        xis_used = None
        for _ in range(2):
            xis_used, shells = vertex_xi_list(
                chart, m_global, xi_g_ref=xi_ref, xi_vertex_mode=holonomy_xi_mode
            )
            A_line, b_line, shells = build_line_incidence(
                chart,
                m_global,
                "spectral_detuning",
                True,
                vertex_xis=xis_used if density_holonomy else None,
                line_k_mode=k_mode if density_holonomy else None,
            )
            A_hol, b_hol, _, _ = holonomy_block(xi_ref)
            parts_cx: list[tuple[np.ndarray, np.ndarray]] = [
                (A_line, b_line),
                (A_hol, b_hol),
                build_continuous_brace_row(xi_ref, XI_EW, anchor_weight),
            ]
            append_mass_row(
                parts_cx,
                mass_row=mass_row,
                mass_row_kind=mass_row_kind,
                xi_g=xi_ref,
                weight=mass_row_weight,
                holonomy_k_mode=k_mode,
                phi=mass_row_phi,
                t=mass_row_t,
            )
            _append_mixing_rows(
                parts_cx,
                shells,
                xis_used,
                mixing_rows=mixing_rows,
                mixing_weight=mixing_weight,
                holonomy_k_mode=k_mode,
            )
            A, b = stack_system(parts_cx)
            c, resid = solve_linear(A, b)
            xi_ref = xi_g_from_brace(float(c[0]), XI_EW)
        return c, resid, shells, xi_ref, xis_used

    if sw.coupling_uses_unit_c0_anchor(scale_witness):
        xi_mass = sw.xi_g_for_witness(scale_witness)
        xis_used, shells = vertex_xi_list(
            chart,
            m_global,
            xi_g_ref=xi_mass if holonomy_xi_mode == "global" else None,
            xi_vertex_mode=holonomy_xi_mode,
        )
        A_line, b_line, shells = build_line_incidence(
            chart,
            m_global,
            "spectral_detuning",
            True,
            vertex_xis=xis_used if density_holonomy else None,
            line_k_mode=k_mode if density_holonomy else None,
        )
        A_hol, b_hol, _, _ = holonomy_block(
            xi_mass if density_holonomy and holonomy_xi_mode == "global" else None
        )
        parts_w: list[tuple[np.ndarray, np.ndarray]] = [
            (A_line, b_line),
            (A_hol, b_hol),
            build_unit_c0_anchor_row(anchor_weight),
        ]
        append_mass_row(
            parts_w,
            mass_row=mass_row,
            mass_row_kind=mass_row_kind,
            xi_g=xi_mass,
            weight=mass_row_weight,
            holonomy_k_mode=k_mode,
            phi=mass_row_phi,
            t=mass_row_t,
        )
        _append_mixing_rows(
            parts_w,
            shells,
            xis_used,
            mixing_rows=mixing_rows,
            mixing_weight=mixing_weight,
            holonomy_k_mode=k_mode,
        )
        A, b = stack_system(parts_w)
        c, resid = solve_linear(A, b)
        return c, resid, shells, xi_mass, xis_used

    xis_pre, _ = vertex_xi_list(
        chart,
        m_global,
        xi_g_ref=xi_g_brace_ref if density_holonomy and holonomy_xi_mode == "global" else None,
        xi_vertex_mode=holonomy_xi_mode,
    )
    A_line, b_line, shells = build_line_incidence(
        chart,
        m_global,
        "spectral_detuning",
        True,
        vertex_xis=xis_pre if density_holonomy else None,
        line_k_mode=k_mode if density_holonomy else None,
    )
    A_hol, b_hol, _, xis_used = holonomy_block(
        xi_g_brace_ref if density_holonomy and holonomy_xi_mode == "global" else None
    )
    parts: list[tuple[np.ndarray, np.ndarray]] = [(A_line, b_line), (A_hol, b_hol)]
    if use_codata_brace and not continuous_xi:
        parts.append(build_em_shell_brace_row(shells, anchor_weight))
    elif scale_setter is not None and scale_witness == "codata_alpha":
        parts.append(anchor_row(scale_setter, shells, anchor_weight))
    if xis_used is None:
        xis_used, _ = vertex_xi_list(
            chart,
            m_global,
            xi_g_ref=xi_g_brace_ref,
            xi_vertex_mode=holonomy_xi_mode,
        )
    _append_mixing_rows(
        parts,
        shells,
        xis_used,
        mixing_rows=mixing_rows,
        mixing_weight=mixing_weight,
        holonomy_k_mode=k_mode,
    )
    append_mass_row(
        parts,
        mass_row=mass_row,
        mass_row_kind=mass_row_kind,
        xi_g=xi_g_for_mass_row(xi_ref, xis_used, shells),
        weight=mass_row_weight,
        holonomy_k_mode=k_mode,
        phi=mass_row_phi,
        t=mass_row_t,
    )
    A, b = stack_system(parts)
    c, resid = solve_linear(A, b)
    return c, resid, shells, xi_ref, xis_used


def build_mixing_geometry_report(
    c: np.ndarray,
    shells: list[int],
    xis: list[float],
    *,
    mixing_rows_in_solve: bool,
) -> MixingGeometryReport:
    w = fano_weight_vector()
    c0 = float(c[0])
    c3 = float(c[3])
    c4 = float(c[4])
    return MixingGeometryReport(
        sin2_triality=sin2_theta_w_triality(),
        sin2_geometric_target=sin2_theta_w_geometric(shells, xis),
        sin2_solved_c3_over_c0=(
            (holonomy_k_at_xi(xis[3], "sigma") * c3)
            / (holonomy_k_at_xi(xis[0], "sigma") * c0)
            if abs(c0) > 1e-15
            else float("nan")
        ),
        alpha_s_geometric=alpha_s_geometric(xis[4], XI_EW),
        inv_alpha_s_geometric=1.0 / alpha_s_geometric(xis[4], XI_EW),
        inv_alpha_s_solved=one_over_alpha_eff(shells[4], c4),
        monogamy_sum_wc=float(np.dot(w, c)),
        generation_ratio_up_12=float(c[1] / c[2]) if abs(c[2]) > 1e-15 else float("nan"),
        generation_ratio_up_23=float(c[2] / c[3]) if abs(c[3]) > 1e-15 else float("nan"),
        generation_ratio_down_45=float(c[4] / c[5]) if abs(c[5]) > 1e-15 else float("nan"),
        generation_ratio_down_56=float(c[5] / c[6]) if abs(c[6]) > 1e-15 else float("nan"),
        mixing_rows_in_solve=mixing_rows_in_solve,
    )


def build_continuous_xi_report(
    c: np.ndarray,
    xi_g_brace_row_ref: float | None,
) -> ContinuousXiReport:
    c0 = float(c[0])
    xi_g = xi_g_from_brace(c0, XI_EW)
    inv_direct = one_over_alpha_eff_xi(xi_g, c0)
    inv_braced = shell_brace_inv_alpha_continuous(c0, xi_g, XI_EW)
    inv_int = one_over_alpha_eff(EM_GAUSS_SHELL, c0)
    return ContinuousXiReport(
        xi_g=xi_g,
        xi_ew=XI_EW,
        xi_g_brace_row_ref=xi_g_brace_row_ref if xi_g_brace_row_ref is not None else XI_G_BRACE_DEFAULT,
        m_continuous=xi_g - 1.0,
        inv_alpha_direct_at_xi_g=inv_direct,
        inv_alpha_braced_at_xi_g=inv_braced,
        inv_alpha_integer_gauss=inv_int,
        residual_direct_vs_integer_gauss=inv_direct - inv_int,
        residual_brace_vs_codata=inv_braced - CODATA_INV_ALPHA,
        sigma_ratio_at_xi_g=sigma_ratio(xi_g, XI_EW),
    )


def coherence_from_solution(
    c: np.ndarray,
    resid: float,
    shells: list[int],
    scale_setter_label: str,
    chart: ShellChart,
    m_global: int,
    anchor_weight: float,
    scale_setter_for_cross: ScaleSetter | None,
    *,
    scale_witness: ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
    continuous_xi: bool = False,
    xi_g_brace_row_ref: float | None = None,
    holonomy_k_mode: str = "log_phi",
    holonomy_xi_mode: str = "sector",
    holonomy_xi_vertices: list[float] | None = None,
    two_objective: TwoObjectiveWitness | None = None,
    mass_row_used: bool = False,
    mass_row_kind: MassRowKind | None = None,
    mass_row_phi: float = 0.0,
    mass_row_t: float = 0.0,
    mixing_rows: bool = False,
    mixing_geometry: MixingGeometryReport | None = None,
) -> CoherenceReport:
    readouts = predict_readouts(c, shells)
    cx = (
        build_continuous_xi_report(c, xi_g_brace_row_ref)
        if continuous_xi
        else None
    )
    if cx is not None:
        readouts.append(
            ScaleReadout(
                name=f"EM Gauss @ ξ_G={cx.xi_g:.3f}",
                vertex=0,
                shell=int(round(cx.m_continuous)),
                inv_alpha_predicted=cx.inv_alpha_direct_at_xi_g,
            )
        )
        readouts.append(
            ScaleReadout(
                name=f"EM braced @ ξ_G={cx.xi_g:.3f}",
                vertex=0,
                shell=int(round(cx.m_continuous)),
                inv_alpha_predicted=cx.inv_alpha_braced_at_xi_g,
            )
        )
    readouts.append(
        ScaleReadout(
            name="EM braced Gauss→EW (int ξ)",
            vertex=0,
            shell=EM_GAUSS_SHELL,
            inv_alpha_predicted=shell_brace_inv_alpha(float(c[0]), EM_GAUSS_SHELL, EW_PHI_SHELL),
        )
    )
    em_names = {
        "EM Gauss v0",
        "EM EW v0",
        "EM braced Gauss→EW (int ξ)",
        "line0 avg",
        "lock-in v0",
    }
    if cx is not None:
        em_names |= {r.name for r in readouts if "ξ_G" in r.name or r.name.startswith("EM braced @")}
    em_invs = [r.inv_alpha_predicted for r in readouts if r.name in em_names]
    rel = [abs(x - CODATA_INV_ALPHA) / CODATA_INV_ALPHA for x in em_invs]
    max_spread = max(rel) if rel else 0.0
    max_delta = max(em_invs) - min(em_invs) if em_invs else 0.0
    cross: dict[str, float] = {}
    if scale_setter_for_cross is not None and scale_witness == "codata_alpha":
        for alt in ScaleSetter.__args__:
            if alt == scale_setter_for_cross:
                continue
            c_alt, _, _, _, _ = solve_line_holonomy_anchor(
                chart,
                m_global,
                alt,
                anchor_weight,
                scale_witness="codata_alpha",
            )
            cross[alt] = float(np.linalg.norm(c - c_alt))
    info_mass: InformationalMassRowReport | None = None
    xi_mass = (
        cx.xi_g
        if cx is not None
        else xi_g_for_mass_row(xi_g_brace_row_ref, holonomy_xi_vertices, shells)
    )
    if mass_row_used and mass_row_kind is not None:
        info_mass = build_informational_mass_report(
            c,
            xi_mass,
            mass_row_kind=mass_row_kind,
            phi=mass_row_phi,
            t=mass_row_t,
            holonomy_k_mode=holonomy_k_mode,
        )
    if scale_witness == "proton_lockin" and xi_g_brace_row_ref is not None:
        xi_p = xi_g_brace_row_ref
        readouts.append(
            ScaleReadout(
                name=f"EM braced @ lock-in ξ={xi_p:.3f} (α prediction)",
                vertex=0,
                shell=int(round(xi_p - 1.0)),
                inv_alpha_predicted=shell_brace_inv_alpha_continuous(float(c[0]), xi_p, XI_EW),
            )
        )
    return CoherenceReport(
        scale_witness=scale_witness,
        scale_setter_used=scale_setter_label,
        c=[float(x) for x in c],
        residual=resid,
        holonomy_k_mode=holonomy_k_mode,
        holonomy_xi_mode=holonomy_xi_mode,
        holonomy_xi_vertices=holonomy_xi_vertices,
        shells=shells,
        readouts=readouts,
        max_rel_spread_vs_codata=max_spread,
        max_abs_delta_among_readouts=max_delta,
        factor_alpha=ALPHA,
        factor_gamma=GAMMA,
        factor_inv_alpha_gut=INV_ALPHA_GUT,
        factor_g_su2=1.0 / 3.0,
        factor_g_u1=GAMMA / 3.0,
        setter_cross_check=cross,
        continuous_xi=cx,
        two_objective=two_objective,
        mass_row_used=mass_row_used,
        mass_row_kind=mass_row_kind,
        informational_mass=info_mass,
        mixing_geometry=mixing_geometry,
    )


def run_coherence(
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    scale_setter: ScaleSetter = "codata_vertex0_gauss",
    anchor_weight: float = 1e3,
    *,
    scale_witness: ScaleWitness = sw.DEFAULT_SCALE_WITNESS,
    use_brace_instead_of_setter: bool = False,
    continuous_xi: bool = False,
    density_holonomy: bool = False,
    holonomy_k_mode: HolonomyKMode = "sigma",
    holonomy_xi_mode: HolonomyXiMode = "sector",
    mass_row: bool = False,
    mass_row_kind: MassRowKind = "informational",
    mass_row_weight: float = 1.0,
    mass_row_phi: float = 0.0,
    mass_row_t: float = 0.0,
    mixing_rows: bool = False,
    mixing_weight: float = 10.0,
    include_two_objective: bool = True,
) -> CoherenceReport:
    if scale_witness == "codata_alpha":
        use_brace = use_brace_instead_of_setter or continuous_xi
    else:
        use_brace = False
        continuous_xi = False  # brace report only for codata_alpha witness
    use_density = density_holonomy
    c, resid, shells, xi_ref, xis = solve_line_holonomy_anchor(
        chart,
        m_global,
        scale_setter if not use_brace and scale_witness == "codata_alpha" else None,
        anchor_weight,
        scale_witness=scale_witness,
        use_brace_instead_of_setter=use_brace,
        continuous_xi=continuous_xi,
        density_holonomy=use_density,
        holonomy_k_mode=holonomy_k_mode,
        holonomy_xi_mode=holonomy_xi_mode,
        mass_row=mass_row,
        mass_row_kind=mass_row_kind,
        mass_row_weight=mass_row_weight,
        mass_row_phi=mass_row_phi,
        mass_row_t=mass_row_t,
        mixing_rows=mixing_rows,
        mixing_weight=mixing_weight,
    )
    two_obj = (
        compute_two_objective_witness(chart, m_global, anchor_weight, mass_row=mass_row)
        if include_two_objective
        and scale_witness == "codata_alpha"
        and (continuous_xi or use_brace)
        else None
    )
    if scale_witness == "proton_lockin":
        label = "proton_lockin_c0=1"
    elif scale_witness == "cmb_now":
        label = "cmb_now_c0=1"
    elif continuous_xi:
        label = "continuous_xi_brace"
    elif use_brace_instead_of_setter:
        label = "em_shell_brace"
    else:
        label = scale_setter
    k_label = holonomy_k_mode if use_density else "log_phi"
    mix_report = None
    if xis is not None:
        mix_report = build_mixing_geometry_report(
            c, shells, xis, mixing_rows_in_solve=mixing_rows
        )
    return coherence_from_solution(
        c,
        resid,
        shells,
        label,
        chart,
        m_global,
        anchor_weight,
        None if use_brace else scale_setter,
        scale_witness=scale_witness,
        continuous_xi=continuous_xi,
        xi_g_brace_row_ref=xi_ref,
        holonomy_k_mode=k_label,
        holonomy_xi_mode=holonomy_xi_mode,
        holonomy_xi_vertices=xis,
        two_objective=two_obj,
        mass_row_used=mass_row,
        mass_row_kind=mass_row_kind if mass_row else None,
        mass_row_phi=mass_row_phi,
        mass_row_t=mass_row_t,
        mixing_geometry=mix_report,
    )


def print_coherence(report: CoherenceReport) -> None:
    print("=" * 72)
    if report.scale_witness == "proton_lockin":
        print("Scale coherence (witness: proton_lockin — CODATA 1/α is prediction only)")
    elif report.scale_witness == "cmb_now":
        print("Scale coherence (witness: cmb_now — cosmology comparison chart)")
    else:
        print("Scale coherence (witness: codata_alpha — CODATA 1/α pinned in solve)")
    print(f"  scale witness: {report.scale_witness}")
    print(f"  setter used: {report.scale_setter_used}")
    print(f"  ||Ac-b|| = {report.residual:.6e}")
    print(
        f"  holonomy+lines: k_v ∝ {report.holonomy_k_mode}  "
        f"(ξ mode: {report.holonomy_xi_mode})"
    )
    if report.holonomy_xi_vertices is not None:
        print(f"  ξ_v (holonomy) = {[round(x, 3) for x in report.holonomy_xi_vertices]}")
    print(f"  shells m_v = {report.shells}")
    print(f"  c_v = {[round(x, 4) for x in report.c]}")
    print(
        f"  recovered factors: α={report.factor_alpha}, γ={report.factor_gamma}, "
        f"1/α_GUT={report.factor_inv_alpha_gut}, g_SU2={report.factor_g_su2:.4f}, "
        f"g_U1={report.factor_g_u1:.4f}"
    )
    print(f"  EM-sector spread (max |1/α - CODATA|/CODATA): {report.max_rel_spread_vs_codata:.4%}")
    print(f"  EM-sector band (max - min 1/α): {report.max_abs_delta_among_readouts:.4f}")
    print("  (quark/colour vertices predict other couplings — not compared to CODATA α)")
    print("  predictions (same c_v, no re-fit):")
    for r in report.readouts:
        d = r.inv_alpha_predicted - CODATA_INV_ALPHA
        print(
            f"    {r.name:28s}  1/α={r.inv_alpha_predicted:9.4f}  "
            f"Δvs CODATA={d:+8.4f}"
        )
    if report.two_objective is not None:
        print_two_objective_witness(
            report.two_objective,
            mass_row=report.mass_row_used,
            mass_row_kind=report.mass_row_kind,
        )
    if report.informational_mass is not None:
        im = report.informational_mass
        print()
        print(f"  Informational-energy mass row ({im.mass_row_kind}, Lean informationalEnergyMassRow):")
        print(f"    ξ_G = {im.xi_g:.4f}   loc = 1/Θ = {im.localization:.4f}   Ω_k = {im.omega_k:.4f}")
        if im.mass_row_kind == "informational":
            print(f"    holonomy_rhs(0) = {im.holonomy_rhs0:.6g}  (legacy vertex share; diagnostic)")
            print(
                f"    c₀ (row target) = {im.row_target_c0:.6g}   "
                f"E_tot = c₀+loc = {im.row_lhs_e_tot:.6g}   budget = 2π·Ω_k = {im.row_rhs_budget:.6g}"
            )
            print(f"    row residual E_tot − 2π·Ω_k = {im.row_residual:.6g}")
        else:
            print(
                f"    c₀ (row target) = {im.row_target_c0:.6g}   "
                f"k(ξ_lock)·c₀ = {im.row_lhs_e_tot:.6g}   budget = rhs·Ω_k = {im.row_rhs_budget:.6g}"
            )
            print(f"    row residual k·c₀ − rhs·Ω_k = {im.row_residual:.6g}")
            print(f"    E_tot = c₀+loc = {im.mass_additive:.6g}  (informational diagnostic)")
        print(
            f"    readout additive = {im.mass_additive:.6g}   "
            f"mult(rest)/N = {im.mass_mult_rest:.6g}"
        )
    if report.mixing_geometry is not None:
        mg = report.mixing_geometry
        sh = report.shells
        print()
        print("  Mixing geometry (Fano detuning rows" + (", in solve" if mg.mixing_rows_in_solve else ", post-solve only") + "):")
        print(f"    sin²θ_W triality g₁²/(g₁²+g₂²)     = {mg.sin2_triality:.6f}  (PDG {PDG_SIN2_THETA_W})")
        print(f"    sin²θ_W geometric target (c₃/c₀) = {mg.sin2_geometric_target:.6f}")
        print(f"    sin²θ_W solved c₃/c₀             = {mg.sin2_solved_c3_over_c0:.6f}")
        print(f"    α_s geometric (φ-slope)          = {mg.alpha_s_geometric:.6f}  (PDG {PDG_ALPHA_S_MZ})")
        print(f"    1/α_s geometric slot             = {mg.inv_alpha_s_geometric:.4f}")
        print(f"    1/α_s solved @ v4                = {mg.inv_alpha_s_solved:.4f}")
        print(f"    Σ w_v c_v (monogamy)             = {mg.monogamy_sum_wc:.6f}")
        print(
            f"    gen ratios c₁/c₂,c₂/c₃,c₄/c₅,c₅/c₆ = "
            f"{mg.generation_ratio_up_12:.4f}, {mg.generation_ratio_up_23:.4f}, "
            f"{mg.generation_ratio_down_45:.4f}, {mg.generation_ratio_down_56:.4f}"
        )
        print(
            f"    vs detuned targets               = "
            f"{geometric_resonance_step(sh[1], sh[2]):.4f}, "
            f"{geometric_resonance_step(sh[2], sh[3]):.4f}, "
            f"{geometric_resonance_step(sh[4], sh[5]):.4f}, "
            f"{geometric_resonance_step(sh[5], sh[6]):.4f}"
        )
    if report.continuous_xi is not None:
        cx = report.continuous_xi
        print()
        print("  Continuous ξ (post-solve brace root, σ = curvatureDensity):")
        print(f"    ξ_EW (fixed)     = {cx.xi_ew:.4f}  (m_EW = {cx.xi_ew - 1:.1f})")
        print(f"    ξ_G (brace row)  = {cx.xi_g_brace_row_ref:.4f}  (linearization ref)")
        print(f"    ξ_G (solved)     = {cx.xi_g:.4f}  (m ≈ {cx.m_continuous:.4f})")
        print(f"    σ(ξ_G)/σ(ξ_EW)   = {cx.sigma_ratio_at_xi_g:.6f}")
        print(
            f"    1/α direct @ ξ_G = {cx.inv_alpha_direct_at_xi_g:.6f}  "
            f"|  integer ξ={XI_GAUSS_INTEGER:.0f} Gauss = {cx.inv_alpha_integer_gauss:.6f}"
        )
        print(
            f"    residual (direct@ξ_G − integer Gauss) = {cx.residual_direct_vs_integer_gauss:+.6f}"
        )
        print(
            f"    1/α braced @ ξ_G = {cx.inv_alpha_braced_at_xi_g:.6f}  "
            f"|  Δvs CODATA = {cx.residual_brace_vs_codata:+.2e}"
        )
    print("  cross-setter ||c - c_alt|| (should → 0 if setters agree):")
    for k, v in sorted(report.setter_cross_check.items()):
        print(f"    vs {k:24s}  ||Δc||={v:.6f}")


@dataclass
class CouplingRun:
    system: str
    shell_chart: str
    m_global: int
    rhs_mode: str
    shells: list[int]
    c: list[float]
    residual: float
    inv_alpha_vertex: list[float]
    inv_alpha_em_vertex0: float
    inv_alpha_em_ew_shell: float
    double_axis_inv_alpha: float
    codata_inv_alpha: float
    paper_inv_alpha: float
    su2_derived: float
    u1_derived: float


def run_one(
    kind: SystemKind,
    chart: ShellChart,
    m_global: int,
    rhs_mode: RhsMode,
    scale_setter: ScaleSetter | None = None,
) -> CouplingRun:
    if kind == "vertex_diagonal":
        A, b, shells = build_vertex_diagonal(chart, m_global, rhs_mode)
    elif kind == "line_incidence":
        A, b, shells = build_line_incidence(chart, m_global, rhs_mode, line_weighted=True)
    elif kind == "line_incidence_monogamy":
        A, b, shells = build_line_incidence_monogamy(chart, m_global, rhs_mode)
    elif kind == "holonomy_only":
        A, b, shells, _ = build_holonomy_vertex(chart, m_global)
    elif kind == "line_plus_holonomy":
        A_l, b_l, shells = build_line_incidence(chart, m_global, "spectral_detuning", True)
        A_h, b_h, _, _ = build_holonomy_vertex(chart, m_global)
        A, b = stack_system([(A_l, b_l), (A_h, b_h)])
        if rhs_mode == "anchor_em":
            A_a, b_a = anchor_row("codata_vertex0_gauss", shells, 1e3)
            A, b = stack_system([(A, b), (A_a, b_a)])
    else:
        raise ValueError(kind)
    if scale_setter is not None and kind not in ("line_plus_holonomy",):
        A_a, b_a = anchor_row(scale_setter, shells, 1e3)
        A, b = stack_system([(A, b), (A_a, b_a)])

    c, resid = solve_linear(A, b)
    inv_v = [one_over_alpha_eff(shells[v], float(c[v])) for v in range(7)]
    return CouplingRun(
        system=kind,
        shell_chart=chart,
        m_global=m_global,
        rhs_mode=rhs_mode,
        shells=shells,
        c=[float(x) for x in c],
        residual=resid,
        inv_alpha_vertex=inv_v,
        inv_alpha_em_vertex0=inv_v[0],
        inv_alpha_em_ew_shell=one_over_alpha_eff(EW_PHI_SHELL, float(c[0])),
        double_axis_inv_alpha=double_axis_inv_alpha(),
        codata_inv_alpha=CODATA_INV_ALPHA,
        paper_inv_alpha=PAPER_INV_ALPHA,
        su2_derived=1.0 / 3.0,
        u1_derived=GAMMA / 3.0,
    )


def closed_form_spectral_c(shells: list[int]) -> list[float]:
    """c_v = (γ/2)m_v / (α log(φ+1)) when rhs = 42·(1+(γ/2)m_v)."""
    out = []
    for m in shells:
        k = log_phi_slot(m)
        if abs(k) < 1e-15:
            out.append(float("nan"))
        else:
            out.append(C_RINDLER * float(m) / k)
    return out


def assemble_sigma_brace_system(
    xi_g: float,
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    anchor_weight: float = 1e3,
    holonomy_k_mode: HolonomyKMode = "sigma",
    holonomy_xi_mode: HolonomyXiMode = "sector",
    *,
    mass_row: bool = False,
    mass_row_kind: MassRowKind = "informational",
    mass_row_weight: float = 1.0,
    mixing_rows: bool = False,
    mixing_weight: float = 10.0,
) -> tuple[np.ndarray, np.ndarray, list[int], list[float]]:
    """15×7 (+ optional Ω_k / mixing rows): lines + σ-holonomy + continuous brace at ξ_G."""
    xis, shells = vertex_xi_list(
        chart, m_global, xi_g_ref=xi_g, xi_vertex_mode=holonomy_xi_mode
    )
    A_l, b_l, _ = build_line_incidence(
        chart,
        m_global,
        "spectral_detuning",
        True,
        vertex_xis=xis,
        line_k_mode=holonomy_k_mode,
    )
    A_h, b_h, _, _ = build_holonomy_vertex(
        chart,
        m_global,
        k_mode=holonomy_k_mode,
        xi_g_ref=xi_g,
        xi_vertex_mode=holonomy_xi_mode,
    )
    A_b, b_b = build_continuous_brace_row(xi_g, XI_EW, anchor_weight)
    parts: list[tuple[np.ndarray, np.ndarray]] = [(A_l, b_l), (A_h, b_h), (A_b, b_b)]
    append_mass_row(
        parts,
        mass_row=mass_row,
        mass_row_kind=mass_row_kind,
        xi_g=xi_g,
        weight=mass_row_weight,
        holonomy_k_mode=holonomy_k_mode,
    )
    _append_mixing_rows(
        parts,
        shells,
        xis,
        mixing_rows=mixing_rows,
        mixing_weight=mixing_weight,
        holonomy_k_mode=holonomy_k_mode,
    )
    A, b = stack_system(parts)
    return A, b, shells, xis


def _witness_at_xi(
    xi_g: float,
    chart: ShellChart,
    m_global: int,
    anchor_weight: float,
    *,
    mass_row: bool = False,
) -> tuple[float, float, float, float]:
    """c₀, ||Ac-b||, Ω_k(ξ_G), braced 1/α after solve at fixed ξ_G."""
    c, _, _, resid, _, _, _ = solve_at_xi_g(
        xi_g,
        chart,
        m_global,
        anchor_weight,
        mass_row=mass_row,
    )
    c0 = float(c[0])
    return c0, resid, omega_k_at_xi(xi_g), shell_brace_inv_alpha_continuous(c0, xi_g, XI_EW)


def compute_two_objective_witness(
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    anchor_weight: float = 1e3,
    xi_lo: float = 3.0,
    xi_hi: float = 5.5,
    n_steps: int = 51,
    *,
    mass_row: bool = False,
) -> TwoObjectiveWitness:
    """Normalization-optimal ξ (brace @ c₀=1) vs structure-optimal ξ (min residual)."""
    xi_norm = xi_g_from_brace(1.0, XI_EW)
    c0_n, r_n, ok_n, br_n = _witness_at_xi(
        xi_norm, chart, m_global, anchor_weight, mass_row=mass_row
    )

    xs = [xi_lo + (xi_hi - xi_lo) * i / (n_steps - 1) for i in range(n_steps)]
    best_xi, best_r = xs[0], float("inf")
    for xi in xs:
        _, r, _, _ = _witness_at_xi(xi, chart, m_global, anchor_weight, mass_row=mass_row)
        if r < best_r:
            best_r, best_xi = r, xi
    c0_s, r_s, ok_s, br_s = _witness_at_xi(
        best_xi, chart, m_global, anchor_weight, mass_row=mass_row
    )

    c0_h, r_h, ok_h, _ = _witness_at_xi(
        XI_HALF_STEP, chart, m_global, anchor_weight, mass_row=mass_row
    )

    i_lock = curvature_integral_discrete(REFERENCE_M)
    return TwoObjectiveWitness(
        xi_normalization=xi_norm,
        m_normalization=xi_norm - 1.0,
        c0_normalization=c0_n,
        residual_normalization=r_n,
        omega_k_normalization=ok_n,
        inv_alpha_braced_norm=br_n,
        xi_structure=best_xi,
        m_structure=best_xi - 1.0,
        c0_structure=c0_s,
        residual_structure=r_s,
        omega_k_structure=ok_s,
        inv_alpha_braced_struct=br_s,
        xi_half_step=XI_HALF_STEP,
        c0_half_step=c0_h,
        residual_half_step=r_h,
        omega_k_half_step=ok_h,
        xi_lockin=XI_LOCKIN,
        omega_k_lockin=1.0,
        curvature_integral_lockin=ssg.curvature_integral_continuous(XI_LOCKIN),
    )


def print_two_objective_witness(
    w: TwoObjectiveWitness,
    *,
    mass_row: bool = False,
    mass_row_kind: MassRowKind | None = None,
) -> None:
    print()
    print("  Two-objective witness (same ρ(ξ), brace → CODATA at each ξ_G)")
    if mass_row:
        kind = mass_row_kind or "omega_k"
        if kind == "informational":
            print("  (+ informational mass row: c₀ + loc(ξ_G) = 2π·Ω_k(ξ_G))")
        else:
            print("  (+ Ω_k mass row: k(ξ_lock)·c₀ = holonomy_rhs·Ω_k(ξ_G))")
    print(f"  {'':28s} {'ξ_G':>7} {'m':>6} {'c₀':>8} {'||Ac-b||':>10} {'Ω_k':>8} {'1/α br':>10}")
    print(f"  {'Normalization (c₀≈1 root)':28s} {w.xi_normalization:7.4f} {w.m_normalization:6.2f} "
          f"{w.c0_normalization:8.4f} {w.residual_normalization:10.4f} {w.omega_k_normalization:8.4f} "
          f"{w.inv_alpha_braced_norm:10.4f}")
    print(f"  {'Structure (min residual)':28s} {w.xi_structure:7.4f} {w.m_structure:6.2f} "
          f"{w.c0_structure:8.4f} {w.residual_structure:10.4f} {w.omega_k_structure:8.4f} "
          f"{w.inv_alpha_braced_struct:10.4f}")
    print(f"  {'Half-step reference':28s} {w.xi_half_step:7.4f} {w.xi_half_step-1:6.2f} "
          f"{w.c0_half_step:8.4f} {w.residual_half_step:10.4f} {w.omega_k_half_step:8.4f} "
          f"{'—':>10}")
    print(f"  {'Lock-in calibration':28s} {w.xi_lockin:7.4f} {w.xi_lockin-1:6.2f} "
          f"{'—':>8} {'—':>10} {w.omega_k_lockin:8.4f} {'—':>10}")
    print(
        f"  Δξ (struct − norm) = {w.xi_structure - w.xi_normalization:+.4f}  "
        f"Δc₀ = {w.c0_structure - w.c0_normalization:+.4f}  "
        f"Δ||Ac-b|| = {w.residual_structure - w.residual_normalization:+.4f}"
    )


def plot_xi_residual_curve(
    out_path: str | Path = "scripts/out/xi_g_residual_curve.png",
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    xi_lo: float = 3.0,
    xi_hi: float = 5.5,
    n_steps: int = 81,
    *,
    mass_row: bool = False,
) -> Path:
    """Residual and c₀ vs ξ_G; mark normalization vs structure optima."""
    try:
        import matplotlib.pyplot as plt
    except ImportError as e:
        raise SystemExit("matplotlib required for --plot-xi-residual") from e

    w = compute_two_objective_witness(
        chart, m_global, mass_row=mass_row, xi_lo=xi_lo, xi_hi=xi_hi, n_steps=n_steps
    )
    xs = [xi_lo + (xi_hi - xi_lo) * i / (n_steps - 1) for i in range(n_steps)]
    resids: list[float] = []
    c0s: list[float] = []
    oks: list[float] = []
    for xi in xs:
        c0, r, ok, _ = _witness_at_xi(xi, chart, m_global, 1e3, mass_row=mass_row)
        resids.append(r)
        c0s.append(c0)
        oks.append(ok)

    fig, (ax0, ax1, ax2) = plt.subplots(3, 1, figsize=(8, 8), sharex=True)
    ax0.plot(xs, resids, "b-", lw=1.5, label=r"$\|Ac-b\|$ (structural)")
    ax0.axvline(w.xi_normalization, color="green", ls="--", label=f"norm ξ={w.xi_normalization:.3f}")
    ax0.axvline(w.xi_structure, color="orange", ls="--", label=f"struct ξ={w.xi_structure:.3f}")
    ax0.axvline(XI_HALF_STEP, color="gray", ls=":", label="ξ=3.5")
    ax0.set_ylabel(r"$\|Ac-b\|$")
    ax0.legend(loc="upper right", fontsize=8)
    ax0.grid(True, alpha=0.3)

    ax1.plot(xs, c0s, "k-", lw=1.5)
    ax1.axhline(1.0, color="gray", ls=":", label=r"$c_0=1$")
    ax1.axvline(w.xi_normalization, color="green", ls="--")
    ax1.axvline(w.xi_structure, color="orange", ls="--")
    ax1.set_ylabel(r"$c_0$")
    ax1.legend(loc="upper right", fontsize=8)
    ax1.grid(True, alpha=0.3)

    ax2.plot(xs, oks, "m-", lw=1.5, label=r"$\Omega_k(\xi_G)$")
    ax2.axhline(1.0, color="red", ls=":", label=rf"$\Omega_k(\xi_{{lock}}={XI_LOCKIN:.0f})=1$")
    ax2.axvline(XI_LOCKIN, color="red", ls=":", alpha=0.5)
    ax2.set_xlabel(r"$\xi_G$ (Gauss / EM horizon coordinate)")
    ax2.set_ylabel(r"$\Omega_k$")
    ax2.legend(loc="upper left", fontsize=8)
    ax2.grid(True, alpha=0.3)

    title = "HQIV coupling: shallow bowl (brace + σ-holonomy + lines)"
    if mass_row:
        title += " + Ω_k mass row"
    fig.suptitle(title, fontsize=11)
    fig.tight_layout()
    path = Path(out_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, dpi=120)
    plt.close(fig)
    return path


def solve_at_xi_g(
    xi_g: float,
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    anchor_weight: float = 1e3,
    *,
    mass_row: bool = False,
    mass_row_kind: MassRowKind = "informational",
    mass_row_weight: float = 1.0,
) -> tuple[np.ndarray, np.ndarray, float, list[float], list[int], list[float]]:
    """Solve constrained system with Gauss readout pinned at ξ_G."""
    A, b, shells, xis = assemble_sigma_brace_system(
        xi_g,
        chart,
        m_global,
        anchor_weight,
        mass_row=mass_row,
        mass_row_kind=mass_row_kind,
        mass_row_weight=mass_row_weight,
    )
    c, resid = solve_linear(A, b)
    row_res = list((A @ c - b).ravel())
    return c, A, b, resid, row_res, shells, xis


def parabolic_min_xi(
    xs: list[float], ys: list[float]
) -> tuple[float, float]:
    """Vertex of parabola through three lowest points near minimum."""
    idx = sorted(range(len(ys)), key=lambda i: ys[i])[:3]
    idx.sort()
    if len(idx) < 3:
        return xs[ys.index(min(ys))], float("nan")
    x0, x1, x2 = (xs[i] for i in idx)
    y0, y1, y2 = (ys[i] for i in idx)
    denom = (x0 - x1) * (x0 - x2) * (x1 - x2)
    if abs(denom) < 1e-15:
        return x1, float("nan")
    xv = (
        x0 * x0 * (y1 - y2)
        + x1 * x1 * (y2 - y0)
        + x2 * x2 * (y0 - y1)
    ) / (2.0 * denom)
    curv = (y0 - y1) / (x0 - x1) - (y1 - y2) / (x1 - x2)
    return xv, 2.0 * curv


def print_half_step_scan(
    chart: ShellChart = "sector",
    m_global: int = REFERENCE_M,
    xi_lo: float = 2.2,
    xi_hi: float = 6.2,
    n_steps: int = 81,
) -> None:
    """Diagnostics for half-step / low-tension pocket near ξ_G ≈ 3.5."""
    print("=" * 72)
    print("Half-step scan: σ-holonomy + lines + continuous brace (15×7)")
    print(f"  ξ_EW fixed at {XI_EW:.1f}; sweep ξ_G ∈ [{xi_lo:.2f}, {xi_hi:.2f}]")
    print()

    xs: list[float] = []
    resids: list[float] = []
    c0s: list[float] = []
    conds: list[float] = []
    for i in range(n_steps):
        xi = xi_lo + (xi_hi - xi_lo) * i / (n_steps - 1)
        c, A, _, resid, _, _, _ = solve_at_xi_g(xi, chart, m_global)
        xs.append(xi)
        resids.append(resid)
        c0s.append(float(c[0]))
        try:
            conds.append(float(np.linalg.cond(A)))
        except np.linalg.LinAlgError:
            conds.append(float("inf"))

    # Finer pocket around half-step for curvature estimate
    fine_xs: list[float] = []
    fine_rs: list[float] = []
    for i in range(41):
        xi = 3.0 + 2.0 * i / 40.0
        _, _, _, r, _, _, _ = solve_at_xi_g(xi, chart, m_global)
        fine_xs.append(xi)
        fine_rs.append(r)
    imin_f = int(np.argmin(fine_rs))
    par_xi, curv = parabolic_min_xi(fine_xs, fine_rs)

    imin = int(np.argmin(resids))
    xi_min = xs[imin]

    print("1. Residual vs ξ_G (structural; brace enforces CODATA each point)")
    print(f"   coarse sweep min at ξ_G = {xi_min:.4f}  ||Ac-b|| = {resids[imin]:.6f}")
    print(
        f"   fine [3,5] pocket: min at ξ = {fine_xs[imin_f]:.4f}  "
        f"||Ac-b|| = {fine_rs[imin_f]:.6f}"
    )
    print(f"   parabolic vertex (fine) ≈ {par_xi:.4f}  (curvature scale ≈ {curv:.4f})")
    brace_xi = xi_g_from_brace(1.0, XI_EW)
    print(f"   brace-only root at c₀=1: ξ_G = {brace_xi:.4f}  (m_eff ≈ {brace_xi-1:.4f})")
    for label, xi in [("half-step ξ=3.5", 3.5), ("continuous root", XI_G_BRACE_DEFAULT)]:
        j = min(range(len(xs)), key=lambda k: abs(xs[k] - xi))
        print(
            f"   {label:20s}  ξ={xs[j]:.4f}  ||Ac-b||={resids[j]:.6f}  "
            f"c₀={c0s[j]:.4f}  (Δc₀ from 1: {c0s[j]-1:+.4f})"
        )
    print()

    print("2. Integer shell bracket (Δ residual between neighbors)")
    print(f"   {'m':>3} {'ξ':>5} {'||Ac-b||':>10} {'Δres':>10} {'c₀':>8} {'c₀−1':>8} {'κ(A)':>10}")
    prev_r = None
    int_rows: list[tuple[int, float, float, float]] = []
    for m in range(2, 8):
        xi = float(m + 1)
        c, A, _, r, _, _, _ = solve_at_xi_g(xi, chart, m_global)
        dr = r - prev_r if prev_r is not None else float("nan")
        kappa = float(np.linalg.cond(A))
        int_rows.append((m, r, float(c[0]), kappa))
        print(
            f"   {m:3d} {xi:5.1f} {r:10.6f} "
            f"{(dr if prev_r is not None else float('nan')):+10.6f} "
            f"{c[0]:8.4f} {c[0]-1:+8.4f} {kappa:10.2e}"
        )
        prev_r = r
    print("   (Δres < 0: moving to higher m lowers tension in this step)")
    print()

    print("3. Half-step vs nodes: c₀ brackets unity")
    for m, r, c0, _ in int_rows:
        if m in (3, 4):
            print(f"   m={m} (ξ={m+1}): ||Ac-b||={r:.4f}, c₀={c0:.4f} ({c0-1:+.4f} from 1)")
    c_half, _, _, r_half, _, _, _ = solve_at_xi_g(3.5, chart, m_global)
    print(
        f"   ξ=3.5 (half):     ||Ac-b||={r_half:.4f}, c₀={c_half[0]:.4f} "
        f"({c_half[0]-1:+.4f} from 1)"
    )
    print()

    print("4. Per-row residual at ξ_G = 3.5 (7 lines + 7 holonomy + 1 brace)")
    _, _, _, _, row_res, shells, xis = solve_at_xi_g(3.5, chart, m_global)
    labels = [f"line{i}" for i in range(7)] + [f"hol{v}" for v in range(7)] + ["brace"]
    print(f"   sector ξ_v = {[round(x, 2) for x in xis]}")
    for lab, rv in zip(labels, row_res):
        print(f"   {lab:8s}  residual={rv:+10.4e}")
    print("   holonomy slot k_v·c_v vs target (phase budget):")
    c, _, _, _, _, _, xis = solve_at_xi_g(3.5, chart, m_global)
    for v in range(7):
        k = holonomy_k_at_xi(xis[v], "sigma")
        lhs = k * float(c[v])
        rhs = holonomy_row_rhs(v)
        print(
            f"   v={v}  k·c={lhs:7.4f}  target={rhs:7.4f}  "
            f"gap={lhs-rhs:+7.4f}  σ(ξ)={shell_shape_at_xi(xis[v]):.4f}"
        )
    print()

    print("5. Conditioning: best κ(A) near low-residual ξ_G")
    j_cond = int(np.argmin(conds))
    print(
        f"   min cond at ξ={xs[j_cond]:.4f}  κ={conds[j_cond]:.2e}  "
        f"(residual there = {resids[j_cond]:.4f})"
    )
    print(
        f"   at ξ=3.5: κ={conds[xs.index(min(xs, key=lambda x: abs(x-3.5)))]:.2e}"
        if any(abs(x - 3.5) < 0.05 for x in xs)
        else ""
    )
    print()
    w = compute_two_objective_witness(chart, m_global)
    print()
    print_two_objective_witness(w)
    print()
    print("Summary:")
    print("  • Brace-only (c₀=1) pins ξ_G ≈ 3.47 — half-step between m=2 and m=3 nodes.")
    print("  • Full 15×7 residual is shallow in m=3–5; best integer m=4 (ξ=5), best c₀≈1 at ξ≈3.5.")
    print("  • Two objectives: CODATA brace geometry vs global structural fit (slightly different ξ).")


def print_report(runs: list[CouplingRun]) -> None:
    print("HQIV 7×7 Fano coupling linear system")
    print(f"  α={ALPHA}, γ={GAMMA}, 1/α_GUT={INV_ALPHA_GUT}, referenceM={REFERENCE_M}")
    print(f"  EM Gauss shell={EM_GAUSS_SHELL}, EW φ-shell={EW_PHI_SHELL}")
    print(f"  TARGET CODATA 1/α={CODATA_INV_ALPHA:.6f}  (paper witness {PAPER_INV_ALPHA} legacy)")
    print(f"  double-axis (c=1) 1/α={double_axis_inv_alpha():.4f}  [paper-era, not CODATA]\n")

    for r in runs:
        print("=" * 72)
        print(f"system={r.system}  shells={r.shell_chart}  m_global={r.m_global}  rhs={r.rhs_mode}")
        print(f"  solve residual ||Ac-b|| = {r.residual:.6e}")
        print(f"  shells m_v = {r.shells}")
        print(f"  c_v      = {[round(x, 4) for x in r.c]}")
        print(f"  1/α_v    = {[round(x, 2) for x in r.inv_alpha_vertex]}")
        print(f"  1/α(v=0) = {r.inv_alpha_em_vertex0:.4f}  |  1/α(v=0,m=EW) = {r.inv_alpha_em_ew_shell:.4f}")
        print(
            f"  vs CODATA {r.codata_inv_alpha:.4f}  |  paper(legacy) {r.paper_inv_alpha}  "
            f"|  double-axis {r.double_axis_inv_alpha:.4f}"
        )
        print(f"  EW derived: g_SU2={r.su2_derived:.4f}, g_U1={r.u1_derived:.4f} (triality 1/3, γ/3)")
        for v in range(7):
            print(f"    v={v} {VERTEX_NAMES[v]:22s}  m={r.shells[v]:2d}  c={r.c[v]:7.4f}  1/α={r.inv_alpha_vertex[v]:8.2f}")


def main() -> None:
    p = argparse.ArgumentParser(description="HQIV 7×7 Fano coupling solver")
    p.add_argument("--json", action="store_true")
    p.add_argument(
        "--coherence",
        action="store_true",
        help="line+holonomy+one CODATA setter; report cross-readout agreement",
    )
    p.add_argument(
        "--scale-witness",
        choices=("proton_lockin", "codata_alpha", "cmb_now"),
        default=sw.DEFAULT_SCALE_WITNESS,
        help="single active scale witness (default proton_lockin)",
    )
    p.add_argument("--scale-setter", choices=list(ScaleSetter.__args__), default="codata_vertex0_gauss")
    p.add_argument(
        "--brace-scale",
        action="store_true",
        help="use geometric Gauss→EW shell brace as the single scale row (no vertex anchor)",
    )
    p.add_argument(
        "--continuous-xi",
        action="store_true",
        help="continuous σ(ξ) brace row (ξ_G≈3.47 post-solve); implies --brace-scale",
    )
    p.add_argument(
        "--density-holonomy",
        action="store_true",
        help="k_v(ξ_v) and line O–Maxwell slots from σ(ξ) or phase (default with --continuous-xi)",
    )
    p.add_argument(
        "--holonomy-k",
        choices=list(HolonomyKMode.__args__),
        default="sigma",
        help="holonomy coefficient: sigma=curvatureDensity, phase=π/(2ξ)",
    )
    p.add_argument(
        "--holonomy-xi",
        choices=list(HolonomyXiMode.__args__),
        default="sector",
        help="sector: ξ_G on v=0 + chart shells; global: one ξ for all vertices",
    )
    p.add_argument(
        "--compare-holonomy",
        action="store_true",
        help="with --coherence: print residual for log_phi vs density holonomy",
    )
    p.add_argument(
        "--half-step-scan",
        action="store_true",
        help="residual vs ξ_G, integer bracket, per-vertex tension (σ-aligned system)",
    )
    p.add_argument(
        "--mass-row",
        action="store_true",
        help="add mass-sector row coupling EM vertex to Ω_k (see --mass-row-kind)",
    )
    p.add_argument(
        "--mass-row-kind",
        choices=list(MassRowKind.__args__),
        default="informational",
        help="informational: c₀+loc(ξ_G)=2π·Ω_k; omega_k: k(ξ_lock)·c₀=rhs·Ω_k",
    )
    p.add_argument(
        "--mass-row-weight",
        type=float,
        default=1.0,
        help="weight on the mass row in the stacked solve",
    )
    p.add_argument(
        "--mass-row-phi",
        type=float,
        default=0.0,
        help="HQVM Φ for lapse in informational mass post-report",
    )
    p.add_argument(
        "--mass-row-t",
        type=float,
        default=0.0,
        help="time slot for lapse in informational mass post-report",
    )
    p.add_argument(
        "--mixing-rows",
        action="store_true",
        help="add Fano mixing rows: monogamy, generation ladders, sin² geom, α_s slot",
    )
    p.add_argument(
        "--mixing-weight",
        type=float,
        default=10.0,
        help="weight for geometric mixing rows (default 10)",
    )
    p.add_argument(
        "--plot-xi-residual",
        action="store_true",
        help="save residual/c₀/Ω_k vs ξ_G plot to scripts/out/xi_g_residual_curve.png",
    )
    p.add_argument(
        "--plot-path",
        default="scripts/out/xi_g_residual_curve.png",
        help="output path for --plot-xi-residual",
    )
    p.add_argument("--shell-chart", choices=list(ShellChart.__args__), default=None)
    p.add_argument("--m-global", type=int, default=REFERENCE_M)
    p.add_argument("--rhs", choices=list(RhsMode.__args__), default=None)
    p.add_argument("--system", choices=list(SystemKind.__args__), default=None)
    args = p.parse_args()
    continuous_xi = args.continuous_xi
    brace_scale = args.brace_scale or continuous_xi
    density_holonomy = args.density_holonomy or continuous_xi
    holonomy_k: HolonomyKMode = args.holonomy_k
    holonomy_xi: HolonomyXiMode = args.holonomy_xi

    if args.half_step_scan:
        print_half_step_scan(args.shell_chart or "sector", args.m_global)
        return

    if args.plot_xi_residual:
        path = plot_xi_residual_curve(
            args.plot_path,
            args.shell_chart or "sector",
            args.m_global,
            mass_row=args.mass_row,
        )
        print(f"Wrote {path}")
        w = compute_two_objective_witness(
            args.shell_chart or "sector",
            args.m_global,
            mass_row=args.mass_row,
        )
        print_two_objective_witness(w, mass_row=args.mass_row)
        return

    if args.coherence:
        witness: ScaleWitness = args.scale_witness
        if witness != "codata_alpha":
            brace_scale = False
            if continuous_xi:
                continuous_xi = False
        report = run_coherence(
            args.shell_chart or "sector",
            args.m_global,
            args.scale_setter,
            scale_witness=witness,
            use_brace_instead_of_setter=brace_scale,
            continuous_xi=continuous_xi,
            density_holonomy=density_holonomy,
            holonomy_k_mode=holonomy_k,
            holonomy_xi_mode=holonomy_xi,
            mass_row=args.mass_row,
            mass_row_kind=args.mass_row_kind,
            mass_row_weight=args.mass_row_weight,
            mass_row_phi=args.mass_row_phi,
            mass_row_t=args.mass_row_t,
            mixing_rows=args.mixing_rows,
            mixing_weight=args.mixing_weight,
        )
        if args.json:
            print(json.dumps(asdict(report), indent=2, default=lambda o: o.__dict__ if hasattr(o, "__dict__") else str(o)))
        else:
            print("HQIV coupling + holonomy + scale coherence")
            bundle = sw.load_witness_bundle()
            sw.print_witness_summary(
                bundle,
                witness,
                inv_alpha_predicted=(
                    report.continuous_xi.inv_alpha_braced_at_xi_g
                    if report.continuous_xi is not None
                    else next(
                        (
                            r.inv_alpha_predicted
                            for r in report.readouts
                            if "α prediction" in r.name
                        ),
                        None,
                    )
                ),
            )
            print()
            print(f"  CODATA 1/α (comparison) = {CODATA_INV_ALPHA:.9f}  (paper {PAPER_INV_ALPHA} legacy)")
            if witness == "codata_alpha":
                mode = "continuous ξ brace" if continuous_xi else "scale row"
            else:
                mode = f"{witness} (c₀=1 normalization)"
            hol = f"density k∝{holonomy_k}" if density_holonomy else "log_phi holonomy"
            mix_note = f" + mixing ({args.mixing_weight:g}w)" if args.mixing_rows else ""
            mass_note = ""
            if args.mass_row:
                if args.mass_row_kind == "informational":
                    mass_note = " + informational mass (c₀+loc=2π·Ω_k)"
                else:
                    mass_note = " + Ω_k mass (k·c₀=rhs·Ω_k)"
            print(
                "  equations: 7 Fano line (spectral) + 7 holonomy (2π, "
                f"{hol}) + 1 {mode}{mass_note}{mix_note}\n"
            )
            print_coherence(report)
            if args.compare_holonomy and continuous_xi:
                r_legacy = run_coherence(
                    args.shell_chart or "sector",
                    args.m_global,
                    args.scale_setter,
                    use_brace_instead_of_setter=True,
                    continuous_xi=True,
                    density_holonomy=False,
                )
                print("\n  Holonomy comparison (continuous brace, 15×7):")
                print(f"    log_phi holonomy only:     ||Ac-b|| = {r_legacy.residual:.6e}")
                print(
                    f"    {holonomy_k} holonomy+lines: ||Ac-b|| = {report.residual:.6e}  "
                    f"(ξ_v on v=0 from solved ξ_G)"
                )
            print("\n  All scale setters (same line+holonomy, one CODATA row each):")
            for setter in ScaleSetter.__args__:
                r = run_coherence(
                    args.shell_chart or "sector",
                    args.m_global,
                    setter,
                    use_brace_instead_of_setter=False,
                )
                em = next(x for x in r.readouts if x.name == "EM Gauss v0")
                br = next(
                    x for x in r.readouts if "braced" in x.name and "int" in x.name
                )
                print(
                    f"    {setter:26s}  1/α(Gauss)={em.inv_alpha_predicted:8.3f}  "
                    f"1/α(braced)={br.inv_alpha_predicted:8.3f}  ||c||={np.linalg.norm(r.c):.3f}"
                )
            if not continuous_xi:
                r_br = run_coherence(
                    args.shell_chart or "sector",
                    args.m_global,
                    args.scale_setter,
                    use_brace_instead_of_setter=True,
                    continuous_xi=False,
                )
                em_b = next(x for x in r_br.readouts if "int ξ" in x.name)
                print(
                    f"    {'em_shell_brace (int ξ)':26s}  1/α(braced)={em_b.inv_alpha_predicted:8.3f}"
                )
                r_cx = run_coherence(
                    args.shell_chart or "sector",
                    args.m_global,
                    args.scale_setter,
                    use_brace_instead_of_setter=True,
                    continuous_xi=True,
                    density_holonomy=density_holonomy,
                    holonomy_k_mode=holonomy_k,
                    holonomy_xi_mode=holonomy_xi,
                )
                cx = r_cx.continuous_xi
                if cx is not None:
                    print(
                        f"    {'continuous_xi_brace':26s}  ξ_G={cx.xi_g:.4f}  "
                        f"1/α@ξ_G={cx.inv_alpha_direct_at_xi_g:8.3f}  "
                        f"1/α(braced)={cx.inv_alpha_braced_at_xi_g:8.3f}"
                    )
            alt = run_one("line_plus_holonomy", "sector", args.m_global, "anchor_em")
            print("\n" + "=" * 72)
            print("line_plus_holonomy + anchor (no coherence loop):")
            print(f"  1/α(v=0)={alt.inv_alpha_em_vertex0:.4f}  shells={alt.shells}")
        return

    if args.system and args.shell_chart and args.rhs:
        runs = [run_one(args.system, args.shell_chart, args.m_global, args.rhs)]
    else:
        runs = []
        for kind in ("vertex_diagonal", "line_incidence", "line_incidence_monogamy"):
            for chart in ("uniform", "lockin", "sector"):
                for rhs in ("spectral_detuning", "anchor_em", "bare_gut"):
                    if kind == "line_incidence_monogamy" and rhs == "bare_gut":
                        continue
                    runs.append(run_one(kind, chart, args.m_global, rhs))

        # Closed-form spectral diagonal for comparison
        shells_sector = [shell_for_vertex(v, "sector", args.m_global) for v in range(7)]
        c_cf = closed_form_spectral_c(shells_sector)
        print("HQIV 7×7 Fano coupling linear system")
        print(f"  closed-form spectral_detuning (sector shells): c_v = (γ/2)m/k_φ")
        print(f"  shells={shells_sector}")
        print(f"  c_v  = {[round(x, 4) for x in c_cf]}")
        inv_cf = [one_over_alpha_eff(shells_sector[v], c_cf[v]) for v in range(7)]
        print(f"  1/α_v= {[round(x, 2) for x in inv_cf]}")
        print()

    if args.json:
        print(json.dumps([asdict(r) for r in runs], indent=2))
    else:
        print_report(runs)

        # Best CODATA proximity scan
        best = min(
            runs,
            key=lambda r: abs(r.inv_alpha_em_vertex0 - CODATA_INV_ALPHA),
        )
        print("\n" + "=" * 72)
        print("Closest 1/α(v=0) to CODATA among grid:")
        print(f"  {best.system} / {best.shell_chart} / rhs={best.rhs_mode}  →  {best.inv_alpha_em_vertex0:.4f}")
        best_ew = min(
            runs,
            key=lambda r: abs(r.inv_alpha_em_ew_shell - CODATA_INV_ALPHA),
        )
        print("Closest 1/α(v=0,c_v) at EW shell m=5 (same c_v[0]):")
        print(f"  {best_ew.system} / {best_ew.shell_chart} / rhs={best_ew.rhs_mode}  →  {best_ew.inv_alpha_em_ew_shell:.4f}")

        report = run_coherence("sector", args.m_global, args.scale_setter)
        print("\n" + "=" * 72)
        print_coherence(report)


if __name__ == "__main__":
    main()
