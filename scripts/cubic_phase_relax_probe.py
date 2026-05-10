#!/usr/bin/env python3
"""
Numeric mirror of the relaxed-quarter / cubic-phase HQIV readouts.

This script mirrors the closed-form Lean definitions from:

- `Hqiv/Geometry/OctonionicLightCone.lean`
- `Hqiv/Physics/FanoResonance.lean`
- `Hqiv/Physics/TrialityRapidityWellEquivalence.lean`
- `Hqiv/Physics/QuarterPeriodRelaxation.lean`
- `Hqiv/Physics/LeptonGenerationLockin.lean`
- `Hqiv/Physics/LeptonResonanceGlobalDetuning.lean`
- `Hqiv/Physics/QuarkMetaResonance.lean`

Formal “where does Clay YM connect?” inventory (proved Story vs Dojo witness gap):
`Hqiv/Story/MassGapWiring.lean` (`HQIVStory` import).

Why Python? The relevant Lean values are `noncomputable` because they route through
`Real.log`, `Real.sqrt`, and threshold search over the same real-valued expressions.

Run:
  python3 scripts/cubic_phase_relax_probe.py
  python3 scripts/cubic_phase_relax_probe.py --json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from itertools import product


# ---------------------------------------------------------------------------
# HQIV constants mirrored from Lean

ALPHA = 3.0 / 5.0
GAMMA = 2.0 / 5.0
C_RINDLER_SHARED = GAMMA / 2.0  # = 1/5

QCD_SHELL = 1
LATTICE_STEP_COUNT = 3
REFERENCE_M = QCD_SHELL + LATTICE_STEP_COUNT  # = 4
M_LOCKIN = REFERENCE_M

PHI_TEMPERATURE_COEFF = 2.0
CHARGED_LEPTON_TAU_MU_THRESHOLD = 9.0 / 4.0
CHARGED_LEPTON_MU_E_THRESHOLD = 16.0 / 9.0

M_TOP_GEV = 172.57
M_BOTTOM_GEV = 4.18
CHARM_SANITY_TARGET_GEV = 1.27
UP_TARGET_GEV = 0.0022
STRANGE_TARGET_GEV = 0.095
DOWN_TARGET_GEV = 0.0047

# Top anchor from the baryogenesis/lock-in side ("now"-corrected external anchor).
TOP_ANCHOR_COORD = 31382.0
# Quark standing-wave complexity evaluation band (S7/S3 control channel).
QUARK_COMPLEXITY_ELL = 2
# "Now" scaling for complexity transfer into coordinate descent.
LAMBDA_NOW = 1.0 + GAMMA
# Real-axis angular amplification exponent.
ANGLE_REAL_AXIS_POWER = 1.0

ALL_BRIDGES = ("s7", "s3", "s4")
ALL_ELLS = (0, 1, 2, 3)

LAYER_SPIN_ONLY = 1
LAYER_CHARGED = 2
LAYER_QUARK = 3

# Lean-aligned SM embedding hypercharge table (`Hqiv.Algebra.SMEmbedding.hyperchargeEigenvalue`)
SM_HYPERCHARGE_EIGENVALUE: dict[int, float] = {
    0: 1.0 / 6.0,
    1: 1.0 / 6.0,
    2: -2.0 / 3.0,
    3: 1.0 / 3.0,
    4: -1.0 / 2.0,
    5: -1.0 / 2.0,
    6: 1.0,
    7: 0.0,
}

# Particle -> SM embedding component index, mirroring `smHyperchargeWeight` in
# `Hqiv/Physics/SM_GR_Unification.lean`.
SM_PARTICLE_HYPERCHARGE_INDEX: dict[str, int] = {
    "e": 6,
    "mu": 6,
    "tau": 6,
    "u": 2,
    "c": 2,
    "t": 2,
    "d": 3,
    "s": 3,
    "b": 3,
    "nu_e": 7,
    "nu_mu": 7,
    "nu_tau": 7,
}


# ---------------------------------------------------------------------------
# Lean-mirrored geometry / detuning


def shell_surface(m: float) -> float:
    return (m + 1.0) * (m + 2.0)


def rindler_detuning_shared(x: float) -> float:
    return 1.0 + C_RINDLER_SHARED * x


def detuned_surface(m: float) -> float:
    return shell_surface(m) / rindler_detuning_shared(m)


def eff_corrected(delta: float, m: float) -> float:
    den = rindler_detuning_shared(m) + delta
    if den <= 0.0:
        raise ValueError("nonpositive detuning denominator in eff_corrected")
    return shell_surface(m) / den


def geometric_resonance_step(m_from: float, m_to: float) -> float:
    return detuned_surface(m_from) / detuned_surface(m_to)


def curvature_density(x: float) -> float:
    return (1.0 / x) * (1.0 + ALPHA * math.log(x))


def shell_shape(m: int) -> float:
    return curvature_density(float(m + 1))


def curvature_integral(n: int) -> float:
    return sum(abs(shell_shape(m)) for m in range(n))


def curvature_integral_real(s: float) -> float:
    if s <= 0.0:
        return 0.0
    # Continuous extension of Σ_m shell_shape(m) on x = s + 1:
    # ∫ (1/x)*(1 + α log x) dx = log x + α/2 * (log x)^2.
    x = s + 1.0
    lx = math.log(x)
    return lx + 0.5 * ALPHA * lx * lx


def omega_k_at_horizon(n: int, horizon_n: int) -> float:
    denom = curvature_integral(horizon_n)
    if denom <= 0.0:
        return 1.0
    return curvature_integral(n) / denom


def omega_k_at_horizon_real(s: float, horizon_s: float) -> float:
    denom = curvature_integral_real(horizon_s)
    if denom <= 0.0:
        return 1.0
    return curvature_integral_real(s) / denom


def rapidity_cp_bias(m: float) -> float:
    return omega_k_at_horizon_real(m, float(M_LOCKIN)) - 1.0


# ---------------------------------------------------------------------------
# Triality cubic phases / spectral weights


REP_8V = "8v"
REP_8S_PLUS = "8s+"
REP_8S_MINUS = "8s-"
ALL_REPS = (REP_8V, REP_8S_PLUS, REP_8S_MINUS)


def triality_cp_orientation(rep: str) -> float:
    if rep == REP_8V:
        return 0.0
    if rep == REP_8S_PLUS:
        return 1.0
    if rep == REP_8S_MINUS:
        return -1.0
    raise ValueError(f"unknown rep {rep}")


def triality_cubic_phase_angle(rep: str) -> float:
    return (2.0 * math.pi / 3.0) * triality_cp_orientation(rep)


def triality_cubic_phase_amplitude(rep: str) -> float:
    return abs(math.sin(triality_cubic_phase_angle(rep)))


def laplace_beltrami_eigenvalue_s7(ell: int) -> float:
    return float(ell * (ell + 6))


def laplace_beltrami_eigenvalue_s3(ell: int) -> float:
    return float(ell * (ell + 2))


def laplace_beltrami_eigenvalue_s4(ell: int) -> float:
    return float(ell * (ell + 3))


def spectral_mode_omega(bridge: str, ell: int) -> float:
    if bridge == "s7":
        lam = laplace_beltrami_eigenvalue_s7(ell)
    elif bridge == "s3":
        lam = laplace_beltrami_eigenvalue_s3(ell)
    elif bridge == "s4":
        lam = laplace_beltrami_eigenvalue_s4(ell)
    else:
        raise ValueError(f"unknown bridge {bridge}")
    return math.sqrt(lam + 1.0)


def spectral_relaxation_weight(bridge: str, ell: int) -> float:
    return math.log(spectral_mode_omega(bridge, ell) + 1.0)


def quarter_relaxation_load(bridge: str, rep: str, spectral_mode_idx: int, m: float) -> float:
    return (
        triality_cubic_phase_amplitude(rep)
        * spectral_relaxation_weight(bridge, spectral_mode_idx)
        * abs(rapidity_cp_bias(m))
    )


def relaxed_detuning_readout(bridge: str, rep: str, spectral_mode_idx: int, m: float) -> float:
    return rindler_detuning_shared(m) * (1.0 + quarter_relaxation_load(bridge, rep, spectral_mode_idx, m))


def relaxed_detuned_surface_readout(bridge: str, rep: str, spectral_mode_idx: int, m: float) -> float:
    return shell_surface(m) / relaxed_detuning_readout(bridge, rep, spectral_mode_idx, m)


def relaxed_geometric_step_readout(
    bridge: str, rep: str, spectral_mode_idx: int, m_from: float, m_to: float
) -> float:
    return (
        relaxed_detuned_surface_readout(bridge, rep, spectral_mode_idx, m_from)
        / relaxed_detuned_surface_readout(bridge, rep, spectral_mode_idx, m_to)
    )


def rep_short_name(rep: str) -> str:
    return rep


# ---------------------------------------------------------------------------
# Lepton readout search and Koide-style invariant


def first_coordinate_at_or_above_threshold(current_s: float, threshold: float) -> float:
    if threshold <= 1.0:
        return current_s
    lo = current_s
    hi = current_s + 1.0
    while geometric_resonance_step(hi, current_s) < threshold:
        hi += 1.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if geometric_resonance_step(mid, current_s) >= threshold:
            hi = mid
        else:
            lo = mid
    return hi


def first_coordinate_at_or_below_ratio(from_s: float, ratio_target: float) -> float:
    if ratio_target <= 1.0:
        return from_s
    lo = 0.0
    hi = from_s
    if geometric_resonance_step(from_s, lo) < ratio_target:
        return lo
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if geometric_resonance_step(from_s, mid) >= ratio_target:
            lo = mid
        else:
            hi = mid
    return lo


def s7_pole_projection(pole_count: int) -> float:
    if pole_count <= 0:
        return 1.0
    ell_eff = max(1, QUARK_COMPLEXITY_ELL * pole_count)
    return math.exp(spectral_relaxation_weight("s7", ell_eff))


def sphere_phase_angle_to_real_axis(bridge: str, ell: int, pole_count: int = 1) -> float:
    ell_eff = max(1, ell * max(1, pole_count))
    omega = spectral_mode_omega(bridge, ell_eff)
    return math.atan(omega)


def real_axis_projection(bridge: str, ell: int, pole_count: int = 1) -> float:
    theta = sphere_phase_angle_to_real_axis(bridge, ell, pole_count)
    return abs(math.cos(theta))


def complexity_threshold_from_geometry(bridge: str, ell: int, pole_count: int = 1) -> float:
    ell_eff = max(1, ell * max(1, pole_count))
    raw = math.exp(spectral_relaxation_weight(bridge, ell_eff))
    proj = max(real_axis_projection(bridge, ell, pole_count), 1.0e-9)
    angular_amp = (1.0 / proj) ** ANGLE_REAL_AXIS_POWER
    return 1.0 + LAMBDA_NOW * (raw - 1.0) * angular_amp


def derived_lepton_coordinates() -> tuple[float, float, float]:
    s_tau = float(REFERENCE_M)
    s_mu = first_coordinate_at_or_above_threshold(s_tau, CHARGED_LEPTON_TAU_MU_THRESHOLD)
    s_e = first_coordinate_at_or_above_threshold(s_mu, CHARGED_LEPTON_MU_E_THRESHOLD)
    return s_tau, s_mu, s_e


def derived_quark_coordinates() -> tuple[float, float, float, float, float, float]:
    # Continuous quark coordinates from top anchor downward:
    #   standing-wave complexity on S7/S3 sets all descent ratios.
    #   Up-like quarks carry two hypercharge poles on S7; down-like carry one.
    s_top = TOP_ANCHOR_COORD
    complexity_s7_up = complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=2)
    complexity_s7_down = complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=1)
    complexity_s3 = complexity_threshold_from_geometry("s3", QUARK_COMPLEXITY_ELL, pole_count=1)
    hyper_drop = complexity_s7_up / max(complexity_s7_down, 1.0e-9)

    # 2-hypercharge to 1-hypercharge channel transfer.
    s_bottom = first_coordinate_at_or_below_ratio(s_top, hyper_drop)

    # Up ladder (top -> charm -> up) controlled by S7 then S3 complexity.
    s_charm = first_coordinate_at_or_below_ratio(s_top, complexity_s7_up)
    s_up = first_coordinate_at_or_below_ratio(s_charm, complexity_s3)

    # Down ladder (bottom -> strange -> down) mirrors the same complexity pattern.
    s_strange = first_coordinate_at_or_below_ratio(s_bottom, complexity_s7_down)
    s_down = first_coordinate_at_or_below_ratio(s_strange, complexity_s3)

    return s_top, s_charm, s_up, s_bottom, s_strange, s_down


def lepton_masses_from_ratios(k_tau_mu: float, k_mu_e: float, tau_anchor: float = 1.0) -> tuple[float, float, float]:
    m_tau = tau_anchor
    m_mu = m_tau / k_tau_mu
    m_e = m_mu / k_mu_e
    return m_tau, m_mu, m_e


def koide_q(m_tau: float, m_mu: float, m_e: float) -> float:
    denom = (math.sqrt(m_tau) + math.sqrt(m_mu) + math.sqrt(m_e)) ** 2
    return (m_tau + m_mu + m_e) / denom


@dataclass(frozen=True)
class LeptonProbe:
    s_tau: float
    s_mu: float
    s_e: float
    k_tau_mu_base: float
    k_mu_e_base: float
    k_tau_mu_relaxed_s7: float
    k_mu_e_relaxed_s7: float
    k_tau_mu_relaxed_s3: float
    k_mu_e_relaxed_s3: float
    koide_q_base: float
    koide_q_relaxed_s7: float
    koide_q_relaxed_s3: float


def compute_lepton_probe() -> LeptonProbe:
    s_tau, s_mu, s_e = derived_lepton_coordinates()

    k_tau_mu_base = geometric_resonance_step(s_mu, s_tau)
    k_mu_e_base = geometric_resonance_step(s_e, s_mu)

    k_tau_mu_relaxed_s7 = relaxed_geometric_step_readout("s7", REP_8S_MINUS, 1, s_mu, s_tau)
    k_mu_e_relaxed_s7 = relaxed_geometric_step_readout("s7", REP_8S_PLUS, 1, s_e, s_mu)

    k_tau_mu_relaxed_s3 = relaxed_geometric_step_readout("s3", REP_8S_MINUS, 1, s_mu, s_tau)
    k_mu_e_relaxed_s3 = relaxed_geometric_step_readout("s3", REP_8S_PLUS, 1, s_e, s_mu)
    koide_q_base = koide_q(*lepton_masses_from_ratios(k_tau_mu_base, k_mu_e_base))
    koide_q_relaxed_s7 = koide_q(*lepton_masses_from_ratios(k_tau_mu_relaxed_s7, k_mu_e_relaxed_s7))
    koide_q_relaxed_s3 = koide_q(*lepton_masses_from_ratios(k_tau_mu_relaxed_s3, k_mu_e_relaxed_s3))

    return LeptonProbe(
        s_tau=s_tau,
        s_mu=s_mu,
        s_e=s_e,
        k_tau_mu_base=k_tau_mu_base,
        k_mu_e_base=k_mu_e_base,
        k_tau_mu_relaxed_s7=k_tau_mu_relaxed_s7,
        k_mu_e_relaxed_s7=k_mu_e_relaxed_s7,
        k_tau_mu_relaxed_s3=k_tau_mu_relaxed_s3,
        k_mu_e_relaxed_s3=k_mu_e_relaxed_s3,
        koide_q_base=koide_q_base,
        koide_q_relaxed_s7=koide_q_relaxed_s7,
        koide_q_relaxed_s3=koide_q_relaxed_s3,
    )


# ---------------------------------------------------------------------------
# Quark-side mirrors


@dataclass(frozen=True)
class QuarkProbe:
    charm_base_gev: float
    up_base_gev: float
    strange_base_gev: float
    down_base_gev: float
    charm_s7_gev: float
    up_s7_gev: float
    strange_s7_gev: float
    down_s7_gev: float
    charm_s4_gev: float
    up_s4_gev: float
    strange_s4_gev: float
    down_s4_gev: float


@dataclass(frozen=True)
class CurrentCharmDiagnostic:
    current_bridge: str
    current_ell: int
    current_rep_top_to_charm: str
    current_rep_charm_to_up: str
    base_top_to_charm_step: float
    relaxed_top_to_charm_step: float
    base_charm_gev: float
    relaxed_charm_gev: float
    cubic_phase_amplitude: float
    spectral_weight: float
    top_cp_bias_abs: float
    charm_cp_bias_abs: float
    top_relax_load: float
    charm_relax_load: float
    top_detuning_base: float
    charm_detuning_base: float
    top_detuning_relaxed: float
    charm_detuning_relaxed: float


@dataclass(frozen=True)
class SweepRow:
    rank_score: float
    koide_delta_from_third: float
    charm_log_error: float
    charm_rel_error: float
    bridge: str
    ell: int
    tau_rep: str
    mu_rep: str
    top_rep: str
    charm_rep: str
    k_tau_mu: float
    k_mu_e: float
    koide_q_value: float
    charm_gev: float
    up_gev: float


@dataclass(frozen=True)
class PrimaryModeSummary:
    mode: str
    base_charm_gev: float
    base_charm_rel_error: float
    best_relaxed_charm_gev: float
    best_relaxed_charm_rel_error: float
    relaxed_beats_base: bool


@dataclass(frozen=True)
class ContentLayerMassRow:
    particle: str
    coord_s: float
    layer_l: int
    model_gev: float
    ref_gev: float | None
    rel_err_pct: float | None


@dataclass(frozen=True)
class ContentLayerSummary:
    normalization_k: float
    top_anchor_coord: float
    top_anchor_mass_gev: float
    delta_global: float
    component_power: float
    spin_coupling: float
    charge_coupling: float
    hypercharge_coupling: float
    rows: list[ContentLayerMassRow]


@dataclass(frozen=True)
class ContentLayerParams:
    component_power: float = 2.0
    spin_coupling: float = 1.0
    charge_coupling: float = 1.0
    hypercharge_coupling: float = 0.25
    delta_global: float = 0.0


@dataclass(frozen=True)
class ContentLayerScanRow:
    score: float
    component_power: float
    spin_coupling: float
    charge_coupling: float
    hypercharge_coupling: float
    delta_global: float
    charm_gev: float
    electron_gev: float
    nu_e_gev: float


def compute_quark_probe() -> QuarkProbe:
    s_top, s_charm, s_up, s_bottom, s_strange, s_down = derived_quark_coordinates()
    k_top_charm_base = geometric_resonance_step(s_top, s_charm)
    k_charm_up_base = geometric_resonance_step(s_charm, s_up)
    k_bottom_strange_base = geometric_resonance_step(s_bottom, s_strange)
    k_strange_down_base = geometric_resonance_step(s_strange, s_down)

    charm_base = M_TOP_GEV / k_top_charm_base
    up_base = charm_base / k_charm_up_base
    strange_base = M_BOTTOM_GEV / k_bottom_strange_base
    down_base = strange_base / k_strange_down_base

    k_top_charm_s7 = relaxed_geometric_step_readout("s7", REP_8S_PLUS, 2, s_top, s_charm)
    k_charm_up_s7 = relaxed_geometric_step_readout("s7", REP_8S_PLUS, 2, s_charm, s_up)
    k_bottom_strange_s7 = relaxed_geometric_step_readout("s7", REP_8V, 2, s_bottom, s_strange)
    k_strange_down_s7 = relaxed_geometric_step_readout("s7", REP_8V, 2, s_strange, s_down)

    charm_s7 = M_TOP_GEV / k_top_charm_s7
    up_s7 = charm_s7 / k_charm_up_s7
    strange_s7 = M_BOTTOM_GEV / k_bottom_strange_s7
    down_s7 = strange_s7 / k_strange_down_s7

    k_top_charm_s4 = relaxed_geometric_step_readout("s4", REP_8S_PLUS, 2, s_top, s_charm)
    k_charm_up_s4 = relaxed_geometric_step_readout("s4", REP_8S_PLUS, 2, s_charm, s_up)
    k_bottom_strange_s4 = relaxed_geometric_step_readout("s4", REP_8V, 2, s_bottom, s_strange)
    k_strange_down_s4 = relaxed_geometric_step_readout("s4", REP_8V, 2, s_strange, s_down)

    charm_s4 = M_TOP_GEV / k_top_charm_s4
    up_s4 = charm_s4 / k_charm_up_s4
    strange_s4 = M_BOTTOM_GEV / k_bottom_strange_s4
    down_s4 = strange_s4 / k_strange_down_s4

    return QuarkProbe(
        charm_base_gev=charm_base,
        up_base_gev=up_base,
        strange_base_gev=strange_base,
        down_base_gev=down_base,
        charm_s7_gev=charm_s7,
        up_s7_gev=up_s7,
        strange_s7_gev=strange_s7,
        down_s7_gev=down_s7,
        charm_s4_gev=charm_s4,
        up_s4_gev=up_s4,
        strange_s4_gev=strange_s4,
        down_s4_gev=down_s4,
    )


def compute_current_charm_diagnostic() -> CurrentCharmDiagnostic:
    current_bridge = "s7"
    current_ell = 2
    current_rep_top_to_charm = REP_8S_PLUS
    current_rep_charm_to_up = REP_8S_PLUS
    s_top, s_charm, _, _, _, _ = derived_quark_coordinates()

    base_top_to_charm_step = geometric_resonance_step(s_top, s_charm)
    relaxed_top_to_charm_step = relaxed_geometric_step_readout(
        current_bridge, current_rep_top_to_charm, current_ell, s_top, s_charm
    )

    top_relax_load = quarter_relaxation_load(current_bridge, current_rep_top_to_charm, current_ell, s_top)
    charm_relax_load = quarter_relaxation_load(current_bridge, current_rep_top_to_charm, current_ell, s_charm)

    top_detuning_base = rindler_detuning_shared(s_top)
    charm_detuning_base = rindler_detuning_shared(s_charm)
    return CurrentCharmDiagnostic(
        current_bridge=current_bridge,
        current_ell=current_ell,
        current_rep_top_to_charm=current_rep_top_to_charm,
        current_rep_charm_to_up=current_rep_charm_to_up,
        base_top_to_charm_step=base_top_to_charm_step,
        relaxed_top_to_charm_step=relaxed_top_to_charm_step,
        base_charm_gev=M_TOP_GEV / base_top_to_charm_step,
        relaxed_charm_gev=M_TOP_GEV / relaxed_top_to_charm_step,
        cubic_phase_amplitude=triality_cubic_phase_amplitude(current_rep_top_to_charm),
        spectral_weight=spectral_relaxation_weight(current_bridge, current_ell),
        top_cp_bias_abs=abs(rapidity_cp_bias(s_top)),
        charm_cp_bias_abs=abs(rapidity_cp_bias(s_charm)),
        top_relax_load=top_relax_load,
        charm_relax_load=charm_relax_load,
        top_detuning_base=top_detuning_base,
        charm_detuning_base=charm_detuning_base,
        top_detuning_relaxed=top_detuning_base * (1.0 + top_relax_load),
        charm_detuning_relaxed=charm_detuning_base * (1.0 + charm_relax_load),
    )


def build_primary_mode_summary(
    current_charm: CurrentCharmDiagnostic, sweep_rows: list[SweepRow]
) -> PrimaryModeSummary:
    base_rel_error = abs(current_charm.base_charm_gev - CHARM_SANITY_TARGET_GEV) / CHARM_SANITY_TARGET_GEV
    best_relaxed = min(sweep_rows, key=lambda row: row.charm_rel_error)
    relaxed_beats_base = best_relaxed.charm_rel_error < base_rel_error
    return PrimaryModeSummary(
        mode="base",
        base_charm_gev=current_charm.base_charm_gev,
        base_charm_rel_error=base_rel_error,
        best_relaxed_charm_gev=best_relaxed.charm_gev,
        best_relaxed_charm_rel_error=best_relaxed.charm_rel_error,
        relaxed_beats_base=relaxed_beats_base,
    )


def _relative_error_pct(model: float, reference: float | None) -> float | None:
    if reference is None or reference == 0.0:
        return None
    return 100.0 * (model / reference - 1.0)


def _content_layer_mass_from_coord(k_norm: float, layer_l: int, coord_s: float, delta_global: float) -> float:
    return k_norm * float(layer_l * layer_l) * eff_corrected(delta_global, coord_s)


def build_content_layer_summary(params: ContentLayerParams | None = None) -> ContentLayerSummary:
    p = params or ContentLayerParams()
    # Nonlinear complexity + axis couplings:
    # - component complexity is superlinear in conserved-axis count;
    # - hypercharge enters through explicit per-particle metadata (slots and |Y|),
    #   not as an exponent in the coupling constant.
    delta_global = p.delta_global
    component_power = p.component_power
    spin_coupling = p.spin_coupling
    charge_coupling = p.charge_coupling
    hypercharge_coupling = p.hypercharge_coupling

    def component_complexity(component_count: int) -> float:
      return float(component_count) ** component_power

    # Sphere projection amplitudes for the active standing-wave channel.
    # - spin/charge content lives on S3;
    # - hypercharge content lives on S7 with pole-count dependence.
    s3_projection = math.exp(spectral_relaxation_weight("s3", QUARK_COMPLEXITY_ELL))

    # Per-particle axis metadata:
    # - charged leptons use spin+charge channels here (no hypercharge slot),
    #   matching current HQIV content-layer bookkeeping.
    # - quarks include explicit hypercharge slots and magnitudes.
    PARTICLE_AXIS_METADATA: dict[str, tuple[int, int, int]] = {
        "nu_e": (1, 0, 0),
        "nu_mu": (1, 0, 0),
        "nu_tau": (1, 0, 0),
        "e": (1, 1, 0),
        "mu": (1, 1, 0),
        "tau": (1, 1, 0),
        # up-type: spin + charge + two hypercharge-channel slots (e1, e4).
        "u": (1, 1, 2),
        "c": (1, 1, 2),
        "t": (1, 1, 2),
        # down-type: spin + charge + one hypercharge-channel slot.
        "d": (1, 1, 1),
        "s": (1, 1, 1),
        "b": (1, 1, 1),
    }

    def particle_hypercharge_abs(particle: str) -> float:
      sm_idx = SM_PARTICLE_HYPERCHARGE_INDEX[particle]
      return abs(SM_HYPERCHARGE_EIGENVALUE[sm_idx])

    def particle_axis_factor(particle: str) -> float:
      spin_slots, charge_slots, hyper_slots = PARTICLE_AXIS_METADATA[particle]
      hyper_abs_y = particle_hypercharge_abs(particle)
      active_axes = spin_slots + charge_slots + hyper_slots
      # Spin and electric-charge channels are S3-projected.
      s3_slots = spin_slots + charge_slots
      spin_charge_factor = (spin_coupling * charge_coupling * s3_projection) ** s3_slots
      # Hypercharge channel is S7-projected and only active for quarks.
      hyper_factor = 1.0 + hypercharge_coupling * s7_pole_projection(hyper_slots) * float(hyper_slots) * hyper_abs_y
      return component_complexity(active_axes) * spin_charge_factor * hyper_factor

    s_top, s_charm, s_up, s_bottom, s_strange, s_down = derived_quark_coordinates()
    top_axis_factor = particle_axis_factor("t")
    k_norm = M_TOP_GEV / (top_axis_factor * eff_corrected(delta_global, s_top))
    s_tau, s_mu, s_e = derived_lepton_coordinates()

    rows: list[ContentLayerMassRow] = []

    # Quarks (color-composed closure layer, l = 3)
    for name, coord_s, ref in (
        ("u", s_up, UP_TARGET_GEV),
        ("c", s_charm, CHARM_SANITY_TARGET_GEV),
        ("t", s_top, M_TOP_GEV),
        ("d", s_down, DOWN_TARGET_GEV),
        ("s", s_strange, STRANGE_TARGET_GEV),
        ("b", s_bottom, M_BOTTOM_GEV),
    ):
        model = k_norm * particle_axis_factor(name) * eff_corrected(delta_global, coord_s)
        rows.append(
            ContentLayerMassRow(
                particle=name,
                coord_s=coord_s,
                layer_l=LAYER_QUARK,
                model_gev=model,
                ref_gev=ref,
                rel_err_pct=_relative_error_pct(model, ref),
            )
        )

    # Charged leptons (charge-decorated closure layer, l = 2) using active ladder shells.
    for name, coord_s, ref in (
        ("e", s_e, 0.0005109989461),
        ("mu", s_mu, 0.1056583755),
        ("tau", s_tau, 1.77686),
    ):
        model = k_norm * particle_axis_factor(name) * eff_corrected(delta_global, coord_s)
        rows.append(
            ContentLayerMassRow(
                particle=name,
                coord_s=coord_s,
                layer_l=LAYER_CHARGED,
                model_gev=model,
                ref_gev=ref,
                rel_err_pct=_relative_error_pct(model, ref),
            )
        )

    # Neutrinos (spin-only closure layer, l = 1), same generation shells.
    # References are loose upper bounds in GeV for audit only.
    for name, coord_s, upper_bound in (
        ("nu_e", s_e, 8.0e-10),
        ("nu_mu", s_mu, 1.9e-7),
        ("nu_tau", s_tau, 1.8e-5),
    ):
        model = k_norm * particle_axis_factor(name) * eff_corrected(delta_global, coord_s)
        rows.append(
            ContentLayerMassRow(
                particle=name,
                coord_s=coord_s,
                layer_l=LAYER_SPIN_ONLY,
                model_gev=model,
                ref_gev=upper_bound,
                rel_err_pct=_relative_error_pct(model, upper_bound),
            )
        )

    return ContentLayerSummary(
        normalization_k=k_norm,
        top_anchor_coord=s_top,
        top_anchor_mass_gev=M_TOP_GEV,
        delta_global=delta_global,
        component_power=component_power,
        spin_coupling=spin_coupling,
        charge_coupling=charge_coupling,
        hypercharge_coupling=hypercharge_coupling,
        rows=rows,
    )


def _content_layer_score(summary: ContentLayerSummary) -> float:
    by_name = {r.particle: r for r in summary.rows}
    refs = {
        "u": 0.0022,
        "d": 0.0047,
        "s": 0.095,
        "c": 1.27,
        "b": 4.18,
        "e": 0.0005109989461,
        "mu": 0.1056583755,
        "tau": 1.77686,
    }
    # Core fit: log-error on charged fermions.
    core = 0.0
    for name, ref in refs.items():
        model = by_name[name].model_gev
        core += abs(math.log(model / ref))
    # Soft penalty on neutrino upper bounds (only when exceeding bound).
    nu_bounds = {"nu_e": 8.0e-10, "nu_mu": 1.9e-7, "nu_tau": 1.8e-5}
    nu_pen = 0.0
    for name, ub in nu_bounds.items():
        ratio = by_name[name].model_gev / ub
        if ratio > 1.0:
            nu_pen += math.log(ratio)
    return core + 0.2 * nu_pen


def build_content_layer_scan_report() -> dict[str, object]:
    # "Bring in Rindler and other things": use delta candidates from global + auxiliary terms.
    delta_candidates: set[float] = {0.0}
    for lam in (0.1, 0.2, 0.4):
        for big_phi in (0.0, 0.01, 0.05):
            for phi in (0.0, 0.01, 0.05):
                for t_coord in (0.0, 1.0):
                    for beta_cum in (0.0, 0.01, 0.05):
                        delta_global = lam * (big_phi + phi * t_coord)
                        delta_aux = delta_global + beta_cum * phi * t_coord
                        delta_candidates.add(round(delta_aux, 6))

    scan_rows: list[ContentLayerScanRow] = []
    for component_power in (1.5, 2.0, 2.5, 3.0):
        for spin_coupling in (0.25, 0.5, 1.0):
            for charge_coupling in (0.5, 1.0, 2.0, 4.0):
                for hypercharge_coupling in (0.0, 0.1, 0.25, 0.5, 1.0):
                    for delta_global in sorted(delta_candidates):
                        params = ContentLayerParams(
                            component_power=component_power,
                            spin_coupling=spin_coupling,
                            charge_coupling=charge_coupling,
                            hypercharge_coupling=hypercharge_coupling,
                            delta_global=delta_global,
                        )
                        summary = build_content_layer_summary(params)
                        by_name = {r.particle: r for r in summary.rows}
                        scan_rows.append(
                            ContentLayerScanRow(
                                score=_content_layer_score(summary),
                                component_power=component_power,
                                spin_coupling=spin_coupling,
                                charge_coupling=charge_coupling,
                                hypercharge_coupling=hypercharge_coupling,
                                delta_global=delta_global,
                                charm_gev=by_name["c"].model_gev,
                                electron_gev=by_name["e"].model_gev,
                                nu_e_gev=by_name["nu_e"].model_gev,
                            )
                        )

    scan_rows.sort(key=lambda r: r.score)
    return {
        "mode": "content_layers_scan",
        "top_20": [asdict(r) for r in scan_rows[:20]],
    }


def compute_sweep_rows() -> list[SweepRow]:
    s_tau, s_mu, s_e = derived_lepton_coordinates()
    s_top, s_charm, s_up, _, _, _ = derived_quark_coordinates()
    rows: list[SweepRow] = []

    for bridge, ell, tau_rep, mu_rep, top_rep, charm_rep in product(
        ALL_BRIDGES, ALL_ELLS, ALL_REPS, ALL_REPS, ALL_REPS, ALL_REPS
    ):
        k_tau_mu = relaxed_geometric_step_readout(bridge, tau_rep, ell, s_mu, s_tau)
        k_mu_e = relaxed_geometric_step_readout(bridge, mu_rep, ell, s_e, s_mu)
        koide_q_value = koide_q(*lepton_masses_from_ratios(k_tau_mu, k_mu_e))
        koide_delta = abs(koide_q_value - (1.0 / 3.0))

        k_top_charm = relaxed_geometric_step_readout(bridge, top_rep, ell, s_top, s_charm)
        k_charm_up = relaxed_geometric_step_readout(bridge, charm_rep, ell, s_charm, s_up)
        charm_gev = M_TOP_GEV / k_top_charm
        up_gev = charm_gev / k_charm_up

        charm_log_error = abs(math.log(charm_gev / CHARM_SANITY_TARGET_GEV))
        charm_rel_error = abs(charm_gev - CHARM_SANITY_TARGET_GEV) / CHARM_SANITY_TARGET_GEV
        rank_score = koide_delta + charm_log_error

        rows.append(
            SweepRow(
                rank_score=rank_score,
                koide_delta_from_third=koide_delta,
                charm_log_error=charm_log_error,
                charm_rel_error=charm_rel_error,
                bridge=bridge,
                ell=ell,
                tau_rep=tau_rep,
                mu_rep=mu_rep,
                top_rep=top_rep,
                charm_rep=charm_rep,
                k_tau_mu=k_tau_mu,
                k_mu_e=k_mu_e,
                koide_q_value=koide_q_value,
                charm_gev=charm_gev,
                up_gev=up_gev,
            )
        )

    rows.sort(key=lambda row: (row.rank_score, row.koide_delta_from_third, row.charm_log_error))
    return rows


# ---------------------------------------------------------------------------
# CLI


def build_report() -> dict[str, object]:
    lepton = compute_lepton_probe()
    quark = compute_quark_probe()
    current_charm = compute_current_charm_diagnostic()
    sweep_rows = compute_sweep_rows()
    primary = build_primary_mode_summary(current_charm, sweep_rows)
    headline_relaxed = [row for row in sweep_rows if row.charm_rel_error < primary.base_charm_rel_error]
    top_relaxed = headline_relaxed[:25]
    weights = {
        f"ell_{ell}": {bridge: spectral_relaxation_weight(bridge, ell) for bridge in ALL_BRIDGES}
        for ell in ALL_ELLS
    }
    return {
        "constants": {
            "alpha": ALPHA,
            "gamma": GAMMA,
            "c_rindler_shared": C_RINDLER_SHARED,
            "referenceM": REFERENCE_M,
            "top_anchor_coord": TOP_ANCHOR_COORD,
            "quark_complexity_ell": QUARK_COMPLEXITY_ELL,
            "lambda_now": LAMBDA_NOW,
            "angle_real_axis_power": ANGLE_REAL_AXIS_POWER,
            "complexity_s7_threshold": math.exp(spectral_relaxation_weight("s7", QUARK_COMPLEXITY_ELL)),
            "complexity_s3_threshold": math.exp(spectral_relaxation_weight("s3", QUARK_COMPLEXITY_ELL)),
            "complexity_s7_up_2pole": complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=2),
            "complexity_s7_down_1pole": complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=1),
            "complexity_s3_spin_charge": complexity_threshold_from_geometry("s3", QUARK_COMPLEXITY_ELL, pole_count=1),
            "hypercharge_channel_drop": complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=2)
            / complexity_threshold_from_geometry("s7", QUARK_COMPLEXITY_ELL, pole_count=1),
        },
        "spectral_relaxation_weights": weights,
        "primary_mode_summary": asdict(primary),
        "current_charm_diagnostic": asdict(current_charm),
        "leptons": asdict(lepton),
        "quarks": asdict(quark),
        "grid_search_top_25": [asdict(row) for row in sweep_rows[:25]],
        "headline_relaxed_top_25_that_beat_base": [asdict(row) for row in top_relaxed],
    }


def build_content_layer_report() -> dict[str, object]:
    summary = build_content_layer_summary()
    return {
        "mode": "content_layers",
        "content_layer_summary": {
            "normalization_k": summary.normalization_k,
            "top_anchor_coord": summary.top_anchor_coord,
            "top_anchor_mass_gev": summary.top_anchor_mass_gev,
            "delta_global": summary.delta_global,
            "component_power": summary.component_power,
            "spin_coupling": summary.spin_coupling,
            "charge_coupling": summary.charge_coupling,
            "hypercharge_coupling": summary.hypercharge_coupling,
            "rows": [asdict(r) for r in summary.rows],
        },
    }


def print_human_report(report: dict[str, object]) -> None:
    print("== Cubic phase / relaxed-quarter probe ==")
    print()

    print("-- spectral log(omega + 1) weights --")
    for ell, values in report["spectral_relaxation_weights"].items():
        print(f"  {ell}: " + ", ".join(f"{k}={v:.9f}" for k, v in values.items()))
    print()

    primary = report["primary_mode_summary"]
    print("-- primary mode selection --")
    print(
        f"  primary mode: {primary['mode']} (base is authoritative unless relaxed beats base)"
    )
    print(
        f"  base charm={primary['base_charm_gev']:.9f} GeV  "
        f"rel_err={100.0 * primary['base_charm_rel_error']:.6f}%"
    )
    print(
        f"  best relaxed charm={primary['best_relaxed_charm_gev']:.9f} GeV  "
        f"rel_err={100.0 * primary['best_relaxed_charm_rel_error']:.6f}%"
    )
    print(f"  relaxed beats base: {primary['relaxed_beats_base']}")
    print()

    diag = report["current_charm_diagnostic"]
    print("-- quick diagnostic: why is current charm high? --")
    print(
        "  current top→charm assignment: "
        f"bridge={diag['current_bridge']}  ell={diag['current_ell']}  rep={diag['current_rep_top_to_charm']}"
    )
    print(
        "  ingredients: "
        f"cubic_amplitude={diag['cubic_phase_amplitude']:.9f}  "
        f"spectral_weight={diag['spectral_weight']:.9f}"
    )
    print(
        "  CP-bias magnitudes: "
        f"|bias(top)|={diag['top_cp_bias_abs']:.9f}  |bias(charm)|={diag['charm_cp_bias_abs']:.9f}"
    )
    print(
        "  relaxation loads: "
        f"load(top)={diag['top_relax_load']:.9f}  load(charm)={diag['charm_relax_load']:.9f}"
    )
    print(
        "  detuning: "
        f"base(top)={diag['top_detuning_base']:.9f} -> relaxed(top)={diag['top_detuning_relaxed']:.9f}; "
        f"base(charm)={diag['charm_detuning_base']:.9f} -> relaxed(charm)={diag['charm_detuning_relaxed']:.9f}"
    )
    print(
        "  step compression: "
        f"base_k={diag['base_top_to_charm_step']:.9f} -> relaxed_k={diag['relaxed_top_to_charm_step']:.9f}; "
        f"base_charm={diag['base_charm_gev']:.9f} GeV -> relaxed_charm={diag['relaxed_charm_gev']:.9f} GeV"
    )
    print()

    lep = report["leptons"]
    print("-- leptons --")
    print(f"  coordinates: tau={lep['s_tau']:.6f}  mu={lep['s_mu']:.6f}  e={lep['s_e']:.6f}")
    print(f"  base steps:        k_tau_mu={lep['k_tau_mu_base']:.12f}  k_mu_e={lep['k_mu_e_base']:.12f}")
    print(f"  relaxed S7 steps:  k_tau_mu={lep['k_tau_mu_relaxed_s7']:.12f}  k_mu_e={lep['k_mu_e_relaxed_s7']:.12f}")
    print(f"  relaxed S3 steps:  k_tau_mu={lep['k_tau_mu_relaxed_s3']:.12f}  k_mu_e={lep['k_mu_e_relaxed_s3']:.12f}")
    print(f"  Koide Q base:      {lep['koide_q_base']:.12f}")
    print(f"  Koide Q relaxed S7:{lep['koide_q_relaxed_s7']:.12f}")
    print(f"  Koide Q relaxed S3:{lep['koide_q_relaxed_s3']:.12f}")
    print()

    q = report["quarks"]
    print("-- quarks (GeV) --")
    print(
        "  base: "
        f"charm={q['charm_base_gev']:.12f}, up={q['up_base_gev']:.12f}, "
        f"strange={q['strange_base_gev']:.12f}, down={q['down_base_gev']:.12f}"
    )
    print(
        "  S7: "
        f"charm={q['charm_s7_gev']:.12f}, up={q['up_s7_gev']:.12f}, "
        f"strange={q['strange_s7_gev']:.12f}, down={q['down_s7_gev']:.12f}"
    )
    print(
        "  S4: "
        f"charm={q['charm_s4_gev']:.12f}, up={q['up_s4_gev']:.12f}, "
        f"strange={q['strange_s4_gev']:.12f}, down={q['down_s4_gev']:.12f}"
    )
    print()

    print("-- grid search: top 25 by |Koide Q - 1/3| + |log(charm / 1.27 GeV)| --")
    print(
        "  note: active step reps are tau_rep (tau→mu), mu_rep (mu→e), "
        "top_rep (top→charm), charm_rep (charm→up)"
    )
    header = (
        "  rank  score        dQ           dlog_charm   charm[GeV]    Q            "
        "bridge ell  tau   mu    top   charm"
    )
    print(header)
    for idx, row in enumerate(report["grid_search_top_25"], start=1):
        print(
            f"  {idx:>2}    "
            f"{row['rank_score']:<11.9f} "
            f"{row['koide_delta_from_third']:<12.9f} "
            f"{row['charm_log_error']:<12.9f} "
            f"{row['charm_gev']:<13.9f} "
            f"{row['koide_q_value']:<12.9f} "
            f"{row['bridge']:<6} {row['ell']:<3}  "
            f"{rep_short_name(row['tau_rep']):<4}  "
            f"{rep_short_name(row['mu_rep']):<4}  "
            f"{rep_short_name(row['top_rep']):<4}  "
            f"{rep_short_name(row['charm_rep']):<4}"
        )
    print()
    filtered = report["headline_relaxed_top_25_that_beat_base"]
    print("-- headline relaxed candidates that beat base (strict charm error) --")
    if not filtered:
        print("  none (base remains primary)")
    else:
        print("  showing up to 25 rows")
        for idx, row in enumerate(filtered, start=1):
            print(
                f"  {idx:>2} charm={row['charm_gev']:.9f} GeV "
                f"rel_err={100.0 * row['charm_rel_error']:.6f}% "
                f"bridge={row['bridge']} ell={row['ell']} "
                f"tau={rep_short_name(row['tau_rep'])} mu={rep_short_name(row['mu_rep'])} "
                f"top={rep_short_name(row['top_rep'])} charm_rep={rep_short_name(row['charm_rep'])}"
            )
    print()
    print("  degeneracy note:")
    print("    - `8s+` and `8s-` tie whenever only the cubic amplitude matters, because")
    print("      the current load uses `abs(sin(2π/3 * orientation))`.")
    print("    - `8v` zeroes the cubic load entirely, so any row with `top_rep=8v` leaves")
    print("      the top→charm step at the base detuned value (hence charm ≈ 1.27 GeV).")
    print("    - `charm_rep` affects the charm→up step, but not the charm sanity score.")


def print_content_layer_report(report: dict[str, object]) -> None:
    payload = report["content_layer_summary"]
    print("== Content-layer mass mode (top-only anchor) ==")
    print()
    print(
        f"normalization k = {payload['normalization_k']:.12e}  "
        f"(top anchor coordinate s={payload['top_anchor_coord']:.6f}, top={payload['top_anchor_mass_gev']} GeV)"
    )
    print(f"delta_global = {payload['delta_global']:.6f}")
    print(
        f"component_power={payload['component_power']:.3f}, "
        f"spin_coupling={payload['spin_coupling']:.3f}, "
        f"charge_coupling={payload['charge_coupling']:.3f}, "
        f"hypercharge_coupling={payload['hypercharge_coupling']:.3f}"
    )
    print()
    print("particle\tcoord_s\tl\tmodel_GeV\tref_GeV_or_ub\trel_err_%")
    for row in payload["rows"]:
        ref = row["ref_gev"]
        err = row["rel_err_pct"]
        ref_s = f"{ref:.12g}" if ref is not None else "-"
        err_s = f"{err:.6f}" if err is not None else "-"
        print(
            f"{row['particle']}\t{row['coord_s']:.6f}\t{row['layer_l']}\t"
            f"{row['model_gev']:.12g}\t{ref_s}\t{err_s}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--mode",
        choices=("baseline", "content_layers", "content_layers_scan"),
        default="baseline",
        help="mass pipeline mode",
    )
    args = parser.parse_args()

    if args.mode == "content_layers":
        report = build_content_layer_report()
    elif args.mode == "content_layers_scan":
        report = build_content_layer_scan_report()
    else:
        report = build_report()
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        if args.mode == "content_layers":
            print_content_layer_report(report)
        elif args.mode == "content_layers_scan":
            print("== Content-layer Rindler scan ==")
            print("rank\tscore\tpower\tspin\tcharge\thyper\tdelta\tcharm\te\tnu_e")
            for i, row in enumerate(report["top_20"], start=1):
                print(
                    f"{i}\t{row['score']:.6f}\t{row['component_power']:.2f}\t"
                    f"{row['spin_coupling']:.2f}\t{row['charge_coupling']:.2f}\t"
                    f"{row['hypercharge_coupling']:.2f}\t{row['delta_global']:.6f}\t"
                    f"{row['charm_gev']:.6g}\t{row['electron_gev']:.6g}\t{row['nu_e_gev']:.6g}"
                )
        else:
            print_human_report(report)


if __name__ == "__main__":
    main()
