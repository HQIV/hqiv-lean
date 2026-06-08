#!/usr/bin/env python3
"""
TUFT neutrino bridge lab (HQIV Python).

Mirrors Lean `HopfShellBeltramiMassBridge`:
  • `tuftOuterCasimirDressingAtXi` = (T13 outer / T12 inner) · κ₆
  • `tuftNeutrinoMassAnchoredAtXi_MeV` = m_τ(ξ) · dressing
  • `neutrinoMassSpectrum_at_xi_from_outerT8_MeV` = outer n=4 T8 anchor + holonomy splits

Absolute neutrino masses are **not** precision PDG targets like charged leptons.
Experiment gives m_ν > 0 and upper **caps** only (loose individual bound ~6 eV;
tighter cosmological Σm_ν ≲ 0.12 eV). Oscillation Δm² values are separate
diagnostics for hierarchy shape, not absolute-mass predictions.

No seesaw. Retired `M_Z` / `(1/140)^k` paths kept as diagnostics only.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Callable

import hqiv_lean_physics_primitives as lean
import hqiv_coupling_linear_system as hcls
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

# Oscillation mass-squared splittings (eV²) — hierarchy diagnostics, not absolute caps.
OSCILLATION_DM2_EV2 = {"dm21": 7.53e-5, "dm31": 2.453e-3}
# Tighter sum cap from cosmology / CMB (eV).
COSMOLOGY_SUM_CAP_EV = 0.12
# Loose experimental upper bound on individual neutrino mass scale (eV).
LOOSE_INDIVIDUAL_MASS_CAP_EV = 6.0
MEV_PER_EV = 1.0e-6

HOLONOMY = (48.0 / 91.0, 96.0 / 91.0, 144.0 / 91.0)


@dataclass(frozen=True)
class HopfSector:
    hopf_winding: int
    chart_shell_m: int
    beltrami_lambda: float
    charged_scalar: float
    neutral_scalar: float
    tuft_role: str


@dataclass(frozen=True)
class CasimirBalance:
    xi: float
    inner_trapping: float
    outer_suppression: float
    effective_casimir_scale: float
    outer_dressing: float
    hopf_spectral_scale_mev: float


@dataclass(frozen=True)
class NeutrinoCandidate:
    name: str
    status: str
    description: str
    m1_mev: float
    m2_mev: float
    m3_mev: float
    lean_targets: tuple[str, ...]


@dataclass(frozen=True)
class NeutrinoComparison:
    model: str
    status: str
    m1_ev: float
    m2_ev: float
    m3_ev: float
    sum_ev: float
    dm21_ev2: float
    dm31_ev2: float
    sum_over_pdg_limit: float
    dm21_ratio_to_pdg: float
    dm31_ratio_to_pdg: float
    ordering: str


def beltrami_lambda(n: int) -> float:
    return float(n + 1)


def tuft_charged_scalar(n: int) -> float:
    return tmse.tuft_lepton_geometric_scalar(n)


def tuft_neutral_scalar(n: int) -> float:
    a = tmse.TUFT_HELICITY_COEFFICIENT
    z3 = tmse.TUFT_APERY_ZETA3
    return (n + 1.0) * math.exp(a * n - z3 * n * n)


def inner_trapping_heavy(xi: float) -> float:
    return tmse.trapping_selection_heavy(lean.ALPHA_HEAVY, lean.omega_k_xi(xi))


def outer_suppression_dynamic(xi: float) -> float:
    return tmse.t13_outer_suppression_at_xi(xi)


def outer_casimir_dressing(xi: float, kappa6: float = tmse.TUFT_HOPF_KAPPA6) -> float:
    """Lean `tuftOuterCasimirDressingAtXi`."""
    inner = inner_trapping_heavy(xi)
    return outer_suppression_dynamic(xi) / inner * kappa6


def casimir_balance(xi: float = tmse.XI_LOCKIN) -> CasimirBalance:
    inner = inner_trapping_heavy(xi)
    outer = outer_suppression_dynamic(xi)
    dress = outer / inner * tmse.TUFT_HOPF_KAPPA6
    return CasimirBalance(
        xi=xi,
        inner_trapping=inner,
        outer_suppression=outer,
        effective_casimir_scale=inner / outer,
        outer_dressing=dress,
        hopf_spectral_scale_mev=tmse.tuft_hopf_spectral_scale_from_vev_mev(
            tmse.tuft_vev_at_xi_mev(xi)
        ),
    )


def hopf_sectors() -> tuple[HopfSector, ...]:
    roles = {
        1: "e sector",
        2: "μ sector",
        3: "τ / charged anchor",
        4: "ν_R outer S⁹ chart (Lean tuftOuterNeutrinoHopfWinding)",
    }
    return tuple(
        HopfSector(n, n + 1, beltrami_lambda(n), tuft_charged_scalar(n), tuft_neutral_scalar(n), roles[n])
        for n in range(1, 5)
    )


def _sort_normal(m1: float, m2: float, m3: float) -> tuple[float, float, float]:
    return tuple(sorted((m1, m2, m3)))


def neutrino_masses_from_holonomy(anchor_mev: float) -> tuple[float, float, float]:
    """Lean `neutrinoMassSpectrum_at_xi_from_outerCasimir_MeV` ordering (ν3, ν2, ν1)."""
    h_light, h_mid, h_heavy = HOLONOMY
    m3 = anchor_mev
    m2 = anchor_mev * h_mid / h_heavy
    m1 = anchor_mev * h_light / h_heavy
    return _sort_normal(m1, m2, m3)


def outer_neutrino_torsion_coeff() -> float:
    """Lean `tuftOuterNeutrinoTorsionCoeff` at winding n=4."""
    return tmse.hopf_torsion_coefficient(4)


def outer_neutrino_t8_subleading() -> float:
    """Lean `tuftOuterNeutrinoT8Subleading`."""
    heavy = tmse.hopf_torsion_coefficient(3)
    coeff = tmse.TUFT_RAY_SINGER_SUBLEADING_COEFF
    return 1.0 + coeff * (outer_neutrino_torsion_coeff() - heavy)


def outer_neutrino_neutral_dressing() -> float:
    """Lean `tuftOuterNeutrinoNeutralDressing`."""
    return tuft_neutral_scalar(4) / tuft_neutral_scalar(3)


def outer_neutrino_full_anchor_mev(xi: float = tmse.XI_LOCKIN) -> float:
    """Lean `tuftOuterNeutrinoFullAnchorAtXi_MeV`."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_mev(xi)
    return (
        tau
        * outer_casimir_dressing(xi)
        * outer_neutrino_neutral_dressing()
        * outer_neutrino_t8_subleading()
    )


def neutrino_masses_from_holonomy_powered(
    anchor_mev: float, exponent: int = 4
) -> tuple[float, float, float]:
    """Lean `tuftNeutrinoHolonomySplitRatioPowered` splits on a given anchor."""
    h_light, h_mid, h_heavy = HOLONOMY
    m3 = anchor_mev
    m2 = anchor_mev * (h_mid / h_heavy) ** exponent
    m1 = anchor_mev * (h_light / h_heavy) ** exponent
    return _sort_normal(m1, m2, m3)


# T11 torsion on integrable shells n = 1, 2, 3 (generation index g = n − 1).
T10_SHELL_TORSION = (2.0 / 5.0, 3.0 / 5.0, 4.0 / 5.0)


def t10_generation_phase_contribution(g: int) -> float:
    """Lean `t10GenerationPhaseContribution`: holonomy row × shell torsion."""
    hol = HOLONOMY[g]
    torsion = T10_SHELL_TORSION[g]
    return hol * torsion


def t10_mixing_phase_matrix() -> dict[str, float]:
    """Lean `assembleT10MixingPhaseMatrix` (+ Fano θ, rapidity CP skew)."""
    c0 = t10_generation_phase_contribution(0)
    c1 = t10_generation_phase_contribution(1)
    c2 = t10_generation_phase_contribution(2)
    return {
        "heavy_to_middle": c2 / c1,
        "middle_to_light": c1 / c0,
        "mixing_angle_rad": math.pi / 4.0,
        "cp_skew_rad": math.pi / 5.0,
    }


def t10_phase_contribution_sum() -> float:
    return sum(t10_generation_phase_contribution(g) for g in range(3))


def t10_overlap_matrix() -> list[list[float]]:
    """Lean `t10NeutrinoOverlapMatrix`: diagonal √(c_g/Σc), adjacent sin θ √(c_i c_j/Σc)."""
    c = [t10_generation_phase_contribution(g) for g in range(3)]
    total = t10_phase_contribution_sum()
    theta = math.pi / 4.0
    st = math.sin(theta)
    n = 3
    overlap = [[0.0] * n for _ in range(n)]
    for i in range(n):
        overlap[i][i] = math.sqrt(c[i] / total)
    for i in range(n - 1):
        val = st * math.sqrt(c[i] * c[i + 1] / total)
        overlap[i][i + 1] = val
        overlap[i + 1][i] = val
    return overlap


def _gram_schmidt_columns(matrix: list[list[float]]) -> list[list[float]]:
    cols = [[matrix[r][c] for r in range(len(matrix))] for c in range(len(matrix[0]))]
    basis: list[list[float]] = []
    for col in cols:
        v = list(col)
        for u in basis:
            dot = sum(a * b for a, b in zip(v, u))
            norm_u_sq = sum(x * x for x in u)
            if norm_u_sq > 0:
                v = [a - dot / norm_u_sq * b for a, b in zip(v, u)]
        norm = math.sqrt(sum(x * x for x in v))
        if norm > 0:
            basis.append([x / norm for x in v])
    return basis


def t10_pmns_unitary_real() -> list[list[float]]:
    """Orthonormal flavor basis from T10 overlap columns (real PMNS scaffold)."""
    basis = _gram_schmidt_columns(t10_overlap_matrix())
    n = len(basis)
    return [[basis[j][i] for j in range(n)] for i in range(n)]


def t10_pmns_angles_from_ratios() -> dict[str, float]:
    """Lean `t10PMNSAngle12/23/13` from T10 phase ratios + Fano lock-in."""
    t10 = t10_mixing_phase_matrix()
    c = [t10_generation_phase_contribution(g) for g in range(3)]
    total = t10_phase_contribution_sum()
    return {
        "theta12_rad": math.asin(math.sqrt(1.0 / (1.0 + t10["middle_to_light"]))),
        "theta23_rad": math.asin(math.sqrt(1.0 / (1.0 + t10["heavy_to_middle"]))),
        "theta13_rad": math.asin(math.sin(t10["mixing_angle_rad"]) * math.sqrt(c[0] / total)),
        "delta_rad": t10["cp_skew_rad"],
    }


def t10_pmns_rotation12(theta: float) -> list[list[float]]:
    c, s = math.cos(theta), math.sin(theta)
    return [[c, s, 0.0], [-s, c, 0.0], [0.0, 0.0, 1.0]]


def t10_pmns_rotation23(theta: float) -> list[list[float]]:
    c, s = math.cos(theta), math.sin(theta)
    return [[1.0, 0.0, 0.0], [0.0, c, s], [0.0, -s, c]]


def t10_pmns_rotation13(theta: float) -> list[list[float]]:
    c, s = math.cos(theta), math.sin(theta)
    return [[c, 0.0, s], [0.0, 1.0, 0.0], [-s, 0.0, c]]


def _matmul(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def t10_pmns_unitary_from_angles() -> list[list[float]]:
    """Lean `t10PMNSUnitaryReal` = R23 R13 R12."""
    ang = t10_pmns_angles_from_ratios()
    return _matmul(
        t10_pmns_rotation23(ang["theta23_rad"]),
        _matmul(
            t10_pmns_rotation13(ang["theta13_rad"]),
            t10_pmns_rotation12(ang["theta12_rad"]),
        ),
    )


def t10_pmns_readout() -> dict[str, object]:
    """Full T10 overlap → PMNS readout bundle."""
    ang = t10_pmns_angles_from_ratios()
    return {
        "overlap_matrix": t10_overlap_matrix(),
        "unitary_real_from_overlap": t10_pmns_unitary_real(),
        "unitary_real_from_angles": t10_pmns_unitary_from_angles(),
        "pmns_angles_rad": ang,
        "pmns_angles_deg": {k: math.degrees(v) for k, v in ang.items() if k.startswith("theta")},
        "mixing_phase_matrix": t10_mixing_phase_matrix(),
    }


def neutrino_masses_from_t10_middle_light(anchor_mev: float) -> tuple[float, float, float]:
    """Lean `neutrinoMassSpectrum_at_xi_from_T10_MeV`: T10 on ν₁–ν₂ split only."""
    mtl = t10_mixing_phase_matrix()["middle_to_light"]
    h_light, h_mid, h_heavy = HOLONOMY
    m3 = anchor_mev
    m2 = m3 * h_mid / h_heavy
    m1 = m3 * h_light / h_heavy / mtl
    return _sort_normal(m1, m2, m3)


def model_tuft_tau_outer_holonomy(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Baseline TUFT bridge: m_τ · (outer/inner) · κ₆ · (holonomy_g / holonomy_heavy)."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    anchor = tau * outer_casimir_dressing(xi)
    m1, m2, m3 = neutrino_masses_from_holonomy(anchor)
    return NeutrinoCandidate(
        "tuft_tau_outer_holonomy",
        "tuft_native",
        "Lean neutrinoMassSpectrum_at_xi_from_outerCasimir_MeV",
        m1,
        m2,
        m3,
        (
            "tuftOuterCasimirDressingAtXi",
            "tuftNeutrinoMassAnchoredAtXi_MeV",
            "neutrinoMassSpectrum_at_xi_from_outerCasimir_MeV",
        ),
    )


def model_tuft_outer_t8_holonomy(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Outer T8 anchor + T10 holonomy splits (no middle→light steepening)."""
    anchor = outer_neutrino_full_anchor_mev(xi)
    m1, m2, m3 = neutrino_masses_from_holonomy(anchor)
    return NeutrinoCandidate(
        "tuft_outer_t8_holonomy",
        "tuft_native",
        "Lean neutrinoMassSpectrum_at_xi_from_outerT8_MeV",
        m1,
        m2,
        m3,
        (
            "tuftOuterNeutrinoFullAnchorAtXi_MeV",
            "tuftOuterNeutrinoNeutralDressing",
            "tuftOuterNeutrinoT8Subleading",
            "neutrinoMassSpectrum_at_xi_from_outerT8_MeV",
        ),
    )


def model_tuft_outer_t8_t10(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Primary: outer T8 anchor + T10 middle→light on ν₁ (Lean T10 spectrum)."""
    anchor = outer_neutrino_full_anchor_mev(xi)
    m1, m2, m3 = neutrino_masses_from_t10_middle_light(anchor)
    t10 = t10_mixing_phase_matrix()
    return NeutrinoCandidate(
        "tuft_outer_t8_t10",
        "tuft_native",
        (
            f"Lean neutrinoMassSpectrum_at_xi_from_T10_MeV; "
            f"middleToLight={t10['middle_to_light']:.3g}, θ={t10['mixing_angle_rad']:.4g}"
        ),
        m1,
        m2,
        m3,
        (
            "neutrinoMassSpectrum_at_xi_from_T10_MeV",
            "assembleT10PMNSMixingReadout",
            "t10NeutrinoOverlapMatrix",
            "t10PMNSUnitaryReal",
        ),
    )


def model_tuft_outer_t8_holonomy_powered(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Diagnostic: holonomy splits steepened by tuftOuterNeutrinoHopfWinding = 4."""
    anchor = outer_neutrino_full_anchor_mev(xi)
    m1, m2, m3 = neutrino_masses_from_holonomy_powered(anchor, exponent=4)
    return NeutrinoCandidate(
        "tuft_outer_t8_holonomy_powered",
        "tuft_native",
        "outer T8 anchor; (hol_g/hol_heavy)^4 splits (open: outer Beltrami rounds)",
        m1,
        m2,
        m3,
        ("tuftNeutrinoHolonomySplitRatioPowered", "tuftOuterNeutrinoHopfWinding"),
    )


def model_tuft_beltrami_split_on_anchor(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Same absolute anchor; splittings from Beltrami (λ_g/λ_3)² instead of holonomy."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    m3 = tau * outer_casimir_dressing(xi)
    m2 = m3 * (beltrami_lambda(2) / beltrami_lambda(3)) ** 2
    m1 = m3 * (beltrami_lambda(1) / beltrami_lambda(3)) ** 2
    return NeutrinoCandidate(
        "tuft_beltrami_split_on_anchor",
        "tuft_native",
        "τ·dressing anchor; Δm from Beltrami eigenvalue ratios squared",
        *_sort_normal(m1, m2, m3),
        ("tuftMinimalBeltramiEigenvalue", "tuftOuterCasimirDressingAtXi"),
    )


def model_tuft_n4_neutral_anchor(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """S⁹ hypothesis: anchor uses neutral scalar at n=4 vs τ at n=3."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    anchor = tau * outer_casimir_dressing(xi) * (tuft_neutral_scalar(4) / tuft_neutral_scalar(3))
    m1, m2, m3 = neutrino_masses_from_holonomy(anchor)
    return NeutrinoCandidate(
        "tuft_n4_neutral_anchor",
        "tuft_native",
        "τ·dressing·(M_neutral(4)/M_neutral(3)); holonomy splits",
        m1,
        m2,
        m3,
        ("tuftOuterNeutrinoHopfWinding", "tuftNeutralGeometricScalar"),
    )


def model_tuft_beltrami_squared_split(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """TUFT Beltrami eigenvalue² splits on outer anchor (not linear holonomy)."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    m3 = tau * outer_casimir_dressing(xi)
    m2 = m3 * (3 / 4) ** 2
    m1 = m3 * (2 / 4) ** 2
    return NeutrinoCandidate(
        "tuft_beltrami_squared_split",
        "tuft_native",
        "anchor × (λ_g/λ_3)² with λ_n = n+1; TUFT determinant ratio",
        *_sort_normal(m1, m2, m3),
        ("tuftBeltramiResonanceRatio", "tuftOuterCasimirDressingAtXi"),
    )


def model_tuft_n4_neutral_beltrami(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """S⁹ outer shell: neutral scalar anchor + Beltrami² splits."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    anchor = tau * outer_casimir_dressing(xi) * (tuft_neutral_scalar(4) / tuft_neutral_scalar(3))
    m3 = anchor
    m2 = m3 * (3 / 4) ** 2
    m1 = m3 * (2 / 4) ** 2
    return NeutrinoCandidate(
        "tuft_n4_neutral_beltrami",
        "tuft_native",
        "τ·dressing·M_neutral(4/3); Beltrami² splits",
        m1,
        m2,
        m3,
        ("tuftNeutralGeometricScalar", "tuftBeltramiResonanceRatio"),
    )


def model_tuft_t8_detuned_split(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """T8 leading term: splittings from `geometricResonanceStep` on lock-in chart shells."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    m3 = tau * outer_casimir_dressing(xi)
    outer_shell = 5  # tuftOuterNeutrinoChartShell = n+1 for n=4
    m2 = m3 * hcls.geometric_resonance_step(3, outer_shell)
    m1 = m3 * hcls.geometric_resonance_step(2, outer_shell)
    return NeutrinoCandidate(
        "tuft_t8_detuned_split",
        "tuft_native",
        "τ·dressing anchor; Δm from T8 detunedShellSurface ratios (shells 2,3 → 5)",
        *_sort_normal(m1, m2, m3),
        ("tuftSectorZetaDet", "geometricResonanceStep", "detunedShellSurface"),
    )


def model_tuft_t8_holonomy_detuned(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    """Combine T10 holonomy with T8 detuned step between outer chart shells."""
    tau, _, _ = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    anchor = tau * outer_casimir_dressing(xi)
    outer_shell = 5
    t8_scale = hcls.geometric_resonance_step(4, outer_shell)
    m1, m2, m3 = neutrino_masses_from_holonomy(anchor * t8_scale)
    return NeutrinoCandidate(
        "tuft_t8_holonomy_detuned",
        "tuft_native",
        "holonomy splits on anchor scaled by T8 step(4→5)",
        m1,
        m2,
        m3,
        ("tuftSectorZetaDet_lockinChart", "tuftNeutrinoHolonomyRatio"),
    )


def model_retired_legacy_140_ladder() -> NeutrinoCandidate:
    m_z_gev = 5.488
    m_outer = lean.REFERENCE_M + 2
    sup = lean.GAMMA / float((m_outer + 1) * (m_outer + 2))
    nu3 = sup * m_z_gev * 1000.0
    nu2 = sup * nu3
    nu1 = sup * nu2
    return NeutrinoCandidate(
        "retired_legacy_140_ladder",
        "retired_diagnostic",
        "Disproved: (1/140)^k · M_Z_derived",
        nu1,
        nu2,
        nu3,
        ("outerHorizonNeutrinoSuppression",),
    )


def model_retired_m_nu_e_at_xi(xi: float = tmse.XI_LOCKIN) -> NeutrinoCandidate:
    m_z_gev = 5.488
    nu = tmse.t13_outer_suppression_at_xi(xi) * tmse.TUFT_HOPF_KAPPA6 * m_z_gev * 1000.0
    return NeutrinoCandidate(
        "retired_m_nu_e_at_xi",
        "retired_diagnostic",
        "Disproved: (ωK/140)·κ₆·M_Z",
        nu,
        nu,
        nu,
        ("m_nu_e_at_xi",),
    )


TUFT_NATIVE_MODELS: dict[str, Callable[[], NeutrinoCandidate]] = {
    "tuft_outer_t8_t10": model_tuft_outer_t8_t10,
    "tuft_outer_t8_holonomy": model_tuft_outer_t8_holonomy,
    "tuft_tau_outer_holonomy": model_tuft_tau_outer_holonomy,
    "tuft_outer_t8_holonomy_powered": model_tuft_outer_t8_holonomy_powered,
    "tuft_beltrami_squared_split": model_tuft_beltrami_squared_split,
    "tuft_n4_neutral_beltrami": model_tuft_n4_neutral_beltrami,
    "tuft_beltrami_split_on_anchor": model_tuft_beltrami_split_on_anchor,
    "tuft_n4_neutral_anchor": model_tuft_n4_neutral_anchor,
    "tuft_t8_detuned_split": model_tuft_t8_detuned_split,
    "tuft_t8_holonomy_detuned": model_tuft_t8_holonomy_detuned,
}

RETIRED_MODELS: dict[str, Callable[[], NeutrinoCandidate]] = {
    "retired_legacy_140_ladder": model_retired_legacy_140_ladder,
    "retired_m_nu_e_at_xi": model_retired_m_nu_e_at_xi,
}

ALL_MODELS = {**TUFT_NATIVE_MODELS, **RETIRED_MODELS}


def passes_absolute_mass_caps(comp: NeutrinoComparison) -> bool:
    """True when all masses are positive and below experimental upper caps."""
    return (
        comp.m1_ev > 0
        and comp.m2_ev > 0
        and comp.m3_ev > 0
        and comp.sum_ev < COSMOLOGY_SUM_CAP_EV
        and comp.m3_ev < LOOSE_INDIVIDUAL_MASS_CAP_EV
    )


def compare_model(result: NeutrinoCandidate) -> NeutrinoComparison:
    e1, e2, e3 = (result.m1_mev / MEV_PER_EV, result.m2_mev / MEV_PER_EV, result.m3_mev / MEV_PER_EV)
    dm21 = e2**2 - e1**2
    dm31 = e3**2 - e1**2
    s = e1 + e2 + e3
    return NeutrinoComparison(
        model=result.name,
        status=result.status,
        m1_ev=e1,
        m2_ev=e2,
        m3_ev=e3,
        sum_ev=s,
        dm21_ev2=dm21,
        dm31_ev2=dm31,
        sum_over_pdg_limit=s / COSMOLOGY_SUM_CAP_EV,
        dm21_ratio_to_pdg=dm21 / OSCILLATION_DM2_EV2["dm21"] if dm21 > 0 else float("nan"),
        dm31_ratio_to_pdg=dm31 / OSCILLATION_DM2_EV2["dm31"] if dm31 > 0 else float("nan"),
        ordering="normal" if e1 < e2 < e3 else "non-normal",
    )


def scale_closure_notes(primary: NeutrinoComparison) -> list[str]:
    cap_ok = passes_absolute_mass_caps(primary)
    return [
        (
            f"Absolute scale Σm_ν = {primary.sum_ev:.4g} eV "
            f"({'passes' if cap_ok else 'FAILS'} caps: 0 < m, Σm < {COSMOLOGY_SUM_CAP_EV} eV, "
            f"m_max < {LOOSE_INDIVIDUAL_MASS_CAP_EV} eV)."
        ),
        (
            f"Oscillation Δm²21 / lab reference = {primary.dm21_ratio_to_pdg:.3g} "
            "(hierarchy diagnostic only — not a charged-lepton-style precision target)."
        ),
        f"Oscillation Δm²31 / lab reference = {primary.dm31_ratio_to_pdg:.3g}.",
        "Charged leptons: T8 full chart frozen (τ/μ/e ~0.998–1.000× PDG); neutrinos use outer n=4 channel only.",
        "T10 3×3 overlap → PMNS wired (θ₁₂, θ₂₃, θ₁₃ from phase ratios; δ=π/5).",
    ]


def build_report() -> dict:
    xi = tmse.XI_LOCKIN
    bal = casimir_balance(xi)
    tau, mu, e = tmse.lepton_mass_spectrum_at_xi_from_vev_mev(xi)
    native = [fn() for fn in TUFT_NATIVE_MODELS.values()]
    retired = [fn() for fn in RETIRED_MODELS.values()]
    comparisons = [compare_model(m) for m in native + retired]
    primary = compare_model(model_tuft_outer_t8_t10(xi))
    return {
        "xi_lockin": xi,
        "casimir_balance": asdict(bal),
        "hopf_sectors": [asdict(s) for s in hopf_sectors()],
        "charged_baseline_mev": {"tau": tau, "mu": mu, "e": e},
        "tuft_native_candidates": [asdict(m) for m in native],
        "retired_diagnostics": [asdict(m) for m in retired],
        "pdg_comparisons": [asdict(c) for c in comparisons],
        "primary_model": primary.model,
        "scale_closure_notes": scale_closure_notes(primary),
        "oscillation_dm2_reference_ev2": OSCILLATION_DM2_EV2,
        "cosmology_sum_cap_ev": COSMOLOGY_SUM_CAP_EV,
        "loose_individual_mass_cap_ev": LOOSE_INDIVIDUAL_MASS_CAP_EV,
        "primary_passes_absolute_caps": passes_absolute_mass_caps(primary),
        "t10_pmns": t10_pmns_readout(),
        "lean_next_targets": [],
    }


def print_report(report: dict) -> None:
    print("=" * 72)
    print("TUFT neutrino bridge (HQIV Python ↔ Lean)")
    print("=" * 72)
    bal = report["casimir_balance"]
    print(
        f"\n@ ξ={bal['xi']}: inner={bal['inner_trapping']:.4f}  outer={bal['outer_suppression']:.6g}  "
        f"Λ_eff={bal['effective_casimir_scale']:.1f}  dressing={bal['outer_dressing']:.4g}"
    )
    cb = report["charged_baseline_mev"]
    print(f"Charged: τ={cb['tau']:.2f} MeV  μ={cb['mu']:.2f}  e={cb['e']:.4f} MeV")
    print("\nTUFT-native (primary first):")
    print(
        f"{'model':<32} {'Σm/eV':>10} {'Σ/cap':>8} {'Δm²21':>8} {'Δm²31':>8} ord"
    )
    print("  (Σ/cap = fraction of cosmology Σm cap; Δm² columns = oscillation diagnostic)")
    print("-" * 72)
    for c in report["pdg_comparisons"]:
        if c["status"] != "tuft_native":
            continue
        mark = "*" if c["model"] == report["primary_model"] else " "
        print(
            f"{mark}{c['model']:<31} {c['sum_ev']:10.4g} {c['sum_over_pdg_limit']:8.2f} "
            f"{c['dm21_ratio_to_pdg']:8.3g} {c['dm31_ratio_to_pdg']:8.3g} {c['ordering']}"
        )
    print("\nScale closure:")
    for note in report["scale_closure_notes"]:
        print(f"  • {note}")
    print("\nRetired:")
    for c in report["pdg_comparisons"]:
        if c["status"] == "retired_diagnostic":
            print(f"  {c['model']}: Σ/0.12 = {c['sum_over_pdg_limit']:.1e}")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--model", choices=sorted(ALL_MODELS))
    args = parser.parse_args()
    if args.model:
        r = ALL_MODELS[args.model]()
        print(json.dumps({"model": asdict(r), "comparison": asdict(compare_model(r))}, indent=2))
        return
    report = build_report()
    if args.json:
        print(json.dumps(report, indent=2))
        return
    print_report(report)


if __name__ == "__main__":
    main()
