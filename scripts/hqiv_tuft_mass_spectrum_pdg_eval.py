#!/usr/bin/env python3
"""
PDG comparison for the TUFT/HQIV dynamic mass spectrum + excited-state readouts.

Mirrors Lean:
  - `leptonMassSpectrum_at_xi`, `heavy_lepton_gap_at_xi`, `tuftExcitedHeavyMassAtXi`
    in `Hqiv/Physics/HopfShellBeltramiMassBridge.lean`
  - `metaHorizonExcitedMassReadout` in `Hqiv/Physics/MetaHorizonExcitedStates.lean`

Run:
  python3 scripts/hqiv_tuft_mass_spectrum_pdg_eval.py
  python3 scripts/hqiv_tuft_mass_spectrum_pdg_eval.py --json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_coupling_linear_system as hcls
import hqiv_continuous_shell_mass as csm
import hqiv_excited_states as hes
import hqiv_tuft_hadron_s7_confinement as h7
import hqiv_hadron_global_excitation as hge
import hqiv_meson_flavor_content as mfc
import hqiv_tuft_global_hadron_readout as tgh
import hqiv_tuft_quark_vev as tqv
import hqiv_tuft_electroweak_boson_readout as ew

ALPHA = 3.0 / 5.0
TUFT_APERY_ZETA3 = 1.2020569031595942
TUFT_FINE_STRUCTURE_ALPHA = 1.0 / 137.035999084
TUFT_HELICITY_COEFFICIENT = 6.0 * math.sqrt(2.0) * math.exp(
    TUFT_APERY_ZETA3 / (24.0 * math.pi * math.pi)
)
XI_LOCKIN = 5.0
REFERENCE_M = 4
T13_OUTER_MODE_COUNT = 140.0
TORSION_HEAVY = 4.0 / 5.0  # phaseLiftCoeff(3) * alpha
HOLONOMY_HEAVY_ROW = 144.0 / 91.0
K_TAU_MU = 175.0 / 76.0
K_MU_E = 4484.0 / 2499.0
PROTON_MEV = 938.27208816
ELECTROWEAK_VEV_MEV = 246_219.65
ETA_PAPER = 6.10e-10
GAMMA_HQIV = 2.0 / 5.0
# Lean `tuftHopfKappa6`: dimensionless topological suppression in
# Λ_Hopf = sqrt(2π) * v * κ₆.  It decomposes as η_lockin * γ * C₂.
TUFT_HOPF_KAPPA6_SECOND_ORDER = 1.1351364492426774
TUFT_HOPF_KAPPA6_MATTER_OVERLAP_BARE = ETA_PAPER * GAMMA_HQIV
TUFT_HOPF_KAPPA6 = TUFT_HOPF_KAPPA6_MATTER_OVERLAP_BARE * TUFT_HOPF_KAPPA6_SECOND_ORDER
# Lean `tuftRaySingerSubleadingCoeff`: Ray–Singer S³ residue in T8 torsion subleading.
TUFT_RAY_SINGER_SUBLEADING_COEFF = 1.0 / (4.0 * math.pi)

PDG_MEV = {
    "tau": 1776.86,
    "mu": 105.6583755,
    "e": 0.5109989461,
    "proton": PROTON_MEV,
    "Delta(1232)": 1232.0,
    "Delta(1600)": 1600.0,
    "N(1440)": 1440.0,
    "N(1520)": 1515.0,
    "N(1650)": 1650.0,
    "N(1680)": 1680.0,
    "N(1710)": 1710.0,
    "rho": 775.26,
    "omega": 782.65,
    "K*(892)": 891.66,
    "phi(1020)": 1019.46,
}

# Breit–Wigner widths (MeV) for vector mesons — PDG pole listings (comparison only).
PDG_WIDTH_MEV: dict[str, float] = {
    "rho": 149.1,
    "omega": 8.49,
    "K*(892)": 47.3,
    "phi(1020)": 4.249,
}

_ROOT = Path(__file__).resolve().parents[1]


def _load_pdg_uncertainty_mev() -> dict[str, float]:
    """Load mass fit uncertainties from `data/hadron_published_masses.json`."""
    path = _ROOT / "data" / "hadron_published_masses.json"
    if not path.is_file():
        return {}
    data = json.loads(path.read_text())
    out: dict[str, float] = {}
    for entry in data.get("entries", []):
        key = entry.get("key")
        unc = entry.get("uncertainty_MeV")
        if key and unc is not None:
            out[str(key)] = float(unc)
    # Aliases used by the meson benchmark grid
    aliases = {
        "rho": "rho0",
        "omega": "omega",
        "K*(892)": "K*+",
        "phi(1020)": "phi",
    }
    merged = dict(out)
    for alias, src in aliases.items():
        if alias not in merged and src in out:
            merged[alias] = out[src]
    return merged


PDG_UNCERTAINTY_MEV = _load_pdg_uncertainty_mev()

# Quark pole masses (GeV) for chart comparison — Lean anchor numerals for t/b
PDG_GEV = {
    "W": 80.379,
    "Z": 91.1876,
    "H": 125.11,
}

# Anomalous magnetic moment (g−2)/2 — comparison layer (FNAL 2021 / CODATA electron).
PDG_ANOMALOUS_MOMENT: dict[str, tuple[float, float]] = {
    "a_e": (115965218073e-14, 28e-14),
    "a_mu": (116592061e-11, 41e-11),
}

PDG_QUARK_GEV = {
    "t": 172.57,
    "b": 4.18,
    "c": 1.27,
    "s": 0.0934,
    "u": 0.00216,
    "d": 0.00467,
}

# Δ(1232): (0,1) P-wave decuplet. N slots use J^P parity on chart (n, ℓ).
BARYON_EXCITED_GRID: list[tuple[int, int, str | None]] = [
    (0, 0, "proton"),
    (0, 1, "Delta(1232)"),
    (0, 2, "N(1440)"),
    (1, 1, "N(1520)"),
    (0, 3, "N(1680)"),
    (0, 3, "N(1710)"),
    (1, 2, None),
    (2, 0, None),
    (2, 1, None),
]

# Meson excited grid — see `hqiv_meson_flavor_content.MESON_EXCITED_GRID`
MESON_EXCITED_GRID = mfc.MESON_EXCITED_GRID


def curvature_primitive(xi: float) -> float:
    lx = math.log(xi)
    return lx + (ALPHA / 2.0) * lx * lx


def omega_k_xi(xi: float) -> float:
    return curvature_primitive(xi) / curvature_primitive(XI_LOCKIN)


def trapping_selection_heavy(alpha: float, c: float) -> float:
    phase_lift_3 = (2.0 * (3 + 1)) / 6.0  # phi(3)/6 = 4/3
    return 1.0 + c * alpha * math.log(1.0 + phase_lift_3 * alpha)


def t13_outer_suppression_at_xi(xi: float) -> float:
    """Lean `t13_outer_suppression_at_xi`: omegaK(xi) / 140."""
    return omega_k_xi(xi) / T13_OUTER_MODE_COUNT


def effective_casimir_scale_at_xi(xi: float) -> float:
    """Lean `effective_casimir_scale_at_xi`: dynamic inner / dynamic T13 outer."""
    alpha_heavy = 3.0 / 5.0
    return trapping_selection_heavy(alpha_heavy, omega_k_xi(xi)) / t13_outer_suppression_at_xi(xi)


def heavy_lepton_gap_at_xi(xi: float) -> float:
    """Lean `heavy_lepton_gap_at_xi`: relative inner/outer scale normalized at ξ=5."""
    return (
        (4.0 / 5.0)
        * (xi / XI_LOCKIN)
        * (effective_casimir_scale_at_xi(xi) / effective_casimir_scale_at_xi(XI_LOCKIN))
    )


def resonance_k_tau_mu_at_xi(xi: float) -> float:
    alpha_heavy = 3.0 / 5.0
    trap_xi = trapping_selection_heavy(alpha_heavy, omega_k_xi(xi))
    trap_ref = trapping_selection_heavy(alpha_heavy, 1.0)
    return K_TAU_MU * trap_xi / trap_ref


def lepton_mass_spectrum_at_xi(xi: float) -> tuple[float, float, float]:
    """Faithful TUFT Beltrami determinant scalar normalized to the heavy n=3 sector."""
    heavy = heavy_lepton_gap_at_xi(xi)
    return (
        heavy,
        heavy * tuft_lepton_geometric_scalar(2) / tuft_lepton_geometric_scalar(3),
        heavy * tuft_lepton_geometric_scalar(1) / tuft_lepton_geometric_scalar(3),
    )


def tuft_vev_at_xi_mev(xi: float, vev_lockin_mev: float = ELECTROWEAK_VEV_MEV) -> float:
    """T/ξ -> vev bridge, normalized to the electroweak vev at ξ_lock."""
    return vev_lockin_mev * heavy_lepton_gap_at_xi(xi) / heavy_lepton_gap_at_xi(XI_LOCKIN)


def tuft_hopf_spectral_scale_from_vev_mev(
    vev_mev: float, kappa6: float = TUFT_HOPF_KAPPA6
) -> float:
    return math.sqrt(2.0 * math.pi) * vev_mev * kappa6


def tuft_lepton_mass_from_vev_at_xi_mev(
    xi: float,
    n: int,
    vev_lockin_mev: float = ELECTROWEAK_VEV_MEV,
    kappa6: float = TUFT_HOPF_KAPPA6,
) -> float:
    return tuft_hopf_spectral_scale_from_vev_mev(tuft_vev_at_xi_mev(xi, vev_lockin_mev), kappa6) * (
        tuft_lepton_geometric_scalar(n)
    )


def lepton_mass_spectrum_at_xi_from_vev_mev(
    xi: float,
    vev_lockin_mev: float = ELECTROWEAK_VEV_MEV,
    kappa6: float = TUFT_HOPF_KAPPA6,
) -> tuple[float, float, float]:
    """Primary physical chart: T/ξ -> vev -> mass, ordered (τ, μ, e)."""
    return (
        tuft_lepton_mass_from_vev_at_xi_mev(xi, 3, vev_lockin_mev, kappa6),
        tuft_lepton_mass_from_vev_at_xi_mev(xi, 2, vev_lockin_mev, kappa6),
        tuft_lepton_mass_from_vev_at_xi_mev(xi, 1, vev_lockin_mev, kappa6),
    )


def legacy_shell_quotient_spectrum_at_xi(xi: float) -> tuple[float, float, float]:
    """Old HQIV shell quotient path retained as a mismatch diagnostic."""
    heavy = heavy_lepton_gap_at_xi(xi)
    k_tm = resonance_k_tau_mu_at_xi(xi)
    return heavy, heavy / k_tm, heavy / (k_tm * K_MU_E)


def tuft_lepton_geometric_scalar(n: int) -> float:
    return (
        (n + 1.0)
        * math.exp(TUFT_HELICITY_COEFFICIENT * n - TUFT_APERY_ZETA3 * n * n)
        * math.exp(n * TUFT_FINE_STRUCTURE_ALPHA / 6.0)
    )


def tuft_anomalous_moment_spurion(n: int) -> float:
    """Lean `tuftAnomalousMomentSpurion`: APS EM spurion from exp(n α_em/6) Beltrami slot."""
    if n <= 0:
        raise ValueError("winding sector n must be ≥ 1")
    return (math.exp(n * TUFT_FINE_STRUCTURE_ALPHA / 6.0) - 1.0) / n


def hopf_torsion_coefficient(n: int) -> float:
    """Lean `HopfShell.torsionMatrixCoefficient` with global α."""
    phase_lift = 2.0 * (n + 1) / 6.0
    return phase_lift * ALPHA


def hopf_t8_torsion_subleading(n: int) -> float:
    """Lean `hopfShellT8TorsionSubleading` on generation winding `n`."""
    heavy = hopf_torsion_coefficient(3)
    mult = float(n + 1)
    coeff = TUFT_RAY_SINGER_SUBLEADING_COEFF if n >= 2 else (2.0 / 5.0) / (2.0 * mult * mult)
    return 1.0 + coeff * (hopf_torsion_coefficient(n) - heavy)


def tuft_lepton_geometric_scalar_t8(n: int) -> float:
    """Lean `tuftLeptonGeometricScalarT8`."""
    return tuft_lepton_geometric_scalar(n) * hopf_t8_torsion_subleading(n) / hopf_t8_torsion_subleading(3)


def lepton_mass_spectrum_at_xi_from_vev_t8_mev(
    xi: float,
    vev_lockin_mev: float = ELECTROWEAK_VEV_MEV,
    kappa6: float = TUFT_HOPF_KAPPA6,
) -> tuple[float, float, float]:
    """Lean `leptonMassSpectrum_at_xi_from_vev_T8_MeV`."""
    scale = tuft_hopf_spectral_scale_from_vev_mev(tuft_vev_at_xi_mev(xi, vev_lockin_mev), kappa6)
    return tuple(scale * tuft_lepton_geometric_scalar_t8(n) for n in (3, 2, 1))


def lepton_mass_spectrum_at_xi_mev(xi: float) -> tuple[float, float, float]:
    """Primary TUFT chart: T8 full (leading + generation-indexed subleading)."""
    return lepton_mass_spectrum_at_xi_from_vev_t8_mev(xi)


def lepton_mass_spectrum_at_xi_mev_leading_only(xi: float) -> tuple[float, float, float]:
    """Leading T8 only (Beltrami body without torsion subleading)."""
    return lepton_mass_spectrum_at_xi_from_vev_mev(xi)


def meta_horizon_excited_mass_mev(n: int, ell: int) -> float:
    return hes.meta_horizon_excited_mass_mev(n, ell, derived_proton_mev=PROTON_MEV, readout="operational")


def tuft_excited_heavy_mass_at_xi_mev(xi: float, n: int, ell: int) -> float:
    ground = tuft_lepton_mass_from_vev_at_xi_mev(xi, 3)
    rad = hes.delta_m_radial_operational_mev(n, derived_proton_mev=PROTON_MEV)
    orb = hes.delta_m_orbital_operational_mev(ell, derived_proton_mev=PROTON_MEV)
    return ground + (ground / PROTON_MEV) * (rad + orb)


def tuft_proton_to_tau_pin_at_lockin() -> float:
    """Lean `tuftProtonToTauPinAtLockin`: derivedProtonMass / τ(ξ_lock)."""
    tau_lock = lepton_mass_spectrum_at_xi_mev(XI_LOCKIN)[0]
    return PROTON_MEV / tau_lock


def tuft_hadron_ground_at_xi_mev(xi: float) -> float:
    """Lean `tuftHadronGroundAtXi_MeV`: τ(ξ) × proton/τ lock-in pin."""
    tau = lepton_mass_spectrum_at_xi_mev(xi)[0]
    return tau * tuft_proton_to_tau_pin_at_lockin()


def tuft_hadron_beltrami_radial_delta_at_xi_mev(xi: float, n: int) -> float:
    """Lean `tuftHadronBeltramiRadialDeltaAtXi` on the heavy chart shell."""
    g = tuft_hadron_ground_at_xi_mev(xi)
    return (g / PROTON_MEV) * hes.delta_m_radial_operational_mev(n, derived_proton_mev=PROTON_MEV)


def tuft_hadron_beltrami_orbital_delta_at_xi_mev(xi: float, ell: int) -> float:
    """Lean `tuftHadronBeltramiOrbitalDeltaAtXi` on the heavy chart shell."""
    g = tuft_hadron_ground_at_xi_mev(xi)
    return (g / PROTON_MEV) * hes.delta_m_orbital_operational_mev(ell, derived_proton_mev=PROTON_MEV)


def tuft_hadron_excited_mass_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """Lean `tuftHadronExcitedMassAtXi_MeV` — global readout on heavy chart."""
    return tgh.tuft_excited_mass_global_at_xi_mev(xi, tgh.TuftExcitationChannel.baryon(n, ell))


def tuft_meson_vector_ground_at_xi_mev(xi: float) -> float:
    """Lean `tuftMesonVectorGroundAtXi_MeV`: strong/heavy chart ratio on vev baryon ground."""
    return tuft_hadron_ground_at_xi_mev(xi) * TUFT_STRONG_CHART_SHELL / TUFT_HEAVY_CHART_SHELL


def tuft_meson_vector_mass_at_xi_mev(xi: float) -> float:
    """Lean `tuftMesonVectorMassAtXi_MeV`: strong-chart ground + scaled ℓ=1 orbital."""
    anchor = tuft_meson_vector_ground_at_xi_mev(xi)
    g = tuft_hadron_ground_at_xi_mev(xi)
    orb = tuft_hadron_beltrami_orbital_delta_at_xi_mev(xi, 1)
    return anchor + (anchor / g) * orb


def tuft_meson_excited_mass_at_xi_mev(xi: float, n: int, ell: int) -> float:
    """Strong-chart meson tower: vev ground + inline Beltrami on m_strong."""
    import hqiv_meson_strong_excitation as mse

    return mse.tuft_meson_excited_mass_at_xi_mev(xi, n, ell)


def build_meson_excited_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    return tgh.build_global_rows(xi, tgh.MESON_EXCITED_CHANNELS, "meson")


def build_baryon_global_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    return tgh.build_global_rows(xi, tgh.BARYON_EXCITED_CHANNELS, "baryon")


def tuft_quark_spectrum_at_xi_mev(xi: float) -> tqv.QuarkSpectrumAtXi:
    tau, _, _ = lepton_mass_spectrum_at_xi_mev(xi)
    tau_lock, _, _ = lepton_mass_spectrum_at_xi_mev(XI_LOCKIN)
    return tqv.tuft_quark_spectrum_at_xi_mev(tau, tau_lock)


TUFT_STRONG_CHART_SHELL = 3  # tuftStrongHopfShellIndex + 1
TUFT_HEAVY_CHART_SHELL = 4  # tuftHeavyHopfWinding + 1


def meson_vector_ground_anchor_mev(derived_proton_mev: float) -> float:
    """Lean `mesonVectorGroundAnchor_MeV`: m_p · (m_strong / m_heavy) = 3/4 · m_p."""
    return derived_proton_mev * TUFT_STRONG_CHART_SHELL / TUFT_HEAVY_CHART_SHELL


def meson_vector_excited_mass_mev(derived_proton_mev: float = 938.27208816) -> float:
    """Lean `mesonVectorExcitedMassReadout`: strong-chart ground + scaled orbital ℓ=1."""
    anchor = meson_vector_ground_anchor_mev(derived_proton_mev)
    dm = hes.delta_m_orbital_operational_mev(1, derived_proton_mev=derived_proton_mev)
    return anchor + dm * (anchor / derived_proton_mev)


def meson_vector_excited_mev_legacy(derived_proton_mev: float = 938.27208816) -> float:
    """Deprecated half-proton anchor (no chart basis; diagnostic only)."""
    meson_anchor = 0.5 * derived_proton_mev
    dm = hes.delta_m_orbital_operational_mev(1, derived_proton_mev=derived_proton_mev)
    return meson_anchor + dm * (meson_anchor / derived_proton_mev)


@dataclass(frozen=True)
class PdgRow:
    observable: str
    hqiv_mev: float
    pdg_mev: float | None
    ratio: float | None
    lean_slot: str
    unit: str = "MeV"
    pdg_sigma_mev: float | None = None
    delta_mev: float | None = None
    sigma_n: float | None = None
    pdg_width_mev: float | None = None
    delta_over_width: float | None = None


@dataclass(frozen=True)
class SpectrumSection:
    title: str
    rows: list[PdgRow]


def _row_anomalous_moment(
    observable: str,
    hqiv: float,
    pdg_key: str,
    lean_slot: str,
) -> PdgRow:
    pdg_val, pdg_sigma = PDG_ANOMALOUS_MOMENT[pdg_key]
    delta = hqiv - pdg_val
    sigma_n = abs(delta) / pdg_sigma if pdg_sigma else None
    ratio = hqiv / pdg_val if pdg_val else None
    return PdgRow(
        observable,
        hqiv,
        pdg_val,
        ratio,
        lean_slot,
        unit="(g−2)/2",
        pdg_sigma_mev=pdg_sigma,
        delta_mev=delta,
        sigma_n=sigma_n,
    )


def _row(
    observable: str,
    hqiv: float,
    pdg_key: str | None,
    lean_slot: str,
    *,
    unit: str = "MeV",
    pdg_gev: str | None = None,
) -> PdgRow:
    if pdg_gev is not None:
        pdg_val = PDG_GEV.get(pdg_gev) or PDG_QUARK_GEV.get(pdg_gev)
        pdg_mev = pdg_val * 1000.0 if pdg_val is not None else None
    elif pdg_key is not None:
        pdg_mev = PDG_MEV.get(pdg_key)
    else:
        pdg_mev = None
    ratio = (hqiv / pdg_mev) if pdg_mev not in (None, 0) else None
    pdg_sigma = PDG_UNCERTAINTY_MEV.get(pdg_key) if pdg_key else None
    delta = (hqiv - pdg_mev) if pdg_mev is not None else None
    sigma_n = (abs(delta) / pdg_sigma) if delta is not None and pdg_sigma not in (None, 0) else None
    width = PDG_WIDTH_MEV.get(pdg_key) if pdg_key else None
    delta_width = (abs(delta) / width) if delta is not None and width not in (None, 0) else None
    return PdgRow(
        observable,
        hqiv,
        pdg_mev,
        ratio,
        lean_slot,
        unit=unit,
        pdg_sigma_mev=pdg_sigma,
        delta_mev=delta,
        sigma_n=sigma_n,
        pdg_width_mev=width,
        delta_over_width=delta_width,
    )


def build_quark_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    q = tuft_quark_spectrum_at_xi_mev(xi)
    labels = [
        ("t", q.t_mev, "tuftQuarkUpTypeAtXi_MeV (gen=2)"),
        ("c", q.c_mev, "tuftQuarkUpTypeAtXi_MeV (gen=1)"),
        ("u", q.u_mev, "tuftQuarkUpTypeAtXi_MeV (gen=0)"),
        ("b", q.b_mev, "tuftQuarkDownTypeAtXi_MeV (gen=2)"),
        ("s", q.s_mev, "tuftQuarkDownTypeAtXi_MeV (gen=1)"),
        ("d", q.d_mev, "tuftQuarkDownTypeAtXi_MeV (gen=0)"),
    ]
    return [
        _row(f"{fl} vev-pinned @ ξ={xi:g}", mass, None, lean, unit="GeV", pdg_gev=fl)
        for fl, mass, lean in labels
    ]


def build_baryon_excited_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    return tgh.build_global_rows(xi, tgh.BARYON_EXCITED_CHANNELS, "baryon")


def build_hadron_global_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    channels = tgh.MESON_EXCITED_CHANNELS + tgh.BARYON_EXCITED_CHANNELS
    return tgh.build_global_rows(xi, channels, "hadron")


def build_spectrum_sections() -> list[SpectrumSection]:
    tau, mu, e = lepton_mass_spectrum_at_xi_mev(XI_LOCKIN)
    tau_lead, mu_lead, e_lead = lepton_mass_spectrum_at_xi_mev_leading_only(XI_LOCKIN)
    _, legacy_mu, legacy_e = lepton_mass_spectrum_at_xi_mev_legacy(XI_LOCKIN)

    g2_rows = [
        _row_anomalous_moment(
            "a_e (TUFT APS spurion, n=1)",
            tuft_anomalous_moment_spurion(1),
            "a_e",
            "tuftAnomalousMomentSpurion",
        ),
        _row_anomalous_moment(
            "a_μ (TUFT APS spurion, n=2)",
            tuft_anomalous_moment_spurion(2),
            "a_mu",
            "tuftAnomalousMomentSpurion",
        ),
    ]

    lepton_rows = [
        _row("τ (T8 full @ ξ_lock)", tau, "tau", "leptonMassSpectrum_at_xi_from_vev_T8_MeV"),
        _row("μ (T8 full)", mu, "mu", "leptonMassSpectrum_at_xi_from_vev_T8_MeV"),
        _row("e (T8 full)", e, "e", "leptonMassSpectrum_at_xi_from_vev_T8_MeV"),
        _row("μ (leading T8 only; diagnostic)", mu_lead, "mu", "leptonMassSpectrum_at_xi_from_vev_MeV"),
        _row("e (leading T8 only; diagnostic)", e_lead, "e", "tuftLeptonGeometricScalar"),
        _row("legacy μ shell quotient", legacy_mu, "mu", "legacyLeptonMassSpectrum_at_xi"),
        _row("legacy e shell quotient", legacy_e, "e", "legacyLeptonMassSpectrum_at_xi"),
    ]

    neutrino_rows: list[PdgRow] = []
    try:
        import hqiv_tuft_neutrino_bridge as nu_bridge
    except ImportError:
        nu_bridge = None  # type: ignore[assignment,misc]
    if nu_bridge is not None:
        nu = nu_bridge.model_tuft_outer_t8_t10(XI_LOCKIN)
        nu_sum_mev = nu.m1_mev + nu.m2_mev + nu.m3_mev
        cosmology_limit_mev = 0.12 * 1.0e-6
        neutrino_rows = [
            PdgRow("ν₃ TUFT outer-Casimir @ ξ_lock", nu.m3_mev, None, None, "neutrinoMassSpectrum_at_xi_from_T10_MeV"),
            PdgRow("ν₂ TUFT outer-Casimir @ ξ_lock", nu.m2_mev, None, None, "neutrinoMassSpectrum_at_xi_from_T10_MeV"),
            PdgRow("ν₁ TUFT outer-Casimir @ ξ_lock", nu.m1_mev, None, None, "neutrinoMassSpectrum_at_xi_from_T10_MeV"),
            PdgRow(
                "Σm_ν TUFT vs cosmology cap 0.12 eV",
                nu_sum_mev,
                cosmology_limit_mev,
                nu_sum_mev / cosmology_limit_mev,
                "tuftOuterCasimirDressingAtXi",
            ),
        ]

    quark_rows = build_quark_rows(XI_LOCKIN)

    ew_boson_rows = [
        _row("W (outer closure × vev scale)", ew.tuft_mw_at_xi_gev(XI_LOCKIN) * 1000.0, None, "tuftMW_atXi_GeV", unit="GeV", pdg_gev="W"),
        _row("Z (W / cos θ_W geometric)", ew.tuft_mz_at_xi_gev(XI_LOCKIN) * 1000.0, None, "tuftMZ_atXi_GeV", unit="GeV", pdg_gev="Z"),
        _row("H (√(2λ) v pinned)", ew.tuft_mh_at_xi_gev(XI_LOCKIN) * 1000.0, None, "tuftMH_atXi_GeV", unit="GeV", pdg_gev="H"),
        _row("H (scalar closure; diagnostic)", ew.tuft_mh_scalar_closure_at_xi_gev(XI_LOCKIN) * 1000.0, None, "tuftMH_scalarClosure_atXi_GeV", unit="GeV", pdg_gev="H"),
        _row("Z (naive g_SU2+g_U1; diagnostic)", ew.M_Z_NAIVE_GEV * 1000.0, None, "M_Z_derived", unit="GeV", pdg_gev="Z"),
    ]

    hadron_ground_rows = [
        _row("proton vev-pinned @ ξ_lock", tuft_hadron_ground_at_xi_mev(XI_LOCKIN), "proton", "tuftHadronGroundAtXi_MeV"),
        _row(
            "proton (derived ground, diagnostic)",
            PROTON_MEV,
            "proton",
            "derivedProtonMass",
        ),
    ]

    return [
        SpectrumSection("Charged leptons (vev → T8)", lepton_rows),
        SpectrumSection("Anomalous magnetic moment (TUFT APS spurion)", g2_rows),
        SpectrumSection("Neutrinos (outer T8+T10)", neutrino_rows),
        SpectrumSection("Quark family (vev-pinned + resonance ladder)", quark_rows),
        SpectrumSection("Electroweak bosons (outer closure + Weinberg)", ew_boson_rows),
        SpectrumSection("Baryon ground", hadron_ground_rows),
        SpectrumSection(
            "Hadron excited states (global readout)",
            build_hadron_global_rows(),
        ),
        SpectrumSection("Superseded / diagnostic readouts", build_diagnostic_hadron_rows()),
    ]


def build_diagnostic_hadron_rows(xi: float = XI_LOCKIN) -> list[PdgRow]:
    """Superseded readouts kept for regression only."""
    return [
        _row(
            "Δ(1232) trapped Planck (n=1, ℓ=0)",
            hes.meta_horizon_trapped_planck_mass_mev(1, 0, derived_proton_mev=PROTON_MEV),
            "Delta(1232)",
            "metaHorizonTrappedPlanckMassReadout",
        ),
        _row(
            "Δ(1232) meta-horizon catalog (n=1, ℓ=0)",
            meta_horizon_excited_mass_mev(1, 0),
            "Delta(1232)",
            "metaHorizonExcitedMassReadout",
        ),
        _row(
            "ρ vector catalog (strong-chart, ℓ=1)",
            meson_vector_excited_mass_mev(PROTON_MEV),
            "rho",
            "mesonVectorExcitedMassReadout",
        ),
        _row(
            "lepton-seeded tower (n=1, ℓ=0) diagnostic",
            tuft_excited_heavy_mass_at_xi_mev(XI_LOCKIN, 1, 0),
            "Delta(1232)",
            "tuftExcitedHeavyMassAtXi",
        ),
        _row(
            "Δ(1232) vev + global G(ξ,n,ℓ) [superseded]",
            hge.tuft_hadron_excited_mass_with_global_correction_at_xi_mev(xi, 0, 1),
            "Delta(1232)",
            "tuftHadronExcitedMassWithGlobalCorrectionAtXi_MeV",
        ),
        _row(
            "Δ(1232) S⁷ whole envelope [superseded]",
            h7.tuft_hadron_whole_s7_mass_at_xi_mev(xi, 0, 1),
            "Delta(1232)",
            "tuftHadronWholeS7MassAtXi_MeV",
        ),
    ]


def build_rows() -> list[PdgRow]:
    """Flat row list (all sections) for JSON export."""
    rows: list[PdgRow] = []
    for section in build_spectrum_sections():
        rows.extend(section.rows)
    return rows


def _format_mass(r: PdgRow) -> tuple[str, str]:
    def fmt(val: float | None, unit: str) -> str:
        if val is None:
            return f"{'—':>16}"
        if unit == "GeV":
            return f"{val / 1000.0:16.6f}"
        if abs(val) < 1.0e-3 and val != 0.0:
            return f"{val:16.6e}"
        return f"{val:16.4f}"

    unit = r.unit
    return fmt(r.hqiv_mev, unit), fmt(r.pdg_mev, unit)


def print_meson_benchmark_summary(xi: float = XI_LOCKIN) -> None:
    """Primary meson + baryon slots on the single global readout."""
    print()
    print("=== Global readout vs PDG precision (σ) and width (Γ) ===")
    print(
        f"{'sector':<8} {'meson/baryon':<14} {'readout':<22} {'HQIV':>10} {'PDG':>10} "
        f"{'±σ':>8} {'Δ':>8} {'|Δ|/σ':>8} {'Γ':>8} {'|Δ|/Γ':>8}"
    )
    print("-" * 110)
    channels = [c for c in tgh.MESON_EXCITED_CHANNELS + tgh.BARYON_EXCITED_CHANNELS if c.pdg_key]
    seen: set[str] = set()
    for ch in channels:
        key = ch.pdg_key
        assert key is not None
        dedupe = f"{ch.valence_quarks}:{key}"
        if dedupe in seen:
            continue
        seen.add(dedupe)
        hqiv = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
        sector = "meson" if ch.is_meson else "baryon"
        row = _row(f"{sector} {key} global", hqiv, key, "tuftExcitedMassGlobalAtXi_MeV")
        pdg = row.pdg_mev
        sig = row.pdg_sigma_mev
        width = row.pdg_width_mev
        if pdg is None:
            continue
        print(
            f"{sector:<8} {key:<14} {'tuftExcitedMassGlobal':<22} {hqiv:10.2f} {pdg:10.2f} "
            f"{(sig if sig is not None else 0):8.3f} {(row.delta_mev if row.delta_mev is not None else 0):+8.2f} "
            f"{(row.sigma_n if row.sigma_n is not None else 0):8.1f} "
            f"{(width if width is not None else 0):8.1f} "
            f"{(row.delta_over_width if row.delta_over_width is not None else 0):8.3f}"
        )
    print(
        "Note: one formula for all — m = g·[1+(R_in−1)·G_twist]; "
        "R_in discrete at full closure (w=1), split if w<1."
    )


def print_spectrum(sections: list[SpectrumSection]) -> None:
    for section in sections:
        if not section.rows:
            continue
        print()
        print(f"=== {section.title} ===")
        unit_hdr = "GeV" if section.title.startswith("Quark") else "MeV"
        show_sigma = section.title.startswith("Meson") or section.title.startswith("Hadron")
        if show_sigma:
            print(
                f"{'Observable':<44} {f'HQIV [{unit_hdr}]':>16} {f'PDG [{unit_hdr}]':>16} "
                f"{'±σ':>8} {'|Δ|/σ':>8} {'|Δ|/Γ':>8}  Lean slot"
            )
            print("-" * 118)
        else:
            print(f"{'Observable':<44} {f'HQIV [{unit_hdr}]':>16} {f'PDG [{unit_hdr}]':>16} {'ratio':>10}  Lean slot")
            print("-" * 105)
        for r in section.rows:
            hqiv, pdg = _format_mass(r)
            ratio = f"{r.ratio:10.4f}" if r.ratio is not None else f"{'—':>10}"
            if show_sigma and r.pdg_mev is not None:
                sig = f"{r.pdg_sigma_mev:8.3f}" if r.pdg_sigma_mev is not None else f"{'—':>8}"
                nsig = f"{r.sigma_n:8.1f}" if r.sigma_n is not None else f"{'—':>8}"
                dgam = f"{r.delta_over_width:8.3f}" if r.delta_over_width is not None else f"{'—':>8}"
                print(f"{r.observable:<44} {hqiv} {pdg} {sig} {nsig} {dgam}  {r.lean_slot}")
            else:
                print(f"{r.observable:<44} {hqiv} {pdg} {ratio}  {r.lean_slot}")


def lepton_mass_spectrum_at_xi_mev_legacy(xi: float) -> tuple[float, float, float]:
    heavy, mu, e = legacy_shell_quotient_spectrum_at_xi(xi)
    lock = heavy_lepton_gap_at_xi(XI_LOCKIN)
    # Legacy diagnostic only: put the shell-quotient ratios on the vev-derived
    # heavy scale so the old mismatch can be compared without a mass anchor.
    scale = tuft_lepton_mass_from_vev_at_xi_mev(XI_LOCKIN, 3) / lock
    return heavy * scale, mu * scale, e * scale


def main() -> None:
    parser = argparse.ArgumentParser(description="TUFT/HQIV mass spectrum vs PDG")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    sections = build_spectrum_sections()
    if args.json:
        payload = [
            {"section": s.title, "rows": [asdict(r) for r in s.rows]} for s in sections
        ]
        print(json.dumps(payload, indent=2))
        return
    print(f"TUFT/HQIV mass spectrum @ ξ_lock = {XI_LOCKIN:g}")
    print_spectrum(sections)
    print_meson_benchmark_summary()


if __name__ == "__main__":
    main()
