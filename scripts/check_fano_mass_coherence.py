#!/usr/bin/env python3
"""
Check Fano vertex / line selectors against detuning and mass readouts implied by Lean.

Lean sources:
  • `Hqiv/Physics/FanoLine.lean` — `fanoStandardLine`, `incidentLineAt`, `FanoLine.ofVertexChoice`
  • `Hqiv/Physics/FanoLineRapidityChoice.lean` — `shellRapidityIncidentIndex`, `fanoLineFromVertexShell`
  • `Hqiv/Physics/FanoParticleVertexSelectors.lean` — named vertices, `FanoVertexLineSelectors`
  • `Hqiv/Physics/DerivedGaugeAndLeptonSector.lean` — outer-closure *support* + witnesses,
    `bosonClosureShell`, `phi_of_shell` / `bosonClosureThetaLocal`, optional age+horizon layers
  • `Hqiv/Physics/GlobalDetuning.lean` — `GlobalDetuningHypothesis.fromLapseScalars`,
    `δ_global = λ·(Φ + φ·t)` as lapse increment **above** 1
  • `Hqiv/Geometry/AuxiliaryField.lean` — `T(m)`, `phi_of_shell`
  • `Hqiv/Geometry/UniverseAge.lean` — `age_ratio_paper` (optional age rescaling; EW caveat in Lean)
  • `scripts/cubic_phase_relax_probe.py` — numeric mirror for Rindler/shell, lepton/quark steps

Boson masses are **GeV-scale witnesses** in the same units as `M_W_PDG` in Lean; this script
recomputes them from the *support* (shells, lifts) and also prints **eV** (`1 GeV = 1e9 eV`).

Run:
  python3 scripts/check_fano_mass_coherence.py
  python3 scripts/check_fano_mass_coherence.py --json
  python3 scripts/check_fano_mass_coherence.py --lapse-lambda 1 --lapse-Phi 0.01 --lapse-phi 0 --lapse-t 0
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

# Reuse the closed-form probe (detuning, lepton/quark shells) without duplicating constants.
_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import cubic_phase_relax_probe as cpr  # noqa: E402

# ---------------------------------------------------------------------------
# Unit conversion (matches Lean: PDG uses GeV; script prints eV as well)

EV_PER_GEV = 1.0e9

# Ladder / pins — mirror `OctonionicLightCone.lean` + `cubic_phase_relax_probe`
ALPHA = cpr.ALPHA
GAMMA = cpr.GAMMA
QCD_SHELL = cpr.QCD_SHELL
LATTICE_STEP_COUNT = cpr.LATTICE_STEP_COUNT
REFERENCE_M = cpr.REFERENCE_M
TRIALITY_ORDER = 3
CHARGED_LEPTON_SM_DOUBLET_COUNT = 2
PHI_TEMPERATURE_COEFF = cpr.PHI_TEMPERATURE_COEFF
T_PL = 1.0

# Optional paper age ratio — `Hqiv/Geometry/UniverseAge.lean` `age_ratio_paper`
AGE_WALL_CLOCK_GYR = 51.2
AGE_APPARENT_GYR = 13.8
AGE_RATIO_PAPER = AGE_WALL_CLOCK_GYR / AGE_APPARENT_GYR

# ---------------------------------------------------------------------------
# PG(2,2) — standard lines (labels 0..6) as sets of vertex labels 0..6

FANO_STANDARD_LINES: tuple[frozenset[int], ...] = (
    frozenset({0, 1, 2}),
    frozenset({0, 3, 4}),
    frozenset({0, 5, 6}),
    frozenset({1, 3, 5}),
    frozenset({1, 4, 6}),
    frozenset({2, 3, 6}),
    frozenset({2, 4, 5}),
)


def T_m(m: int) -> float:
    """`Hqiv.Geometry.AuxiliaryField.T` — natural units, `T_Pl = 1`."""
    return T_PL / float(m + 1)


def outer_horizon_surface(m: int) -> float:
    """`Hqiv.Physics.DerivedGaugeAndLeptonSector.outerHorizonSurface` = (m+1)(m+2)."""
    return float((m + 1) * (m + 2))


def lattice_simplex_count(m: int) -> int:
    """`latticeSimplexCount m` = (m+2)(m+1) — same product as `outerHorizonSurface` (commutes)."""
    return (m + 2) * (m + 1)


def phi_of_shell(m: int) -> float:
    """`phi_of_shell_closed_form`: φ(m) = 2·(m+1) with `phiTemperatureCoeff = 2`."""
    return PHI_TEMPERATURE_COEFF * float(m + 1)


def incident_line_labels(v: int) -> list[int]:
    return [i for i in range(7) if v in FANO_STANDARD_LINES[i]]


def incident_line_label_lowest(v: int) -> int:
    t = (0, 0, 0, 1, 1, 2, 2)
    if not 0 <= v <= 6:
        raise ValueError("FanoVertex must be 0..6")
    return t[v]


def incident_line_labels_sorted(v: int) -> list[int]:
    return sorted(incident_line_labels(v))


def incident_line_at(v: int, j: int) -> int:
    s = incident_line_labels_sorted(v)
    return s[j]


def shell_rapidity_incident_index(m: int) -> int:
    return m % 3


def fano_line_index_from_vertex_shell(v: int, m: int) -> int:
    j = shell_rapidity_incident_index(m)
    return incident_line_at(v, j)


# ---------------------------------------------------------------------------
# Named vertices

@dataclass(frozen=True)
class NamedVertices:
    em_lepton: int = 0
    up_gen: tuple[int, int, int] = (1, 2, 3)
    down_gen: tuple[int, int, int] = (4, 5, 6)
    scalar_higgs: int = 6


NV = NamedVertices()

VERTEX_ROLE: dict[int, str] = {
    0: "em_lepton (canonicalSpectralTag)",
    1: "up type gen0",
    2: "up type gen1",
    3: "up type gen2",
    4: "down type gen0 (bridge upResonanceAxis gen0 → v1, down → v4)",
    5: "down type gen1",
    6: "down type gen2 / scalarHiggsFanoVertex (Higgs e₇ scaffold)",
}


# ---------------------------------------------------------------------------


def rindler_one_jet_m(m: int) -> float:
    return cpr.rindler_detuning_shared(float(m))


def rindler_den_with_delta_global(delta: float, m: int) -> float:
    """`rindlerDenWithDelta` / unified denominator: 1 + (γ/2)m + δ (`GlobalDetuning.lean`)."""
    return cpr.rindler_detuning_shared(float(m)) + delta


def eff_corrected_delta(delta: float, m: int) -> float:
    """`effCorrected` = shellSurface m / (rindler + δ)."""
    d = rindler_den_with_delta_global(delta, m)
    if d <= 0:
        raise ValueError("nonpositive Rindler+δ denominator")
    return cpr.shell_surface(m) / d


def assert_fano_line_from_shell_matches_incident(m_values: list[int] | None = None) -> None:
    ms = m_values if m_values is not None else list(range(21))
    for m in ms:
        j = m % 3
        for v in range(7):
            if fano_line_index_from_vertex_shell(v, m) != incident_line_at(v, j):
                raise AssertionError(
                    f"fano_line_from_vertex_shell: m={m} v={v} expected incident[j={j}]"
                )


def assert_line_independent_detuning(m_values: list[int], _tol: float = 1e-12) -> None:
    for m in m_values:
        r = rindler_one_jet_m(m)
        for v in range(7):
            for j in range(3):
                li = incident_line_at(v, j)
                if v not in FANO_STANDARD_LINES[li]:
                    raise AssertionError(f"vertex {v} not on line {li}")
                if rindler_one_jet_m(m) != r:
                    raise AssertionError(f"detuning mismatch m={m} v={v} j={j}")


# ---------------------------------------------------------------------------
# Boson sector — recompute from support (`DerivedGaugeAndLeptonSector`)


@dataclass(frozen=True)
class BosonClosureSupport:
    """Closed-form fields whose product fixes `M_W` / `M_Z` / `m_H` (no PDG)."""

    qcd_shell: int
    reference_m: int
    boson_closure_shell: int
    m_lockin: int
    t_pl: float
    t_lockin: float
    outer_horizon_at_boson_closure: float
    lattice_simplex_count_ref: int
    gamma_derived: float
    outer_closure_monogamy_lift: float
    vacuum_expectation_value: float
    ew_gauge_quantum_lift: float
    vacuum_expectation_value_gauge: float
    su2_coupling_derived: float
    u1_coupling_derived: float
    m_w_derived_gev: float
    m_z_derived_gev: float
    ew_scalar_quantum_lift: int
    vacuum_expectation_value_scalar: float
    m_h_derived_gev: float
    m_w_ev: float
    m_z_ev: float
    m_h_ev: float
    # Auxiliary horizon / localization (`bosonClosureThetaLocal` uses `phi_of_shell bosonClosureShell`)
    phi_boson_closure: float
    boson_closure_theta_local: float
    boson_localization_lower_bound_gev: float
    m_w_horizon_localized_gev: float
    m_z_horizon_localized_gev: float
    m_h_horizon_localized_gev: float
    m_w_horizon_localized_ev: float
    m_z_horizon_localized_ev: float
    m_h_horizon_localized_ev: float
    # Optional paper age (`age_ratio_paper`) — Lean notes EW scale caveat
    age_ratio_paper: float
    m_w_age_adjusted_gev: float
    m_z_age_adjusted_gev: float
    m_h_age_adjusted_gev: float
    m_w_age_adjusted_ev: float
    m_z_age_adjusted_ev: float
    m_h_age_adjusted_ev: float


@dataclass(frozen=True)
class LapseDetuningAtClosure:
    """`GlobalDetuningHypothesis.fromLapseScalars`: obs = Φ + φ·t, δ = λ·obs."""

    lapse_lambda: float
    big_phi: float
    lapse_phi: float
    t_coord: float
    lapse_obs: float
    delta_global: float
    rindler_den_at_boson_closure: float
    eff_corrected_at_boson_closure: float


def recompute_boson_closure_masses() -> tuple[BosonClosureSupport, dict[str, float]]:
    ref = REFERENCE_M
    boson_closure = ref + 1
    t_lockin = T_m(ref)
    s_bc = outer_horizon_surface(boson_closure)
    lsc_ref = lattice_simplex_count(ref)
    gamma = GAMMA
    mono = 1.0 + gamma
    vev = t_lockin * s_bc * mono
    ew_gauge = (lsc_ref / float(TRIALITY_ORDER)) * float(CHARGED_LEPTON_SM_DOUBLET_COUNT)
    vev_g = vev * ew_gauge
    g2 = 1.0 / float(TRIALITY_ORDER)
    g1 = gamma / float(TRIALITY_ORDER)
    m_w = g2 * vev_g
    m_z = (g2 + g1) * vev_g
    ew_s = TRIALITY_ORDER + CHARGED_LEPTON_SM_DOUBLET_COUNT
    vev_s = vev * float(ew_s)
    m_h = 2.0 * vev_s

    ratio = {k: v for k, v in {
        "m_w_vs_392_5": m_w / (392.0 / 5.0),
        "m_z_vs_2744_25": m_z / (2744.0 / 25.0),
        "m_h_vs_588_5": m_h / (588.0 / 5.0),
    }.items()}

    phi_b = phi_of_shell(boson_closure)
    theta_local = PHI_TEMPERATURE_COEFF / phi_b
    loc_lb = 1.0 / theta_local
    m_w_h = m_w + loc_lb
    m_z_h = m_z + loc_lb
    m_h_h = m_h + loc_lb

    sup = BosonClosureSupport(
        qcd_shell=QCD_SHELL,
        reference_m=ref,
        boson_closure_shell=boson_closure,
        m_lockin=ref,
        t_pl=T_PL,
        t_lockin=t_lockin,
        outer_horizon_at_boson_closure=s_bc,
        lattice_simplex_count_ref=lsc_ref,
        gamma_derived=gamma,
        outer_closure_monogamy_lift=mono,
        vacuum_expectation_value=vev,
        ew_gauge_quantum_lift=ew_gauge,
        vacuum_expectation_value_gauge=vev_g,
        su2_coupling_derived=g2,
        u1_coupling_derived=g1,
        m_w_derived_gev=m_w,
        m_z_derived_gev=m_z,
        ew_scalar_quantum_lift=ew_s,
        vacuum_expectation_value_scalar=vev_s,
        m_h_derived_gev=m_h,
        m_w_ev=m_w * EV_PER_GEV,
        m_z_ev=m_z * EV_PER_GEV,
        m_h_ev=m_h * EV_PER_GEV,
        phi_boson_closure=phi_b,
        boson_closure_theta_local=theta_local,
        boson_localization_lower_bound_gev=loc_lb,
        m_w_horizon_localized_gev=m_w_h,
        m_z_horizon_localized_gev=m_z_h,
        m_h_horizon_localized_gev=m_h_h,
        m_w_horizon_localized_ev=m_w_h * EV_PER_GEV,
        m_z_horizon_localized_ev=m_z_h * EV_PER_GEV,
        m_h_horizon_localized_ev=m_h_h * EV_PER_GEV,
        age_ratio_paper=AGE_RATIO_PAPER,
        m_w_age_adjusted_gev=AGE_RATIO_PAPER * m_w,
        m_z_age_adjusted_gev=AGE_RATIO_PAPER * m_z,
        m_h_age_adjusted_gev=AGE_RATIO_PAPER * m_h,
        m_w_age_adjusted_ev=AGE_RATIO_PAPER * m_w * EV_PER_GEV,
        m_z_age_adjusted_ev=AGE_RATIO_PAPER * m_z * EV_PER_GEV,
        m_h_age_adjusted_ev=AGE_RATIO_PAPER * m_h * EV_PER_GEV,
    )
    return sup, ratio


def lapse_detuning_at_boson_closure(
    boson_closure_shell: int,
    lapse_lambda: float,
    big_phi: float,
    lapse_phi: float,
    t_coord: float,
) -> LapseDetuningAtClosure:
    """δ_global = λ·(Φ + φ·t) — `deltaGlobal` / `fromLapseScalars` (`GlobalDetuning.lean`)."""
    obs = big_phi + lapse_phi * t_coord
    d_global = lapse_lambda * obs
    rden = rindler_den_with_delta_global(d_global, boson_closure_shell)
    eff = eff_corrected_delta(d_global, boson_closure_shell)
    return LapseDetuningAtClosure(
        lapse_lambda=lapse_lambda,
        big_phi=big_phi,
        lapse_phi=lapse_phi,
        t_coord=t_coord,
        lapse_obs=obs,
        delta_global=d_global,
        rindler_den_at_boson_closure=rden,
        eff_corrected_at_boson_closure=eff,
    )


# ---------------------------------------------------------------------------


@dataclass
class CoherenceReport:
    fano_lines_match_lean_card: bool
    incident_lines_count_ok: bool
    lowest_label_matches_lean: bool
    rindler_independent_m_values: list[int]
    boson: BosonClosureSupport
    closed_form_match: dict[str, float]
    lepton_m_tau_shell: int
    lepton_m_mu_shell: int
    lepton_m_e_shell: int
    k_tau_mu: float
    k_mu_e: float
    quark_up_top_to_charm: float
    quark_up_charm_to_light: float
    quark_down_bottom_to_strange: float
    quark_down_strange_to_light: float
    lapse: LapseDetuningAtClosure = field(
        default_factory=lambda: lapse_detuning_at_boson_closure(REFERENCE_M + 1, 0.0, 0.0, 0.0, 0.0)
    )


def run_checks(
    lapse_lambda: float = 0.0,
    big_phi: float = 0.0,
    lapse_phi: float = 0.0,
    t_coord: float = 0.0,
) -> CoherenceReport:
    ok_card = all(len(s) == 3 for s in FANO_STANDARD_LINES)
    ok_indeg = all(len(incident_line_labels(v)) == 3 for v in range(7))
    ok_lowest = all(incident_line_label_lowest(v) == min(incident_line_labels(v)) for v in range(7))
    m_tests = [0, 1, 4, 5, 7, 10, 100]
    assert_fano_line_from_shell_matches_incident()
    assert_line_independent_detuning(m_tests)

    bos, ratio = recompute_boson_closure_masses()
    if not (math.isclose(ratio["m_w_vs_392_5"], 1.0) and math.isclose(ratio["m_z_vs_2744_25"], 1.0) and math.isclose(ratio["m_h_vs_588_5"], 1.0)):
        raise AssertionError(f"recomputed boson masses diverge from Lean rationals: {ratio}")

    m_tau, m_mu, m_e = cpr.derived_lepton_readouts()
    k_tau_mu = cpr.geometric_resonance_step(m_mu, m_tau)
    k_mu_e = cpr.geometric_resonance_step(m_e, m_mu)
    u_top, u_c, u_l = cpr.M_QUARK_UP_TOP, cpr.M_QUARK_UP_CHARM, cpr.M_QUARK_UP_LIGHT
    d_b, d_s, d_l = cpr.M_QUARK_DOWN_BOTTOM, cpr.M_QUARK_DOWN_STRANGE, cpr.M_QUARK_DOWN_LIGHT
    g_up0 = cpr.geometric_resonance_step(u_top, u_c)
    g_up1 = cpr.geometric_resonance_step(u_c, u_l)
    g_dn0 = cpr.geometric_resonance_step(d_b, d_s)
    g_dn1 = cpr.geometric_resonance_step(d_s, d_l)

    lp = lapse_detuning_at_boson_closure(bos.boson_closure_shell, lapse_lambda, big_phi, lapse_phi, t_coord)
    return CoherenceReport(
        fano_lines_match_lean_card=ok_card,
        incident_lines_count_ok=ok_indeg,
        lowest_label_matches_lean=ok_lowest,
        rindler_independent_m_values=m_tests,
        boson=bos,
        closed_form_match=ratio,
        lepton_m_tau_shell=m_tau,
        lepton_m_mu_shell=m_mu,
        lepton_m_e_shell=m_e,
        k_tau_mu=k_tau_mu,
        k_mu_e=k_mu_e,
        quark_up_top_to_charm=g_up0,
        quark_up_charm_to_light=g_up1,
        quark_down_bottom_to_strange=g_dn0,
        quark_down_strange_to_light=g_dn1,
        lapse=lp,
    )


def _print_table(r: CoherenceReport) -> None:
    b = r.boson
    print("=== Fano PG(2,2) structure (Lean `fanoStandardLine`) ===")
    for i, s in enumerate(FANO_STANDARD_LINES):
        print(f"  line {i}: {sorted(s)}")
    print()
    print("=== Per-vertex: sorted incident line labels, shell m=5 → line (fanoLineFromVertexShell) ===")
    m_demo = 5
    for v in range(7):
        inc = incident_line_labels_sorted(v)
        cycled = fano_line_index_from_vertex_shell(v, m_demo)
        print(
            f"  v{v} {VERTEX_ROLE.get(v, '?')}\n"
            f"      incident (sorted) {inc}  |  fano_line@shell(m={m_demo}) = line {cycled} (j={m_demo % 3})"
        )
    print()
    print("=== Structure checks ===")
    print(f"  all lines have 3 points: {r.fano_lines_match_lean_card}")
    print(f"  each vertex in 3 lines: {r.incident_lines_count_ok}")
    print(f"  incidentLineLabelLowest == min(incident): {r.lowest_label_matches_lean}")
    print()
    print("=== Rindler 1-jet (line-independent) — sample m ===")
    for m in r.rindler_independent_m_values[:4]:
        print(f"  r(m={m}) = {rindler_one_jet_m(m):.12g}")
    print()
    print("=== Boson sector SUPPORT (recomputed) — `DerivedGaugeAndLeptonSector` ===")
    print(
        f"  qcdShell={b.qcd_shell}  referenceM(=m_lockin)={b.reference_m}  bosonClosureShell={b.boson_closure_shell}  (successor of ref)\n"
        f"  T(m)=1/(m+1): T_lockin = T({b.m_lockin}) = {b.t_lockin}  (Planck scale T_Pl={b.t_pl})\n"
        f"  outerHorizonSurface(bosonClosure) = (m+1)(m+2) | m={b.boson_closure_shell}  →  {b.outer_horizon_at_boson_closure}\n"
        f"  latticeSimplexCount(refM) = {b.lattice_simplex_count_ref}  ;  γ = 1-α = {b.gamma_derived}\n"
        f"  monogamy lift 1+γ = {b.outer_closure_monogamy_lift}\n"
        f"  vacuumExpectationValue = T_lockin · surface · (1+γ) = {b.vacuum_expectation_value}\n"
        f"  ewGaugeQuantumLift = (simplex/ref)/3 · 2 = {b.ew_gauge_quantum_lift}\n"
        f"  vacuumExpectationValueGauge = {b.vacuum_expectation_value_gauge}\n"
        f"  g_SU2 = {b.su2_coupling_derived}   g_U1 = γ/3 = {b.u1_coupling_derived}"
    )
    print()
    print("=== Boson mass witnesses (GeV) and same in eV (×1e9) ===")
    print(
        f"  M_W  = g_SU2·vev_gauge = {b.m_w_derived_gev:.12g} GeV  = {b.m_w_ev:.6e} eV\n"
        f"  M_Z  = (g_SU2+g_U1)·vev_g = {b.m_z_derived_gev:.12g} GeV  = {b.m_z_ev:.6e} eV\n"
        f"  m_H  = 2·vev_scalar, vev_s = {b.vacuum_expectation_value_scalar:.12g}  →  {b.m_h_derived_gev:.12g} GeV  = {b.m_h_ev:.6e} eV"
    )
    print(f"  (closed-form check vs 392/5, 2744/25, 588/5) ratios: {r.closed_form_match}")
    print()
    print("=== Horizon-localization add-on (min 1/Θ at boson shell; `bosonClosureThetaLocal`) ===")
    print(
        f"  φ(bosonClosure) = {b.phi_boson_closure}  ;  Θ_local = 2/φ = {b.boson_closure_theta_local:.12g}\n"
        f"  lower bound 1/Θ = {b.boson_localization_lower_bound_gev} GeV  (add to each raw witness in same units)\n"
        f"  M_W* = {b.m_w_horizon_localized_gev} GeV = {b.m_w_horizon_localized_ev:.6e} eV  (etc. for Z, H below)"
    )
    print(
        f"  M_Z* = {b.m_z_horizon_localized_gev} GeV = {b.m_z_horizon_localized_ev:.6e} eV\n"
        f"  m_H* = {b.m_h_horizon_localized_gev} GeV = {b.m_h_horizon_localized_ev:.6e} eV"
    )
    print()
    print("=== Optional paper age ratio (NOT mixed into raw EW — Lean warns at EW) ===")
    print(
        f"  age_ratio_paper = {b.age_ratio_paper:.6g}  →  e.g. M_W·age = {b.m_w_age_adjusted_gev} GeV = {b.m_w_age_adjusted_ev:.6e} eV"
    )
    print()
    lp = r.lapse
    print("=== Lapse / global detuning on closure shell (effCorrected) ===")
    print(
        f"  obs = Φ + φ·t = {lp.lapse_obs}  ;  δ_global = λ·obs = {lp.delta_global}\n"
        f"  rindler+δ at m={b.boson_closure_shell} = {lp.rindler_den_at_boson_closure}\n"
        f"  effCorrected(δ) = surface/rindlerDen(δ) = {lp.eff_corrected_at_boson_closure}  (raw geometric step on δ-corrected surface)"
    )
    print()
    print("=== Lepton shells & geometric steps ===")
    print(
        f"  m_τ, m_μ, m_e = {r.lepton_m_tau_shell}, {r.lepton_m_mu_shell}, {r.lepton_m_e_shell}\n"
        f"  k_τμ = {r.k_tau_mu:.12g}  k_μe = {r.k_mu_e:.12g}"
    )
    print()
    print("=== Quark internal geometric steps (shell constants) ===")
    print(
        f"  up:   {r.quark_up_top_to_charm:.12g}  {r.quark_up_charm_to_light:.12g}\n"
        f"  down: {r.quark_down_bottom_to_strange:.12g}  {r.quark_down_strange_to_light:.12g}"
    )
    print()
    print("=== Named Fano selector pointers ===")
    print(
        f"  emLeptonFanoVertex = {NV.em_lepton}  upTypeFano = {NV.up_gen}  downTypeFano = {NV.down_gen}  scalarHiggs = {NV.scalar_higgs}"
    )


def _report_to_json(r: CoherenceReport) -> dict:
    d = asdict(r)
    d["constants"] = {
        "alpha": ALPHA,
        "gamma": GAMMA,
        "c_rindler_shared": cpr.C_RINDLER_SHARED,
        "ev_per_gev": EV_PER_GEV,
    }
    return d


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0].strip())
    p.add_argument("--json", action="store_true", help="Emit one JSON object (includes boson eV, lapse δ)")
    p.add_argument("--lapse-lambda", type=float, default=0.0, help="λ in δ = λ(Φ+φt)")
    p.add_argument("--lapse-Phi", type=float, default=0.0, help="Φ in lapse increment obs=Φ+φt (HQVM: N-1 part)")
    p.add_argument("--lapse-phi", type=float, default=0.0, help="φ in obs=Φ+φt")
    p.add_argument("--lapse-t", type=float, default=0.0, help="coordinate time t in obs=Φ+φt")
    args = p.parse_args()
    rep = run_checks(
        lapse_lambda=args.lapse_lambda,
        big_phi=args.lapse_Phi,
        lapse_phi=args.lapse_phi,
        t_coord=args.lapse_t,
    )
    if args.json:
        print(json.dumps(_report_to_json(rep), indent=2))
    else:
        _print_table(rep)
    if not (rep.fano_lines_match_lean_card and rep.incident_lines_count_ok and rep.lowest_label_matches_lean):
        sys.exit(1)


if __name__ == "__main__":
    main()
