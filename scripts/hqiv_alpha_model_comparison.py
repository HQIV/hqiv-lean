#!/usr/bin/env python3
"""
HQIV alpha_EM model comparison harness.

Compares three candidate routings on the atom benchmark panel:
  - global_brace:     `alpha_EM_primary` (Gauss m=3 -> EW m=5 double-axis brace)
  - nuclear_tracking: `alpha_eff_at_shell(m_nuc(A))`
  - electronic_tracking: shell-local `alpha_eff_at_shell(m_shell)` on discharge occupancy

Does **not** replace the canonical atom prediction path. Emits diagnostics,
witness JSON, and an explicit non-uniqueness audit.

Mirrors Lean:
  - `Hqiv.Physics.EffectiveAlphaReadout`
  - `Hqiv.Physics.BoundStates`
  - `Hqiv.QuantumChemistry.AtomOutsideCurvatureFight`

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_model_comparison.py
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_model_comparison.py --json
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_model_comparison.py --write-json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Literal

import hqiv_alpha_readout as alpha_readout
import hqiv_atom_construction as ac
import hqiv_isotope_hydrogenic_scales as ihs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
import hqiv_nuclear_inside_outside_binding as niob
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_scale_witness as sw

AlphaModel = Literal["global_brace", "nuclear_tracking", "electronic_tracking"]
ElectronicAggregation = Literal["outermost", "occupancy_mean", "valence_mean"]

BENCHMARK_ELEMENTS = ("H", "He", "Li", "C", "N", "O", "Na", "Fe")
DEFAULT_JSON_PATH = Path(__file__).resolve().parents[1] / "data" / "alpha_model_comparison_witnesses.json"

LEAN_MODULES = (
    "Hqiv.Physics.EffectiveAlphaReadout",
    "Hqiv.Physics.DoublePreferredAxisAlpha",
    "Hqiv.Physics.BoundStates",
    "Hqiv.QuantumChemistry.AtomOutsideCurvatureFight",
    "Hqiv.QuantumChemistry.AtomNucleusCurvatureShell",
    "Hqiv.QuantumChemistry.AtomElectronicDischarge",
)


class AlphaModelKind(str, Enum):
    GLOBAL_BRACE = "global_brace"
    NUCLEAR_TRACKING = "nuclear_tracking"
    ELECTRONIC_TRACKING = "electronic_tracking"


@dataclass(frozen=True)
class AlphaCandidateReadout:
    """Single alpha candidate with provenance."""

    model: AlphaModelKind
    inv_alpha: float
    alpha: float
    shell_source: str
    shell_m: int | None
    xi: float | None
    note: str

    def rel_error_vs_codata_inv(self, codata_inv: float = sw.CODATA_INV_ALPHA) -> float:
        return self.inv_alpha / codata_inv - 1.0


@dataclass(frozen=True)
class ElementAlphaPanel:
    element: str
    z: int
    mass_number: int
    m_nuc: int
    electron_shells: tuple[int, ...]
    global_brace: AlphaCandidateReadout
    nuclear_tracking: AlphaCandidateReadout
    electronic_outermost: AlphaCandidateReadout
    electronic_occupancy_mean: AlphaCandidateReadout
    electronic_valence_mean: AlphaCandidateReadout | None
    alpha_eff_lockin: AlphaCandidateReadout
    codata_comparison: AlphaCandidateReadout


@dataclass
class FightDiagnostics:
    """Outside-fight variants (alpha-ratio policy only; rest of formula unchanged)."""

    canonical_mev: float
    nuclear_ratio_policy_mev: float
    global_unity_ratio_mev: float
    ratio_policy_note: str


@dataclass
class HydrogenicDiagnostics:
    """Hydrogenic binding magnitude [MeV] under different alpha assignments."""

    canonical_mev: float
    global_brace_mev: float
    nuclear_tracking_mev: float
    electronic_outermost_mev: float


@dataclass
class ElementComparisonRow:
    element: str
    z: int
    alpha_panel: ElementAlphaPanel
    fight: FightDiagnostics
    hydrogenic: HydrogenicDiagnostics
    closed_mass_canonical_mev: float
    closed_mass_nuclear_fight_mev: float
    closed_mass_global_fight_mev: float
    nist_mass_amu: float | None
    relative_error_canonical_mass: float | None
    relative_error_nuclear_fight_mass: float | None
    first_ionization_ev_canonical: float
    nist_first_ionization_ev: float | None
    relative_error_ionization: float | None


@dataclass
class UniquenessAudit:
    summary: str
    open_assumptions: list[str]
    why_not_unique: list[str]
    candidate_routings: list[str]
    recommendation: str


@dataclass
class AlphaModelComparisonReport:
    lean_modules: tuple[str, ...] = field(default_factory=lambda: LEAN_MODULES)
    scale_witness: str = sw.DEFAULT_SCALE_WITNESS
    codata_inv_alpha: float = sw.CODATA_INV_ALPHA
    primary_global_inv_alpha: float = 0.0
    primary_global_vs_codata_pct: float = 0.0
    rows: list[ElementComparisonRow] = field(default_factory=list)
    uniqueness_audit: UniquenessAudit | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "lean_modules": list(self.lean_modules),
            "scale_witness": self.scale_witness,
            "codata_inv_alpha": self.codata_inv_alpha,
            "primary_global_inv_alpha": self.primary_global_inv_alpha,
            "primary_global_vs_codata_pct": self.primary_global_vs_codata_pct,
            "rows": [
                {
                    "element": r.element,
                    "z": r.z,
                    "alpha_panel": _alpha_panel_to_dict(r.alpha_panel),
                    "fight": asdict(r.fight),
                    "hydrogenic": asdict(r.hydrogenic),
                    "closed_mass_canonical_mev": r.closed_mass_canonical_mev,
                    "closed_mass_nuclear_fight_mev": r.closed_mass_nuclear_fight_mev,
                    "closed_mass_global_fight_mev": r.closed_mass_global_fight_mev,
                    "nist_mass_amu": r.nist_mass_amu,
                    "relative_error_canonical_mass": r.relative_error_canonical_mass,
                    "relative_error_nuclear_fight_mass": r.relative_error_nuclear_fight_mass,
                    "first_ionization_ev_canonical": r.first_ionization_ev_canonical,
                    "nist_first_ionization_ev": r.nist_first_ionization_ev,
                    "relative_error_ionization": r.relative_error_ionization,
                }
                for r in self.rows
            ],
            "uniqueness_audit": asdict(self.uniqueness_audit) if self.uniqueness_audit else None,
        }


def _alpha_candidate(
    model: AlphaModelKind,
    inv_alpha: float,
    *,
    shell_source: str,
    shell_m: int | None = None,
    xi: float | None = None,
    note: str = "",
) -> AlphaCandidateReadout:
    return AlphaCandidateReadout(
        model=model,
        inv_alpha=inv_alpha,
        alpha=1.0 / inv_alpha,
        shell_source=shell_source,
        shell_m=shell_m,
        xi=xi,
        note=note,
    )


def alpha_eff_lockin_readout(*, c: float = 1.0) -> AlphaCandidateReadout:
    m = lean.REFERENCE_M
    inv = ihs.one_over_alpha_eff_at_shell(m, c)
    return _alpha_candidate(
        AlphaModelKind.ELECTRONIC_TRACKING,
        inv,
        shell_source="alpha_eff_at_shell(referenceM)",
        shell_m=m,
        xi=float(m + 1),
        note="lock-in shell for outside-fight ratio denominator",
    )


def global_brace_readout(*, c_fano: float = 1.0) -> AlphaCandidateReadout:
    r = alpha_readout.resolve_alpha_em(c_fano=c_fano)
    return _alpha_candidate(
        AlphaModelKind.GLOBAL_BRACE,
        r.inv_alpha,
        shell_source="one_over_alpha_EM_double_axis (m=3 -> m=5 brace)",
        shell_m=None,
        xi=None,
        note=r.note,
    )


def nuclear_tracking_readout(a: int, *, c: float = 1.0) -> AlphaCandidateReadout:
    m = ncb.nucleus_curvature_shell(a) if a > 1 else lean.REFERENCE_M
    inv = ihs.one_over_alpha_eff_at_shell(m, c)
    return _alpha_candidate(
        AlphaModelKind.NUCLEAR_TRACKING,
        inv,
        shell_source="alpha_eff_at_shell(m_nuc(A))",
        shell_m=m,
        xi=float(m + 1),
        note=f"inside-ratio argmin drum at A={a}",
    )


def electronic_readout_at_shell(m: int, *, c: float = 1.0, label: str) -> AlphaCandidateReadout:
    inv = ihs.one_over_alpha_eff_at_shell(m, c)
    return _alpha_candidate(
        AlphaModelKind.ELECTRONIC_TRACKING,
        inv,
        shell_source=label,
        shell_m=m,
        xi=float(m + 1),
        note=f"discharge shell m={m}",
    )


def _occupancy_mean_inv_alpha(shells: list[int], *, c: float = 1.0) -> tuple[float, str]:
    if not shells:
        return float("nan"), "empty"
    invs = [ihs.one_over_alpha_eff_at_shell(m, c) for m in shells]
    return sum(invs) / len(invs), "mean over all electron discharge shells"


def _valence_mean_inv_alpha(shells: list[int], z: int, *, c: float = 1.0) -> tuple[float | None, str]:
    if z <= 2:
        return None, "no valence sector (Z<=2)"
    valence = shells[2:]
    if not valence:
        return None, "no valence shells booked"
    invs = [ihs.one_over_alpha_eff_at_shell(m, c) for m in valence]
    return sum(invs) / len(invs), "mean over valence discharge shells only"


def build_element_alpha_panel(element: str, *, c: float = 1.0) -> ElementAlphaPanel:
    z = ac.AtomComparisonLayer.z_for_element(element)
    a = ac.stable_mass_number_for_charge(z)
    shells = ac.atom_electron_shells(z)
    m_nuc = ncb.nucleus_curvature_shell(a) if a > 1 else lean.REFERENCE_M

    occ_mean_inv, _ = _occupancy_mean_inv_alpha(shells, c=c)
    val_mean_inv, _ = _valence_mean_inv_alpha(shells, z, c=c)

    outer_m = shells[-1] if shells else lean.REFERENCE_M

    valence_readout = None
    if val_mean_inv is not None:
        valence_readout = _alpha_candidate(
            AlphaModelKind.ELECTRONIC_TRACKING,
            val_mean_inv,
            shell_source="occupancy_mean(valence shells)",
            shell_m=None,
            xi=None,
            note="average 1/alpha_eff on valence discharge shells",
        )

    return ElementAlphaPanel(
        element=element,
        z=z,
        mass_number=a,
        m_nuc=m_nuc,
        electron_shells=tuple(shells),
        global_brace=global_brace_readout(),
        nuclear_tracking=nuclear_tracking_readout(a, c=c),
        electronic_outermost=electronic_readout_at_shell(
            outer_m, c=c, label="alpha_eff_at_shell(outermost discharge shell)"
        ),
        electronic_occupancy_mean=_alpha_candidate(
            AlphaModelKind.ELECTRONIC_TRACKING,
            occ_mean_inv,
            shell_source="occupancy_mean(all discharge shells)",
            shell_m=None,
            xi=None,
            note="average 1/alpha_eff over all booked electrons",
        ),
        electronic_valence_mean=valence_readout,
        alpha_eff_lockin=alpha_eff_lockin_readout(c=c),
        codata_comparison=_alpha_candidate(
            AlphaModelKind.GLOBAL_BRACE,
            sw.CODATA_INV_ALPHA,
            shell_source="CODATA comparison tier",
            note="never a proton_lockin solve input",
        ),
    )


def _outside_fight_with_alpha_ratio_policy(
    z: int,
    *,
    ratio_for_shell: Callable[[int, int, float], float],
    c: float = 1.0,
) -> float:
    """
    Recompute outside fight with a custom alpha-ratio policy.

    `ratio_for_shell(m_shell, m_nuc, ae_lock)` returns the factor replacing
    `(alpha_eff(m_shell)/alpha_eff(lock))^2` in the canonical formula.
    """
    if z <= 1:
        return 0.0
    a = ac.stable_mass_number_for_charge(z)
    m_nuc = ncb.nucleus_curvature_shell(a) if a > 1 else lean.REFERENCE_M
    _total_bind, _inside, b_out = niob.nuclear_cluster_binding_mev(
        m_nuc, a, m_cluster=m_nuc, c=c
    )
    if b_out <= 0.0:
        return 0.0
    b_out_per_nucleon = b_out / float(a)
    shells = ac.atom_electron_shells(z)
    ae_lock = ihs.alpha_eff_at_shell(lean.REFERENCE_M, c)
    exposure = float(z) / float(a)
    fight = 0.0
    for m_shell in shells:
        xi = float(m_shell + 1)
        theta = niob.contact_phase_theta_rad((m_nuc, m_shell, lean.REFERENCE_M))
        geff = niob.outside_contact_coupling(theta)
        mod = notd.outside_curvature_binding_modulator(xi, bonded=True)
        load = max(0.0, mod - 1.0)
        alpha_ratio_sq = ratio_for_shell(m_shell, m_nuc, ae_lock)
        fight += (
            lean.STRONG_CHANNEL_FRACTION
            * b_out_per_nucleon
            * load
            * geff
            * alpha_ratio_sq
            * exposure
        )
    return fight


def _canonical_ratio_sq(m_shell: int, m_nuc: int, ae_lock: float, *, c: float = 1.0) -> float:
    _ = m_nuc
    ae = ihs.alpha_eff_at_shell(m_shell, c)
    return (ae / ae_lock) ** 2


def _nuclear_ratio_sq(m_shell: int, m_nuc: int, ae_lock: float, *, c: float = 1.0) -> float:
    _ = m_shell
    ae = ihs.alpha_eff_at_shell(m_nuc, c)
    return (ae / ae_lock) ** 2


def _global_unity_ratio_sq(m_shell: int, m_nuc: int, ae_lock: float) -> float:
    _ = m_shell, m_nuc, ae_lock
    return 1.0


def fight_diagnostics(z: int, *, c: float = 1.0) -> FightDiagnostics:
    canonical = ac.atom_electronic_outside_curvature_fight_mev(z, c=c)
    nuclear_policy = _outside_fight_with_alpha_ratio_policy(
        z,
        ratio_for_shell=lambda ms, mn, al: _nuclear_ratio_sq(ms, mn, al, c=c),
        c=c,
    )
    global_policy = _outside_fight_with_alpha_ratio_policy(
        z,
        ratio_for_shell=_global_unity_ratio_sq,
        c=c,
    )
    return FightDiagnostics(
        canonical_mev=canonical,
        nuclear_ratio_policy_mev=nuclear_policy,
        global_unity_ratio_mev=global_policy,
        ratio_policy_note=(
            "canonical uses (alpha_eff(m_shell)/alpha_eff(lock))^2; "
            "nuclear_policy uses (alpha_eff(m_nuc)/alpha_eff(lock))^2 for all electrons; "
            "global_unity uses ratio=1 (shows atom spine decoupling from alpha_EM_primary)"
        ),
    )


def hydrogenic_diagnostics(z: int, panel: ElementAlphaPanel, *, c: float = 1.0) -> HydrogenicDiagnostics:
    canonical = ac.atom_hydrogenic_binding_mev(z, c=c)
    ae_global = panel.global_brace.alpha
    ae_nuc = panel.nuclear_tracking.alpha
    ae_outer = panel.electronic_outermost.alpha

    def bind_from_alpha(ae: float) -> float:
        if z == 0:
            return 0.0
        bind_au = z * z * ae * ae / 2.0
        # Hartree scale rides on the *derived* electron mass (m_e in a.u. = 1),
        # not the hard-coded CODATA proton/electron ratio.
        return bind_au * ac.derived_electron_mass_mev()

    return HydrogenicDiagnostics(
        canonical_mev=canonical,
        global_brace_mev=bind_from_alpha(ae_global),
        nuclear_tracking_mev=bind_from_alpha(ae_nuc),
        electronic_outermost_mev=bind_from_alpha(ae_outer),
    )


def _closed_mass_with_fight(z: int, fight_mev: float, *, c: float = 1.0) -> float:
    if z <= 0:
        return 0.0
    m_e = ac.derived_electron_mass_mev()
    nuc = ac.atom_nuclear_cluster_mass_mev(z, c=c)
    bind = ac.atom_electronic_binding_mev(z, c=c)
    return nuc + float(z) * m_e - bind + fight_mev


def build_element_comparison_row(element: str, *, c: float = 1.0) -> ElementComparisonRow:
    z = ac.AtomComparisonLayer.z_for_element(element)
    panel = build_element_alpha_panel(element, c=c)
    fight = fight_diagnostics(z, c=c)
    hydro = hydrogenic_diagnostics(z, panel, c=c)

    closed_canonical = ac.atom_closed_mass_mev(z, c=c)
    closed_nuclear_fight = _closed_mass_with_fight(z, fight.nuclear_ratio_policy_mev, c=c)
    closed_global_fight = _closed_mass_with_fight(z, fight.global_unity_ratio_mev, c=c)

    nist_mass = ac.AtomComparisonLayer.nist_mass_amu(element)
    nist_ie = ac.AtomComparisonLayer.nist_first_ionization_ev(element)
    ion_canonical = ac.atom_first_ionization_ev(z, c=c)

    rel_mass_canon = None
    rel_mass_nuc = None
    rel_ie = None
    if nist_mass is not None and nist_mass > 0:
        rel_mass_canon = closed_canonical / ac.MEV_PER_AMU / nist_mass - 1.0
        rel_mass_nuc = closed_nuclear_fight / ac.MEV_PER_AMU / nist_mass - 1.0
    if nist_ie is not None and nist_ie > 0:
        rel_ie = ion_canonical / nist_ie - 1.0

    return ElementComparisonRow(
        element=element,
        z=z,
        alpha_panel=panel,
        fight=fight,
        hydrogenic=hydro,
        closed_mass_canonical_mev=closed_canonical,
        closed_mass_nuclear_fight_mev=closed_nuclear_fight,
        closed_mass_global_fight_mev=closed_global_fight,
        nist_mass_amu=nist_mass,
        relative_error_canonical_mass=rel_mass_canon,
        relative_error_nuclear_fight_mass=rel_mass_nuc,
        first_ionization_ev_canonical=ion_canonical,
        nist_first_ionization_ev=nist_ie,
        relative_error_ionization=rel_ie,
    )


def shell_index_matching_inv_alpha(target_inv: float, *, m_max: int = 80) -> int:
    """First shell m where bare alpha_eff ladder crosses target 1/alpha (diagnostic)."""
    best_m = 0
    best_err = float("inf")
    for m in range(m_max + 1):
        inv = ihs.one_over_alpha_eff_at_shell(m)
        err = abs(inv - target_inv)
        if err < best_err:
            best_err = err
            best_m = m
    return best_m


def build_uniqueness_audit(report: AlphaModelComparisonReport) -> UniquenessAudit:
    codata_m = shell_index_matching_inv_alpha(sw.CODATA_INV_ALPHA)
    primary = report.primary_global_inv_alpha

    return UniquenessAudit(
        summary=(
            "HQIV currently hosts multiple alpha roles (lattice alpha=3/5, global alpha_EM_primary, "
            "and shell-local alpha_eff(m)). No proved selector picks one routing for all sectors."
        ),
        open_assumptions=[
            "Global brace uses fixed chart roles emGaussShell=3 and electroweakPhiShell=5.",
            "Nuclear drum m_nuc(A) comes from inside-ratio argmin, independent of EM brace.",
            "Electronic discharge shells come from TUFT chart + Z period rule, not m_nuc(A).",
            "Outside fight uses shell-local alpha_eff ratios; global alpha_EM_primary is not routed into atom mass.",
            "Slater binding in the atom spine uses unit Coulomb Hartree scaling without alpha_eff.",
        ],
        why_not_unique=[
            "Bare O-Maxwell ladder one_over_alpha_EM_derived(m) is monotone in m and crosses CODATA "
            f"near m≈{codata_m}, while primary brace is fixed at m=3->5 (1/α≈{primary:.2f}).",
            "Nuclear-tracking and electronic-tracking are both valid shell-local evaluations of the same "
            "alpha_eff(m) formula on different shell indices.",
            "Improving CODATA agreement on alpha can worsen atom mass or ionization because mass is "
            "dominated by nuclear cluster binding, not alpha_EM_primary.",
            "No Lean theorem yet identifies a variational/modal functional whose unique minimizer "
            "selects the global brace chart pair or ties EM to m_nuc(A).",
        ],
        candidate_routings=[
            "global_brace: sector topology / TUFT APS exp(n alpha/6) slot",
            "nuclear_tracking: alpha_eff(m_nuc(A)) for nucleus-linked dressing",
            "electronic_tracking: alpha_eff(m_shell) for bound-state and outside-fight ratios",
        ],
        recommendation=_recommendation_from_rows(report.rows),
    )


def _recommendation_from_rows(rows: list[ElementComparisonRow]) -> str:
    """Heuristic recommendation from benchmark panel (not a proof)."""
    if not rows:
        return "Insufficient data; keep alpha routing open."

    mass_deltas = [
        abs(r.closed_mass_nuclear_fight_mev - r.closed_mass_canonical_mev)
        for r in rows
        if r.z > 1
    ]
    avg_mass_shift = sum(mass_deltas) / len(mass_deltas) if mass_deltas else 0.0

    codata_inv = sw.CODATA_INV_ALPHA
    nuclear_closer = 0
    global_closer = 0
    electronic_closer = 0
    for r in rows:
        p = r.alpha_panel
        err_n = abs(p.nuclear_tracking.inv_alpha - codata_inv)
        err_g = abs(p.global_brace.inv_alpha - codata_inv)
        err_e = abs(p.electronic_outermost.inv_alpha - codata_inv)
        if err_n < err_g and err_n < err_e:
            nuclear_closer += 1
        elif err_g < err_n and err_g < err_e:
            global_closer += 1
        else:
            electronic_closer += 1

    if avg_mass_shift > 1.0:
        mass_note = (
            f"Nuclear alpha-ratio policy shifts outside-fight by O({avg_mass_shift:.2f}) MeV on average — "
            "too large to silently merge with global brace."
        )
    else:
        mass_note = (
            f"Nuclear alpha-ratio policy shifts outside-fight by O({avg_mass_shift:.4f}) MeV on average — "
            "small on mass panel but not zero."
        )

    return (
        "Keep a split architecture: global_brace for TUFT/sector topology; electronic_tracking "
        "for atom outside-fight and hydrogenic diagnostics; nuclear_tracking only where nucleus "
        f"coupling is explicit. {mass_note} "
        f"CODATA proximity scorecard (closer 1/alpha): nuclear={nuclear_closer}, "
        f"global={global_closer}, electronic={electronic_closer} elements. "
        "Next Lean target: formal `alpha_EM_local` router distinguishing global vs shell-local roles, "
        "plus IR running lemma from brace to Thomson scale — not a single unified alpha."
    )


def build_comparison_report(
    elements: tuple[str, ...] = BENCHMARK_ELEMENTS,
    *,
    c: float = 1.0,
) -> AlphaModelComparisonReport:
    primary = alpha_readout.resolve_alpha_em()
    report = AlphaModelComparisonReport(
        primary_global_inv_alpha=primary.inv_alpha,
        primary_global_vs_codata_pct=100.0 * (primary.inv_alpha / sw.CODATA_INV_ALPHA - 1.0),
    )
    for sym in elements:
        report.rows.append(build_element_comparison_row(sym, c=c))
    report.uniqueness_audit = build_uniqueness_audit(report)
    return report


def _alpha_panel_to_dict(panel: ElementAlphaPanel) -> dict[str, Any]:
    def cand(c: AlphaCandidateReadout) -> dict[str, Any]:
        return {
            **asdict(c),
            "model": c.model.value,
            "rel_error_vs_codata_inv": c.rel_error_vs_codata_inv(),
        }

    out: dict[str, Any] = {
        "element": panel.element,
        "z": panel.z,
        "mass_number": panel.mass_number,
        "m_nuc": panel.m_nuc,
        "electron_shells": list(panel.electron_shells),
        "global_brace": cand(panel.global_brace),
        "nuclear_tracking": cand(panel.nuclear_tracking),
        "electronic_outermost": cand(panel.electronic_outermost),
        "electronic_occupancy_mean": cand(panel.electronic_occupancy_mean),
        "alpha_eff_lockin": cand(panel.alpha_eff_lockin),
        "codata_comparison": cand(panel.codata_comparison),
    }
    if panel.electronic_valence_mean is not None:
        out["electronic_valence_mean"] = cand(panel.electronic_valence_mean)
    return out


def write_json_report(path: Path, report: AlphaModelComparisonReport) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2) + "\n", encoding="utf-8")


def print_report(report: AlphaModelComparisonReport) -> None:
    print("HQIV alpha_EM model comparison")
    print(f"  scale_witness          = {report.scale_witness}")
    print(f"  CODATA 1/alpha         = {report.codata_inv_alpha:.6f}")
    print(
        f"  global_brace 1/alpha   = {report.primary_global_inv_alpha:.4f} "
        f"({report.primary_global_vs_codata_pct:+.2f}% vs CODATA)"
    )
    print()
    print(f"{'Elem':<4} {'Z':>2} {'m_nuc':>5} {'1/a_glob':>9} {'1/a_nuc':>9} {'1/a_out':>9} "
          f"{'fight_can':>10} {'fight_nuc':>10} {'dM_nuc':>9}")
    for r in report.rows:
        p = r.alpha_panel
        dm = r.closed_mass_nuclear_fight_mev - r.closed_mass_canonical_mev
        print(
            f"{r.element:<4} {r.z:2d} {p.m_nuc:5d} "
            f"{p.global_brace.inv_alpha:9.3f} {p.nuclear_tracking.inv_alpha:9.3f} "
            f"{p.electronic_outermost.inv_alpha:9.3f} "
            f"{r.fight.canonical_mev:10.5f} {r.fight.nuclear_ratio_policy_mev:10.5f} "
            f"{dm:9.5f}"
        )
    print()
    if report.uniqueness_audit:
        ua = report.uniqueness_audit
        print("Uniqueness audit")
        print(f"  {ua.summary}")
        print()
        print("  Why not unique:")
        for line in ua.why_not_unique:
            print(f"    - {line}")
        print()
        print(f"  Recommendation: {ua.recommendation}")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV alpha_EM model comparison harness")
    parser.add_argument("--json", action="store_true", help="Print JSON to stdout")
    parser.add_argument("--write-json", action="store_true", help=f"Write {DEFAULT_JSON_PATH}")
    parser.add_argument(
        "--element",
        action="append",
        dest="elements",
        help="Restrict to element symbol (repeatable)",
    )
    args = parser.parse_args()

    elements = tuple(args.elements) if args.elements else BENCHMARK_ELEMENTS
    report = build_comparison_report(elements)

    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        print_report(report)

    if args.write_json:
        write_json_report(DEFAULT_JSON_PATH, report)
        if not args.json:
            print(f"\nWrote {DEFAULT_JSON_PATH}")


if __name__ == "__main__":
    main()
