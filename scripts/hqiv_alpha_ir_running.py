#!/usr/bin/env python3
"""
HQIV alpha_EM IR-running bridge (W-scale -> Thomson-scale).

Motivation
----------
The double-axis brace lands the **electroweak / W structural shell** at 1/alpha ~= 129
(the HQIV analogue of alpha(M_Z)). Hydrogen spectroscopy lives in the **deep IR**
(Rydberg / eV scale), where the same coupling has run out to 1/alpha ~= 137
(the Thomson / alpha(0) value). The ~6% gap between "W" and "H" is therefore
**running of one coupling between two scales**, not two inconsistent constants.

This module exposes a *single, simple* dynamic coupling on the O-Maxwell shell
ladder and identifies the named scales as evaluations of it:

    1/alpha_bare(m) = 42 * (1 + c * (3/5) * ln(2(m+1) + 1))      [monotone in m]

It is intentionally **not** a derived RG theorem. It is the honest phenomenological
bridge whose endpoints HQIV already reproduces:
  - bare ladder crosses the W/M_Z value 1/alpha ~= 129 near m ~= 14
  - bare ladder crosses the Thomson value 1/alpha ~= 137 near m ~= 20
  - the structural EW shell (m=5) is lifted to ~129 by the Gauss->EW brace

Also provides an **observable router**: most HQIV calculations do not need raw
alpha at all (mass/binding is dominated by nuclear curvature + proton lock-in).
Raw alpha matters for spectroscopy-class observables.

Mirrors / consumes:
  - scripts/hqiv_isotope_hydrogenic_scales.py  (bare shell ladder)
  - scripts/hqiv_alpha_readout.py              (EW double-axis brace ~129)
  - scripts/hqiv_scale_witness.py              (CODATA comparison tier)

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_ir_running.py
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_ir_running.py --json
  PYTHONPATH=scripts python3 scripts/hqiv_alpha_ir_running.py --write-json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any

import hqiv_alpha_readout as alpha_readout
import hqiv_isotope_hydrogenic_scales as ihs
import hqiv_scale_witness as sw

ALPHA_HQIV = ihs.ALPHA_HQIV  # 3/5
ONE_OVER_ALPHA_BARE = ihs.ONE_OVER_ALPHA_BARE  # 42
REFERENCE_M = sw.REFERENCE_M  # 4
EM_GAUSS_SHELL = REFERENCE_M - 1  # 3
ELECTROWEAK_SHELL = REFERENCE_M + 1  # 5 (W structural shell)
CODATA_INV_ALPHA = sw.CODATA_INV_ALPHA  # ~137.036 (Thomson)
PAPER_INV_ALPHA_MZ = 127.9  # legacy alpha(M_Z) witness

DEFAULT_JSON_PATH = Path(__file__).resolve().parents[1] / "data" / "alpha_ir_running_witnesses.json"

LEAN_MODULES = (
    "Hqiv.Physics.EffectiveAlphaReadout",
    "Hqiv.Physics.DoublePreferredAxisAlpha",
    "Hqiv.Physics.SM_GR_Unification",
)


# ---------------------------------------------------------------------------
# Simple dynamic coupling on the shell ladder
# ---------------------------------------------------------------------------


def bare_inv_alpha_at_shell(m: float, c: float = 1.0) -> float:
    """Continuous bare O-Maxwell ladder: 1/alpha(m) = 42(1 + c*(3/5)*ln(2(m+1)+1))."""
    phi = 2.0 * (m + 1.0)
    return ONE_OVER_ALPHA_BARE * (1.0 + c * ALPHA_HQIV * math.log(phi + 1.0))


def bare_alpha_at_shell(m: float, c: float = 1.0) -> float:
    return 1.0 / bare_inv_alpha_at_shell(m, c)


def shell_for_bare_inv_alpha(target_inv: float, c: float = 1.0) -> float:
    """
    Invert the bare ladder: shell m where 1/alpha_bare(m) == target_inv.

    From 1/alpha = 42(1 + c*(3/5)*ln(2m+3)):
        2m + 3 = exp( (target/42 - 1) / (c*3/5) )
    """
    inner = (target_inv / ONE_OVER_ALPHA_BARE - 1.0) / (c * ALPHA_HQIV)
    two_m_plus_three = math.exp(inner)
    return (two_m_plus_three - 3.0) / 2.0


def ew_brace_inv_alpha(c_fano: float = 1.0) -> float:
    """Gauss->EW double-axis brace (structural EW shell lifted to alpha(M_Z) analogue ~129)."""
    return alpha_readout.resolve_alpha_em(c_fano=c_fano).inv_alpha


# ---------------------------------------------------------------------------
# Named scales as points on the running curve
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class AlphaScalePoint:
    name: str
    inv_alpha: float
    alpha: float
    ladder_shell_equiv: float
    note: str

    @classmethod
    def from_inv(cls, name: str, inv_alpha: float, *, c: float = 1.0, note: str = "") -> "AlphaScalePoint":
        return cls(
            name=name,
            inv_alpha=inv_alpha,
            alpha=1.0 / inv_alpha,
            ladder_shell_equiv=shell_for_bare_inv_alpha(inv_alpha, c),
            note=note,
        )


def named_scale_points(*, c: float = 1.0) -> list[AlphaScalePoint]:
    """The endpoints HQIV reproduces, expressed on one running ladder."""
    brace = ew_brace_inv_alpha(c)
    return [
        AlphaScalePoint.from_inv(
            "ew_structural_shell_bare",
            bare_inv_alpha_at_shell(ELECTROWEAK_SHELL, c),
            c=c,
            note="bare ladder at structural EW shell m=5 (pre-brace)",
        ),
        AlphaScalePoint.from_inv(
            "ew_brace_W",
            brace,
            c=c,
            note="Gauss->EW double-axis brace; W / alpha(M_Z) analogue",
        ),
        AlphaScalePoint.from_inv(
            "paper_mz_witness",
            PAPER_INV_ALPHA_MZ,
            c=c,
            note="legacy alpha(M_Z) = 1/127.9 witness",
        ),
        AlphaScalePoint.from_inv(
            "thomson_codata",
            CODATA_INV_ALPHA,
            c=c,
            note="Thomson / alpha(0); hydrogen spectroscopy scale (comparison)",
        ),
    ]


@dataclass(frozen=True)
class RunningSpan:
    """The W -> Thomson running segment expressed on the bare ladder."""

    w_inv_alpha: float
    w_ladder_shell: float
    thomson_inv_alpha: float
    thomson_ladder_shell: float
    delta_inv_alpha: float
    pct_run: float
    note: str


def w_to_thomson_span(*, c: float = 1.0) -> RunningSpan:
    w_inv = ew_brace_inv_alpha(c)
    th_inv = CODATA_INV_ALPHA
    w_shell = shell_for_bare_inv_alpha(w_inv, c)
    th_shell = shell_for_bare_inv_alpha(th_inv, c)
    return RunningSpan(
        w_inv_alpha=w_inv,
        w_ladder_shell=w_shell,
        thomson_inv_alpha=th_inv,
        thomson_ladder_shell=th_shell,
        delta_inv_alpha=th_inv - w_inv,
        pct_run=100.0 * (th_inv / w_inv - 1.0),
        note=(
            "W (EW brace ~129) and Thomson (~137) are two evaluations of one monotone "
            "ladder; the IR shells between them are the (unproved) running segment"
        ),
    )


# ---------------------------------------------------------------------------
# Observable router: when is raw alpha actually needed?
# ---------------------------------------------------------------------------


class AlphaNeed(str, Enum):
    NONE = "none"  # raw alpha not needed (dominated by curvature / lock-in)
    GLOBAL_BRACE = "global_brace"  # EW-scale alpha (W): TUFT / sector topology
    IR_THOMSON = "ir_thomson"  # alpha(0): spectroscopy-class precision
    SHELL_LOCAL_RATIO = "shell_local_ratio"  # relative alpha_eff ratio only


@dataclass(frozen=True)
class ObservableAlphaPolicy:
    observable: str
    need: AlphaNeed
    rationale: str


_OBSERVABLE_POLICIES: tuple[ObservableAlphaPolicy, ...] = (
    ObservableAlphaPolicy(
        "atomic_mass",
        AlphaNeed.NONE,
        "closed mass dominated by nuclear cluster + Z*m_e + proton lock-in; raw alpha decouples",
    ),
    ObservableAlphaPolicy(
        "nuclear_binding",
        AlphaNeed.NONE,
        "inside/outside curvature network uses lattice alpha=3/5, not fine-structure alpha",
    ),
    ObservableAlphaPolicy(
        "bbn_abundances",
        AlphaNeed.NONE,
        "network weights and freezeout use lattice/curvature couplings",
    ),
    ObservableAlphaPolicy(
        "tuft_sector_determinant",
        AlphaNeed.GLOBAL_BRACE,
        "exp(n*alpha/6) APS spurion needs EW-scale alpha (the W value ~129)",
    ),
    ObservableAlphaPolicy(
        "g_minus_2",
        AlphaNeed.GLOBAL_BRACE,
        "anomalous moment spurion uses global brace alpha at sector scale",
    ),
    ObservableAlphaPolicy(
        "outside_curvature_fight",
        AlphaNeed.SHELL_LOCAL_RATIO,
        "uses (alpha_eff(m_shell)/alpha_eff(lock))^2 ratio; absolute scale cancels",
    ),
    ObservableAlphaPolicy(
        "fine_structure_spectroscopy",
        AlphaNeed.IR_THOMSON,
        "Rydberg / fine structure / Lamb shift live at q^2 -> 0; need alpha(0) ~= 1/137",
    ),
    ObservableAlphaPolicy(
        "ionization_precision",
        AlphaNeed.IR_THOMSON,
        "precise ionization energies need Thomson-scale alpha, not structural shell",
    ),
    ObservableAlphaPolicy(
        "hydrogen_binding_precise",
        AlphaNeed.IR_THOMSON,
        "H 1s binding uses alpha(0); structural shell m=1 (1/alpha~83) overbinds ~2.76x",
    ),
)


def observable_alpha_policy(observable: str) -> ObservableAlphaPolicy:
    key = observable.strip().lower()
    for p in _OBSERVABLE_POLICIES:
        if p.observable == key:
            return p
    raise KeyError(f"Unknown observable {observable!r}")


def alpha_for_observable(observable: str, *, c: float = 1.0) -> float | None:
    """
    Resolve the alpha an observable should use, or None if raw alpha is not needed.

    - NONE              -> None (curvature/lock-in dominated)
    - GLOBAL_BRACE      -> EW brace alpha (~1/129)
    - IR_THOMSON        -> alpha(0) (~1/137)
    - SHELL_LOCAL_RATIO -> None (relative ratio; caller uses alpha_eff ladder directly)
    """
    policy = observable_alpha_policy(observable)
    if policy.need is AlphaNeed.NONE or policy.need is AlphaNeed.SHELL_LOCAL_RATIO:
        return None
    if policy.need is AlphaNeed.GLOBAL_BRACE:
        return 1.0 / ew_brace_inv_alpha(c)
    if policy.need is AlphaNeed.IR_THOMSON:
        return 1.0 / CODATA_INV_ALPHA
    raise AssertionError("unreachable")


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------


@dataclass
class AlphaIrRunningReport:
    lean_modules: tuple[str, ...] = field(default_factory=lambda: LEAN_MODULES)
    scale_witness: str = sw.DEFAULT_SCALE_WITNESS
    em_gauss_shell: int = EM_GAUSS_SHELL
    electroweak_shell: int = ELECTROWEAK_SHELL
    scale_points: list[AlphaScalePoint] = field(default_factory=list)
    w_to_thomson: RunningSpan | None = None
    observable_policies: list[ObservableAlphaPolicy] = field(default_factory=list)
    status_note: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "lean_modules": list(self.lean_modules),
            "scale_witness": self.scale_witness,
            "em_gauss_shell": self.em_gauss_shell,
            "electroweak_shell": self.electroweak_shell,
            "scale_points": [asdict(p) for p in self.scale_points],
            "w_to_thomson": asdict(self.w_to_thomson) if self.w_to_thomson else None,
            "observable_policies": [
                {**asdict(p), "need": p.need.value} for p in self.observable_policies
            ],
            "status_note": self.status_note,
        }


def build_report(*, c: float = 1.0) -> AlphaIrRunningReport:
    return AlphaIrRunningReport(
        scale_points=named_scale_points(c=c),
        w_to_thomson=w_to_thomson_span(c=c),
        observable_policies=list(_OBSERVABLE_POLICIES),
        status_note=(
            "Endpoints reproduced (W brace ~129, Thomson ~137 near ladder m~20). "
            "The running curve between them is a phenomenological bridge on the bare "
            "O-Maxwell ladder, NOT yet a proved RG theorem. Most HQIV observables do "
            "not need raw alpha; spectroscopy-class observables use the IR/Thomson value."
        ),
    )


def write_json_report(path: Path, report: AlphaIrRunningReport) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report.to_dict(), indent=2) + "\n", encoding="utf-8")


def print_report(report: AlphaIrRunningReport) -> None:
    print("HQIV alpha_EM IR-running bridge (W -> Thomson)")
    print(f"  scale_witness     = {report.scale_witness}")
    print(f"  EM Gauss shell    = m={report.em_gauss_shell}")
    print(f"  electroweak shell = m={report.electroweak_shell} (W structural row)")
    print()
    print(f"  {'scale':<26} {'1/alpha':>10} {'alpha':>14} {'ladder m':>9}  note")
    for p in report.scale_points:
        print(
            f"  {p.name:<26} {p.inv_alpha:10.4f} {p.alpha:14.10f} "
            f"{p.ladder_shell_equiv:9.2f}  {p.note}"
        )
    print()
    if report.w_to_thomson:
        s = report.w_to_thomson
        print("  W -> Thomson running span (on bare ladder):")
        print(
            f"    W:       1/alpha={s.w_inv_alpha:8.4f}  ladder m~{s.w_ladder_shell:5.2f}"
        )
        print(
            f"    Thomson: 1/alpha={s.thomson_inv_alpha:8.4f}  ladder m~{s.thomson_ladder_shell:5.2f}"
        )
        print(
            f"    delta(1/alpha)={s.delta_inv_alpha:+.4f}  ({s.pct_run:+.2f}% run W->Thomson)"
        )
    print()
    print("  Observable alpha router (when is raw alpha needed?):")
    for p in report.observable_policies:
        print(f"    {p.observable:<28} -> {p.need.value:<18} {p.rationale}")
    print()
    print(f"  Status: {report.status_note}")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV alpha_EM IR-running bridge")
    parser.add_argument("--json", action="store_true", help="Print JSON to stdout")
    parser.add_argument("--write-json", action="store_true", help=f"Write {DEFAULT_JSON_PATH}")
    args = parser.parse_args()

    report = build_report()
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
