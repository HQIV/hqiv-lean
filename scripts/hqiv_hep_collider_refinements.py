#!/usr/bin/env python3
"""
HEP collider refinements: MC parton shower, thrust distribution, ggH pT, QGP v2/R_AA, PDF x-shape.

Lean mirror: `Hqiv/Physics/HepColliderRefinements.lean`
Builds on `hqiv_strong_sector_collider_discharge.py` (leading-order discharge).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_hep_collider_refinements.py --strict
  PYTHONPATH=scripts python3 scripts/hqiv_hep_collider_refinements.py --json-out data/hep_collider_refinement_witness.json
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_strong_sector_collider_discharge as dsc

Status = Literal["pass", "fail", "skip"]

ROOT = dsc.ROOT
DEFAULT_OBS = ROOT / "data" / "hep_collider_refinement_observations.json"
DEFAULT_JSON = ROOT / "data" / "hep_collider_refinement_witness.json"

CF = dsc.CF
N_STRONG = dsc.N_STRONG
PETRA_SQRTS_MEV = 35000.0


@dataclass(frozen=True)
class RefinementRow:
    case_id: str
    quantity: str
    predicted: float
    reference: float
    reference_sigma: float | None
    n_sigma: float | None
    tolerance_sigma: float
    status: Status
    unit: str
    lean_def: str
    notes: str = ""


def thrust_from_n_axes(n_axes: int, alpha_s: float) -> float:
    """Thrust mean slot tied to discharged ⟨T⟩ for 3-jet; higher for 2-jet."""
    if n_axes <= 2:
        return 0.98
    if n_axes == 3:
        return dsc.mean_thrust_discharge(alpha_s)
    return max(0.55, dsc.mean_thrust_discharge(alpha_s) - 0.06 * (n_axes - 3))


def thrust_with_fluctuation(n_axes: int, alpha_s: float, rng: random.Random) -> float:
    """Event thrust: axis mean minus one-sided width fluctuation."""
    base = thrust_from_n_axes(n_axes, alpha_s)
    width = thrust_distribution_width(alpha_s)
    return max(0.0, min(1.0, base - width * abs(rng.gauss(0.0, 1.0))))


def thrust_distribution_width(alpha_s: float) -> float:
    """Lean `thrustDistributionWidth`."""
    return dsc.GAMMA * alpha_s / math.pi * math.sqrt(N_STRONG)


def emission_probability_per_step(alpha_s: float) -> float:
    """Lean `partonShowerEmissionProbability`."""
    return min(0.95, alpha_s / math.pi * CF * dsc.STRONG_CHANNEL_FRACTION)


def parton_shower_event(
    alpha_s: float,
    rng: random.Random,
    *,
    sqrt_s_mev: float = PETRA_SQRTS_MEV,
    max_extra_steps: int = 2,
) -> tuple[int, int]:
    """Shower with PETRA 3-jet/2-jet partition from discharged R23."""
    r23 = dsc.petra_r23_discharge(alpha_s, sqrt_s_mev)
    f_three = r23 / (1.0 + r23)
    p_extra = emission_probability_per_step(alpha_s)

    if rng.random() < f_three:
        axes = 3
        steps = 1
        while steps < 1 + max_extra_steps and rng.random() < p_extra * non_abelian_splitting_damp():
            axes += 1
            steps += 1
    else:
        axes = 2
        steps = 0
    return axes, steps


def non_abelian_splitting_damp() -> float:
    """Per-step damp from C_F/C_A (Lean `partonShowerStepDamp`)."""
    return CF / dsc.CA


def mc_shower_summary(
    alpha_s: float,
    *,
    n_events: int = 8000,
    seed: int = 42,
) -> dict[str, float]:
    rng = random.Random(seed)
    thrusts: list[float] = []
    n_three = 0
    n_four_plus = 0
    for _ in range(n_events):
        axes, _ = parton_shower_event(alpha_s, rng)
        t = thrust_with_fluctuation(axes, alpha_s, rng)
        thrusts.append(t)
        if axes == 3:
            n_three += 1
        if axes >= 4:
            n_four_plus += 1
    mean_t = sum(thrusts) / len(thrusts)
    frac_high = sum(1 for t in thrusts if t > 0.9) / len(thrusts)
    var = sum((t - mean_t) ** 2 for t in thrusts) / max(len(thrusts) - 1, 1)
    return {
        "mean_thrust": mean_t,
        "thrust_std": math.sqrt(var),
        "fraction_T_gt_0p9": frac_high,
        "fraction_3_jet": n_three / n_events,
        "fraction_4plus_jet": n_four_plus / n_events,
    }


def gg_h_pt_falloff_gev() -> float:
    """Lean `ggHpTFalloffGeV` = γ m_H / (1 + γ)."""
    return dsc.GAMMA * 125.11 / (1.0 + dsc.GAMMA)


def gg_h_mean_pt_gev(alpha_s: float) -> float:
    """Mean pT = λ for exponential exp(-pT/λ)."""
    return gg_h_pt_falloff_gev()


def gg_h_pt_fraction_above(alpha_s: float, pt_cut_gev: float = 30.0) -> float:
    """P(pT > cut) for exponential falloff exp(-pT/λ)."""
    lam = gg_h_pt_falloff_gev()
    return math.exp(-pt_cut_gev / lam)


def qgp_v2_discharge() -> float:
    """Lean `qgpV2Discharge` = γ η/s."""
    return dsc.GAMMA * dsc.qgp_eta_over_s_discharge()


def qgp_raa_at_pt(pt_gev: float) -> float:
    """Lean `qgpRAAWeightAtPT`: exp(-pT / (γ M_p / 100 GeV))."""
    scale = dsc.GAMMA * dsc.DERIVED_PROTON_MEV / 100.0
    return math.exp(-pt_gev / max(scale, 1e-6))


def pdf_gluon_x_shape(x: float) -> float:
    """Lean `pdfGluonShapeAtX` (unnormalised slot)."""
    if not 0.0 < x < 1.0:
        return 0.0
    moment = dsc.pdf_gluon_first_moment_discharge()
    return moment * (x ** (dsc.GAMMA - 1.0)) * ((1.0 - x) ** dsc.GAMMA)


def pdf_gluon_normalized(x: float, *, n_grid: int = 200) -> float:
    xs = [(i + 0.5) / n_grid for i in range(n_grid)]
    vals = [pdf_gluon_x_shape(xi) for xi in xs]
    norm = sum(vals) / n_grid
    return pdf_gluon_x_shape(x) / max(norm, 1e-30)


def pdf_gluon_x_ratio(x_num: float, x_den: float) -> float:
    return pdf_gluon_normalized(x_num) / max(pdf_gluon_normalized(x_den), 1e-30)


def pdf_gluon_xf(x: float) -> float:
    """Bjorken x times normalised gluon density."""
    return x * pdf_gluon_normalized(x)


def evaluate_refinement(case: dict[str, Any], *, petra_alpha: float, higgs_alpha: float) -> RefinementRow:
    cid = case["id"]
    ref = float(case["reference"])
    ref_sig = case.get("reference_sigma")
    ref_sig_f = None if ref_sig is None else float(ref_sig)
    tol = float(case.get("tolerance_sigma", 2.0))

    if cid == "thrust_fraction_T_gt_0p9":
        pred = mc_shower_summary(petra_alpha)["fraction_T_gt_0p9"]
        lean_def = "thrustDistributionWidth + partonShowerMC"
    elif cid == "thrust_std":
        pred = mc_shower_summary(petra_alpha)["thrust_std"]
        lean_def = "thrustDistributionWidth"
    elif cid == "four_jet_fraction_petra":
        pred = mc_shower_summary(petra_alpha)["fraction_4plus_jet"]
        lean_def = "partonShowerMC"
    elif cid == "ggH_mean_pT":
        pred = gg_h_mean_pt_gev(higgs_alpha)
        lean_def = "ggHpTFalloffGeV"
    elif cid == "ggH_frac_pT_gt_30":
        pred = gg_h_pt_fraction_above(higgs_alpha, 30.0)
        lean_def = "ggHpTSpectrum"
    elif cid == "qgp_v2":
        pred = qgp_v2_discharge()
        lean_def = "qgpV2Discharge"
    elif cid == "qgp_RAA_5GeV":
        pred = qgp_raa_at_pt(5.0)
        lean_def = "qgpRAAWeightAtPT"
    elif cid == "pdf_fg_ratio_0p1_over_0p01":
        pred = pdf_gluon_x_ratio(0.1, 0.01)
        lean_def = "pdfGluonShapeAtX"
    elif cid == "pdf_fg_at_x0p1":
        pred = pdf_gluon_xf(0.1)
        lean_def = "pdfGluonShapeAtX (x f_g slot)"
    else:
        return RefinementRow(
            case_id=cid,
            quantity=case.get("quantity", cid),
            predicted=float("nan"),
            reference=ref,
            reference_sigma=ref_sig_f,
            n_sigma=None,
            tolerance_sigma=tol,
            status="skip",
            unit=case.get("unit", ""),
            lean_def="",
            notes="unknown case",
        )

    n_sig = None
    if ref_sig_f is not None and ref_sig_f > 0:
        n_sig = abs(pred - ref) / ref_sig_f
        status: Status = "pass" if n_sig <= tol else "fail"
    else:
        status = "pass" if abs(pred - ref) < 1e-9 else "fail"

    return RefinementRow(
        case_id=cid,
        quantity=case["quantity"],
        predicted=pred,
        reference=ref,
        reference_sigma=ref_sig_f,
        n_sigma=n_sig,
        tolerance_sigma=tol,
        status=status,
        unit=case.get("unit", ""),
        lean_def=lean_def,
    )


def build_witness(observations_path: Path = DEFAULT_OBS) -> dict[str, Any]:
    obs = json.loads(observations_path.read_text(encoding="utf-8"))
    petra_mu = PETRA_SQRTS_MEV / 2.0
    petra_alpha = dsc.alpha_strong_running_lo(dsc.ALPHA_S_MZ, dsc.MZ_MEV, petra_mu)
    higgs_alpha = dsc.alpha_strong_running_lo(dsc.ALPHA_S_MZ, dsc.MZ_MEV, 125.11 * 1000.0)

    rows = [
        evaluate_refinement(c, petra_alpha=petra_alpha, higgs_alpha=higgs_alpha)
        for c in obs["cases"]
    ]
    mc = mc_shower_summary(petra_alpha)

    return {
        "lean_module": "Hqiv/Physics/HepColliderRefinements.lean",
        "upstream": "hqiv_strong_sector_collider_discharge.py",
        "mc_shower_petra": mc,
        "cases": [asdict(r) for r in rows],
        "summary": {
            "pass": sum(1 for r in rows if r.status == "pass"),
            "fail": sum(1 for r in rows if r.status == "fail"),
            "total": len(rows),
            "all_pass": all(r.status == "pass" for r in rows),
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser(description="HEP collider refinement witness")
    ap.add_argument("--observations", type=Path, default=DEFAULT_OBS)
    ap.add_argument("--json-out", type=Path, default=None)
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    witness = build_witness(args.observations)
    text = json.dumps(witness, indent=2)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
        print(f"Wrote {args.json_out}")
    else:
        print(text)

    for row in witness["cases"]:
        ns = row["n_sigma"]
        ns_txt = f"{ns:.2f}σ" if ns is not None else "exact"
        print(
            f"[{row['status'].upper():4}] {row['case_id']}: "
            f"pred={row['predicted']:.6g} ref={row['reference']:.6g} ({ns_txt})"
        )

    if args.strict and not witness["summary"]["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
