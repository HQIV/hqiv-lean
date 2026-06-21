#!/usr/bin/env python3
"""
Strong-sector collider phenomenology discharge witness.

Lean mirror: `Hqiv/Physics/StrongSectorColliderDischarge.lean`

Derives PETRA R23, mean thrust, non-abelian splitting, ggH σ proxy, QGP η/s,
glueball masses, and PDF gluon moment from the zero-knob spine (α=3/5, γ=2/5,
beta_3=-7, composite-trace binding).  Comparison targets are in
`data/strong_sector_collider_observations.json` only.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_strong_sector_collider_discharge.py
  PYTHONPATH=scripts python3 scripts/hqiv_strong_sector_collider_discharge.py --json-out data/strong_sector_collider_discharge.json
  PYTHONPATH=scripts python3 scripts/hqiv_strong_sector_collider_discharge.py --strict
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_excited_states as hes
import hqiv_repo_paths as paths
import hqiv_tuft_hadron_s7_confinement as s7

Status = Literal["pass", "fail", "skip"]

ALPHA = hes.ALPHA
GAMMA = hes.GAMMA
STRONG_CHANNEL_FRACTION = 4.0 / 8.0  # Lean `bbnStrongChannelFraction`

ROOT = paths.repo_root(Path(__file__))
DEFAULT_OBS = ROOT / "data" / "strong_sector_collider_observations.json"
DEFAULT_JSON = ROOT / "data" / "strong_sector_collider_discharge.json"

# Lean witnesses (SM_GR_Unification)
ALPHA_S_MZ = 0.1180
MZ_MEV = 91187.6
DERIVED_PROTON_MEV = 938.27208816
NC = 3
CA = 3.0
CF = 4.0 / 3.0
N_STRONG = 4
TRIPLE_BUDGET = 9
BETA0 = 7.0  # (-beta_3) in Lean convention


@dataclass(frozen=True)
class DischargeRow:
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


def alpha_strong_running_lo(alpha0: float, mu0_mev: float, mu_mev: float) -> float:
    """Lean `alphaStrongRunningLO`."""
    if mu_mev <= 0 or mu0_mev <= 0:
        return 0.0
    return alpha0 / (1.0 + BETA0 / (2.0 * math.pi) * alpha0 * math.log(mu_mev / mu0_mev))


def non_abelian_splitting_from_filter() -> float:
    """Lean `nonAbelianSplittingFromFilter` = C_A/C_F."""
    return CA / CF


def petra_r23_discharge(alpha_s: float, sqrt_s_mev: float) -> float:
    """Lean `petraR23Discharge`."""
    return (
        1.0
        + alpha_s / math.pi * (CA / NC) * (N_STRONG / 8.0) * math.log(sqrt_s_mev / MZ_MEV)
    )


def mean_thrust_discharge(alpha_s: float) -> float:
    """Lean `meanThrustDischarge`."""
    return 1.0 - N_STRONG * GAMMA * alpha_s / math.pi


def gg_h_sigma_pb_lo(alpha_s: float, m_top_gev: float, v_ew: float = 246.22) -> float:
    """Lean `ggHSigmaPbLODischarge` (pb)."""
    dim = (alpha_s / math.pi) ** 2 * (m_top_gev / v_ew) ** 2
    return (
        dim
        * (N_STRONG / 8.0)
        * (TRIPLE_BUDGET / NC)
        * (GAMMA / 8.0)
        * (21.0 / 20.0)
        * 389379.0
    )


def gg_h_sigma_pb_nlo(alpha_s: float, m_top_gev: float, v_ew: float = 246.22) -> float:
    """Lean `ggHSigmaPbNLODischarge` (pb)."""
    return gg_h_sigma_pb_lo(alpha_s, m_top_gev, v_ew) * non_abelian_splitting_from_filter()


def pdf_gluon_first_moment_discharge() -> float:
    """Lean `pdfGluonFirstMomentDischarge`."""
    return ALPHA_S_MZ * CF * STRONG_CHANNEL_FRACTION / 2.0


def qgp_eta_over_s_discharge() -> float:
    """Lean `qgpEtaOverSDischarge`."""
    return (1.0 / (4.0 * math.pi)) * CA * STRONG_CHANNEL_FRACTION / (2.0 * GAMMA)


def glueball_0pp_mass_mev() -> float:
    """Lean `glueball0ppMassMeV`."""
    return DERIVED_PROTON_MEV * GAMMA * (TRIPLE_BUDGET / 2.0)


def glueball_2pp_mass_mev() -> float:
    """Lean `glueball2ppMassMeV`."""
    return s7.hadron_whole_s7_ijk_dressing(DERIVED_PROTON_MEV, 1, 0)


def pdf_gluon_moment(m_max: int = 6) -> float:
    """Legacy shell ladder (superseded by `pdfGluonFirstMomentDischarge`)."""
    return pdf_gluon_first_moment_discharge()


def parton_shower_step_weight(m: int, s: int, *, c: float = 1.0) -> float:
    """Lean `partonShowerStepWeight` with unit nucleon trace on one generator slot."""
    cell = hes.binding_coupling_at_shell(m, c)
    return cell**s


def evaluate_case(
    case: dict[str, Any],
    *,
    petra_alpha: float,
    higgs_alpha: float,
) -> DischargeRow:
    cid = case["id"]
    ref = float(case["reference"])
    ref_sig = case.get("reference_sigma")
    ref_sig_f = None if ref_sig is None else float(ref_sig)
    tol = float(case.get("tolerance_sigma", 2.0))

    if cid == "petra_r23":
        sqrt_s = float(case.get("sqrt_s_gev", 35.0)) * 1000.0
        pred = petra_r23_discharge(petra_alpha, sqrt_s)
        lean_def = "petraR23Discharge"
    elif cid == "petra_mean_thrust":
        pred = mean_thrust_discharge(petra_alpha)
        lean_def = "meanThrustDischarge"
    elif cid == "nonabelian_splitting":
        pred = non_abelian_splitting_from_filter()
        lean_def = "nonAbelianSplittingFromFilter"
    elif cid == "ggH_sigma_lo":
        pred = gg_h_sigma_pb_lo(higgs_alpha, 172.76)
        lean_def = "ggHSigmaPbLODischarge"
    elif cid == "ggH_sigma_nlo":
        pred = gg_h_sigma_pb_nlo(higgs_alpha, 172.76)
        lean_def = "ggHSigmaPbNLODischarge"
    elif cid == "qgp_eta_s":
        pred = qgp_eta_over_s_discharge()
        lean_def = "qgpEtaOverSDischarge"
    elif cid == "glueball_0pp":
        pred = glueball_0pp_mass_mev()
        lean_def = "glueball0ppMassMeV"
    elif cid == "glueball_2pp":
        pred = glueball_2pp_mass_mev()
        lean_def = "glueball2ppMassMeV"
    elif cid == "pdf_gluon_moment":
        pred = pdf_gluon_moment()
        lean_def = "pdfGluonFirstMomentDischarge"
    else:
        return DischargeRow(
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
            notes="unknown case id",
        )

    n_sig = None
    if ref_sig_f is not None and ref_sig_f > 0:
        n_sig = abs(pred - ref) / ref_sig_f
        status: Status = "pass" if n_sig <= tol else "fail"
    else:
        status = "pass" if abs(pred - ref) < 1e-9 else "fail"

    return DischargeRow(
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


def build_witness(
    observations_path: Path = DEFAULT_OBS,
) -> dict[str, Any]:
    obs = json.loads(observations_path.read_text(encoding="utf-8"))
    petra_mu = 35.0 * 1000.0 / 2.0
    higgs_mu = 125.11 * 1000.0
    petra_alpha = alpha_strong_running_lo(ALPHA_S_MZ, MZ_MEV, petra_mu)
    higgs_alpha = alpha_strong_running_lo(ALPHA_S_MZ, MZ_MEV, higgs_mu)

    rows = [
        evaluate_case(c, petra_alpha=petra_alpha, higgs_alpha=higgs_alpha)
        for c in obs["cases"]
    ]
    n_pass = sum(1 for r in rows if r.status == "pass")
    n_fail = sum(1 for r in rows if r.status == "fail")

    return {
        "lean_module": "Hqiv/Physics/StrongSectorColliderDischarge.lean",
        "build": "lake build paper_gluon_curvature",
        "inputs": {
            "alpha_s_at_MZ": ALPHA_S_MZ,
            "beta0_from_beta3": BETA0,
            "derived_proton_mev": DERIVED_PROTON_MEV,
            "alpha": ALPHA,
            "gamma": GAMMA,
        },
        "running": {
            "alpha_s_at_petra_scale": petra_alpha,
            "alpha_s_at_higgs_scale": higgs_alpha,
            "petra_mu_mev": petra_mu,
        },
        "parton_shower": {
            "three_jet_steps": 1,
            "step_weight_shell4_unit_trace": parton_shower_step_weight(4, 1),
        },
        "cases": [asdict(r) for r in rows],
        "summary": {
            "pass": n_pass,
            "fail": n_fail,
            "total": len(rows),
            "all_pass": n_fail == 0,
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser(description="Strong-sector collider discharge witness")
    ap.add_argument("--observations", type=Path, default=DEFAULT_OBS)
    ap.add_argument("--json-out", type=Path, default=None)
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    witness = build_witness(args.observations)
    text = json.dumps(witness, indent=2, sort_keys=False)
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
