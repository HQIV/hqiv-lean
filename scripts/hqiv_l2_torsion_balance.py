#!/usr/bin/env python3
"""
L2 phase-gradient torsion balance readout (primary E_* laboratory anchor).

Lean mirror: Hqiv.Physics.L2TorsionBalanceWitness

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_l2_torsion_balance.py
  PYTHONPATH=scripts python3 scripts/hqiv_l2_torsion_balance.py --json data/l2_torsion_readout.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_lean_physics_primitives as lean
import hqiv_solar_dynamics as sd

GAMMA = lean.GAMMA
XI_LOCKIN = lean.XI_LOCKIN
REFERENCE_M = lean.REFERENCE_M
T_PL = 1.0  # natural units (Lean `T_Pl_eq`)

LEAN_MODULES = [
    "Hqiv.Physics.L2TorsionBalanceWitness",
    "Hqiv.Physics.CoronalLongitudinalStress",
    "Hqiv.Physics.OMaxwellLongitudinalMomentumBridge",
    "Hqiv.Physics.CoronalEstarSIAnchorWitness",
    "Hqiv.Physics.HopfShellBeltramiMassBridge",
    "Hqiv.Physics.InformationalEnergyMass",
]

L2_FORCE_BAND_LOW = 1.0e-14
L2_FORCE_BAND_HIGH = 1.0e-13


def longitudinal_to_transverse_ratio_theta(theta_local: float) -> float:
    """Lean `longitudinalToTransverseRatioTheta`: γ / Θ_local."""
    if theta_local == 0.0:
        return 0.0
    return GAMMA / theta_local


def longitudinal_to_transverse_ratio_at_xi(xi: float, *, t_pl: float = T_PL) -> float:
    """Lean `longitudinalToTransverseRatioAtXi`: γ · (ξ / T_Pl)."""
    if t_pl == 0.0:
        return 0.0
    return GAMMA * (xi / t_pl)


def longitudinal_to_transverse_ratio_lab(t_local: float, *, t_pl: float = T_PL) -> float:
    """Lean `longitudinalToTransverseRatioLab`: (γ/5) · (T / T_Pl)."""
    if t_pl == 0.0:
        return 0.0
    return (GAMMA / 5.0) * (t_local / t_pl)


def l2_lockin_one_shell_jump() -> float:
    """Lean `l2LockinOneShellJump` at referenceM → referenceM+1: Δφ = 2."""
    return sd.phi_jump(REFERENCE_M, REFERENCE_M + 1)


def l2_torsion_force_denominator(
    area: float,
    nq: float,
    delta_phi: float,
    *,
    coupling_log: float = 1.0,
) -> float:
    """Lean `l2TorsionForceDenominator`: A nq (3/20π) Λ_s Δφ at E_* = 1."""
    return area * nq * (3.0 / (20.0 * math.pi)) * coupling_log * delta_phi


def coronal_longitudinal_force_boundary(
    area: float,
    nq: float,
    estar: float,
    phi_photo: float,
    phi_corona: float,
    *,
    coupling_log: float = 1.0,
) -> float:
    """Lean `coronalLongitudinalForceBoundary`."""
    return (
        area
        * nq
        * estar
        * (3.0 / (20.0 * math.pi))
        * coupling_log
        * (phi_corona - phi_photo)
    )


def estar_from_l2_torsion_force(
    f_measured: float,
    area: float,
    nq: float,
    delta_phi: float,
    *,
    coupling_log: float = 1.0,
) -> float:
    """Lean `estarFromL2TorsionForce`: E_* = F / denom when denom ≠ 0."""
    denom = l2_torsion_force_denominator(
        area, nq, delta_phi, coupling_log=coupling_log
    )
    if denom == 0.0:
        return 0.0
    return f_measured / denom


@dataclass(frozen=True)
class L2TorsionBalanceReadout:
    f_measured: float
    area_m2: float
    nq_m3: float
    coupling_log: float
    phi_photo: float
    phi_corona: float
    delta_phi: float
    estar: float
    force_boundary: float
    ratio_at_lockin: float
    ratio_lab_lockin_temperature: float
    kappa6_at_lockin: float
    in_program_band: bool
    claim_status: str


def l2_torsion_balance_readout(
    f_measured: float,
    *,
    area_m2: float = 1.0e-4,
    nq_m3: float = 1.0e28,
    coupling_log: float = 1.0,
    m_photo: int = REFERENCE_M,
    m_corona: int = REFERENCE_M + 1,
) -> L2TorsionBalanceReadout:
    """Representative L2 row: lock-in one-shell jump + programme force band."""
    phi_photo = sd.phi_of_shell(m_photo)
    phi_corona = sd.phi_of_shell(m_corona)
    delta_phi = phi_corona - phi_photo
    estar = estar_from_l2_torsion_force(
        f_measured, area_m2, nq_m3, delta_phi, coupling_log=coupling_log
    )
    force = coronal_longitudinal_force_boundary(
        area_m2, nq_m3, estar, phi_photo, phi_corona, coupling_log=coupling_log
    )
    ratio_lockin = longitudinal_to_transverse_ratio_at_xi(XI_LOCKIN)
    t_lockin = T_PL / XI_LOCKIN
    ratio_lab = longitudinal_to_transverse_ratio_lab(t_lockin)
    in_band = L2_FORCE_BAND_LOW <= f_measured <= L2_FORCE_BAND_HIGH
    return L2TorsionBalanceReadout(
        f_measured=f_measured,
        area_m2=area_m2,
        nq_m3=nq_m3,
        coupling_log=coupling_log,
        phi_photo=phi_photo,
        phi_corona=phi_corona,
        delta_phi=delta_phi,
        estar=estar,
        force_boundary=force,
        ratio_at_lockin=ratio_lockin,
        ratio_lab_lockin_temperature=ratio_lab,
        kappa6_at_lockin=lean.tuft_hopf_kappa6_at_lockin(),
        in_program_band=in_band,
        claim_status="l2_torsion_witness",
    )


def build_readout_payload(
    f_measured: float = 3.0e-14,
    **kwargs: Any,
) -> dict[str, Any]:
    row = l2_torsion_balance_readout(f_measured, **kwargs)
    return {
        "source": "scripts/hqiv_l2_torsion_balance.py",
        "lean_modules": LEAN_MODULES,
        "proved_algebra": [
            "longitudinalToTransverseRatioAtLockin_eq_two",
            "l2LockinOneShellJump_eq_two",
            "coronalLongitudinalForceBoundary_l2_estar_calibration_direct",
            "l2TorsionBalanceHonestyLedger_discharged",
        ],
        "program_force_band_N": {
            "low": L2_FORCE_BAND_LOW,
            "high": L2_FORCE_BAND_HIGH,
        },
        "l2_torsion_balance": asdict(row),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="L2 torsion balance readout")
    parser.add_argument("--json", type=Path, help="Write JSON witness")
    parser.add_argument(
        "--force",
        type=float,
        default=3.0e-14,
        help="Measured axial force [N] (programme band default)",
    )
    args = parser.parse_args()
    payload = build_readout_payload(f_measured=args.force)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        print(f"Wrote {args.json}")
    else:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
