#!/usr/bin/env python3
"""
Sandbox: Δ-generated internal circle, 2π monodromy, triality-shaped wells,
and lapse / velocity screen (1 − v²) — built on the same 8×8 manifold
operator as `spinor_mass_operator_reality_probe.py`.

Lean alignment (read-only narrative for this script):
  - `phaseLiftDelta` / `manifoldMassOp8` → `Hqiv/Physics/MassFromSpinorRho.lean`
  - φ(m) = 2(m+1) → `Hqiv/Geometry/AuxiliaryField.lean` style ladder

No PDG fitting: scans are internal energy landscapes and discrete bit counts only.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent


def _load_probe():
    path = SCRIPT_DIR / "spinor_mass_operator_reality_probe.py"
    spec = importlib.util.spec_from_file_location("spinor_mass_probe", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def exp_theta_delta_mat(theta: float, n: int = 8) -> np.ndarray:
    """exp(θ Δ) with HQIV unit Δ in the (e₁,e₇) plane (0-based indices 1 and 7)."""
    u = np.eye(n, dtype=np.float64)
    c, s = math.cos(theta), math.sin(theta)
    u[1, 1] = c
    u[1, 7] = -s
    u[7, 1] = s
    u[7, 7] = c
    return u


def verify_monodromy() -> dict[str, float]:
    """Block-exponential on (e₁,e₇): exp(2πΔ)=I (period of the Δ-circle)."""
    two_pi = 2.0 * math.pi
    u = exp_theta_delta_mat(two_pi)
    err = float(np.max(np.abs(u - np.eye(8))))
    return {"max_abs_exp_2pi_minus_I": err}


def rotated_state(theta: float) -> np.ndarray:
    """|ψ(θ)⟩ = exp(θ Δ)|e₁⟩ — lives on the Δ-circle in the (e₁,e₇) plane."""
    v = np.zeros(8, dtype=np.float64)
    v[1] = 1.0
    u = exp_theta_delta_mat(theta)
    return u @ v


def manifold_expectation(H: np.ndarray, theta: float) -> float:
    psi = rotated_state(theta)
    return float(psi @ H @ psi)


def triality_well(theta: float, *, amplitude: float, screen: float) -> float:
    """
    Periodic barrier with three minima per 2π (triality tiling on S¹).
    screen = (1 - v²) lapse factor; amplitude scales with shell via caller.
    """
    return float(screen) * float(amplitude) * 0.5 * (1.0 - math.cos(3.0 * theta))


def total_energy(
    theta: float,
    H: np.ndarray,
    *,
    well_amplitude: float,
    screen: float,
) -> float:
    return manifold_expectation(H, theta) + triality_well(
        theta, amplitude=well_amplitude, screen=screen
    )


def scan_theta_grid(
    H: np.ndarray,
    *,
    well_amplitude: float,
    screen: float,
    n: int = 7200,
) -> dict[str, Any]:
    thetas = np.linspace(0.0, 2.0 * math.pi, n, endpoint=False)
    vals = np.array(
        [total_energy(float(t), H, well_amplitude=well_amplitude, screen=screen) for t in thetas]
    )
    j = int(np.argmin(vals))
    return {
        "theta_min": float(thetas[j]),
        "E_min": float(vals[j]),
        "E_max": float(vals.max()),
        "E_mean": float(vals.mean()),
    }


def triality_sector_minima(
    H: np.ndarray,
    *,
    well_amplitude: float,
    screen: float,
) -> list[dict[str, float]]:
    """
    Near each of the three cos(3θ) wells (θ ≈ 0, 2π/3, 4π/3), refine by local grid.
    """
    centers = [0.0, 2.0 * math.pi / 3.0, 4.0 * math.pi / 3.0]
    out: list[dict[str, float]] = []
    for c in centers:
        loc = np.linspace(c - 0.08, c + 0.08, 400)
        best_t, best_e = c, float("inf")
        for t in loc:
            e = total_energy(float(t), H, well_amplitude=well_amplitude, screen=screen)
            if e < best_e:
                best_e = e
                best_t = float(t)
        out.append({"sector_center": c, "theta_refined": best_t, "E_min": best_e})
    return out


def horizon_entropy_toy(
    *,
    n_bins: int,
    screen: float,
    well_amplitude: float,
    collapse_frac: float = 0.25,
) -> dict[str, Any]:
    """
    Toy: each angular bin carries ~1 bit if the screened well depth falls below
    a fixed fraction of its v=0 depth — crude stand-in for 'well dissolved into horizon'.
    """
    depths0 = []
    depths_h = []
    for k in range(n_bins):
        theta = 2.0 * math.pi * (k + 0.5) / float(n_bins)
        d0 = triality_well(theta, amplitude=well_amplitude, screen=1.0)
        dh = triality_well(theta, amplitude=well_amplitude, screen=screen)
        depths0.append(d0)
        depths_h.append(dh)
    thresh = collapse_frac * max(depths0) if depths0 else 0.0
    collapsed = sum(1 for d in depths_h if d <= thresh + 1e-15)
    return {
        "n_bins": n_bins,
        "screen": screen,
        "well_amplitude": well_amplitude,
        "collapse_threshold": thresh,
        "collapsed_bins": collapsed,
        "bits_toy": float(collapsed),
    }


def run_report(probe: Any, *, v_fast: float, shell_ms: list[int]) -> dict[str, Any]:
    sg = probe._load_spinor_module()
    mats64 = probe.monomial_arrays_float(sg)
    mats6 = np.stack([mats64[1 << k] for k in range(6)], axis=0)

    mono = verify_monodromy()

    v = float(v_fast)
    if not (0.0 <= v < 1.0):
        raise ValueError("boost velocity v must satisfy 0 <= v < 1")
    screen_fast = 1.0 - v * v

    rows = []
    for m in shell_ms:
        H = probe.manifold_mass_op_8(
            mats6, m, 0, 1, lambda_mix=1.0, zeta_curv=1.0, zeta_phase=1.0
        )
        phi = probe.phi_of_shell(m)
        # Well strength tied to auxiliary ladder (same mass units as φ/6 Δ term).
        well_amp = 0.2 * phi

        base = scan_theta_grid(H, well_amplitude=well_amp, screen=1.0)
        fast = scan_theta_grid(H, well_amplitude=well_amp, screen=screen_fast)
        sectors = triality_sector_minima(H, well_amplitude=well_amp, screen=1.0)
        sectors_fast = triality_sector_minima(
            H, well_amplitude=well_amp, screen=screen_fast
        )

        rows.append(
            {
                "shell_m": m,
                "phi_of_shell": phi,
                "well_amplitude": well_amp,
                "grid_scan_rest": base,
                "grid_scan_boosted": fast,
                "triality_wells_rest": sectors,
                "triality_wells_boosted": sectors_fast,
            }
        )

    ent = [
        horizon_entropy_toy(n_bins=96, screen=1.0, well_amplitude=1.0),
        horizon_entropy_toy(n_bins=96, screen=screen_fast, well_amplitude=1.0),
    ]

    return {
        "monodromy_check": mono,
        "boost_velocity_c": v,
        "screen_factor_1_minus_v2": screen_fast,
        "manifold_pair": [0, 1],
        "shell_scans": rows,
        "horizon_entropy_toy": ent,
        "notes": [
            "exp(2πΔ)=I on the (e₁,e₇) block; orthogonal directions fixed.",
            "Total energy = ⟨ψ(θ)|H|ψ(θ)⟩ + screen·(A/2)(1−cos3θ); three wells per 2π.",
            "screen = (1−v²) models lapse: v→1 flattens the triality barrier.",
        ],
    }


def print_human_summary(rep: dict[str, Any]) -> None:
    print("mass_well_monodromy_sandbox")
    mc = rep["monodromy_check"]
    print(f"  exp(2πΔ)≈I  max|·−I| = {mc['max_abs_exp_2pi_minus_I']:.3e}")
    v = rep["boost_velocity_c"]
    sf = rep["screen_factor_1_minus_v2"]
    print(f"  boost v = {v:g}  → screen (1−v²) = {sf:.6g}")
    print()
    for row in rep["shell_scans"]:
        m = row["shell_m"]
        ph = row["phi_of_shell"]
        wa = row["well_amplitude"]
        br = row["grid_scan_rest"]
        bb = row["grid_scan_boosted"]
        print(
            f"  shell m={m}  φ(m)={ph:g}  well_amp={wa:g}  "
            f"E_max rest={br['E_max']:.4g}  boosted={bb['E_max']:.4g}  "
            f"E_min rest={br['E_min']:.4g}"
        )
    print()
    for i, h in enumerate(rep["horizon_entropy_toy"]):
        tag = "rest" if i == 0 else "boosted screen"
        print(
            f"  entropy toy ({tag}): collapsed_bins={h['collapsed_bins']}/{h['n_bins']}  "
            f"screen={h['screen']:.6g}"
        )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--velocity",
        type=float,
        default=0.99,
        metavar="V",
        help="boost speed v in (1−v²) screen; 0 ≤ v < 1 (default 0.99)",
    )
    ap.add_argument(
        "--shells",
        type=str,
        default="0,1,3,4",
        help='comma-separated shell indices m for φ(m)=2(m+1) (default "0,1,3,4")',
    )
    ap.add_argument(
        "--human",
        action="store_true",
        help="print short text summary in addition to JSON",
    )
    args = ap.parse_args()
    shell_ms = [int(x.strip()) for x in args.shells.split(",") if x.strip()]
    probe = _load_probe()
    rep = run_report(probe, v_fast=args.velocity, shell_ms=shell_ms)
    if args.human:
        print_human_summary(rep)
        print()
    print(json.dumps(rep, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as e:
        print(f"error: {e}", file=sys.stderr)
        raise SystemExit(1)
