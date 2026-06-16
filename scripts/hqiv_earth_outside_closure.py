#!/usr/bin/env python3
"""
Earth-scale outside-closure witness: K = B_curv(ξ) × f_g(ε).

Universe age enters through ξ = T_Pl/(k_B T) (CMB monopole or lab temperature).
Gravity well enters through the cumulative weak-field stack
(Earth + Sun @ 1 AU + Galactic v_c²/c² + CMB dipole v/c).

Mirrors the stack used in relic-ν opacity / weak-width catalysis and names it as
the single Earth input for downstream binding and decay readouts.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_earth_outside_closure.py
  PYTHONPATH=scripts python3 scripts/hqiv_earth_outside_closure.py --json data/earth_outside_closure.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "earth_outside_closure.json"


def witness_block(
    *,
    lab_temperature_K: float = notd.LAB_ROOM_TEMPERATURE_K,
    gravity_tier: notd.GravityBindingTier = "full",
) -> dict[str, Any]:
    presets: list[tuple[str, notd.LabOutsideEnvironment]] = [
        (
            "earth_surface_300K_full_gravity",
            notd.LabOutsideEnvironment(
                lab_temperature_K=lab_temperature_K,
                reference_temperature_K=notd.CMB_TEMPERATURE_K,
                gravity_tier=gravity_tier,
            ),
        ),
        (
            "earth_surface_cmb_temperature_full_gravity",
            notd.LabOutsideEnvironment(
                lab_temperature_K=notd.CMB_TEMPERATURE_K,
                reference_temperature_K=notd.CMB_TEMPERATURE_K,
                gravity_tier=gravity_tier,
            ),
        ),
        (
            "deep_space_cmb_reference",
            notd.LabOutsideEnvironment(
                lab_temperature_K=notd.CMB_TEMPERATURE_K,
                reference_temperature_K=notd.CMB_TEMPERATURE_K,
                gravity_tier="none",
                cmb_dipole_velocity_m_s=0.0,
            ),
        ),
        (
            "lockin_anchor_neutral",
            notd.LabOutsideEnvironment(
                lab_xi=notd.XI_LOCKIN,
                anchor_xi=notd.XI_LOCKIN,
                gravity_tier="none",
                cmb_dipole_velocity_m_s=0.0,
            ),
        ),
        (
            "bbn_T_0p1_MeV",
            notd.LabOutsideEnvironment(
                lab_temperature_K=notd.T_MeV_from_xi(notd.xi_from_T_MeV(0.1))
                / notd.K_B_MEV_PER_K,
                reference_temperature_K=notd.CMB_TEMPERATURE_K,
                gravity_tier="none",
                cmb_dipole_velocity_m_s=0.0,
                anchor_xi=notd.XI_LOCKIN,
            ),
        ),
    ]
    rows = {label: notd.earth_outside_closure_k(env).to_dict() for label, env in presets}
    earth = rows["earth_surface_300K_full_gravity"]
    return {
        "source": "scripts/hqiv_earth_outside_closure.py",
        "lean_modules": [
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.ProtonMassDecomposition",
            "Hqiv.Physics.HomogeneousCurvatureSecondOrder",
        ],
        "formula": {
            "K": "B_curv(xi) * f_g(epsilon)",
            "B_curv": "curvature_budget_at_xi(xi, xi_lock); unity at xi_lock=5",
            "xi_age": "T_Pl_MeV / (k_B * T_K)",
            "f_g": "1 + gamma * ((1 + epsilon)^alpha - 1); alpha=3/5, gamma=2/5",
            "epsilon": "GM/(Rc^2) stack + CMB dipole v/c",
        },
        "policy": (
            "K_mass_chart uses xi_lock (B_curv=1, gravity well only). "
            "K_ambient uses lab temperature xi for width/lifetime pipelines. "
            "Not a fit knob: lattice rationals + SI gravity stack + CMB T."
        ),
        "earth_default": earth,
        "presets": rows,
        "usage": {
            "mass_ledger": "multiply outside own-binding increment by K_mass_chart",
            "width_ledger": "multiply outside caustic depth by K_ambient",
            "bbn_epochs": "K at hot xi from outside_curvature_binding_modulator (bonded/free)",
        },
        "slot_ppm": {
            "K_mass_chart_minus_1_ppm": (earth["K_mass_chart"] - 1.0) * 1.0e6,
            "K_ambient_minus_1_ppm": (earth["K_ambient"] - 1.0) * 1.0e6,
            "increment_vs_anchor_ppm": earth["increment_vs_anchor"] * 1.0e6,
        },
    }


def print_report(block: dict[str, Any]) -> None:
    earth = block["earth_default"]
    ppm = block["slot_ppm"]
    print("HQIV Earth outside-closure K witness")
    print("=" * 72)
    print(
        f"ξ_lock={earth['xi_lock']:.1f}  "
        f"ξ_CMB={earth['xi_cmb']:.3e}  "
        f"ξ_ambient={earth['xi_ambient']:.3e}"
    )
    print(
        f"B_curv: lock={earth['B_curv_lock']:.6f}  "
        f"ambient={earth['B_curv_ambient']:.6f}  "
        f"cmb={earth['B_curv_cmb']:.6f}"
    )
    print(
        f"f_g: grav={earth['f_gravity']:.9f}  "
        f"dipole={earth['f_kinetic']:.9f}  "
        f"combined={earth['f_gravity_combined']:.9f}"
    )
    print(
        f"K_mass_chart={earth['K_mass_chart']:.9f}  "
        f"K_ambient={earth['K_ambient']:.6f}  "
        f"K_imprint={earth['K_imprint']:.6f}"
    )
    print(
        f"ppm: K_mass−1={ppm['K_mass_chart_minus_1_ppm']:.4f}  "
        f"K_amb−1={ppm['K_ambient_minus_1_ppm']:.1f}  "
        f"Δanchor={ppm['increment_vs_anchor_ppm']:.4f}"
    )
    stack = earth["gravity_stack"]
    print(
        f"ε: earth={stack['earth']:.3e}  sun={stack['sun']:.3e}  "
        f"gal={stack['galaxy']:.3e}  total={stack['total_gravity']:.3e}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Earth outside-closure K witness")
    parser.add_argument("--json", type=Path, default=None, help="Write witness JSON")
    parser.add_argument("--lab-temperature-K", type=float, default=notd.LAB_ROOM_TEMPERATURE_K)
    parser.add_argument(
        "--gravity-tier",
        choices=["none", "earth", "solar_system", "full"],
        default="full",
    )
    args = parser.parse_args()
    block = witness_block(
        lab_temperature_K=args.lab_temperature_K,
        gravity_tier=args.gravity_tier,
    )
    print_report(block)
    out = args.json or DEFAULT_JSON
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(block, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
