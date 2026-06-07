#!/usr/bin/env python3
"""
LiH binding energy with HQIV dynamic shell-chart physics.

Mirrors the post-T12/T13 machinery used in bulk baryogenesis / BBN:
  - ωK(ξ), dynamic T13 outer suppression, inner–outer Casimir (`hqiv_lean_physics_primitives`)
  - Compton-window nuclear-torus angles (`lih_derivation_scan`)
  - Lean LiH dissociation indicator (`Hqiv.QuantumChemistry.LiHDerivation`)

Primary binding readout (eV, chemist convention — positive = bound):

  E_bind = η_p · bond_surplus(4→3+1) · EV_per_λ · vev_geom(4,3,1)
           · (1 + binding_curvature_correction)

where η_p is Compton IR-window participation on the Li p shell,
vev_geom is the geometric mean of `tuft_vev_factor_at_xi` on the Compton triplet,
and binding feedback uses Lean `dynamicBindingCurvatureFeedbackAtXi` (γ·4/8·B_curv(ξ)).

Run:
  python3 scripts/hqiv_lih_dynamic_binding.py
  python3 scripts/hqiv_lih_dynamic_binding.py --json-out data/lih_dynamic_binding.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import hqiv_lean_physics_primitives as lean
from bonded_horizon_casimir_float import EV_PER_LAMBDA_UNIT, bond_horizon_surplus_dimless
from lih_derivation_scan import (
    LIH_REFERENCE_EV,
    compton_window_angles_from_detuning_lapse,
    lattice_full_mode_energy,
    lih_bonded_surplus_dimless,
    lih_p_uplift_dimless,
)

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "lih_dynamic_binding.json"

# Canonical Compton valence shells (Lean: `lihComptonUsedShells_eq_spec`)
LIH_M_LI_S = 4
LIH_M_LI_P = 3
LIH_M_H_S = 1
PHASE_THETA = math.pi / 2.0


def xi_of_shell(m: int) -> float:
    return float(m + 1)


def phase_participation_eta(x: float) -> float:
    """Lean `phaseParticipationEta` = x / phaseTheta."""
    return x / PHASE_THETA


@dataclass(frozen=True)
class ShellDynamicRow:
    site: str
    m: int
    xi: float
    E_site_static: float
    E_site_dynamic: float
    omega_k: float
    tuft_vev_factor: float
    effective_casimir: float
    t13_outer_suppression: float


@dataclass(frozen=True)
class LiHBindingResult:
    mode: str
    binding_ev: float
    reference_ev: float
    error_pct: float
    dimless_core: float
    notes: str


def dynamic_site_energy_dimless(m: int) -> float:
    xi = xi_of_shell(m)
    return lattice_full_mode_energy(m) * lean.tuft_vev_factor_at_xi(xi)


def shell_dynamic_rows() -> list[ShellDynamicRow]:
    specs = (
        ("Li_s", LIH_M_LI_S, 1),
        ("Li_p", LIH_M_LI_P, 3),
        ("H_s", LIH_M_H_S, 1),
    )
    rows: list[ShellDynamicRow] = []
    for site, m, _mult in specs:
        xi = xi_of_shell(m)
        rows.append(
            ShellDynamicRow(
                site=site,
                m=m,
                xi=xi,
                E_site_static=lattice_full_mode_energy(m),
                E_site_dynamic=dynamic_site_energy_dimless(m),
                omega_k=lean.omega_k_xi(xi),
                tuft_vev_factor=lean.tuft_vev_factor_at_xi(xi),
                effective_casimir=lean.effective_casimir_scale_at_xi(xi),
                t13_outer_suppression=lean.t13_outer_suppression_at_xi(xi),
            )
        )
    return rows


def valence_trace_dimless(*, dynamic: bool, p_participation: float = 1.0) -> float:
    if dynamic:
        e_li_s = dynamic_site_energy_dimless(LIH_M_LI_S)
        e_li_p = dynamic_site_energy_dimless(LIH_M_LI_P)
        e_h = dynamic_site_energy_dimless(LIH_M_H_S)
    else:
        e_li_s = lattice_full_mode_energy(LIH_M_LI_S)
        e_li_p = lattice_full_mode_energy(LIH_M_LI_P)
        e_h = lattice_full_mode_energy(LIH_M_H_S)
    return e_li_s + p_participation * 3.0 * e_li_p + e_h


def compton_context() -> tuple[tuple[float, float, float], float, dict[str, Any]]:
    compton, detuning = compton_window_angles_from_detuning_lapse()
    mean_angle = sum(compton.angles_rad) / 3.0
    eta_p = phase_participation_eta(mean_angle)
    meta = {
        "angles_rad": compton.angles_rad,
        "mean_angle_rad": mean_angle,
        "eta_p": eta_p,
        "shared_time_s": compton.shared_time_s,
        "in_window": compton.in_window,
        "detuning_lapse_fraction": detuning.lapse_fraction,
    }
    return compton.angles_rad, eta_p, meta


def vev_geometric_mean_bare(shells: tuple[int, ...] = (LIH_M_LI_S, LIH_M_LI_P, LIH_M_H_S)) -> float:
    factors = [lean.tuft_vev_factor_at_xi(xi_of_shell(m)) for m in shells]
    return math.prod(factors) ** (1.0 / len(factors))


def vev_geometric_mean(shells: tuple[int, int, int] = (LIH_M_LI_S, LIH_M_LI_P, LIH_M_H_S)) -> float:
    """Cluster-mass-networked Compton geomean (Li A = 7, H A = 1)."""
    import hqiv_nuclear_curvature_binding as ncb

    return ncb.vev_geometric_mean_networked_for_compton_triplet(
        shells,
        heavy_mass_number=ncb.stable_mass_number(3, 3),
        light_mass_number=1,
    )


def binding_results(angles: tuple[float, float, float], eta_p: float) -> list[LiHBindingResult]:
    bond = bond_horizon_surplus_dimless(4, 3, 1, angles)
    vev_g = vev_geometric_mean()
    xi_contact = lean.xi_from_compton_triplet((LIH_M_LI_S, LIH_M_LI_P, LIH_M_H_S))
    feedback = lean.dynamic_binding_curvature_feedback_at_xi(xi_contact)
    ev_per = EV_PER_LAMBDA_UNIT

    dynamic_bind_core = eta_p * bond * vev_g * feedback
    dynamic_bind = dynamic_bind_core * ev_per

    static_indicator = lih_bonded_surplus_dimless(angles) + lih_p_uplift_dimless(LIH_M_LI_P)
    static_bind = -static_indicator * ev_per

    participation_indicator = bond + eta_p * lih_p_uplift_dimless(LIH_M_LI_P)
    participation_bind = -participation_indicator * ev_per

    bond_only_bind = bond * ev_per

    def _row(mode: str, binding: float, dimless: float, notes: str) -> LiHBindingResult:
        return LiHBindingResult(
            mode=mode,
            binding_ev=binding,
            reference_ev=LIH_REFERENCE_EV,
            error_pct=(binding - LIH_REFERENCE_EV) / LIH_REFERENCE_EV * 100.0,
            dimless_core=dimless,
            notes=notes,
        )

    return [
        _row(
            "dynamic_compton_participation",
            dynamic_bind,
            dynamic_bind_core,
            f"η_p · bond · vev_geom · dynamicBindingFeedbackAtXi({xi_contact:.3f}) · EV_per_λ — primary readout",
        ),
        _row(
            "bond_surplus_only_compton",
            bond_only_bind,
            bond,
            "bond_horizon_surplus only (no η_p / vev / binding feedback)",
        ),
        _row(
            "legacy_full_indicator_static",
            static_bind,
            static_indicator,
            "−(bond + 3·E_site(Li_p)) · EV_per_λ — pre-dynamic Lean scan convention",
        ),
        _row(
            "legacy_participation_indicator",
            participation_bind,
            participation_indicator,
            "−(bond + η_p·3·E_site(Li_p)) · EV_per_λ — LiHDerivation participation branch",
        ),
    ]


def build_payload() -> dict[str, Any]:
    angles, eta_p, compton_meta = compton_context()
    rows = shell_dynamic_rows()
    bindings = binding_results(angles, eta_p)
    primary = next(r for r in bindings if r.mode == "dynamic_compton_participation")

    xi_lih = lean.xi_from_compton_triplet((LIH_M_LI_S, LIH_M_LI_P, LIH_M_H_S))
    return {
        "source": "scripts/hqiv_lih_dynamic_binding.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.LiH",
            "Hqiv.QuantumChemistry.LiHDerivation",
            "Hqiv.Physics.HopfShellBeltramiMassBridge",
            "Hqiv.Physics.DynamicBBNBaryogenesis",
            "Hqiv.Physics.BaryogenesisWitness",
        ],
        "python_primitives": "hqiv_lean_physics_primitives",
        "reference_binding_ev": LIH_REFERENCE_EV,
        "ev_per_lambda_unit": EV_PER_LAMBDA_UNIT,
        "compton_shells_m": [LIH_M_LI_S, LIH_M_LI_P, LIH_M_H_S],
        "compton_context": compton_meta,
        "contact_xi": xi_lih,
        "dynamic_binding_curvature_coupling": lean.dynamic_binding_curvature_coupling_at_xi(
            xi_lih
        ),
        "dynamic_binding_curvature_feedback_factor": lean.dynamic_binding_curvature_feedback_at_xi(
            xi_lih
        ),
        "dynamic_binding_curvature_correction": lean.dynamic_binding_curvature_correction_at_xi(
            xi_lih
        ),
        "vev_geometric_mean_compton": vev_geometric_mean(),
        "vev_geometric_mean_compton_bare": vev_geometric_mean_bare(),
        "valence_trace_dimless": {
            "static_full_p": valence_trace_dimless(dynamic=False, p_participation=1.0),
            "dynamic_full_p": valence_trace_dimless(dynamic=True, p_participation=1.0),
            "dynamic_eta_p": valence_trace_dimless(dynamic=True, p_participation=eta_p),
        },
        "shell_dynamic_rows": [asdict(r) for r in rows],
        "binding_readouts": [asdict(r) for r in bindings],
        "primary_binding_ev": primary.binding_ev,
        "primary_error_pct": primary.error_pct,
        "formula_primary": (
            "E_bind = eta_p * bond_surplus(4,3,1) * EV_per_lambda * "
            "geomean(tuft_vev_factor_at_xi) * dynamicBindingCurvatureFeedbackAtXi(xi_contact)"
        ),
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV LiH dynamic binding (Compton shells 4, 3, 1)")
    print("=" * 60)
    print(f"Reference D0 (W4-17/GMTKN55)     = {payload['reference_binding_ev']:.6f} eV")
    print(f"EV_per_lambda (H anchor)         = {payload['ev_per_lambda_unit']:.12f}")
    print()
    ctx = payload["compton_context"]
    print("Compton + detuning-lapse window:")
    print(f"  η_p (phase participation)      = {ctx['eta_p']:.6f}")
    print(f"  angles (rad)                   = {ctx['angles_rad']}")
    print(f"  lapse_fraction                 = {ctx['detuning_lapse_fraction']:.6f}")
    print()
    print("Dynamic shell chart (integer readout samples):")
    print(f"  {'site':>5} {'m':>3} {'ξ':>5} {'E_static':>10} {'E_dyn':>10} "
          f"{'ωK':>8} {'vev':>8} {'Casimir':>10}")
    for row in payload["shell_dynamic_rows"]:
        print(
            f"  {row['site']:>5} {row['m']:3d} {row['xi']:5.1f} "
            f"{row['E_site_static']:10.2f} {row['E_site_dynamic']:10.2f} "
            f"{row['omega_k']:8.4f} {row['tuft_vev_factor']:8.4f} "
            f"{row['effective_casimir']:10.2f}"
        )
    vt = payload["valence_trace_dimless"]
    print()
    print("Valence site-energy trace (dimless):")
    print(f"  static (full p)                = {vt['static_full_p']:.6f}")
    print(f"  dynamic (full p)               = {vt['dynamic_full_p']:.6f}")
    print(f"  dynamic (η_p-weighted p)       = {vt['dynamic_eta_p']:.6f}")
    print()
    print("Binding readouts:")
    for row in payload["binding_readouts"]:
        print(
            f"  [{row['mode']}]"
            f"\n    E_bind = {row['binding_ev']:+.6f} eV  "
            f"(err {row['error_pct']:+.2f}%)"
            f"\n    {row['notes']}"
        )
    print()
    print("Primary dynamic readout:")
    print(f"  E_bind = {payload['primary_binding_ev']:.6f} eV  "
          f"(err {payload['primary_error_pct']:+.2f}%)")
    print(f"  {payload['formula_primary']}")


def main() -> None:
    parser = argparse.ArgumentParser(description="LiH binding with HQIV dynamic shell physics")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    payload = build_payload()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")

    print_report(payload)
    print()
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()
