#!/usr/bin/env python3
"""
Proton mass decomposition: inner composite-trace anchor vs outside-curvature slots.

Mirror of `Hqiv.Physics.ProtonMassDecomposition`.

  M_p^obs = M_p^inner − τ(m=4)·(f_lab/f_anchor − 1)

Outside slots (lab vs hadronic lock-in anchor):

  • CMB monopole temperature → ``ξ_CMB = T_Pl/(k_B T_CMB)`` (universe-age chart)
  • Lab temperature ``T_lab`` (room / cryogenic)
  • Gravity ``ε = Σ GM/(Rc²)`` (Earth + Sun + Galactic disk)
  • CMB dipole proper motion ``v/c`` (additive lapse on ``G_eff``)

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_proton_mass_decomposition.py
  PYTHONPATH=scripts python3 scripts/hqiv_proton_mass_decomposition.py --patch-witness
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_nuclear_inside_outside_binding as niob
import hqiv_nuclear_outside_temperature_dynamics as notd

ROOT = Path(__file__).resolve().parents[1]
WITNESS_JSON = ROOT / "data" / "hqiv_witnesses.json"
PDG_PROTON_MEV = 938.27208816

GravityTier = Literal["none", "earth", "solar_system", "full"]


@dataclass(frozen=True)
class ProtonMassDecomposition:
    inner_raw_mev: float
    trace_mev: float
    outside_modulator: float
    outside_release_increment_mev: float
    outside_gravity_increment_mev: float
    outside_kinetic_increment_mev: float
    outside_total_increment_mev: float
    observed_dynamic_mev: float
    xi: float
    bonded: bool
    phi_gravity_epsilon: float
    cmb_proper_motion_v_over_c: float
    observed_vs_pdg_ppm: float
    lab_outside: dict[str, float]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _load_witness() -> dict[str, Any]:
    if WITNESS_JSON.is_file():
        return json.loads(WITNESS_JSON.read_text(encoding="utf-8"))
    return {
        "derivedProtonMass_MeV": 938.272,
        "referenceM": notd.REFERENCE_M,
    }


def proton_inner_raw_mev() -> float:
    return float(_load_witness()["derivedProtonMass_MeV"])


def proton_binding_trace_mev(shell: int = notd.REFERENCE_M) -> float:
    return niob.nucleon_trace_binding_mev(shell)


def default_lab_environment(
    *,
    gravity_tier: GravityTier = "full",
    lab_temperature_K: float = notd.LAB_ROOM_TEMPERATURE_K,
    cmb_dipole_velocity_m_s: float = notd.CMB_DIPOLE_V_M_S,
) -> notd.LabOutsideEnvironment:
    return notd.LabOutsideEnvironment(
        lab_temperature_K=lab_temperature_K,
        reference_temperature_K=notd.CMB_TEMPERATURE_K,
        gravity_tier=gravity_tier,
        cmb_dipole_velocity_m_s=cmb_dipole_velocity_m_s,
    )


def proton_mass_decomposition(
    env: notd.LabOutsideEnvironment | None = None,
    *,
    shell: int = notd.REFERENCE_M,
) -> ProtonMassDecomposition:
    env = env or default_lab_environment()
    inner = proton_inner_raw_mev()
    trace = proton_binding_trace_mev(shell)
    mod_lab = env.hadronic_lab_modulator()
    mod_anchor = env.anchor_modulator()
    temp_support = env.support_ratio_vs_cmb()
    grav = env.gravity_modulator()
    kin = env.kinetic_modulator()
    grav_inc = trace * (grav - 1.0)
    kin_inc = trace * grav * (kin - 1.0)
    rel_inc = trace * (temp_support - 1.0)
    outside_total = trace * (mod_lab / mod_anchor - 1.0)
    observed = inner - outside_total
    ppm = (observed - PDG_PROTON_MEV) / PDG_PROTON_MEV * 1.0e6
    lab_audit = notd.lab_outside_decomposition(env, shell=shell, inner_raw_mev=inner)
    return ProtonMassDecomposition(
        inner_raw_mev=inner,
        trace_mev=trace,
        outside_modulator=mod_lab,
        outside_release_increment_mev=rel_inc,
        outside_gravity_increment_mev=grav_inc,
        outside_kinetic_increment_mev=kin_inc,
        outside_total_increment_mev=outside_total,
        observed_dynamic_mev=observed,
        xi=env.lab_xi_from_temperature,
        bonded=env.bonded,
        phi_gravity_epsilon=env.gravity_phi_epsilon,
        cmb_proper_motion_v_over_c=env.cmb_proper_motion_v_over_c,
        observed_vs_pdg_ppm=ppm,
        lab_outside=lab_audit.to_dict(),
    )


def witness_decomposition_block(
    *,
    gravity_tier: GravityTier = "full",
) -> dict[str, Any]:
    lockin = proton_mass_decomposition(
        notd.LabOutsideEnvironment(
            lab_xi=notd.XI_LOCKIN,
            gravity_tier="none",
            cmb_dipole_velocity_m_s=0.0,
            anchor_xi=notd.XI_LOCKIN,
        )
    )
    lab_full = proton_mass_decomposition(default_lab_environment(gravity_tier=gravity_tier))
    bbn_xi = notd.xi_from_T_MeV(0.1)
    bbn = proton_mass_decomposition(
        notd.LabOutsideEnvironment(
            lab_temperature_K=notd.T_MeV_from_xi(bbn_xi) / notd.K_B_MEV_PER_K,
            gravity_tier="none",
            cmb_dipole_velocity_m_s=0.0,
            anchor_xi=notd.XI_LOCKIN,
        )
    )
    audit = lab_full.lab_outside
    k_earth = notd.earth_outside_closure_k(default_lab_environment(gravity_tier=gravity_tier))
    return {
        "lean_module": "Hqiv.Physics.ProtonMassDecomposition",
        "policy": (
            "inner anchor at xi_lock; lab slots = CMB T + lab T + gravity + CMB dipole v/c"
        ),
        "pdg_proton_mass_mev": PDG_PROTON_MEV,
        "cmb_temperature_K": notd.CMB_TEMPERATURE_K,
        "lab_room_temperature_K": notd.LAB_ROOM_TEMPERATURE_K,
        "cmb_dipole_v_m_s": notd.CMB_DIPOLE_V_M_S,
        "outside_closure_K": k_earth.to_dict(),
        "lockin_neutral": lockin.to_dict(),
        "lab_earth_full_stack": lab_full.to_dict(),
        "bbn_free_branch": bbn.to_dict(),
        "slot_ppm_budget": {
            "temperature_support_vs_cmb_ppm": (audit["support_ratio_vs_cmb"] - 1.0) * 1.0e6,
            "gravity_geff_ppm_on_trace": (audit["gravity_modulator"] - 1.0)
            * audit["trace_mev"]
            / PDG_PROTON_MEV
            * 1.0e6,
            "cmb_dipole_kinetic_ppm_on_trace": (audit["kinetic_modulator"] - 1.0)
            * audit["trace_mev"]
            / PDG_PROTON_MEV
            * 1.0e6,
            "combined_hadronic_chart_ppm": audit["mass_shift_ppm_vs_anchor"],
            "K_mass_chart_minus_1_ppm": (k_earth.K_mass_chart - 1.0) * 1.0e6,
            "K_ambient_minus_1_ppm": (k_earth.K_ambient - 1.0) * 1.0e6,
            "note": (
                "Mass chart stays on xi_lock; T_lab vs T_CMB is the ~10^3 ppm support "
                "slot (widths/lifetimes). Gravity + dipole on xi_lock are ~1 ppm on mass. "
                "K_ambient = B_curv(xi_lab)*f_g books universe-age + gravity for width ledger."
            ),
        },
        "xi_chart": {
            "anchor_xi_lock": notd.XI_LOCKIN,
            "xi_cmb_monopole": audit["reference_xi"],
            "xi_lab_room_300K": audit["lab_xi"],
        },
        "gravity_tier": gravity_tier,
    }


def patch_witness_json(*, gravity_tier: GravityTier = "full") -> Path:
    raw = _load_witness()
    block = witness_decomposition_block(gravity_tier=gravity_tier)
    raw["protonMassDecomposition"] = block
    raw["protonInnerRawMass_MeV"] = block["lockin_neutral"]["inner_raw_mev"]
    lab = block["lab_earth_full_stack"]
    raw["protonObservedMass_MeV"] = lab["observed_dynamic_mev"]
    raw["protonOutsideIncrement_MeV"] = lab["outside_total_increment_mev"]
    WITNESS_JSON.write_text(json.dumps(raw, indent=2) + "\n", encoding="utf-8")
    return WITNESS_JSON


def print_report(block: dict[str, Any]) -> None:
    print("HQIV proton mass decomposition (inner anchor + lab outside slots)")
    print("=" * 72)
    print(
        f"ξ_lock={block['xi_chart']['anchor_xi_lock']:.1f}  "
        f"ξ_CMB={block['xi_chart']['xi_cmb_monopole']:.3e}  "
        f"ξ_300K={block['xi_chart']['xi_lab_room_300K']:.3e}"
    )
    ppm = block["slot_ppm_budget"]
    print(
        f"slot ppm  T_support={ppm['temperature_support_vs_cmb_ppm']:.1f}  "
        f"grav={ppm['gravity_geff_ppm_on_trace']:.3f}  "
        f"dipole={ppm['cmb_dipole_kinetic_ppm_on_trace']:.3f}  "
        f"hadronic_chart={ppm['combined_hadronic_chart_ppm']:.3f}"
    )
    for label in ("lockin_neutral", "lab_earth_full_stack", "bbn_free_branch"):
        row = block[label]
        print(
            f"{label:<22} "
            f"inner={row['inner_raw_mev']:.6f} "
            f"Δout={row['outside_total_increment_mev']:.3e} MeV "
            f"obs={row['observed_dynamic_mev']:.6f} "
            f"({row['observed_vs_pdg_ppm']:.4f} ppm vs PDG)"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Proton inner/outside mass decomposition")
    parser.add_argument("--patch-witness", action="store_true")
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--gravity-tier", choices=["none", "earth", "solar_system", "full"], default="full")
    args = parser.parse_args()
    block = witness_decomposition_block(gravity_tier=args.gravity_tier)
    print_report(block)
    if args.patch_witness:
        path = patch_witness_json(gravity_tier=args.gravity_tier)
        print(f"Patched {path}")
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(block, indent=2) + "\n")
        print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()
