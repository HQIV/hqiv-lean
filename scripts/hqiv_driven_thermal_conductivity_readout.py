#!/usr/bin/env python3
"""
Driven phonon thermal-conductivity assay (temperature-profile softener).

Lean: ``Hqiv.QuantumChemistry.PhaseMaterialResponse.drivenPhononThermalConductivity``

  k_driven = k_th / (1 + γ · |ΔT| / T_melt)

Identity at ΔT = 0.  Discrete Fourier / gradient slot without continuum PDE.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_driven_thermal_conductivity_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_driven_thermal_conductivity_readout.py \\
    --json-out data/driven_thermal_conductivity_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_lean_physics_primitives as lean
import hqiv_phase_material_response as pmr
from hqiv_lab.species_panel import panel_entry

DEFAULT_JSON = _REPO_ROOT / "data" / "driven_thermal_conductivity_audit.json"
GAMMA = lean.GAMMA


def driven_phonon_thermal_conductivity(
    k_th: float, delta_t: float, melt_k: float
) -> float:
    """Lean ``drivenPhononThermalConductivity``."""
    denom = 1.0 + GAMMA * abs(float(delta_t)) / max(float(melt_k), 1e-9)
    return float(k_th) / denom


def temperature_profile_samples(
    melt_k: float, *, n: int = 5
) -> list[float]:
    """ΔT samples as fractions of T_melt: 0, γ/2, γ, α, 1 (HQIV rationals)."""
    fracs = [0.0, GAMMA / 2.0, GAMMA, lean.ALPHA, 1.0][: max(int(n), 1)]
    return [f * float(melt_k) for f in fracs]


def driven_row(molecule: str) -> dict[str, Any]:
    entry = panel_entry(molecule)
    melt = float(entry.nist_melt_k)
    t_wit = float(entry.witness_temperature_k)
    out = pmr.material_response_readout(
        molecule,
        allotrope=entry.allotrope,
        phase="solid",
        temperature_k=t_wit,
    )
    k0 = float(out["thermal_conductivity_W_mK"])
    profile = []
    for dt in temperature_profile_samples(melt):
        kd = driven_phonon_thermal_conductivity(k0, dt, melt)
        profile.append(
            {
                "delta_T_K": dt,
                "delta_T_over_melt": dt / melt if melt > 0 else None,
                "k_driven_W_mK": kd,
                "softener": k0 / kd if kd > 0 else None,
            }
        )
    return {
        "molecule": molecule,
        "allotrope": entry.allotrope,
        "temperature_k": t_wit,
        "melt_k": melt,
        "k_th_W_mK": k0,
        "k_th_one_way_W_mK": out.get("thermal_conductivity_one_way_W_mK"),
        "profile": profile,
        "identity_at_zero_gradient": abs(
            driven_phonon_thermal_conductivity(k0, 0.0, melt) - k0
        )
        < 1e-12,
        "formula": "k_driven = k_th / (1 + γ · |ΔT| / T_melt)",
    }


def build_driven_thermal_audit(
    molecules: tuple[str, ...] = ("H2O", "CH4", "NH3", "HF"),
) -> dict[str, Any]:
    rows = [driven_row(m) for m in molecules]
    # Pure identity on a unit k_th.
    k_id = driven_phonon_thermal_conductivity(1.0, 0.0, 273.15)
    k_soft = driven_phonon_thermal_conductivity(1.0, 273.15, 273.15)
    identity = {
        "zero_gradient_identity": abs(k_id - 1.0) < 1e-12,
        "full_melt_softener": abs(k_soft - 1.0 / (1.0 + GAMMA)) < 1e-12,
        "all_rows_identity_at_zero": all(r["identity_at_zero_gradient"] for r in rows),
        "profile_monotone_softening": all(
            r["profile"][i]["k_driven_W_mK"] >= r["profile"][i + 1]["k_driven_W_mK"] - 1e-12
            for r in rows
            for i in range(len(r["profile"]) - 1)
        ),
    }
    return {
        "source": "scripts/hqiv_driven_thermal_conductivity_readout.py",
        "lean_modules": ["Hqiv.QuantumChemistry.PhaseMaterialResponse"],
        "formula": {
            "k_th": "(1/3) ρ c_spec v_s ℓ G_eff B_hom (cage-limited)",
            "driven": "k_driven = k_th / (1 + γ · |ΔT| / T_melt)",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "NIST melt temperatures are quarantine only (panel)",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_driven_thermal_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        k_end = r["profile"][-1]["k_driven_W_mK"]
        print(
            f"  {r['molecule']:4} k_th={r['k_th_W_mK']:.4f}  "
            f"k(ΔT=T_m)={k_end:.4f} W/(m·K)"
        )


if __name__ == "__main__":
    main()
