#!/usr/bin/env python3
"""
HQIV generalized phase diagrams — pure species and mixtures from (T, P).

First-principles: motif → end members → mixture fraction → ρ_curv → phase label.
External LLPT / two-state papers: comparison rows only (never inputs).

Lean: ``Hqiv.QuantumChemistry.PhaseDiagramMixture``
Python: ``hqiv_lab/phase_diagram.py``

Usage:
  PYTHONPATH=.:scripts python3 scripts/hqiv_phase_diagram.py H2O --t 200 --p-atm 1250
  PYTHONPATH=.:scripts python3 scripts/hqiv_phase_diagram.py --mixture H2O:0.9,CH3OH:0.1 --grid
  PYTHONPATH=.:scripts python3 scripts/hqiv_phase_diagram.py --json data/phase_diagram_audit.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

_REPO = Path(__file__).resolve().parent.parent
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))
if str(_REPO / "scripts") not in sys.path:
    sys.path.insert(0, str(_REPO / "scripts"))

import hqiv_thermodynamic_phase_from_tp as tptp
from hqiv_lab.phase_diagram import (
    MixtureComponent,
    WATER_HOH_ANGLE_OBSERVATIONS,
    WATER_LLPT_OBSERVATIONS,
    end_members_for_molecule,
    hoh_angle_witness_row,
    low_density_free_energy_minimum,
    low_density_liquid_fraction,
    metastable_liquid_kinetic_floor_k,
    material_scales_for_spec,
    phase_diagram_grid,
    phase_diagram_point,
    widom_second_order_window_center_k,
    widom_second_order_window_weight,
    widom_line_compressibility_proxy,
    widom_proxy_peak_at_pressure,
)
from hqiv_lab.spec import resolve_spec

DEFAULT_SPECIES: tuple[str, ...] = ("H2O", "CH4", "NH3", "CH3OH", "HF")


def _parse_mixture(text: str) -> tuple[MixtureComponent, ...]:
    parts = [p.strip() for p in text.split(",") if p.strip()]
    out: list[MixtureComponent] = []
    for part in parts:
        name, frac_s = part.split(":")
        out.append(MixtureComponent(name=name.strip(), mole_fraction=float(frac_s)))
    return tuple(out)


def _nearest_hqiv_llcp_row(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    """Closest grid point to Sciortino LLCP observation (comparison only)."""
    target_t = 198.0
    target_p_atm = 1250.0
    liquid_rows = [
        r
        for r in rows
        if r["derived_phase"] in ("metastable_liquid", "liquid")
    ]
    if not liquid_rows:
        return None
    return min(
        liquid_rows,
        key=lambda r: abs(r["temperature_K"] - target_t)
        + 10.0 * abs(r["pressure_atm"] - target_p_atm),
    )


def build_audit_payload(
    species: tuple[str, ...] = DEFAULT_SPECIES,
    *,
    t_min: float = 80.0,
    t_max: float = 330.0,
    t_step: float = 10.0,
    p_atm_values: tuple[float, ...] = (1.0, 100.0, 500.0, 1250.0),
) -> dict[str, Any]:
    temps = tuple(round(t, 2) for t in _frange(t_min, t_max, t_step))
    pressures = tuple(p * tptp.STP_PRESSURE_PA for p in p_atm_values)
    blocks: dict[str, Any] = {}

    for name in species:
        grid = phase_diagram_grid(name, temperatures_k=temps, pressures_pa=pressures, bulk=True)
        low, high = end_members_for_molecule(name)
        t_melt, _ = tptp.characteristic_temperatures_K(tptp.material_scales_bulk_h2o() if name == "H2O" else tptp.material_scales_from_network_name(name))
        blocks[name] = {
            "molecule": name,
            "end_members": {
                "low_density": {"label": low.label, "rho_curv": low.rho_curv},
                "high_density": {"label": high.label, "rho_curv": high.rho_curv},
            },
            "kinetic_floor_K": metastable_liquid_kinetic_floor_k(t_melt) if name == "H2O" else None,
            "grid": grid,
        }
        if name == "H2O":
            blocks[name]["comparison_nearest_llcp"] = _nearest_hqiv_llcp_row(grid)
            mat = material_scales_for_spec(resolve_spec("H2O"), bulk=True)
            widom_grid = []
            for t_k in temps:
                if t_k < 120.0 or t_k > 280.0:
                    continue
                widom_grid.append(
                    {
                        "temperature_K": t_k,
                        "pressure_atm": 1.0,
                        "compressibility_proxy": widom_line_compressibility_proxy(
                            t_k, tptp.STP_PRESSURE_PA, mat
                        ),
                    }
                )
            peak = widom_proxy_peak_at_pressure(mat, tptp.STP_PRESSURE_PA)
            t_melt_h2o, _ = tptp.characteristic_temperatures_K(mat)
            window_center = widom_second_order_window_center_k(t_melt_h2o)
            f_at_window = low_density_liquid_fraction(window_center, tptp.STP_PRESSURE_PA, mat)
            f_baseline = low_density_liquid_fraction(220.0, tptp.STP_PRESSURE_PA, mat)
            f_defect = low_density_liquid_fraction(
                220.0,
                tptp.STP_PRESSURE_PA,
                mat,
                local_coordination_excess=0.25,
            )
            kim_obs = next(
                (
                    o
                    for o in WATER_LLPT_OBSERVATIONS
                    if o.get("label", "").startswith("compressibility maximum")
                ),
                None,
            )
            blocks[name]["widom_compressibility_proxy"] = {
                "grid_1atm": widom_grid,
                "peak": peak,
                "free_energy_minimum_at_window": low_density_free_energy_minimum(
                    window_center, tptp.STP_PRESSURE_PA, mat
                ),
                "gamma2_window": {
                    "T_melt_K": t_melt_h2o,
                    "center_K": window_center,
                    "weight_at_center": widom_second_order_window_weight(window_center, t_melt_h2o),
                    "weight_at_150K": widom_second_order_window_weight(150.0, t_melt_h2o),
                    "peak_minus_center_K": peak["temperature_K"] - window_center,
                },
                "comparison_kim_peak_T_K": kim_obs["T_K"] if kim_obs else None,
                "peak_T_residual_K": abs(peak["temperature_K"] - kim_obs["T_K"])
                if kim_obs
                else None,
            }
            blocks[name]["hoh_angle_witness"] = {
                "window_center_1atm": hoh_angle_witness_row(f_at_window),
                "cytosol_310K_1atm": hoh_angle_witness_row(
                    low_density_liquid_fraction(310.15, tptp.STP_PRESSURE_PA, mat)
                ),
            }
            blocks[name]["nucleation_defect_witness"] = {
                "temperature_K": 220.0,
                "pressure_atm": 1.0,
                "local_coordination_excess": 0.25,
                "f_low_density_baseline": f_baseline,
                "f_low_density_defect": f_defect,
                "f_low_density_excess": f_defect - f_baseline,
            }

    mixture = (MixtureComponent("H2O", 0.85), MixtureComponent("CH3OH", 0.15))
    mix_grid = phase_diagram_grid(mixture, temperatures_k=temps, pressures_pa=pressures)
    blocks["H2O+CH3OH"] = {
        "mixture": [{"name": c.name, "mole_fraction": c.mole_fraction} for c in mixture],
        "grid": mix_grid,
    }

    return {
        "source": "scripts/hqiv_phase_diagram.py",
        "derivation": "HQIV motif + cohesive ladder (no MD/DFT inputs)",
        "comparison_policy": "external observations grade readouts only",
        "water_llpt_observations": list(WATER_LLPT_OBSERVATIONS),
        "water_hoh_angle_observations": list(WATER_HOH_ANGLE_OBSERVATIONS),
        "species": blocks,
    }


def _frange(start: float, stop: float, step: float) -> list[float]:
    pts: list[float] = []
    x = start
    while x <= stop + 1e-9:
        pts.append(x)
        x += step
    return pts


def print_point(pt: Any) -> None:
    print(f"T={pt.temperature_k:.2f} K  P={pt.pressure_pa / tptp.STP_PRESSURE_PA:.1f} atm")
    print(f"  phase={pt.derived_phase}")
    if pt.liquid_subphase is not None:
        print(f"  subphase={pt.liquid_subphase.value}  f_LDL={pt.f_low_density:.4f}")
    print(f"  rho_curv={pt.rho_curv:.4f}  xi={pt.xi:.4e}")
    print(f"  T_melt={pt.T_melt_K:.2f} K  notes: {pt.notes}")


def main() -> int:
    parser = argparse.ArgumentParser(description="HQIV generalized phase diagram")
    parser.add_argument("molecule", nargs="?", default="H2O")
    parser.add_argument("--mixture", type=str, help="e.g. H2O:0.9,CH3OH:0.1")
    parser.add_argument("--t", type=float, default=273.15, help="temperature [K]")
    parser.add_argument("--p-atm", type=float, default=1.0, help="pressure [atm]")
    parser.add_argument("--grid", action="store_true", help="emit small T×P grid to stdout")
    parser.add_argument(
        "--json",
        type=Path,
        default=None,
        help="write audit JSON (default: data/phase_diagram_audit.json when --grid)",
    )
    parser.add_argument("--species", nargs="*", default=list(DEFAULT_SPECIES))
    args = parser.parse_args()

    pressure_pa = args.p_atm * tptp.STP_PRESSURE_PA

    if args.grid or args.json:
        out_path = args.json or (_REPO / "data" / "phase_diagram_audit.json")
        payload = build_audit_payload(tuple(args.species))
        print("HQIV phase diagram audit")
        print("=" * 60)
        for name, block in payload["species"].items():
            n_pts = len(block.get("grid", []))
            print(f"  {name}: {n_pts} (T,P) points")
        if payload["species"].get("H2O", {}).get("comparison_nearest_llcp"):
            near = payload["species"]["H2O"]["comparison_nearest_llcp"]
            print(
                f"\nH2O nearest HQIV point to Sciortino LLCP grid cell:"
                f" T={near['temperature_K']} K P={near['pressure_atm']:.0f} atm"
                f" phase={near['derived_phase']} f_LDL={near.get('f_low_density')}"
            )
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"\nWrote {out_path}")
        return 0

    target: str | tuple[MixtureComponent, ...]
    if args.mixture:
        target = _parse_mixture(args.mixture)
    else:
        target = args.molecule

    pt = phase_diagram_point(target, temperature_k=args.t, pressure_pa=pressure_pa)
    print_point(pt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
