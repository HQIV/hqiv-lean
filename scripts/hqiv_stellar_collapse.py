#!/usr/bin/env python3
"""
Stellar-collapse witness: ZAMS mass → iron core → HQIV ε-tipping outcome.

Maps presupernova cores through the same curvature-slot ceilings as
``hqiv_compact_object_mass`` (NS max at ε = γ/2, direct BH when ε_s ≥ ½).

Compares HQIV direct-BH mass ceiling to schematic stellar-evolution bands
(core-mass power law + fallback; pair-instability disruption window).

Run:
  python3 scripts/hqiv_stellar_collapse.py
  python3 scripts/hqiv_stellar_collapse.py --json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

from hqiv_compact_object_mass import (  # noqa: E402
    C_RINDLER_SHARED,
    EPS_CHARM_TIP,
    EPS_HORIZON,
    EPS_TOP_TIP,
    GAMMA,
    M_SUN_KG,
    RHO_NUCLEAR_KG_M3,
    compactness_rs_over_r,
    epsilon_for_mass_msun,
    gradient_collapse_hypothesis,
    gravitational_phi_epsilon,
    horizon_mass_at_radius,
    layered_mass_kg,
    mass_from_epsilon_crit,
    matter_density,
    radius_uniform_density,
    zone_outer_radii,
)

OutcomeKind = Literal[
    "white_dwarf_or_no_collapse",
    "neutron_star",
    "heavy_ns_near_ceiling",
    "charmed_tail_metastable",
    "direct_black_hole",
    "pair_instability_disrupted",
]

# Trad comparison windows (not HQIV inputs — labeled in witness JSON).
PAIR_INSTABILITY_ZAMS_LO_MSUN = 140.0
PAIR_INSTABILITY_ZAMS_HI_MSUN = 260.0
LITERATURE_DIRECT_BH_CEILING_MSUN = 45.0  # schematic upper stellar-origin band


@dataclass(frozen=True)
class IronCorePrescription:
    """Schematic iron-core mass at collapse (comparison scaffold)."""

    label: str
    zams_mass_msun: float
    iron_core_mass_msun: float
    notes: str


def iron_core_mass_msun(zams_mass_msun: float) -> float:
    """
    Power-law iron-core mass at core bounce (witness scaffold).

    Calibrated loosely to CO-core / Fe-core tracks for 15–60 M☉ progenitors;
    not a fitted potential — comparison layer only.
    """
    if zams_mass_msun < 8.0:
        return 0.0
    return 0.08 * (zams_mass_msun - 5.0) ** 1.55


def fallback_bh_mass_msun(zams_mass_msun: float, core_mass_msun: float) -> float:
    """
    Failed-supernova fallback envelope (trad comparison).

    Direct-collapse channel uses core mass only; fallback channel adds envelope.
    """
    if zams_mass_msun < 18.0:
        return core_mass_msun
    # Schematic failed-SN fallback fraction rising with ZAMS.
    frac = min(0.55, 0.12 + 0.008 * (zams_mass_msun - 18.0))
    return max(core_mass_msun, frac * zams_mass_msun)


def hqiv_remnant_at_uniform_nuclear(core_mass_msun: float) -> dict[str, float | str]:
    """Classify a uniform nuclear-density core by surface ε slots."""
    if core_mass_msun <= 0.0:
        return {
            "outcome": "white_dwarf_or_no_collapse",
            "epsilon_surface": 0.0,
            "radius_km": 0.0,
            "compactness_rs_over_r": 0.0,
            "remnant_mass_msun": 0.0,
        }

    mass_kg = core_mass_msun * M_SUN_KG
    radius_m = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3)
    eps_s = gravitational_phi_epsilon(mass_kg, radius_m)
    eps_c = eps_s * 1.5
    rs_r = compactness_rs_over_r(mass_kg, radius_m)

    rho_c = matter_density("charmed")
    rho_t = matter_density("top")
    r_top, r_charm = zone_outer_radii(eps_s, radius_m)
    m_layered = layered_mass_kg(radius_m, r_top, r_charm, rho_c=rho_c, rho_t=rho_t) / M_SUN_KG
    m_horizon_fixed_r = horizon_mass_at_radius(radius_m) / M_SUN_KG

    if eps_s < C_RINDLER_SHARED:
        outcome: OutcomeKind = "neutron_star"
    elif eps_s < EPS_CHARM_TIP:
        outcome = "heavy_ns_near_ceiling"
    elif eps_s < EPS_HORIZON:
        outcome = "charmed_tail_metastable"
    else:
        outcome = "direct_black_hole"

    remnant = core_mass_msun if outcome == "direct_black_hole" else min(core_mass_msun, m_layered)

    return {
        "outcome": outcome,
        "epsilon_surface": eps_s,
        "epsilon_center": eps_c,
        "radius_km": radius_m / 1000.0,
        "compactness_rs_over_r": rs_r,
        "remnant_mass_msun": remnant,
        "layered_mass_msun": m_layered,
        "horizon_mass_at_same_r_msun": m_horizon_fixed_r,
        "r_charm_over_R": r_charm / radius_m if radius_m > 0 else 0.0,
    }


@dataclass(frozen=True)
class StellarCollapseRow:
    zams_mass_msun: float
    iron_core_mass_msun: float
    outcome_uniform: str
    remnant_uniform_msun: float
    epsilon_surface: float
    compactness_rs_over_r: float
    horizon_at_core_radius_msun: float
    fallback_bh_mass_msun: float
    trad_pair_instability: bool
    notes: str


def stellar_collapse_row(zams_mass_msun: float) -> StellarCollapseRow:
    core = iron_core_mass_msun(zams_mass_msun)
    uni = hqiv_remnant_at_uniform_nuclear(core)
    mass_kg = core * M_SUN_KG if core > 0 else 0.0
    r_m = radius_uniform_density(mass_kg, RHO_NUCLEAR_KG_M3) if core > 0 else 0.0
    m_horizon_r = horizon_mass_at_radius(r_m) / M_SUN_KG if r_m > 0 else 0.0
    pi = PAIR_INSTABILITY_ZAMS_LO_MSUN <= zams_mass_msun <= PAIR_INSTABILITY_ZAMS_HI_MSUN

    outcome = str(uni["outcome"])
    remnant = float(uni["remnant_mass_msun"])
    fallback = fallback_bh_mass_msun(zams_mass_msun, core)

    notes = ""
    if pi:
        outcome = "pair_instability_disrupted"
        remnant = 0.0
        notes = "trad PI window — no direct BH (comparison)"
    elif outcome == "direct_black_hole":
        notes = f"core ε≥½; fallback channel up to {fallback:.1f} M☉"
    elif outcome == "neutron_star":
        notes = "core below γ/2 ceiling"

    return StellarCollapseRow(
        zams_mass_msun=zams_mass_msun,
        iron_core_mass_msun=core,
        outcome_uniform=outcome,
        remnant_uniform_msun=remnant,
        epsilon_surface=float(uni["epsilon_surface"]),
        compactness_rs_over_r=float(uni["compactness_rs_over_r"]),
        horizon_at_core_radius_msun=m_horizon_r,
        fallback_bh_mass_msun=fallback,
        trad_pair_instability=pi,
        notes=notes,
    )


def hqiv_geometry_ceilings() -> dict[str, object]:
    grad = gradient_collapse_hypothesis()
    tail = grad["mass_tail_msun"]
    m_horizon_uniform = mass_from_epsilon_crit(EPS_HORIZON, RHO_NUCLEAR_KG_M3) / M_SUN_KG
    m_ns_max = mass_from_epsilon_crit(C_RINDLER_SHARED, RHO_NUCLEAR_KG_M3) / M_SUN_KG
    return {
        "neutron_star_max_msun": m_ns_max,
        "epsilon_ns_max": C_RINDLER_SHARED,
        "direct_bh_uniform_sphere_msun": m_horizon_uniform,
        "epsilon_horizon": EPS_HORIZON,
        "direct_bh_at_ns_radius_msun": tail["horizon_at_same_R"],
        "charmed_tail_at_ns_radius_msun": tail["charmed_core_at_same_R"],
        "top_seed_at_ns_radius_msun": tail["top_seed_at_same_R"],
        "gradient_collapse_tail": tail,
        "tipping_thresholds": grad["tipping_thresholds"],
        "interpretation": (
            "Uniform nuclear sphere: one mass at ε=γ/2 (NS max) and one at ε=½ (Schwarzschild). "
            "Gradient-collapse at fixed NS radius gives a lower direct-BH threshold (~5 M☉) "
            "before envelope fallback."
        ),
    }


def scan_direct_bh_ceiling(rows: list[StellarCollapseRow]) -> dict[str, object]:
    below_pi = [r for r in rows if not r.trad_pair_instability]
    direct = [r for r in below_pi if r.outcome_uniform == "direct_black_hole"]
    fallback_max_below_pi = max((r.fallback_bh_mass_msun for r in below_pi), default=0.0)
    uniform_direct_max_below_pi = max((r.remnant_uniform_msun for r in direct), default=0.0)
    zams_at_ns_max = None
    zams_at_horizon = None
    zams_fallback_near_45 = None
    for z in range(8, 200):
        r = stellar_collapse_row(float(z))
        if zams_at_ns_max is None and r.epsilon_surface >= C_RINDLER_SHARED:
            zams_at_ns_max = float(z)
        if zams_at_horizon is None and r.epsilon_surface >= EPS_HORIZON:
            zams_at_horizon = float(z)
        if (
            zams_fallback_near_45 is None
            and not r.trad_pair_instability
            and r.fallback_bh_mass_msun >= LITERATURE_DIRECT_BH_CEILING_MSUN - 2.0
        ):
            zams_fallback_near_45 = float(z)
    ceil = hqiv_geometry_ceilings()

    return {
        "hqiv_threshold_uniform_horizon_msun": ceil["direct_bh_uniform_sphere_msun"],
        "hqiv_threshold_horizon_at_ns_radius_msun": ceil["direct_bh_at_ns_radius_msun"],
        "hqiv_neutron_star_max_msun": ceil["neutron_star_max_msun"],
        "max_uniform_direct_bh_below_pi_msun": uniform_direct_max_below_pi,
        "max_fallback_bh_below_pi_msun": fallback_max_below_pi,
        "zams_first_epsilon_ge_ns_max": zams_at_ns_max,
        "zams_first_epsilon_ge_horizon": zams_at_horizon,
        "zams_fallback_reaches_literature_ceiling": zams_fallback_near_45,
        "literature_direct_bh_ceiling_msun": LITERATURE_DIRECT_BH_CEILING_MSUN,
        "same_epsilon_ceilings_as_compact_object": True,
        "verdict": (
            "Same ε slots as compact-object witness: NS max ~1.98 M☉ (ε=γ/2), "
            f"Schwarzschild threshold ~{ceil['direct_bh_uniform_sphere_msun']:.1f} M☉ for uniform "
            f"nuclear sphere, gradient-tail threshold ~{ceil['direct_bh_at_ns_radius_msun']:.1f} M☉ "
            "at fixed NS radius. Stellar cores above the threshold form direct BHs with "
            "M_rem = M_core (no HQIV cap below pair instability). Trad fallback channel "
            f"reaches ~{LITERATURE_DIRECT_BH_CEILING_MSUN:.0f} M☉ near ZAMS "
            f"{zams_fallback_near_45 or '—'} — comparable to population-synthesis ceiling."
        ),
    }


def stellar_collapse_witness(
    zams_grid: list[float] | None = None,
) -> dict[str, object]:
    if zams_grid is None:
        zams_grid = [
            8, 10, 12, 15, 18, 20, 25, 30, 35, 40, 45, 50, 60, 70, 80,
            100, 120, 140, 160, 200, 260, 300,
        ]
    rows = [stellar_collapse_row(z) for z in zams_grid]
    ceilings = hqiv_geometry_ceilings()
    scan = scan_direct_bh_ceiling(rows)
    return {
        "lean_modules": [
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.GlobalDetuning",
            "Hqiv.Physics.HepDecayReadout",
            "Hqiv.Physics.GravitationalWaveRingdownScaffold",
        ],
        "python_modules": [
            "hqiv_compact_object_mass",
            "hqiv_stellar_collapse",
        ],
        "lattice_constants": {
            "alpha": 0.6,
            "gamma": GAMMA,
            "c_rindler_shared": C_RINDLER_SHARED,
            "epsilon_charm_tip": EPS_CHARM_TIP,
            "epsilon_top_tip_center": EPS_TOP_TIP,
            "epsilon_horizon": EPS_HORIZON,
        },
        "hqiv_geometry_ceilings": ceilings,
        "iron_core_prescription": {
            "formula": "M_Fe ≈ 0.08 (M_ZAMS − 5)^{1.55} for M_ZAMS ≥ 8",
            "role": "comparison scaffold — not an HQIV axiom",
        },
        "trad_comparison": {
            "pair_instability_zams_window_msun": [
                PAIR_INSTABILITY_ZAMS_LO_MSUN,
                PAIR_INSTABILITY_ZAMS_HI_MSUN,
            ],
            "literature_direct_bh_ceiling_msun": LITERATURE_DIRECT_BH_CEILING_MSUN,
            "fallback_formula": "failed-SN fraction of ZAMS (schematic)",
        },
        "direct_bh_ceiling_scan": scan,
        "rows": [asdict(r) for r in rows],
    }


def print_report(data: dict[str, object]) -> None:
    ceil = data["hqiv_geometry_ceilings"]
    scan = data["direct_bh_ceiling_scan"]
    print("HQIV stellar collapse → compact-object ε ceilings")
    print(f"  NS max (ε=γ/2):     {ceil['neutron_star_max_msun']:.2f} M☉")
    print(f"  Direct BH (ε=½):    {ceil['direct_bh_uniform_sphere_msun']:.2f} M☉ (uniform sphere)")
    print(f"  Direct BH @ NS R:   {ceil['direct_bh_at_ns_radius_msun']:.2f} M☉ (gradient tail)")
    print()
    print("ZAMS scan (iron core → ε outcome):")
    print(
        f"  {'ZAMS':>6} {'M_core':>7} {'ε_s':>6} {'Rs/R':>6} "
        f"{'outcome':<28} {'M_rem':>6} {'M_fb':>6}"
    )
    for row in data["rows"]:
        if row["zams_mass_msun"] < 8:
            continue
        print(
            f"  {row['zams_mass_msun']:6.0f} "
            f"{row['iron_core_mass_msun']:7.2f} "
            f"{row['epsilon_surface']:6.3f} "
            f"{row['compactness_rs_over_r']:6.3f} "
            f"{row['outcome_uniform']:<28} "
            f"{row['remnant_uniform_msun']:6.2f} "
            f"{row['fallback_bh_mass_msun']:6.1f}"
        )
    print()
    print("Thresholds vs stellar scan:")
    print(
        f"  ε=γ/2 NS max:       {scan['hqiv_neutron_star_max_msun']:.2f} M☉ "
        f"(ZAMS≥{scan['zams_first_epsilon_ge_ns_max']} crosses)"
    )
    print(
        f"  ε=½ uniform sphere: {scan['hqiv_threshold_uniform_horizon_msun']:.2f} M☉ "
        f"(ZAMS≥{scan['zams_first_epsilon_ge_horizon']} core crosses)"
    )
    print(
        f"  ε=½ at NS radius:   {scan['hqiv_threshold_horizon_at_ns_radius_msun']:.2f} M☉ "
        "(gradient-collapse witness)"
    )
    print(
        f"  Max core-BH < PI:   {scan['max_uniform_direct_bh_below_pi_msun']:.1f} M☉ "
        f"(fallback max {scan['max_fallback_bh_below_pi_msun']:.1f} M☉)"
    )
    print(
        f"  Fallback ~45 M☉:    ZAMS {scan['zams_fallback_reaches_literature_ceiling']} "
        f"(lit. band ~{scan['literature_direct_bh_ceiling_msun']:.0f} M☉)"
    )
    print()
    print(scan["verdict"])


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV stellar collapse ε-ceiling witness")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    data = stellar_collapse_witness()
    if args.json:
        out = _ROOT / "data" / "stellar_collapse_witness.json"
        out.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out}", file=sys.stderr)
    else:
        print_report(data)


if __name__ == "__main__":
    main()
