#!/usr/bin/env python3
"""Report how much HQIV closes Anderson-style Earth flyby anomalies."""

from __future__ import annotations

from dataclasses import replace

import hqiv_orbital_flyby_omaxwell as orb


MISSION_KEYS = ("near_1998", "galileo_1990", "cassini_1999", "rosetta_2005")


def print_gap_table(coupling: orb.HQIVOrbitCoupling, label: str, *, include_third_body_delta: bool = False) -> None:
    print(f"\n{label}")
    print(
        f"{'case':<16} {'lit mm/s':>9} {'HQIV-GR':>10} {'% lit':>8} "
        f"{'3body':>10} {'annual':>8} {'gal':>9} {'lat in':>8} {'lat out':>8} {'mean f':>11}"
    )
    print("-" * 110)
    for key in MISSION_KEYS:
        case = orb.FLYBY_CATALOG[key]
        settings = orb.propagation_settings_for(orb.EARTH, case)
        row = orb.compare_classical_vs_hqiv(case, orb.EARTH, coupling, settings)
        lit = float(case.reported_anomaly_mm_s or 0.0)
        excess = float(row["hqiv_minus_classical_mm_s"])
        third_body_shift = float("nan")
        if include_third_body_delta:
            settings_no3 = replace(settings, use_third_bodies=False)
            row_no3 = orb.compare_classical_vs_hqiv(case, orb.EARTH, coupling, settings_no3)
            third_body_shift = excess - float(row_no3["hqiv_minus_classical_mm_s"])
        pct = 100.0 * excess / lit if lit else float("nan")
        classical = row["classical"]
        hqiv = row["hqiv"]
        annual = orb.annual_frame_projection(
            orb.flyby_initial_state(case, orb.EARTH).r,
            orb.flyby_initial_state(case, orb.EARTH).v,
            case.encounter_date,
        )
        gal = orb.galactic_disk_lapse_fraction(case.encounter_date)
        print(
            f"{key:<16} {lit:9.2f} {excess:10.4f} {pct:8.1f} "
            f"{third_body_shift:10.4f} "
            f"{annual:8.3f} {gal:9.2e} "
            f"{float(classical['asymptote_lat_in_deg']):8.2f} "
            f"{float(classical['asymptote_lat_out_deg']):8.2f} "
            f"{float(hqiv['mean_f_blend']):11.9f}"
        )


def main() -> None:
    nominal = orb.paper_nominal_coupling()
    legacy = orb.paper_legacy_coupling()
    print(
        "Galactic disk term: "
        f"support={orb.galactic_disk_support_fraction():.3f}, "
        f"RindlerDen={orb.galactic_rindler_denominator():.3e}"
    )
    print_gap_table(
        nominal,
        "Nominal: derived λ=γ sin²θ ρ_pol + G_eff time factor",
        include_third_body_delta=True,
    )
    print_gap_table(
        replace(nominal, lapse_drag_vector_fraction=0.5),
        "Sensitivity: fixed λ=0.5 (old knob)",
    )
    print_gap_table(
        replace(nominal, lapse_drag_lense_thirring=False),
        "Ablation: drop L-T 3-vector (isotropic only, latitude-weighted ε)",
    )
    print_gap_table(
        replace(nominal, lapse_drag_colatitude=False, lapse_drag_lense_thirring=False),
        "Ablation: drop colatitude weight AND L-T",
    )
    print_gap_table(
        legacy,
        "Legacy: scalar ε in φ_eff, G_eff on GM source",
    )
    print_gap_table(replace(nominal, galactic_disk_lapse_phi=False), "Ablation: no galactic disk Rindler lapse")
    print_gap_table(replace(nominal, lapse_drag_phi=False), "Ablation: no co-spin lapse φ")
    print_gap_table(replace(nominal, modified_inertia_geodesic=False), "Ablation: no a_GR/f geodesic")


if __name__ == "__main__":
    main()
