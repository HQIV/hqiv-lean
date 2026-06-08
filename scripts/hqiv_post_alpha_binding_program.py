#!/usr/bin/env python3
"""
Post-α binding energy program (A > 4): geometry, MeV bridge, legacy comparison.

Derives binding from HQIV sphere-touch ledger + composite-trace coupling — no PDG mass
injection.  Experimental binding energies appear only in the comparison table.

Lean: `Hqiv.Physics.PostAlphaBindingGeometry`, `HQIVNuclei` sphere-touch energies.

Run:
  python3 scripts/hqiv_post_alpha_binding_program.py
  python3 scripts/hqiv_post_alpha_binding_program.py --json data/post_alpha_binding_program.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes
import hqiv_post_alpha_sphere_touching as touch

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "post_alpha_binding_program.json"
M_P = 938.272
M_SHELL = hes.REFERENCE_M

# Experimental total binding (MeV) — comparison layer only (AME-style rounded values).
PDG_BINDING_MEV: dict[tuple[int, int], float] = {
    (2, 1): 2.2246,
    (3, 1): 8.4818,
    (3, 2): 7.7180,
    (4, 2): 28.2957,
    (5, 3): 26.33,
    (5, 4): 25.0,
    (6, 3): 31.9946,
    (7, 3): 39.2446,
    (7, 4): 37.6006,
    (8, 4): 56.4995,
    (9, 4): 58.1649,
    (12, 6): 92.1617,
    (16, 8): 127.6193,
}


def sphere_touch_contact_energy_unit_mev(m: int) -> float:
    """Lean `sphereTouchContactEnergyUnit m = R_m²`; R_m = m+1 at shell m."""
    r = float(m + 1)
    return r * r


def geometry_to_mev_coupling(m: int, c: float = 1.0) -> float:
    """Lean `geometryToMeVCoupling`: trace binding per contact unit."""
    trace = hes.e_bind_from_nucleon_trace_mev(m, c)
    unit = sphere_touch_contact_energy_unit_mev(m)
    return trace / unit if unit > 0 else 0.0


def post_alpha_geometric_touch_energy(m: int, A: int, Z: int) -> float:
    """Lean `postAlphaGeometricTouchEnergy` (effective valleys × R_m²)."""
    if A <= 4:
        return 0.0
    unit = sphere_touch_contact_energy_unit_mev(m)
    eff = touch.post_alpha_outside_valley_count_effective(A, Z)
    spin = touch.spin_stability_participation(A, Z)
    # When spin gates facet chart off, only cap + far count (geometry file uses spin on facets).
    p_sum = touch.proton_facet_touch_contact_sum(touch.bbn_proton_facet_touches(A, Z))
    cap = float(touch.CONSTRUCTIVE_VALLEY_CAP)
    far = touch.far_neutron_weighted_contact_sum(A, Z)
    return (cap + spin * float(p_sum) + far) * unit


def post_alpha_cluster_binding_geometry_mev(m: int, A: int, Z: int, c: float = 1.0) -> float:
    """Lean `postAlphaClusterBindingFromGeometry`."""
    return post_alpha_geometric_touch_energy(m, A, Z) * geometry_to_mev_coupling(m, c)


def post_alpha_incremental_contact_count(A: int, Z: int) -> float:
    if A <= 4:
        return 0.0
    return touch.post_alpha_outside_valley_count_effective(A, Z) - float(
        touch.CONSTRUCTIVE_VALLEY_CAP
    )


def post_alpha_core_well_deepening(A: int, Z: int) -> float:
    """Extra contacts deepen the α wells they touch."""
    if A <= 4:
        return 1.0
    inc = post_alpha_incremental_contact_count(A, Z)
    return 1.0 + bbn.STRONG_CHANNEL_FRACTION * inc / float(touch.CONSTRUCTIVE_VALLEY_CAP)


def proton_facet_partial_contact_sum(A: int, Z: int) -> int:
    return sum(
        t.contact_count
        for t in touch.bbn_proton_facet_touches(A, Z)
        if t.contact_count < touch.PROTON_FACET_VERTEX_CONTACTS
    )


def post_alpha_light_contact_fraction(A: int, Z: int) -> float:
    """Partial facets + far neutrons = lighter additions."""
    if A <= 4:
        return 0.0
    facet = float(touch.proton_facet_touch_contact_sum(touch.bbn_proton_facet_touches(A, Z)))
    partial = float(proton_facet_partial_contact_sum(A, Z))
    far = touch.far_neutron_weighted_contact_sum(A, Z)
    total = facet + far
    return (partial + far) / total if total > 0 else 0.0


def post_alpha_alpha_core_geometric_energy(m: int, A: int, Z: int) -> float:
    if A <= 4:
        return 0.0
    return float(touch.CONSTRUCTIVE_VALLEY_CAP) * sphere_touch_contact_energy_unit_mev(m)


def post_alpha_network_binding_mev(m: int, A: int, Z: int, c: float = 1.0) -> float:
    """Deepened core wells interact on the contact graph (γ)."""
    if A <= 4:
        return 0.0
    deepening = post_alpha_core_well_deepening(A, Z)
    return (
        bbn.GAMMA_HQIV
        * (deepening - 1.0)
        * post_alpha_alpha_core_geometric_energy(m, A, Z)
        * geometry_to_mev_coupling(m, c)
    )


def post_alpha_well_relaxation_mev(m: int, A: int, Z: int, c: float = 1.0) -> float:
    """Lighter extras let the collective well relax — small BE/A loss."""
    if A <= 4:
        return 0.0
    trace = hes.e_bind_from_nucleon_trace_mev(m, c)
    return (
        float(A - 4)
        * post_alpha_light_contact_fraction(A, Z)
        * bbn.STRONG_CHANNEL_FRACTION
        * bbn.GAMMA_HQIV
        * trace
    )


def post_alpha_cluster_binding_with_network_mev(
    m: int, A: int, Z: int, c: float = 1.0
) -> float:
    """Lean `postAlphaClusterBindingWithNetwork`."""
    if A <= 4:
        return ladder_cluster_binding_mev(A, Z, c)
    base = post_alpha_cluster_binding_geometry_mev(m, A, Z, c)
    return (
        base * post_alpha_core_well_deepening(A, Z)
        + post_alpha_network_binding_mev(m, A, Z, c)
        - post_alpha_well_relaxation_mev(m, A, Z, c)
    )


def binding_per_nucleon_mev(binding_mev: float, A: int) -> float:
    return binding_mev / float(A) if A > 0 else 0.0


def post_alpha_cluster_binding_pre_relax_mev(
    m: int, A: int, Z: int, c: float = 1.0
) -> float:
    """Deepening + network, before well relaxation (Lean `postAlphaBindingPerNucleonPreRelax` numerator)."""
    if A <= 4:
        return 0.0
    base = post_alpha_cluster_binding_geometry_mev(m, A, Z, c)
    return (
        base * post_alpha_core_well_deepening(A, Z)
        + post_alpha_network_binding_mev(m, A, Z, c)
    )


def post_alpha_cluster_binding_legacy_mev(A: int, Z: int, c: float = 1.0) -> float:
    """Lean `postAlphaClusterBindingLegacyNormalized` / `bbnClusterBinding` for A > 4."""
    return float(A) * hes.e_bind_from_nucleon_trace_mev(M_SHELL, c) * bbn.valley_binding_factor(A, Z)


def ladder_cluster_binding_mev(A: int, Z: int = 0, c: float = 1.0) -> float:
    """Full `bbn.cluster_binding_mev` (A≤4 valley ladder + post-α factor)."""
    return bbn.cluster_binding_mev(M_SHELL, A, c, Z=Z)


@dataclass(frozen=True)
class BindingRow:
    label: str
    A: int
    Z: int
    effective_valleys: float
    geometric_touch_energy_R2_units: float
    geometry_to_mev_coupling: float
    binding_geometry_mev: float
    core_well_deepening: float
    network_binding_mev: float
    well_relaxation_mev: float
    binding_with_network_mev: float
    be_per_A_geometry: float
    be_per_A_network: float
    binding_legacy_A_times_factor_mev: float
    binding_bbn_cluster_mev: float
    pdg_binding_mev: float | None
    pdg_be_per_A: float | None
    ratio_geometry_over_pdg: float | None
    ratio_network_over_pdg: float | None
    ratio_legacy_over_pdg: float | None
    ratio_geometry_over_legacy: float | None
    notes: str


def build_rows(
    nuclei: list[tuple[int, int, str]],
    *,
    m_shell: int = M_SHELL,
    c: float = 1.0,
) -> list[BindingRow]:
    coupling = geometry_to_mev_coupling(m_shell, c)
    trace = hes.e_bind_from_nucleon_trace_mev(m_shell, c)
    rows: list[BindingRow] = []
    for A, Z, label in nuclei:
        eff = (
            touch.post_alpha_outside_valley_count_effective(A, Z)
            if A > 4
            else float(bbn.valley_count(A, Z))
        )
        geom_e = post_alpha_geometric_touch_energy(m_shell, A, Z)
        bind_geom = post_alpha_cluster_binding_geometry_mev(m_shell, A, Z, c)
        deepening = post_alpha_core_well_deepening(A, Z)
        net_bind = post_alpha_network_binding_mev(m_shell, A, Z, c)
        relax = post_alpha_well_relaxation_mev(m_shell, A, Z, c)
        bind_net = post_alpha_cluster_binding_with_network_mev(m_shell, A, Z, c)
        bind_legacy = post_alpha_cluster_binding_legacy_mev(A, Z, c) if A > 4 else ladder_cluster_binding_mev(A, Z, c)
        bind_bbn = ladder_cluster_binding_mev(A, Z, c)
        pdg = PDG_BINDING_MEV.get((A, Z))
        pdg_be_a = (pdg / A) if pdg and A > 0 else None
        notes = []
        if A <= 4:
            notes.append("A≤4: caustic ladder; network row N/A.")
        if A > 4:
            notes.append(
                f"deepen={deepening:.4f} net=+{net_bind:.3f} relax=-{relax:.3f} light_frac={post_alpha_light_contact_fraction(A, Z):.2f}"
            )
        rows.append(
            BindingRow(
                label=label,
                A=A,
                Z=Z,
                effective_valleys=eff,
                geometric_touch_energy_R2_units=geom_e / sphere_touch_contact_energy_unit_mev(m_shell)
                if A > 4
                else eff,
                geometry_to_mev_coupling=coupling,
                binding_geometry_mev=bind_geom,
                core_well_deepening=deepening,
                network_binding_mev=net_bind,
                well_relaxation_mev=relax,
                binding_with_network_mev=bind_net,
                be_per_A_geometry=binding_per_nucleon_mev(bind_geom, A),
                be_per_A_network=binding_per_nucleon_mev(bind_net, A),
                binding_legacy_A_times_factor_mev=bind_legacy,
                binding_bbn_cluster_mev=bind_bbn,
                pdg_binding_mev=pdg,
                pdg_be_per_A=pdg_be_a,
                ratio_geometry_over_pdg=(bind_geom / pdg if pdg and pdg > 0 else None),
                ratio_network_over_pdg=(bind_net / pdg if pdg and pdg > 0 else None),
                ratio_legacy_over_pdg=(bind_legacy / pdg if pdg and pdg > 0 else None),
                ratio_geometry_over_legacy=(
                    bind_geom / bind_legacy if bind_legacy > 0 else None
                ),
                notes=" ".join(notes),
            )
        )
    rows.append(
        BindingRow(
            label="(calibration)",
            A=0,
            Z=0,
            effective_valleys=0.0,
            geometric_touch_energy_R2_units=0.0,
            geometry_to_mev_coupling=coupling,
            binding_geometry_mev=trace,
            core_well_deepening=1.0,
            network_binding_mev=0.0,
            well_relaxation_mev=0.0,
            binding_with_network_mev=trace,
            be_per_A_geometry=0.0,
            be_per_A_network=0.0,
            binding_legacy_A_times_factor_mev=trace,
            binding_bbn_cluster_mev=trace,
            pdg_binding_mev=None,
            pdg_be_per_A=None,
            ratio_geometry_over_pdg=None,
            ratio_network_over_pdg=None,
            ratio_legacy_over_pdg=None,
            ratio_geometry_over_legacy=1.0,
            notes=f"nucleon trace at m={m_shell}: {trace:.4f} MeV; unit R_m²={sphere_touch_contact_energy_unit_mev(m_shell):.1f}",
        )
    )
    return rows


def program_summary(rows: list[BindingRow]) -> dict:
    be7 = next((r for r in rows if r.A == 7 and r.Z == 4), None)
    li7 = next((r for r in rows if r.A == 7 and r.Z == 3), None)
    he4 = next((r for r in rows if r.A == 4 and r.Z == 2), None)
    return {
        "policy": "PDG binding energies are comparison-only; not fitted into HQIV.",
        "binding_shell_m": M_SHELL,
        "proton_anchor_MeV": M_P,
        "network_mechanism": (
            "Extra A lowers energy of touched α sites (deepening); deepened wells interact (γ network); "
            "lighter partial/far additions relax the well → slightly lower BE/A vs pre-relax BE/A "
            "(deepening still raises binding vs bare geometry)."
        ),
        "open_problems": [
            "Double-counting: α caustic core vs incremental facet contacts.",
            "Calibrate deepening/network/relaxation to absolute PDG B without fits.",
            "Map network binding to reaction Q (formation/capture) without separate barriers.",
        ],
        "seven_be_vs_seven_li": {
            "geometry_ordering_ok": (
                be7 is not None
                and li7 is not None
                and be7.binding_geometry_mev > li7.binding_geometry_mev
            ),
            "network_ordering_ok": (
                be7 is not None
                and li7 is not None
                and be7.binding_with_network_mev > li7.binding_with_network_mev
            ),
            "legacy_ordering_ok": (
                be7 is not None
                and li7 is not None
                and be7.binding_legacy_A_times_factor_mev > li7.binding_legacy_A_times_factor_mev
            ),
            "Q_capture_network_MeV": (
                bbn.be7_to_li7_capture_q(
                    be7.binding_with_network_mev, li7.binding_with_network_mev
                )
                if be7 and li7
                else None
            ),
        },
        "he4_reference": {
            "bbn_cluster_binding_MeV": he4.binding_bbn_cluster_mev if he4 else None,
            "pdg_binding_MeV": he4.pdg_binding_mev if he4 else None,
        },
        "integrator_status": (
            "BBN Li/Be integrator still uses bbn.cluster_binding_mev (legacy); "
            "witness path bbnClusterBindingFromCausticGeometry uses postAlphaClusterBindingWithNetwork."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, default=None, help="Write witness JSON")
    args = parser.parse_args()

    nuclei = [
        (2, 1, "²H"),
        (3, 2, "³He"),
        (4, 2, "⁴He"),
        (5, 3, "⁵Li"),
        (5, 4, "⁵Be"),
        (6, 3, "⁶Li"),
        (7, 3, "⁷Li"),
        (7, 4, "⁷Be"),
        (8, 4, "⁸Be"),
        (12, 6, "¹²C"),
        (16, 8, "¹⁶O"),
    ]
    rows = build_rows(nuclei)
    summary = program_summary(rows)
    payload = {
        "source": "scripts/hqiv_post_alpha_binding_program.py",
        "summary": summary,
        "rows": [asdict(r) for r in rows],
    }

    print("HQIV post-α binding program (A > 4)")
    print("=" * 60)
    print(f"Shell m={M_SHELL}  trace={rows[-1].binding_geometry_mev:.4f} MeV  coupling={rows[-1].geometry_to_mev_coupling:.6f} MeV/R²")
    print()
    print(
        f"{'Nucl':<6} {'effV':>5} {'netB':>7} {'BE/A_g':>7} {'BE/A_n':>7} {'PDG/A':>7} {'relax':>6}"
    )
    for r in rows[:-1]:
        pdg_a = f"{r.pdg_be_per_A:7.2f}" if r.pdg_be_per_A else "      —"
        print(
            f"{r.label:<6} {r.effective_valleys:5.1f} {r.binding_with_network_mev:7.2f} "
            f"{r.be_per_A_geometry:7.3f} {r.be_per_A_network:7.3f} {pdg_a} {r.well_relaxation_mev:6.3f}"
        )
    print()
    print("Open problems:")
    for item in summary["open_problems"]:
        print(f"  • {item}")
    print()
    print(summary["integrator_status"])

    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"\nWrote {args.json}")


if __name__ == "__main__":
    main()
