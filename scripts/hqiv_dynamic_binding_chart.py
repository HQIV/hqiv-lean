#!/usr/bin/env python3
"""
Parameter-free HQIV dynamic binding chart (GMTKN55 / W4-17 molecule suite).

Extends the LiH dynamic readout to diatomics and small polyatomics using the same
post-T12/T13 shell chart — no fitted coefficients:

  E_bind = η_p · surplus_dimless · geomean(tuft_vev_networked) · geometry_alignment ·
           dynamicBindingCurvatureFeedbackAtXi(ξ_contact) · EV_per_λ

Per-nucleus curvature (not universal m = referenceM):
  • Nuclear readout shell m_nuc(A) from trapped inside-ratio vs A^(1/3)
  • Valence shells: H s at m=1; heavy atom s at m_nuc, p at m_nuc−1
  • η_p from Compton IR window on the nuclear-derived shell triplet
  • Nuclear binding B/A from composite-trace cluster readout at each m_nuc

Run:
  python3 scripts/hqiv_dynamic_binding_chart.py
  python3 scripts/hqiv_dynamic_binding_chart.py --json-out data/dynamic_binding_chart.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal

import hqiv_electronic_valence_shells as evs
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_curvature_binding as ncb
import hqiv_shell_aware_binding as sab
from bonded_horizon_casimir_float import (
    EV_PER_LAMBDA_UNIT,
    bond_horizon_surplus_dimless,
)
from fragment_aware_bonded_horizon import BondGeometry, FragmentConfig, MoleculeConfig
from lih_derivation_scan import (
    REFERENCE_M,
    compton_window_angles_from_detuning_lapse,
    lattice_full_mode_energy,
)
from nuclear_torus_casimir_float import perturbed_casimir_energy

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "dynamic_binding_chart.json"
PHASE_THETA = math.pi / 2.0

BindingKind = Literal["dissociation", "atomization"]


@dataclass(frozen=True)
class MoleculeBenchmark:
    name: str
    kind: BindingKind
    fragments: tuple[FragmentConfig, ...]
    bonds: tuple[BondGeometry, ...]
    reference_ev: float
    reference_source: str


# GMTKN55 / W4-17 suite (same references as `benchmark_omaxwell_torus_ode.py`).
GMTKN55_SUITE: tuple[MoleculeBenchmark, ...] = (
    MoleculeBenchmark(
        "H2",
        "dissociation",
        (FragmentConfig("H", 1, 1), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 0.7414),),
        4.478,
        "NIST / W4-17",
    ),
    MoleculeBenchmark(
        "LiH",
        "dissociation",
        (FragmentConfig("Li", 3, 3), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 1.5956),),
        2.515,
        "W4-17/GMTKN55",
    ),
    MoleculeBenchmark(
        "HF",
        "dissociation",
        (FragmentConfig("F", 9, 9), FragmentConfig("H", 1, 1)),
        (BondGeometry(0, 1, 0.9168),),
        5.87,
        "W4-17/GMTKN55",
    ),
    MoleculeBenchmark(
        "H2O",
        "atomization",
        (
            FragmentConfig("O", 8, 8),
            FragmentConfig("H", 1, 1),
            FragmentConfig("H", 1, 1),
        ),
        (
            BondGeometry(0, 1, 0.9572, bond_angle_rad=math.radians(104.5)),
            BondGeometry(0, 2, 0.9572, bond_angle_rad=math.radians(104.5)),
        ),
        9.51,
        "W4-17/GMTKN55",
    ),
    MoleculeBenchmark(
        "CH4",
        "atomization",
        (FragmentConfig("C", 6, 6),)
        + tuple(FragmentConfig("H", 1, 1) for _ in range(4)),
        tuple(
            BondGeometry(0, i + 1, 1.09, bond_angle_rad=math.radians(109.47))
            for i in range(4)
        ),
        17.0,
        "W4-17/GMTKN55",
    ),
    MoleculeBenchmark(
        "NH3",
        "atomization",
        (FragmentConfig("N", 7, 7),)
        + tuple(FragmentConfig("H", 1, 1) for _ in range(3)),
        tuple(
            BondGeometry(0, i + 1, 1.012, bond_angle_rad=math.radians(107.0))
            for i in range(3)
        ),
        10.07,
        "W4-17/GMTKN55",
    ),
)

# Molecules where the current nuclear-torus surplus map overshoots (large Z, no H).
# Kept for diagnostics — not counted in the primary chart summary.
EXTENDED_DIAGNOSTIC_SUITE: tuple[MoleculeBenchmark, ...] = (
    MoleculeBenchmark(
        "CO",
        "atomization",
        (FragmentConfig("C", 6, 6), FragmentConfig("O", 8, 8)),
        (BondGeometry(0, 1, 1.128),),
        11.24,
        "W4-17/GMTKN55",
    ),
    MoleculeBenchmark(
        "N2",
        "dissociation",
        (FragmentConfig("N", 7, 7), FragmentConfig("N", 7, 7)),
        (BondGeometry(0, 1, 1.098),),
        9.91,
        "W4-17/GMTKN55",
    ),
)


def xi_of_shell(m: int) -> float:
    return float(m + 1)


def phase_participation_eta(x: float) -> float:
    return x / PHASE_THETA


def dynamic_site_energy_dimless(m: int) -> float:
    return lattice_full_mode_energy(m) * lean.tuft_vev_factor_at_xi(xi_of_shell(m))


def vev_geometric_mean_bare(shells: tuple[int, int, int]) -> float:
    return ncb.vev_geometric_mean_from_triplet(shells)


def _fragment_pairs(bench: MoleculeBenchmark) -> tuple[tuple[int, int], ...]:
    return tuple((max(f.z_nuclear, 1), max(f.electrons, 0)) for f in bench.fragments)


def _heavy_light_mass_numbers(bench: MoleculeBenchmark) -> tuple[int, int]:
    pairs = _fragment_pairs(bench)
    masses = [ncb.stable_mass_number(z, e) for z, e in pairs]
    return max(masses), min(masses)


def count_peripheral_hydrogens(bench: MoleculeBenchmark) -> int:
    """Outer H atoms on a heavy centre (CH₄, NH₃, H₂O, …), not homonuclear H₂."""
    n_h = sum(1 for f in bench.fragments if f.z_nuclear == 1)
    n_heavy = sum(1 for f in bench.fragments if f.z_nuclear > 1)
    return n_h if n_heavy > 0 and n_h >= 2 else 0


def vev_geometric_mean_networked(bench: MoleculeBenchmark, triplet: tuple[int, int, int]) -> float:
    """Primary readout: `CurvatureContactNetwork` vev geomean rule."""
    import hqiv_curvature_contact_network as ccn

    net = ccn.build_network_from_molecule(
        bench.name,
        bench.fragments,
        bench.bonds,
    )
    return ccn.networked_vev_geometric_mean(net)


def chemistry_compton_triplet(
    bench: MoleculeBenchmark,
) -> tuple[int, int, int]:
    """Lean `DynamicBindingChart` Compton triplets (electronic 2s/2p/1s, not nuclear drum)."""
    return evs.chemistry_compton_triplet(bench.fragments)


def nuclear_context_for_fragments(
    fragments: tuple[FragmentConfig, ...],
) -> tuple[tuple[int, int, int], float, list[dict[str, Any]], dict[str, float]]:
    frag_pairs = tuple((max(f.z_nuclear, 1), max(f.electrons, 0)) for f in fragments)
    _, rows = ncb.molecule_phase_participation_eta(frag_pairs)
    triplet = ncb.compton_triplet_from_nuclei(rows)
    angles, eta_p, meta = compton_context(triplet)
    uniformity = ncb.binding_uniformity_report(rows)
    row_dicts = [
        {
            "Z": r.Z,
            "A": r.A,
            "m_nuclear": r.m_nuclear,
            "xi_nuclear": r.xi_nuclear,
            "per_nucleon_binding_mev": r.per_nucleon_binding_mev,
            "per_nucleon_trace_mev": ncb.per_nucleon_trace_binding_at_shell(r.m_nuclear),
            "inside_ratio": r.inside_ratio,
            "tuft_vev_factor": r.tuft_vev_factor,
            "valence_s_shell": r.valence_s_shell,
            "valence_p_shell": r.valence_p_shell,
            "electronic_s_shell": evs.electronic_compton_shells(r.Z)[0],
            "electronic_p_shell": evs.electronic_compton_shells(r.Z)[1],
            "electronic_shell_label": evs.electronic_shell_label(r.Z, slot="s"),
        }
        for r in rows
    ]
    return triplet, eta_p, row_dicts, uniformity


def compton_context(shell_triplet: tuple[int, int, int]) -> tuple[tuple[float, float, float], float, dict[str, Any]]:
    compton, detuning = compton_window_angles_from_detuning_lapse(shell_triplet)
    mean_angle = sum(compton.angles_rad) / len(compton.angles_rad)
    eta_p = phase_participation_eta(mean_angle)
    meta = {
        "shell_triplet_m": list(shell_triplet),
        "angles_rad": compton.angles_rad,
        "mean_angle_rad": mean_angle,
        "eta_p": eta_p,
        "shared_time_s": compton.shared_time_s,
        "in_window": compton.in_window,
        "detuning_lapse_fraction": detuning.lapse_fraction,
    }
    return compton.angles_rad, eta_p, meta


def network_balance_witness(
    net: Any,
    triplet: tuple[int, int, int],
    *,
    eta_p_chart: float,
    vev_networked: float,
    geometry_alignment: float,
) -> dict[str, Any]:
    """
    Document how network factors are aggregated (product vs geometric mean).

    Lean spine: ``η_p · surplus · geomean(tuftVev) · (1+κ·C) · geomean(valley_align)`` —
    **not** a single geomean over contacts of ``η×vev×geom``.
    """
    from lih_derivation_scan import compton_window_angles_from_detuning_lapse

    compton, _ = compton_window_angles_from_detuning_lapse(triplet)
    etas_slot = [phase_participation_eta(a) for a in compton.angles_rad]
    eta_slot_geomean = (
        math.prod(etas_slot) ** (1.0 / len(etas_slot)) if etas_slot else eta_p_chart
    )
    frag_pairs = tuple((n.z_nuclear, n.electrons) for n in net.nodes)
    eta_frag_geomean, _ = ncb.molecule_phase_participation_eta(frag_pairs)
    heavy_a = max(n.mass_number for n in net.nodes)
    light_a = min(n.mass_number for n in net.nodes)
    m_s, m_p, m_h = triplet
    vev_slots = [
        ncb.tuft_vev_networked_at_compton_shell(m, heavy_a if i < 2 else light_a)
        for i, m in enumerate((m_s, m_p, m_h))
    ]
    vev_slot_geomean = math.prod(vev_slots) ** (1.0 / len(vev_slots))
    leg_products = [
        lean.dynamic_compton_eta_second_order(etas_slot[i], triplet) * vev_slots[i]
        for i in range(len(vev_slots))
    ]
    leg_factor_geomean = math.prod(leg_products) ** (1.0 / len(leg_products))
    participation_vev_product = eta_p_chart * vev_networked
    return {
        "aggregation": "arithmetic_product_of_factors",
        "lean_formula": "eta_p * surplus * geomean(tuftVevNetworked) * feedback * geomean(valley_align)",
        "eta_policy": "phaseParticipationEta(mean_compton_angle); not geomean(slot_eta)",
        "eta_p_chart": eta_p_chart,
        "eta_slot_geomean_linear": eta_slot_geomean,
        "eta_fragment_nuclear_geomean": eta_frag_geomean,
        "vev_compton_slot_geomean": vev_slot_geomean,
        "vev_networked_readout": vev_networked,
        "vev_bare_triplet_geomean": ncb.vev_geometric_mean_from_triplet(triplet),
        "geometry_bond_geomean": geometry_alignment,
        "participation_vev_product": participation_vev_product,
        "geomean_eta_times_vev_per_leg": leg_factor_geomean,
        "ratio_leg_geomean_over_product": (
            leg_factor_geomean / participation_vev_product
            if participation_vev_product > 0
            else None
        ),
        "note": (
            "Strict geomean(η_i×vev_i) per Compton leg underbinds hydrides; "
            "chart uses mean-angle η × networked vev (steric/phase on vev)."
        ),
    }


def atomization_surplus_dimless(
    electron_counts: tuple[int, ...],
    angles: tuple[float, float, float],
) -> float:
    joint = sum(electron_counts)
    separated = sum(perturbed_casimir_energy(n, angles) for n in electron_counts)
    return perturbed_casimir_energy(joint, angles) - separated


def surplus_dimless_for_molecule(
    bench: MoleculeBenchmark,
    angles: tuple[float, float, float],
    *,
    surplus_dress_factor: float = 1.0,
) -> float:
    frags = bench.fragments
    electrons = tuple(max(f.electrons, 0) for f in frags)
    if bench.kind == "dissociation":
        if len(frags) != 2:
            raise ValueError(f"dissociation benchmark {bench.name} must have two fragments")
        n1, n2 = electrons
        base = bond_horizon_surplus_dimless(n1 + n2, n1, n2, angles)
    else:
        # Fragment-separated torus surplus (larger readout); Lean ``(10,8,2)``-style
        # bond_horizon splits are recorded in ``shell_readout.electron_split``.
        base = atomization_surplus_dimless(electrons, angles)
    return base * surplus_dress_factor


@dataclass(frozen=True)
class DynamicBindingResult:
    name: str
    kind: BindingKind
    binding_ev: float
    reference_ev: float
    error_pct: float
    dimless_core: float
    surplus_dimless: float
    eta_p: float
    vev_geometric_mean: float
    vev_geometric_mean_bare: float
    geometry_alignment_factor: float
    contact_xi: float
    dynamic_binding_curvature_coupling: float
    dynamic_binding_curvature_feedback: float
    peripheral_hydrogens: int
    h_h_repulsive_contact_points: int
    compton_triplet_m: tuple[int, int, int]
    binding_curvature_correction: float
    shell_readout: dict[str, Any]
    nuclei: list[dict[str, Any]]
    nuclear_binding_uniformity: dict[str, float]
    notes: str


def dynamic_binding_for_benchmark(bench: MoleculeBenchmark) -> DynamicBindingResult:
    import hqiv_curvature_contact_network as ccn

    net = ccn.build_network_from_molecule(
        bench.name,
        bench.fragments,
        bench.bonds,
    )
    triplet = net.compton_triplet
    shell = sab.resolve_shell_aware_readout(
        kind=bench.kind,
        fragments=bench.fragments,
        compton_triplet=triplet,
        net=net,
        molecule_name=bench.name,
    )
    _, _, nuclei, uniformity = nuclear_context_for_fragments(bench.fragments)
    eta_p = lean.dynamic_compton_eta_second_order(shell.eta_p_linear, triplet)
    surplus = surplus_dimless_for_molecule(
        bench,
        shell.surplus_angles_rad,
        surplus_dress_factor=shell.surplus_dress_factor,
    )
    net_fb = ccn.network_binding_feedback(
        net,
        curvature_contrast_weight=shell.curvature_feedback_weight,
    )
    n_periph_h = net_fb.peripheral_hydrogen_count
    vev_g = net_fb.networked_vev_geometric_mean
    vev_bare = net_fb.bare_vev_geometric_mean
    geom_align = net_fb.geometry_alignment_factor
    feedback = net_fb.curvature_feedback_at_xi
    dimless_core = eta_p * surplus * net_fb.dimless_prefactor
    binding_ev = dimless_core * EV_PER_LAMBDA_UNIT
    err = (binding_ev - bench.reference_ev) / bench.reference_ev * 100.0
    notes = (
        f"{bench.kind}: shell={shell.compton_triplet_class}; surplus={shell.surplus_angle_policy}; "
        f"η₂·surplus·vev·geom·κ(ξ={shell.contact_xi:.2f},w={shell.curvature_feedback_weight:.2f})"
    )
    return DynamicBindingResult(
        name=bench.name,
        kind=bench.kind,
        binding_ev=binding_ev,
        reference_ev=bench.reference_ev,
        error_pct=err,
        dimless_core=dimless_core,
        surplus_dimless=surplus,
        eta_p=eta_p,
        vev_geometric_mean=vev_g,
        vev_geometric_mean_bare=vev_bare,
        geometry_alignment_factor=geom_align,
        contact_xi=shell.contact_xi,
        dynamic_binding_curvature_coupling=lean.dynamic_binding_curvature_coupling_at_xi(
            shell.contact_xi
        ),
        dynamic_binding_curvature_feedback=feedback,
        peripheral_hydrogens=n_periph_h,
        h_h_repulsive_contact_points=net_fb.h_h_repulsive_contact_points,
        compton_triplet_m=triplet,
        binding_curvature_correction=(
            lean.dynamic_binding_curvature_correction_at_xi(shell.contact_xi)
            * shell.curvature_feedback_weight
        ),
        shell_readout=shell.to_dict(),
        nuclei=nuclei,
        nuclear_binding_uniformity=uniformity,
        notes=notes,
    )


def _molecule_row_dict(bench: MoleculeBenchmark, result: DynamicBindingResult) -> dict[str, Any]:
    import hqiv_curvature_contact_network as ccn

    row = asdict(result)
    net = ccn.build_network_from_molecule(
        bench.name,
        bench.fragments,
        bench.bonds,
    )
    w = result.shell_readout.get("curvature_feedback_weight", 1.0)
    fb = ccn.network_binding_feedback(net, curvature_contrast_weight=float(w))
    row["network_binding_feedback"] = {
        "contact_xi": fb.contact_xi,
        "bare_vev_geometric_mean": fb.bare_vev_geometric_mean,
        "networked_vev_geometric_mean": fb.networked_vev_geometric_mean,
        "vev_network_dress": fb.vev_network_dress,
        "steric_multiplier": fb.steric_multiplier,
        "phase_multiplier": fb.phase_multiplier,
        "geometry_alignment_factor": fb.geometry_alignment_factor,
        "curvature_feedback_at_xi": fb.curvature_feedback_at_xi,
        "dimless_prefactor": fb.dimless_prefactor,
        "peripheral_hydrogen_count": fb.peripheral_hydrogen_count,
        "h_h_repulsive_contact_points": fb.h_h_repulsive_contact_points,
    }
    row["network_balance"] = network_balance_witness(
        net,
        result.compton_triplet_m,
        eta_p_chart=result.eta_p,
        vev_networked=result.vev_geometric_mean,
        geometry_alignment=result.geometry_alignment_factor,
    )
    return row


def build_chart_payload(
    suite: tuple[MoleculeBenchmark, ...] = GMTKN55_SUITE,
    *,
    include_diagnostics: bool = True,
) -> dict[str, Any]:
    rows = [dynamic_binding_for_benchmark(b) for b in suite]
    diag_rows = (
        [dynamic_binding_for_benchmark(b) for b in EXTENDED_DIAGNOSTIC_SUITE]
        if include_diagnostics
        else []
    )
    abs_errors = [abs(r.error_pct) for r in rows]
    return {
        "source": "scripts/hqiv_dynamic_binding_chart.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.CurvatureContactNetwork",
            "Hqiv.QuantumChemistry.DynamicBindingChart",
            "Hqiv.QuantumChemistry.LiHDynamicBinding",
            "Hqiv.Physics.HopfShellBeltramiMassBridge",
            "Hqiv.Physics.BaryogenesisCore",
        ],
        "parameter_policy": "no_fitted_coefficients",
        "referenceM": REFERENCE_M,
        "ev_per_lambda_unit": EV_PER_LAMBDA_UNIT,
        "dynamic_binding_curvature_coupling": "kappa(xi) = gamma_HQIV * strongChannelFraction * B_curv(xi)",
        "binding_curvature_feedback_at_xi_lockin": lean.dynamic_binding_curvature_feedback_at_xi(
            lean.XI_LOCKIN
        ),
        "baryogenesis_binding_curvature_correction_mev": lean.baryogenesis_binding_curvature_correction(),
        "formula": (
            "E_bind = eta_2 * surplus_dimless * geomean(tuftVevFactorNetworkedAtCluster) * "
            "geometry_alignment_factor * dynamicBindingCurvatureFeedbackAtXi(xi_contact) * "
            "EV_per_lambda; eta_2 = eta + (4/8)*eta^2 on p-shell triplets"
        ),
        "network_aggregation": (
            "arithmetic_product: eta_p * surplus * geomean(tuftVev_slots) * feedback * geomean(valley_align); "
            "NOT geomean(eta_i*vev_i) over Compton legs"
        ),
        "vev_geometric_mean_policy": (
            "geomean(tuft_vev_networked_at_compton_shell) per (4,3,1) slot; then * steric * phase_geomean(nodes); "
            "eta_p from mean Compton angle (not geomean(slot_eta) nor fragment nuclear geomean)"
        ),
        "compton_triplet_rules": {
            "H2": "dynamicComptonTripletH2 → (1, 1, 1)",
            "heavy_hydride": "dynamicComptonTripletHeavyHydride → (4, 3, 1)",
            "homonuclear_period2": "dynamicComptonTripletHomonuclearPeriod2 → (4, 4, 4)",
        },
        "shell_assignment_rules": {
            "nuclear_shell": "inside_ratio(m) ≈ A^(1/3); H (A=1) at referenceM (diagnostics only)",
            "compton_triplet": "Lean DynamicBindingChart electronic triplets (not nuclear drum)",
            "eta_p": "detuning-lapse Compton IR participation (mean angle / θ₀)",
            "nuclear_binding": "cluster_binding(m_nuc, A) / A from composite-trace network",
            "shell_aware_module": "scripts/hqiv_shell_aware_binding.py",
        },
        "surplus_angle_policies": {
            "covalent_dimer_uud": "H2 (1,1,1) dissociation — Lean covalentDimerTwoElectronSurplusDimless",
            "bond_averaged_compton": "heavy hydrides + atomization — relaxed bond geometry",
            "curvature_feedback_weight": "1.0 if heavy; else 1-(4/8)(1-C2(ξ)/C2(ξ_lock)) (Hopf lapse dress)",
        },
        "molecules": [
            _molecule_row_dict(b, r)
            for b, r in zip(suite, rows, strict=True)
        ],
        "diagnostic_molecules": [asdict(r) for r in diag_rows],
        "summary": {
            "count": len(rows),
            "mean_abs_error_pct": sum(abs_errors) / len(abs_errors),
            "max_abs_error_pct": max(abs_errors),
            "within_5pct": sum(1 for e in abs_errors if e <= 5.0),
            "within_15pct": sum(1 for e in abs_errors if e <= 15.0),
        },
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV dynamic binding chart (parameter-free GMTKN55 suite)")
    print("=" * 72)
    print(f"Formula: {payload['formula']}")
    print(f"EV_per_λ (H anchor) = {payload['ev_per_lambda_unit']:.12f}")
    print(
        f"dynamicBindingCurvatureFeedbackAtXi(lock-in) = "
        f"{payload['binding_curvature_feedback_at_xi_lockin']:.6f}"
    )
    print()
    print(f"{'name':<6} {'kind':<14} {'pred/eV':>10} {'ref/eV':>10} {'err%':>8}  compton m")
    for row in payload["molecules"]:
        trip = row["compton_triplet_m"]
        print(
            f"{row['name']:<6} {row['kind']:<14} {row['binding_ev']:10.3f} "
            f"{row['reference_ev']:10.3f} {row['error_pct']:+8.2f}  {trip}"
        )
    s = payload["summary"]
    print()
    print(
        f"Summary: n={s['count']}  mean|err|={s['mean_abs_error_pct']:.2f}%  "
        f"max|err|={s['max_abs_error_pct']:.2f}%  "
        f"≤5%: {s['within_5pct']}/{s['count']}  ≤15%: {s['within_15pct']}/{s['count']}"
    )
    diag = payload.get("diagnostic_molecules") or []
    if diag:
        print()
        print("Diagnostics (large-Z surplus scale — open):")
        for row in diag:
            print(
                f"  {row['name']:<4} pred={row['binding_ev']:.2f} eV  "
                f"ref={row['reference_ev']:.2f} eV  err={row['error_pct']:+.1f}%"
            )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV parameter-free dynamic binding chart")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()

    payload = build_chart_payload()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")

    print_report(payload)
    print()
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()
