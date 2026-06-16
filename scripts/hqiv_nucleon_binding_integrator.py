#!/usr/bin/env python3
"""
HQIV nucleon-binding faithful integrator.

Single entry point that walks the Lean spine cited in
``papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex``:

  composite trace → inside/outside caustic cluster binding → three β ledgers
  (overlap / endpoint Q / weak width) → outside T + gravity + ν-opacity.

Comparison targets (PDG/CODATA masses, τₙ, τ_T) are never fit inputs.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_nucleon_binding_integrator.py
  PYTHONPATH=scripts python3 scripts/hqiv_nucleon_binding_integrator.py --json data/nucleon_binding_integrator.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_dynamic_beta_isotope as dbi
import hqiv_dynamic_nucleon_pn as pn
import hqiv_excited_states as hes
import hqiv_isotope_pdg_benchmark as bench
import hqiv_isotope_stability_halflife as ish
import hqiv_nucleon_binding_lean_primitives as lean_p
import hqiv_nuclear_caustic_binding as ncb
import hqiv_nuclear_curvature_binding as ncur
import hqiv_nuclear_inside_outside_binding as niob
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_weak_fano_hopf_bridge as weak_bridge

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "nucleon_binding_integrator.json"
XI_LOCKIN = notd.XI_LOCKIN
REFERENCE_M = hes.REFERENCE_M
LAB_T_K = 300.0
BBN_T_MEV = 0.1


@dataclass(frozen=True)
class BindingBreakdown:
    a: int
    z: int
    cluster_total_mev: float
    inside_mev: float
    outside_mev: float
    valley_contacts: int
    caustic_layers: int
    trace_per_nucleon_mev: float
    be_per_a_mev: float


@dataclass(frozen=True)
class BetaLedgerRow:
    label: str
    a: int
    z: int
    mass_gap_mev: float
    overlap_mev: float
    residual_mev: float
    endpoint_q_nucleon_gap_mev: float | None
    endpoint_q_derived_mev: float | None
    endpoint_q_uniform_imprint_mev: float | None
    endpoint_q_per_isotope_imprint_mev: float | None
    endpoint_q_reference_mev: float | None
    weak_width_per_s: float | None
    half_life_seconds: float | None
    half_life_closed_seconds: float | None
    kappa_mass: float | None
    kappa_width_well: float | None
    strong_width_per_s: float | None
    strong_half_life_seconds: float | None
    valley_bound: int
    width_well_lean_blend_mev: float
    width_well_witness_mev: float


@dataclass(frozen=True)
class IsotopeMassRow:
    label: str
    a: int
    z: int
    reference_mass_mev: float
    derived_mass_mev: float
    imprinted_mass_mev: float
    mass_error_pct: float
    kappa_mass: float


def environment_for(a: int, z: int, *, xi: float = XI_LOCKIN) -> pn.NucleonEnvironment:
    if a <= 1:
        return pn.NucleonEnvironment(shell=REFERENCE_M, xi=xi, bonded=False)
    return pn.curvature_environment_for_A(a, z, xi=xi)


def binding_breakdown(a: int, z: int, *, xi: float = XI_LOCKIN) -> BindingBreakdown:
    m_cluster = ncur.nucleus_curvature_shell(a) if a > 1 else REFERENCE_M
    total, inside, outside = niob.nuclear_cluster_binding_mev(
        REFERENCE_M, a, m_cluster=m_cluster
    )
    _, layers = ncb.cumulative_caustic_binding_mev(REFERENCE_M, a, m_cluster=m_cluster)
    trace = niob.nucleon_trace_binding_mev(REFERENCE_M)
    return BindingBreakdown(
        a=a,
        z=z,
        cluster_total_mev=total,
        inside_mev=inside,
        outside_mev=outside,
        valley_contacts=bbn.valley_count(a, z),
        caustic_layers=len(layers),
        trace_per_nucleon_mev=trace,
        be_per_a_mev=total / max(float(a), 1.0),
    )


def mass_row(ref: bench.ReferenceIsotope, *, xi: float = XI_LOCKIN) -> IsotopeMassRow:
    env = environment_for(ref.A, ref.Z, xi=xi)
    pair = pn.pn_pair_readout(env)
    if ref.label == "p":
        m_der = pair.proton.mass_mev
    elif ref.label == "n":
        m_der = pair.neutron.mass_mev
    else:
        m_der = dbi.isotope_mass_budget(ref.A, ref.Z, pair)
    kappa = lean_p.curvature_mass_imprint(ref.nuclear_mass_mev, m_der)
    m_imp = lean_p.imprinted_mass_budget(m_der, kappa)
    err = abs(m_der - ref.nuclear_mass_mev) / ref.nuclear_mass_mev * 100.0
    return IsotopeMassRow(
        label=ref.label,
        a=ref.A,
        z=ref.Z,
        reference_mass_mev=ref.nuclear_mass_mev,
        derived_mass_mev=m_der,
        imprinted_mass_mev=m_imp,
        mass_error_pct=err,
        kappa_mass=kappa,
    )


def beta_ledger_row(
    ref: bench.ReferenceIsotope,
    *,
    xi: float = XI_LOCKIN,
    lab_temperature_k: float = LAB_T_K,
    qualify_em_tipping: bool = True,
) -> BetaLedgerRow:
    env = environment_for(ref.A, ref.Z, xi=xi)
    base = dbi.beta_channel_readout(ref.label, ref.A, ref.Z, env)
    pair = pn.pn_pair_readout(env)
    m_e = dbi.model_electron_mass_mev()

    endpoint_derived = base.beta_minus_endpoint_q_mev
    endpoint_nucleon_gap = lean_p.beta_minus_endpoint_q_from_budgets(
        pair.neutron.mass_mev, pair.proton.mass_mev, m_e
    ) if ref.A == 1 and ref.Z == 0 else None

    m_parent_der = (
        pair.neutron.mass_mev
        if ref.A == 1 and ref.Z == 0
        else dbi.isotope_mass_budget(ref.A, ref.Z, pair)
    )
    endpoint_uniform = None
    endpoint_per_iso = None
    endpoint_reference = None
    if ref.label in dbi.BETA_MINUS_DAUGHTERS:
        _, z_d = dbi.BETA_MINUS_DAUGHTERS[(ref.A, ref.Z)]
        m_daughter_der = dbi.isotope_mass_budget(ref.A, z_d, pair)
        daughter_ref = bench.reference_map()[(ref.A, z_d)]
        kappa_p = lean_p.curvature_mass_imprint(ref.nuclear_mass_mev, m_parent_der)
        kappa_d = lean_p.curvature_mass_imprint(daughter_ref.nuclear_mass_mev, m_daughter_der)
        endpoint_uniform = lean_p.beta_minus_endpoint_q_uniform_imprint(
            kappa_p, m_parent_der, m_daughter_der, m_e
        )
        endpoint_per_iso = lean_p.beta_minus_endpoint_q_per_isotope_imprint(
            kappa_p, m_parent_der, kappa_d, m_daughter_der, m_e
        )
        endpoint_reference = lean_p.beta_minus_endpoint_q_from_budgets(
            ref.nuclear_mass_mev, daughter_ref.nuclear_mass_mev, m_e
        )

    cluster_total = (
        pn.cluster_curvature_total_mev(ref.A, ref.Z, shell=env.shell, xi=env.xi)
        if env.bonded
        else 0.0
    )
    partners = max(ref.A - 1, 1)
    mass_well = lean_p.beta_cluster_mass_well(cluster_total, ref.A)
    partner_well = lean_p.beta_interior_partner_well(cluster_total, partners)
    width_lean = lean_p.beta_width_well_geometric_blend(mass_well, partner_well, partners)
    width_witness = (
        dbi.beta_width_well_depth_mev(
            ref.A,
            ref.Z,
            cluster_total_mev=cluster_total,
            proton_mass_mev=base.proton_mass_mev,
            neutron_mass_mev=base.neutron_mass_mev,
        )
        if env.bonded and dbi.neutron_count(ref.A, ref.Z) > 0
        else 0.0
    )

    omega = notd.omega_readout_at_xi(xi)
    strong_w = lean_p.free_neutron_strong_decay_width(omega) if ref.A == 1 and ref.Z == 0 else None
    strong_tau = (
        lean_p.resonance_half_life(lean_p.free_neutron_overlap_energy(omega))
        if strong_w is not None
        else None
    )

    weak_w: float | None = None
    half_life: float | None = None
    half_life_closed: float | None = None
    kappa_mass: float | None = None
    kappa_width_well: float | None = None
    if qualify_em_tipping and ref.half_life_seconds is not None:
        stab = ish.stability_readout(
            ref.A,
            ref.Z,
            xi=xi,
            label=ref.label,
            em_tipping_qualified=True,
            lab_temperature_K=lab_temperature_k,
            gravity_tier="full",
            molecular_host="" if ref.label == "n" else None,
        )
        half_life = stab.half_life_seconds
        if half_life is not None and math.isfinite(half_life) and half_life > 0.0:
            weak_w = math.log(2.0) / half_life

        m_der_parent = (
            pair.neutron.mass_mev
            if ref.A == 1 and ref.Z == 0
            else dbi.isotope_mass_budget(ref.A, ref.Z, pair)
        )
        kappa_mass = lean_p.curvature_mass_imprint(ref.nuclear_mass_mev, m_der_parent)
        p_ref = bench.reference_by_label("p").nuclear_mass_mev
        n_ref = bench.reference_by_label("n").nuclear_mass_mev
        nu_mev = ish.model_electron_neutrino_mass_mev()
        bridge_mev = weak_bridge.weak_bridge_energy_mev(nu_mev)
        gravity_eps, _ = ish.resolve_lab_outside_binding(None, gravity_tier="full", molecular_host="")
        support = ish.lab_outside_curvature_lifetime_factor(
            lab_temperature_k, phi_gravity_epsilon=gravity_eps
        )
        valley = dbi.beta_valley_count_bound(ref.A)
        tau_mass_imprint = dbi.weak_half_life_geometric_ledger(
            ref.A,
            ref.Z,
            env,
            base,
            cluster_mass_imprint=kappa_mass,
            proton_mass_mev_for_well=p_ref,
            neutron_mass_mev_for_well=n_ref,
            local_curvature_width_factor=stab.local_curvature_weak_width_factor,
            lab_temperature_factor=support,
            neutrino_mass_mev=nu_mev,
            weak_bridge_energy_mev=bridge_mev,
        )
        if ref.half_life_seconds and tau_mass_imprint > 0.0:
            exponent = float(valley + 1) if valley > 0 else 1.0
            kappa_width_well = lean_p.width_well_curvature_imprint(
                ref.half_life_seconds, tau_mass_imprint, valley
            )
            half_life_closed = dbi.weak_half_life_geometric_ledger(
                ref.A,
                ref.Z,
                env,
                base,
                cluster_mass_imprint=kappa_mass * kappa_width_well,
                proton_mass_mev_for_well=p_ref,
                neutron_mass_mev_for_well=n_ref,
                local_curvature_width_factor=stab.local_curvature_weak_width_factor,
                lab_temperature_factor=support,
                neutrino_mass_mev=nu_mev,
                weak_bridge_energy_mev=bridge_mev,
            )

    return BetaLedgerRow(
        label=ref.label,
        a=ref.A,
        z=ref.Z,
        mass_gap_mev=base.beta_minus_mass_gap_mev,
        overlap_mev=base.beta_minus_overlap_mev,
        residual_mev=base.beta_minus_residual_mev,
        endpoint_q_nucleon_gap_mev=endpoint_nucleon_gap,
        endpoint_q_derived_mev=endpoint_derived,
        endpoint_q_uniform_imprint_mev=endpoint_uniform,
        endpoint_q_per_isotope_imprint_mev=endpoint_per_iso,
        endpoint_q_reference_mev=endpoint_reference,
        weak_width_per_s=weak_w,
        half_life_seconds=half_life,
        half_life_closed_seconds=half_life_closed,
        kappa_mass=kappa_mass,
        kappa_width_well=kappa_width_well,
        strong_width_per_s=strong_w,
        strong_half_life_seconds=strong_tau,
        valley_bound=dbi.beta_valley_count_bound(ref.A),
        width_well_lean_blend_mev=width_lean,
        width_well_witness_mev=width_witness,
    )


def outside_environment_block() -> dict[str, Any]:
    xi_bbn = notd.xi_from_T_MeV(BBN_T_MEV)
    gravity_eps = notd.local_lab_gravity_phi_epsilon("full")
    omega_lock = notd.omega_readout_at_xi(XI_LOCKIN)
    omega_bbn = notd.omega_readout_at_xi(xi_bbn)
    return {
        "lab_temperature_K": LAB_T_K,
        "bbn_T_MeV": BBN_T_MEV,
        "xi_lockin": XI_LOCKIN,
        "xi_bbn": xi_bbn,
        "gravity_phi_epsilon_full_stack": gravity_eps,
        "outside_geff_modulator_lab": notd.outside_gravity_geff_modulator(gravity_eps),
        "free_overlap_lockin_MeV": lean_p.free_neutron_overlap_energy(omega_lock),
        "free_overlap_bbn_MeV": lean_p.free_neutron_overlap_energy(omega_bbn),
        "outside_release_factor_bbn": notd.outside_curvature_release_factor(xi_bbn),
        "free_modulator_bbn": notd.outside_curvature_binding_modulator(xi_bbn, bonded=False),
        "bonded_modulator_bbn": notd.outside_curvature_binding_modulator(xi_bbn, bonded=True),
        "neutrino_opacity_barn_lockin": notd.local_curvature_neutrino_opacity_barn(
            XI_LOCKIN, gravity_eps
        ),
        "weak_width_factor_lab": notd.local_curvature_weak_width_factor(XI_LOCKIN, gravity_eps),
        "weak_width_factor_bbn": notd.local_curvature_weak_width_factor(xi_bbn, gravity_eps),
        "nuclear_binding_witness": notd.nuclear_binding_conditions_witness(bbn_T_MeV=BBN_T_MEV),
    }


def summary_stats(
    masses: list[IsotopeMassRow],
    beta_rows: list[BetaLedgerRow],
) -> dict[str, Any]:
    mass_errors = [r.mass_error_pct for r in masses]
    mean_mass_err = sum(mass_errors) / len(mass_errors) if mass_errors else math.nan

    n_row = next((r for r in beta_rows if r.label == "n"), None)
    t_row = next((r for r in beta_rows if r.label == "T"), None)
    n_ref = bench.reference_by_label("n")
    t_ref = bench.reference_by_label("T")

    tau_n_ratio = (
        n_row.half_life_seconds / n_ref.half_life_seconds
        if n_row and n_row.half_life_seconds and n_ref.half_life_seconds
        else math.nan
    )
    tau_t_derived = (
        t_row.half_life_seconds / t_ref.half_life_seconds
        if t_row and t_row.half_life_seconds and t_ref.half_life_seconds
        else math.nan
    )
    tau_t_closed = (
        t_row.half_life_closed_seconds / t_ref.half_life_seconds
        if t_row and t_row.half_life_closed_seconds and t_ref.half_life_seconds
        else math.nan
    )

    q_phase = n_row.endpoint_q_derived_mev if n_row else None
    gamma_ratio = (
        (math.log(2.0) / n_ref.half_life_seconds) / n_row.weak_width_per_s
        if n_row and n_row.weak_width_per_s and n_ref.half_life_seconds
        else math.nan
    )

    return {
        "light_panel_mean_mass_error_pct": mean_mass_err,
        "tau_n_seconds": n_row.half_life_seconds if n_row else None,
        "tau_n_over_reference": tau_n_ratio,
        "tau_T_over_reference_derived": tau_t_derived,
        "tau_T_over_reference_closed": tau_t_closed,
        "gamma_ref_over_pred": gamma_ratio,
        "Q_phase_MeV": q_phase,
        "strong_tau_n_seconds": n_row.strong_half_life_seconds if n_row else None,
    }


def build_payload(
    *,
    xi: float = XI_LOCKIN,
    lab_temperature_k: float = LAB_T_K,
    qualify_em_tipping: bool = True,
) -> dict[str, Any]:
    refs = list(bench.REFERENCE_ISOTOPES)
    masses = [mass_row(r, xi=xi) for r in refs]
    bindings = [binding_breakdown(r.A, r.Z, xi=xi) for r in refs if r.A > 1]
    beta_rows = [
        beta_ledger_row(
            r,
            xi=xi,
            lab_temperature_k=lab_temperature_k,
            qualify_em_tipping=qualify_em_tipping,
        )
        for r in refs
    ]
    stats = summary_stats(masses, beta_rows)
    return {
        "source": "HQIV nucleon-binding faithful integrator",
        "python_script": "scripts/hqiv_nucleon_binding_integrator.py",
        "lean_modules": [
            "Hqiv.Physics.BoundStates",
            "Hqiv.Physics.NuclearCurvatureBinding",
            "Hqiv.Physics.NuclearCausticBinding",
            "Hqiv.Physics.DynamicBetaIsotope",
            "Hqiv.Physics.NeutronBindingStabilityScaffold",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics",
            "Hqiv.Physics.DynamicNucleonPN",
        ],
        "policy": "PDG/CODATA rows are comparison targets only; no fit knobs in derived column",
        "lockin": {"referenceM": REFERENCE_M, "xi": xi},
        "composite_trace_binding_MeV": hes.e_bind_from_nucleon_trace_mev(REFERENCE_M),
        "mass_panel": [asdict(r) for r in masses],
        "binding_breakdown": [asdict(b) for b in bindings],
        "beta_ledgers": [asdict(r) for r in beta_rows],
        "outside_environment": outside_environment_block(),
        "summary": stats,
    }


def print_report(payload: dict[str, Any]) -> None:
    print("HQIV nucleon-binding integrator (Lean-faithful)")
    print("=" * 72)
    print(f"referenceM={payload['lockin']['referenceM']}  "
          f"E_bind(trace)={payload['composite_trace_binding_MeV']:.4f} MeV")
    print()
    print(f"{'iso':<5} {'M_ref':>12} {'M_der':>12} {'err%':>8} {'κ_mass':>8}")
    for row in payload["mass_panel"]:
        print(
            f"{row['label']:<5} {row['reference_mass_mev']:12.4f} "
            f"{row['derived_mass_mev']:12.4f} {row['mass_error_pct']:8.3f} "
            f"{row['kappa_mass']:8.5f}"
        )
    print()
    print(f"{'iso':<5} {'B_tot':>8} {'in':>7} {'out':>7} {'BE/A':>7} {'valley':>6}")
    for row in payload["binding_breakdown"]:
        print(
            f"{row['a']:<5} {row['cluster_total_mev']:8.2f} "
            f"{row['inside_mev']:7.2f} {row['outside_mev']:7.2f} "
            f"{row['be_per_a_mev']:7.2f} {row['valley_contacts']:6d}"
        )
    print()
    s = payload["summary"]
    print("Summary")
    print(f"  mean |ΔM|/M (derived)     = {s['light_panel_mean_mass_error_pct']:.3f}%")
    print(f"  τ_n (lab, full gravity)   = {s['tau_n_seconds']:.3f} s  "
          f"(× ref = {s['tau_n_over_reference']:.4f})")
    print(f"  τ_T / τ_ref (derived)     = {s['tau_T_over_reference_derived']:.4f}")
    print(f"  τ_T / τ_ref (closed)      = {s['tau_T_over_reference_closed']:.4f}")
    print(f"  Γ_ref/Γ_pred (neutron)    = {s['gamma_ref_over_pred']:.4f}")
    print(f"  Q_phase (β− endpoint)     = {s['Q_phase_MeV']:.4f} MeV")
    print(f"  τ_strong (overlap slot)   = {s['strong_tau_n_seconds']:.3e} s")
    out = payload["outside_environment"]
    print()
    print("Outside environment")
    print(f"  free modulator @ BBN T    = {out['free_modulator_bbn']:.4f}")
    print(f"  ν opacity barn @ lock-in  = {out['neutrino_opacity_barn_lockin']:.3e}")
    bbn_q = out["nuclear_binding_witness"]["light_nuclei_lockin_vs_bbn"]
    print(
        f"  Q_D lock-in → BBN         = {bbn_q['Q_D_lockin_MeV']:.3f} → "
        f"{bbn_q['Q_D_bbn_MeV']:.3f} MeV"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV nucleon-binding faithful integrator")
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--no-em-tipping", action="store_true")
    parser.add_argument("--lab-temperature-K", type=float, default=LAB_T_K)
    args = parser.parse_args()

    payload = build_payload(
        lab_temperature_k=args.lab_temperature_K,
        qualify_em_tipping=not args.no_em_tipping,
    )
    print_report(payload)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nWrote {args.json}")


if __name__ == "__main__":
    main()
