#!/usr/bin/env python3
"""
Benchmark HQIV isotope readouts against light-isotope reference data.

This is a comparison layer only: reference masses / half-lives are not fed back into
the HQIV functions.

References are PDG/CODATA/NIST-style nuclear masses for the light panel and standard
published half-lives/stability labels.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_dynamic_beta_isotope as dbi
import hqiv_dynamic_nucleon_pn as pn
import hqiv_isotope_stability_halflife as ish
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as notd
import hqiv_weak_fano_hopf_bridge as weak_bridge

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_JSON = ROOT / "data" / "isotope_pdg_benchmark.json"

YEAR_SECONDS = 365.25 * 24.0 * 3600.0


@dataclass(frozen=True)
class ReferenceIsotope:
    label: str
    A: int
    Z: int
    nuclear_mass_mev: float
    half_life_seconds: float | None
    stability: str
    source: str


REFERENCE_ISOTOPES: tuple[ReferenceIsotope, ...] = (
    ReferenceIsotope("p", 1, 1, 938.27208816, None, "stable_or_lower_bound", "PDG proton mass"),
    ReferenceIsotope("n", 1, 0, 939.56542052, 879.4, "beta_minus", "PDG/CODATA neutron"),
    ReferenceIsotope("D", 2, 1, 1875.61294257, None, "stable", "CODATA deuteron"),
    ReferenceIsotope("T", 3, 1, 2808.92113298, 12.32 * YEAR_SECONDS, "beta_minus", "NIST/CODATA triton"),
    ReferenceIsotope("He3", 3, 2, 2808.39160743, None, "stable", "CODATA helion"),
    ReferenceIsotope("He4", 4, 2, 3727.3794066, None, "stable", "CODATA alpha particle"),
)


@dataclass(frozen=True)
class BenchmarkRow:
    label: str
    A: int
    Z: int
    reference_mass_mev: float
    predicted_mass_mev: float
    mass_error_mev: float
    mass_error_pct: float
    reference_stability: str
    predicted_structurally_shielded: bool
    predicted_stable_qualified: bool
    predicted_channel: str
    reference_half_life_seconds: float | None
    predicted_half_life_seconds: float | None
    half_life_ratio_pred_over_ref: float | None
    notes: str


@dataclass(frozen=True)
class NeutronLifetimeReference:
    method: str
    half_life_seconds: float
    lab_temperature_K: float
    trap_magnetic_field_tesla: float
    source: str


@dataclass(frozen=True)
class IsotopeMethodTensionCase:
    label: str
    central_half_life_seconds: float
    tension_note: str


NEUTRON_LIFETIME_REFERENCES: tuple[NeutronLifetimeReference, ...] = (
    NeutronLifetimeReference(
        "bottle",
        877.75,
        4.0,
        2.5,
        "representative UCN magnetic-bottle average (superconducting trap class)",
    ),
    NeutronLifetimeReference(
        "beam",
        888.0,
        300.0,
        0.0,
        "representative beam average (decay-in-flight, negligible trap B)",
    ),
)


ISOTOPE_METHOD_TENSION_CASES: tuple[IsotopeMethodTensionCase, ...] = (
    IsotopeMethodTensionCase(
        "28Al",
        134.432,
        "TwinSol-style modern value; historical high-precision outlier is a method/systematics target.",
    ),
    IsotopeMethodTensionCase(
        "71Ge",
        11.468 * 24.0 * 3600.0,
        "HPGe remeasurement class; half-life shift cannot explain the Gallium anomaly if method factors are small.",
    ),
)


def neutron_method_environment_ledger(
    *,
    qualify_em_tipping: bool,
    neutrino_mass_mev: float | None,
) -> list[dict]:
    """
    Document setup-dependent outside-curvature slots for the bottle/beam tension.

    Primary bottle lever: UCN trap magnetic field B → ρ_mag(B) curvature on the weak
    Fano/Hopf bridge (Lean `trapWeakWidthFactorFromMagnetic`). Temperature is metadata
    and a sub-leading outside-support witness (~10³ ppm), not the split driver.
    """
    rows: list[dict] = []
    refs = {r.method: r for r in NEUTRON_LIFETIME_REFERENCES}
    bottle_ref = refs["bottle"].half_life_seconds
    beam_ref = refs["beam"].half_life_seconds
    split_ppm = 1.0e6 * (beam_ref / bottle_ref - 1.0)

    slot_notes = {
        "bottle": (
            "UCN magnetic trap embedding: superconducting bottle field B books ρ_mag(B) "
            "curvature on the weak Fano/Hopf bridge (not the neV Zeeman slot). "
            "Material boundary contacts + trap-induced decoherence on the weak bridge. "
            "Dilute fermionic gas — Pauli forbids strong-width composite coupling. "
            "Cryogenic storage (often 4 K) is metadata; B is the determining curvature lever."
        ),
        "beam": (
            "Free-branch decay-in-flight with directed transport coherence along the beam "
            "pipe; room-temperature beam line; effectively single-particle weak beta- "
            "(no trap ensemble / wall-exchange ledger). Co-spin horizon Doppler from "
            "beam velocity (v/c ~ few ppm) is an additive lapse slot (flyby readout). "
            "Measures protons from beta- in a kinematic endpoint window."
        ),
    }

    for ref in NEUTRON_LIFETIME_REFERENCES:
        row = ish.stability_readout(
            1,
            0,
            label="n",
            em_tipping_qualified=qualify_em_tipping,
            lab_temperature_K=ref.lab_temperature_K,
            neutrino_mass_mev=neutrino_mass_mev,
            molecular_host="",
        )
        pred = row.half_life_seconds or math.nan
        ratio = pred / ref.half_life_seconds if row.half_life_seconds else math.nan
        partner_ppm = None
        if ref.method == "bottle":
            partner_ppm = split_ppm
        elif ref.method == "beam":
            partner_ppm = -split_ppm
        rows.append(
            {
                "method": ref.method,
                "reference_half_life_seconds": ref.half_life_seconds,
                "lab_temperature_K": ref.lab_temperature_K,
                "trap_magnetic_field_tesla": ref.trap_magnetic_field_tesla,
                "trap_magnetic_curvature_fraction": lean.trap_magnetic_curvature_fraction(
                    ref.trap_magnetic_field_tesla
                ),
                "trap_weak_width_factor_from_magnetic": lean.trap_weak_width_factor_from_magnetic(
                    ref.trap_magnetic_field_tesla
                ),
                "predicted_half_life_seconds": pred,
                "pred_over_ref": ratio,
                "outside_support_factor": row.lab_outside_curvature_factor,
                "lab_gravity_binding_stack": row.lab_gravity_binding_stack,
                "bottle_beam_split_ppm": split_ppm,
                "partner_ppm_vs_other_method": partner_ppm,
                "interpretive_slots": slot_notes[ref.method],
                "source": ref.source,
            }
        )

    # Temperature-only slice of the split (4 K bottle vs 300 K beam class).
    t_bottle = ish.stability_readout(
        1, 0, label="n", em_tipping_qualified=qualify_em_tipping,
        lab_temperature_K=refs["bottle"].lab_temperature_K, molecular_host="",
    )
    t_beam = ish.stability_readout(
        1, 0, label="n", em_tipping_qualified=qualify_em_tipping,
        lab_temperature_K=refs["beam"].lab_temperature_K, molecular_host="",
    )
    temp_only_ppm = 1.0e6 * (
        (t_beam.half_life_seconds or 0.0) / (t_bottle.half_life_seconds or 1.0) - 1.0
    )
    rows.append(
        {
            "comparison": "temperature_only_bottle_T_vs_beam_T",
            "bottle_T_K": refs["bottle"].lab_temperature_K,
            "beam_T_K": refs["beam"].lab_temperature_K,
            "ppm_delta_tau": temp_only_ppm,
            "note": (
                "Sub-leading control only (~10³ ppm from 4 K vs 300 K outside support); "
                "not the primary bottle/beam split driver."
            ),
        }
    )
    f_bottle = lean.trap_weak_width_factor_from_magnetic(refs["bottle"].trap_magnetic_field_tesla)
    f_beam = lean.trap_weak_width_factor_from_magnetic(refs["beam"].trap_magnetic_field_tesla)
    magnetic_tau_bottle_over_beam = f_beam / f_bottle
    magnetic_tau_beam_over_bottle = f_bottle / f_beam
    magnetic_ppm = 1.0e6 * (magnetic_tau_beam_over_bottle - 1.0)
    rows.append(
        {
            "comparison": "magnetic_trap_bottle_B_vs_beam_B",
            "bottle_B_tesla": refs["bottle"].trap_magnetic_field_tesla,
            "beam_B_tesla": refs["beam"].trap_magnetic_field_tesla,
            "bottle_rho_mag": lean.trap_magnetic_curvature_fraction(
                refs["bottle"].trap_magnetic_field_tesla
            ),
            "beam_rho_mag": lean.trap_magnetic_curvature_fraction(
                refs["beam"].trap_magnetic_field_tesla
            ),
            "bottle_width_factor": f_bottle,
            "beam_width_factor": f_beam,
            "predicted_tau_bottle_over_beam": magnetic_tau_bottle_over_beam,
            "predicted_tau_beam_over_bottle": magnetic_tau_beam_over_bottle,
            "predicted_beam_over_bottle_split_ppm": magnetic_ppm,
            "observed_beam_over_bottle_split_ppm": split_ppm,
            "observed_fraction_of_saturated_envelope": split_ppm / magnetic_ppm
            if magnetic_ppm
            else math.nan,
            "note": (
                "Primary structural lever: UCN trap B → ρ_mag(B) on weak Fano/Hopf bridge "
                "(Lean trapWeakWidthFactorFromMagnetic). Beam sees f≈1; bottle at B≥1 T "
                "books f≈1+γ/18; observed beam/bottle split lies below this saturated "
                "method envelope."
            ),
        }
    )
    rows.append(
        {
            "comparison": "spin_statistics_ensemble_policy",
            "note": (
                "Half-integer neutrons cannot couple into a shared strong-width composite "
                "(Pauli exchange phase -1). If coupling were allowed, Ledger-I overlap "
                "would give t1/2 ~ 1e-22 s, not ~880 s. Bottle and beam both measure "
                "Ledger-III weak width; the split is trap magnetic curvature + embedding, "
                "not temperature alone and not instantaneous beta from fermion coupling."
            ),
        }
    )
    return rows


def isotope_method_tension_panel() -> list[dict]:
    """Method/environment predictions for isotope half-life tension examples."""
    environments = (
        ("neutral_lab", 1.0, "No trap/collider curvature width dressing."),
        (
            "ucn_trap_saturated",
            lean.trap_weak_width_factor_from_magnetic(
                lean.REPRESENTATIVE_BOTTLE_TRAP_FIELD_TESLA
            ),
            "Saturated magnetic trap envelope; neutron-bottle scale, not assumed for ordinary samples.",
        ),
        (
            "collider_4T",
            lean.collider_beta_method_width_factor(4.0, 4.0, 0.0),
            "4 T collider/reference field with no comoving-stream occupancy.",
        ),
        (
            "collider_4T_stream1",
            lean.collider_beta_method_width_factor(4.0, 4.0, 1.0),
            "4 T field plus full comoving stream occupancy.",
        ),
    )
    rows: list[dict] = []
    for case in ISOTOPE_METHOD_TENSION_CASES:
        for env_id, width_factor, note in environments:
            tau = lean.apparent_beta_half_life_from_method(
                case.central_half_life_seconds,
                width_factor,
            )
            rows.append(
                {
                    "isotope": case.label,
                    "environment": env_id,
                    "central_half_life_seconds": case.central_half_life_seconds,
                    "local_width_factor": width_factor,
                    "predicted_apparent_half_life_seconds": tau,
                    "method_shift_ppm": lean.method_shift_ppm(width_factor),
                    "method_shift_percent": 100.0 * (tau / case.central_half_life_seconds - 1.0),
                    "tension_note": case.tension_note,
                    "interpretation": note,
                }
            )
    rows.append(
        {
            "comparison": "isotope_tension_policy",
            "note": (
                "HQIV method curvature predicts percent-level shifts only in strong trap/"
                "collider environments. If an isotope discrepancy exceeds this envelope "
                "without such a method environment, it remains an experimental systematic "
                "or a missing isotope-structure ledger, not a fitted lifetime correction."
            ),
        }
    )
    return rows


def neutron_width_ledger_comparison(
    *,
    qualify_em_tipping: bool,
    neutrino_mass_mev: float | None,
    lab_temperature_K: float = 300.0,
) -> dict:
    """Width-ledger accuracy for free neutron (preferred over raw tau ratio)."""
    row = ish.stability_readout(
        1,
        0,
        label="n",
        em_tipping_qualified=qualify_em_tipping,
        lab_temperature_K=lab_temperature_K,
        neutrino_mass_mev=neutrino_mass_mev,
        molecular_host="",
    )
    tau_pred = row.half_life_seconds or math.nan
    q_phase = row.beta_phase_space_q_mev or math.nan
    gamma_pred = math.log(2.0) / tau_pred if tau_pred and tau_pred > 0 else math.nan
    width_central = row.local_curvature_weak_width_factor
    width_low = row.local_curvature_weak_width_factor_low
    width_high = row.local_curvature_weak_width_factor_high
    tau_low = tau_pred * width_central / width_high if tau_pred and width_high > 0 else math.nan
    tau_high = tau_pred * width_central / width_low if tau_pred and width_low > 0 else math.nan
    refs = []
    for ref in NEUTRON_LIFETIME_REFERENCES:
        tau_ref = ref.half_life_seconds
        gamma_ref = math.log(2.0) / tau_ref
        tau_ratio = tau_pred / tau_ref
        gamma_ratio = gamma_ref / gamma_pred
        delta_q_mev = q_phase * (math.exp(math.log(gamma_ratio) / 5.0) - 1.0)
        refs.append(
            {
                "method": ref.method,
                "reference_half_life_seconds": tau_ref,
                "tau_pred_over_ref": tau_ratio,
                "gamma_ref_over_pred": gamma_ratio,
                "delta_q_phase_keV": delta_q_mev * 1000.0,
                "delta_q_phase_fraction": delta_q_mev / q_phase if q_phase else math.nan,
            }
        )
    tau_pdg = 879.4
    gamma_pdg = math.log(2.0) / tau_pdg
    gamma_ratio_pdg = gamma_pdg / gamma_pred
    delta_q_pdg = q_phase * (math.exp(math.log(gamma_ratio_pdg) / 5.0) - 1.0)
    return {
        "policy": "compare width ledger via Q_phase; tau is integrated clock-time display",
        "lab_temperature_K": lab_temperature_K,
        "local_curvature_neutrino_opacity_barn": row.local_curvature_neutrino_opacity_barn,
        "local_curvature_weak_width_factor": width_central,
        "local_curvature_weak_width_factor_band": {
            "low": width_low,
            "central": width_central,
            "high": width_high,
        },
        "predicted_half_life_seconds": tau_pred,
        "predicted_half_life_seconds_band": {
            "low": tau_low,
            "central": tau_pred,
            "high": tau_high,
        },
        "predicted_gamma_per_s": gamma_pred,
        "q_phase_mev": q_phase,
        "pdg_codata": {
            "reference_half_life_seconds": tau_pdg,
            "tau_pred_over_ref": tau_pred / tau_pdg,
            "gamma_ref_over_pred": gamma_ratio_pdg,
            "delta_q_phase_keV": delta_q_pdg * 1000.0,
            "delta_q_phase_fraction": delta_q_pdg / q_phase if q_phase else math.nan,
        },
        "method_references": refs,
    }


def environment_for_reference(ref: ReferenceIsotope, *, xi: float) -> pn.NucleonEnvironment:
    if ref.A <= 1:
        return pn.NucleonEnvironment(shell=notd.REFERENCE_M, xi=xi, bonded=False)
    return pn.caustic_environment_for_A(ref.A, xi=xi)


def predicted_mass_for_reference(ref: ReferenceIsotope, *, xi: float) -> float:
    if ref.label == "p":
        return pn.pn_pair_readout(environment_for_reference(ref, xi=xi)).proton.mass_mev
    if ref.label == "n":
        return pn.pn_pair_readout(environment_for_reference(ref, xi=xi)).neutron.mass_mev
    env = environment_for_reference(ref, xi=xi)
    pair = pn.pn_pair_readout(env)
    return dbi.isotope_mass_budget(ref.A, ref.Z, pair)


def reference_map() -> dict[tuple[int, int], ReferenceIsotope]:
    return {(ref.A, ref.Z): ref for ref in REFERENCE_ISOTOPES}


def reference_by_label(label: str) -> ReferenceIsotope:
    for ref in REFERENCE_ISOTOPES:
        if ref.label == label:
            return ref
    raise KeyError(label)


def curvature_imprint_control_row(
    ref: ReferenceIsotope,
    *,
    qualify_em_tipping: bool,
    xi: float,
    lab_temperature_K: float,
    neutrino_mass_mev: float | None,
) -> dict | None:
    """
    PDG-mass control on the geometric width ledger (comparison layer).

    * ``kappa_mass`` = M_ref / M_derived closes the mass readout.
    * Same geometric-mean width well with PDG nucleon masses in the blend.
    * ``kappa_width_well`` closes τ when applied to the cluster caustic depth
      (width-ledger curvature imprint for other decay calculations).
    """
    if ref.half_life_seconds is None or not qualify_em_tipping:
        return None
    if ref.label not in {"n", "T"}:
        return None

    derived = ish.stability_readout(
        ref.A,
        ref.Z,
        xi=xi,
        label=ref.label,
        em_tipping_qualified=True,
        lab_temperature_K=lab_temperature_K,
        neutrino_mass_mev=neutrino_mass_mev,
        molecular_host="" if ref.label == "n" else None,
    )
    env = environment_for_reference(ref, xi=xi)
    base = dbi.beta_channel_readout(ref.label, ref.A, ref.Z, env)
    pair = pn.pn_pair_readout(env)
    m_der = dbi.isotope_mass_budget(ref.A, ref.Z, pair)
    kappa_mass = ref.nuclear_mass_mev / m_der if m_der > 0.0 else math.nan

    p_ref = reference_by_label("p").nuclear_mass_mev
    n_ref = reference_by_label("n").nuclear_mass_mev
    nu_mev = ish.model_electron_neutrino_mass_mev() if neutrino_mass_mev is None else neutrino_mass_mev
    bridge_mev = weak_bridge.weak_bridge_energy_mev(nu_mev)
    width_central = derived.local_curvature_weak_width_factor
    gravity_eps, _ = ish.resolve_lab_outside_binding(None, gravity_tier="full", molecular_host="")
    support = ish.lab_outside_curvature_lifetime_factor(lab_temperature_K, phi_gravity_epsilon=gravity_eps)

    tau_der = derived.half_life_seconds or math.nan
    tau_ref = ref.half_life_seconds

    valley = dbi.beta_valley_count_bound(ref.A)

    tau_pdg_nucleons = dbi.weak_half_life_geometric_ledger(
        ref.A,
        ref.Z,
        env,
        base,
        cluster_mass_imprint=1.0,
        proton_mass_mev_for_well=p_ref,
        neutron_mass_mev_for_well=n_ref,
        local_curvature_width_factor=width_central,
        lab_temperature_factor=support,
        neutrino_mass_mev=nu_mev,
        weak_bridge_energy_mev=bridge_mev,
    )
    tau_mass_imprint = dbi.weak_half_life_geometric_ledger(
        ref.A,
        ref.Z,
        env,
        base,
        cluster_mass_imprint=kappa_mass,
        proton_mass_mev_for_well=p_ref,
        neutron_mass_mev_for_well=n_ref,
        local_curvature_width_factor=width_central,
        lab_temperature_factor=support,
        neutrino_mass_mev=nu_mev,
        weak_bridge_energy_mev=bridge_mev,
    )

    exponent = float(valley + 1) if valley > 0 else 1.0
    kappa_width_well = (tau_ref / tau_mass_imprint) ** (1.0 / exponent) if tau_mass_imprint > 0 else math.nan
    tau_closed = dbi.weak_half_life_geometric_ledger(
        ref.A,
        ref.Z,
        env,
        base,
        cluster_mass_imprint=kappa_mass * kappa_width_well,
        proton_mass_mev_for_well=p_ref,
        neutron_mass_mev_for_well=n_ref,
        local_curvature_width_factor=width_central,
        lab_temperature_factor=support,
        neutrino_mass_mev=nu_mev,
        weak_bridge_energy_mev=bridge_mev,
    )

    daughter_key = dbi.BETA_MINUS_DAUGHTERS.get((ref.A, ref.Z))
    q_atomic = None
    q_imprinted = None
    kappa_daughter = None
    if daughter_key is not None:
        _, z_d = daughter_key
        refs = reference_map()
        parent_ref = ref.nuclear_mass_mev
        d_ref = refs[(ref.A, z_d)].nuclear_mass_mev
        m_der_d = dbi.isotope_mass_budget(ref.A, z_d, pair)
        kappa_daughter = d_ref / m_der_d if m_der_d > 0.0 else math.nan
        q_atomic = dbi.beta_minus_endpoint_q_atomic(parent_ref, d_ref)
        q_imprinted = (
            kappa_mass * m_der - kappa_daughter * m_der_d - dbi.model_electron_mass_mev()
        )
    q_nucleon_gap = base.beta_minus_endpoint_q_mev

    return {
        "label": ref.label,
        "A": ref.A,
        "Z": ref.Z,
        "derived_mass_mev": m_der,
        "reference_mass_mev": ref.nuclear_mass_mev,
        "kappa_mass": kappa_mass,
        "mass_imprint_ppm": (kappa_mass - 1.0) * 1.0e6,
        "pdg_nucleon_masses_in_geometric_well": {"proton_mev": p_ref, "neutron_mev": n_ref},
        "endpoint_q_nucleon_gap_mev": q_nucleon_gap,
        "endpoint_q_atomic_mev": q_atomic,
        "endpoint_q_with_per_isotope_mass_imprint_mev": q_imprinted,
        "kappa_mass_daughter": kappa_daughter,
        "endpoint_q_policy": (
            "HQIV width ledger uses nucleon-gap Q (≈782 keV for T→He3): parent and daughter "
            "share the same derived ΔM so Qβ− = ΔM − m_e. Applying each isotope's own "
            "κ_mass = M_ref/M_derived to the mass budget moves Q to the atomic table slot "
            "(≈18.5 keV for tritium) without a separate atomic input. Uniform κ on both "
            "isotopes preserves the nucleon gap. Geometric-mean interior well depth is a "
            "separate width-ledger factor (κ_width_well)."
        ),
        "valley_exponent": valley + 1,
        "half_life_derived_seconds": tau_der,
        "half_life_reference_seconds": tau_ref,
        "tau_ratio_derived_over_ref": tau_der / tau_ref if tau_ref else math.nan,
        "half_life_pdg_nucleons_geometric_well_seconds": tau_pdg_nucleons,
        "half_life_mass_imprint_seconds": tau_mass_imprint,
        "tau_ratio_mass_imprint_over_ref": tau_mass_imprint / tau_ref if tau_ref else math.nan,
        "kappa_width_well_on_cluster": kappa_width_well,
        "width_imprint_ppm": (kappa_width_well - 1.0) * 1.0e6,
        "half_life_closed_seconds": tau_closed,
        "tau_ratio_closed_over_ref": tau_closed / tau_ref if tau_ref else math.nan,
        "use_for_other_calculations": {
            "mass_ledger": "multiply isotope mass readout by kappa_mass",
            "width_ledger": "multiply cluster caustic depth by kappa_mass * kappa_width_well_on_cluster",
            "note": (
                "kappa_mass comes from PDG/CODATA mass closure; kappa_width_well closes the "
                "decay clock with the same geometric-mean interior well and PDG nucleon masses "
                "in the blend. Not fed back into HQIV fit rows."
            ),
        },
    }


def curvature_imprint_control_panel(
    *,
    qualify_em_tipping: bool,
    xi: float,
    lab_temperature_K: float,
    neutrino_mass_mev: float | None,
) -> list[dict]:
    rows: list[dict] = []
    for label in ("n", "T"):
        ref = reference_by_label(label)
        row = curvature_imprint_control_row(
            ref,
            qualify_em_tipping=qualify_em_tipping,
            xi=xi,
            lab_temperature_K=lab_temperature_K,
            neutrino_mass_mev=neutrino_mass_mev,
        )
        if row is not None:
            rows.append(row)
    return rows


def benchmark_row(
    ref: ReferenceIsotope,
    *,
    qualify_em_tipping: bool,
    xi: float,
    lab_temperature_K: float,
    neutrino_mass_mev: float | None,
) -> BenchmarkRow:
    pred_mass = predicted_mass_for_reference(ref, xi=xi)
    mass_error = pred_mass - ref.nuclear_mass_mev
    mass_error_pct = mass_error / ref.nuclear_mass_mev * 100.0
    stability = ish.stability_readout(
        ref.A,
        ref.Z,
        xi=xi,
        label=ref.label,
        em_tipping_qualified=qualify_em_tipping,
        lab_temperature_K=lab_temperature_K,
        neutrino_mass_mev=neutrino_mass_mev,
    )
    ratio = None
    if ref.half_life_seconds is not None and stability.half_life_seconds is not None:
        ratio = stability.half_life_seconds / ref.half_life_seconds
    return BenchmarkRow(
        label=ref.label,
        A=ref.A,
        Z=ref.Z,
        reference_mass_mev=ref.nuclear_mass_mev,
        predicted_mass_mev=pred_mass,
        mass_error_mev=mass_error,
        mass_error_pct=mass_error_pct,
        reference_stability=ref.stability,
        predicted_structurally_shielded=stability.structurally_shielded,
        predicted_stable_qualified=stability.dynamically_stable,
        predicted_channel=stability.active_channel,
        reference_half_life_seconds=ref.half_life_seconds,
        predicted_half_life_seconds=stability.half_life_seconds,
        half_life_ratio_pred_over_ref=ratio,
        notes=stability.notes,
    )


def neutron_lifetime_temperature_sweep(*, qualify_em_tipping: bool, neutrino_mass_mev: float | None) -> list[dict]:
    out = []
    for temp in (ish.CMB_TEMPERATURE_K, 4.0, 77.0, 300.0):
        row = ish.stability_readout(
            1,
            0,
            label="n",
            em_tipping_qualified=qualify_em_tipping,
            lab_temperature_K=temp,
            neutrino_mass_mev=neutrino_mass_mev,
        )
        out.append(
            {
                "lab_temperature_K": temp,
                "lab_gravity_phi_epsilon": row.lab_gravity_phi_epsilon,
                "outside_gravity_factor": row.lab_outside_gravity_factor,
                "outside_support_factor": row.lab_outside_curvature_factor,
                "predicted_half_life_seconds": row.half_life_seconds,
            }
        )
    return out


def neutron_lifetime_reference_comparison(
    *, qualify_em_tipping: bool, neutrino_mass_mev: float | None
) -> list[dict]:
    out = []
    for ref in NEUTRON_LIFETIME_REFERENCES:
        row = ish.stability_readout(
            1,
            0,
            label="n",
            em_tipping_qualified=qualify_em_tipping,
            lab_temperature_K=ref.lab_temperature_K,
            neutrino_mass_mev=neutrino_mass_mev,
        )
        ratio = None
        if row.half_life_seconds is not None:
            ratio = row.half_life_seconds / ref.half_life_seconds
        out.append(
            {
                "method": ref.method,
                "reference_half_life_seconds": ref.half_life_seconds,
                "lab_temperature_K": ref.lab_temperature_K,
                "lab_gravity_phi_epsilon": row.lab_gravity_phi_epsilon,
                "outside_gravity_factor": row.lab_outside_gravity_factor,
                "outside_support_factor": row.lab_outside_curvature_factor,
                "predicted_half_life_seconds": row.half_life_seconds,
                "pred_over_ref": ratio,
                "source": ref.source,
            }
        )
    return out


def build_payload(
    *,
    qualify_em_tipping: bool = False,
    xi: float = notd.XI_LOCKIN,
    lab_temperature_K: float = ish.CMB_TEMPERATURE_K,
    neutrino_mass_mev: float | None = None,
) -> dict:
    rows = [
        benchmark_row(
            ref,
            qualify_em_tipping=qualify_em_tipping,
            xi=xi,
            lab_temperature_K=lab_temperature_K,
            neutrino_mass_mev=neutrino_mass_mev,
        )
        for ref in REFERENCE_ISOTOPES
    ]
    abs_mass = [abs(r.mass_error_pct) for r in rows]
    return {
        "source": "scripts/hqiv_isotope_pdg_benchmark.py",
        "comparison_policy": "reference isotope data used only for benchmark, not for HQIV fit",
        "em_tipping_qualified": qualify_em_tipping,
        "xi": xi,
        "lab_temperature_K": lab_temperature_K,
        "neutrino_mass_mev": ish.model_electron_neutrino_mass_mev()
        if neutrino_mass_mev is None
        else neutrino_mass_mev,
        "rows": [asdict(r) for r in rows],
        "neutron_lifetime_temperature_sweep": neutron_lifetime_temperature_sweep(
            qualify_em_tipping=qualify_em_tipping,
            neutrino_mass_mev=neutrino_mass_mev,
        ),
        "neutron_lifetime_reference_comparison": neutron_lifetime_reference_comparison(
            qualify_em_tipping=qualify_em_tipping,
            neutrino_mass_mev=neutrino_mass_mev,
        ),
        "neutron_method_environment_ledger": neutron_method_environment_ledger(
            qualify_em_tipping=qualify_em_tipping,
            neutrino_mass_mev=neutrino_mass_mev,
        ),
        "neutron_width_ledger_comparison": neutron_width_ledger_comparison(
            qualify_em_tipping=qualify_em_tipping,
            neutrino_mass_mev=neutrino_mass_mev,
        ),
        "isotope_method_tension_panel": isotope_method_tension_panel(),
        "curvature_imprint_control": curvature_imprint_control_panel(
            qualify_em_tipping=qualify_em_tipping,
            xi=xi,
            lab_temperature_K=lab_temperature_K,
            neutrino_mass_mev=neutrino_mass_mev,
        ),
        "summary": {
            "count": len(rows),
            "mean_abs_mass_error_pct": sum(abs_mass) / len(abs_mass),
            "max_abs_mass_error_pct": max(abs_mass),
        },
    }


def print_report(payload: dict) -> None:
    print("HQIV isotope benchmark vs reference data")
    print("=" * 84)
    print(f"EM tipping qualified: {payload['em_tipping_qualified']}")
    print(f"lab temperature for half-life: {payload['lab_temperature_K']} K")
    print(f"electron neutrino mass in β phase space: {payload['neutrino_mass_mev']:.6g} MeV")
    print(f"{'iso':<5} {'A':>2} {'Z':>2} {'pred MeV':>12} {'ref MeV':>12} {'err %':>9} {'chan':>12} {'t1/2 pred/ref':>16}")
    for row in payload["rows"]:
        ratio = row["half_life_ratio_pred_over_ref"]
        ratio_str = "-" if ratio is None else f"{ratio:.3g}"
        print(
            f"{row['label']:<5} {row['A']:>2} {row['Z']:>2} "
            f"{row['predicted_mass_mev']:12.3f} {row['reference_mass_mev']:12.3f} "
            f"{row['mass_error_pct']:9.3f} {row['predicted_channel']:>12} {ratio_str:>16}"
        )
    s = payload["summary"]
    print()
    print(
        f"Summary: n={s['count']} mean|mass err|={s['mean_abs_mass_error_pct']:.3f}% "
        f"max|mass err|={s['max_abs_mass_error_pct']:.3f}%"
    )
    if payload["em_tipping_qualified"]:
        print()
        print("neutron lifetime temperature sweep")
        for row in payload["neutron_lifetime_temperature_sweep"]:
            print(
                f"  T={row['lab_temperature_K']:8.3f} K  "
                f"factor={row['outside_support_factor']:.9f}  "
                f"t1/2={row['predicted_half_life_seconds']:.6g} s"
            )
        print()
        print("neutron width ledger (preferred accuracy unit @ 300 K)")
        w = payload.get("neutron_width_ledger_comparison", {})
        pdg = w.get("pdg_codata", {})
        if pdg:
            band = w.get("predicted_half_life_seconds_band", {})
            wf = w.get("local_curvature_weak_width_factor_band", {})
            print(
                f"  nu_opacity={w.get('local_curvature_neutrino_opacity_barn', 0):.3e} barn  "
                f"width×={wf.get('central', 1):.4f} "
                f"({wf.get('low', 1):.4f}–{wf.get('high', 1):.4f})"
            )
            print(
                f"  Q_phase={w.get('q_phase_mev', 0):.4f} MeV  "
                f"Gamma_ref/Gamma_pred={pdg.get('gamma_ref_over_pred', 0):.4f}  "
                f"delta_Q={pdg.get('delta_q_phase_keV', 0):.2f} keV "
                f"({100 * pdg.get('delta_q_phase_fraction', 0):.2f}% of Q_phase)"
            )
            print(
                f"  tau_pred={w.get('predicted_half_life_seconds', 0):.3f} s  "
                f"band={band.get('low', 0):.1f}–{band.get('high', 0):.1f} s  "
                f"tau_pred/tau_pdg={pdg.get('tau_pred_over_ref', 0):.3f}"
            )
        print()
        print("neutron bottle vs beam (interpretive ledger)")
        for row in payload.get("neutron_method_environment_ledger", []):
            if row.get("comparison"):
                if "ppm_delta_tau" in row:
                    print(f"  {row['comparison']}: ppm Δτ={row['ppm_delta_tau']:.1f}  ({row['note']})")
                elif "predicted_beam_over_bottle_split_ppm" in row:
                    print(
                        f"  {row['comparison']}: predicted beam/bottle "
                        f"ppm={row['predicted_beam_over_bottle_split_ppm']:.1f}, "
                        f"observed ppm={row['observed_beam_over_bottle_split_ppm']:.1f}"
                    )
                else:
                    print(f"  {row['comparison']}: {row.get('note', '')}")
            else:
                print(
                    f"  {row['method']:<6} ref={row['reference_half_life_seconds']:.2f}s "
                    f"pred/ref={row['pred_over_ref']:.3f}  T={row['lab_temperature_K']} K"
                )
        print()
        print("isotope method tension panel")
        for row in payload.get("isotope_method_tension_panel", []):
            if row.get("comparison"):
                print(f"  {row['comparison']}: {row['note']}")
                continue
            print(
                f"  {row['isotope']:<4} {row['environment']:<22} "
                f"width={row['local_width_factor']:.9f} "
                f"shift={row['method_shift_percent']:+.4f}%"
            )
        print()
        print("curvature imprint control (PDG mass + geometric well; comparison layer)")
        for row in payload.get("curvature_imprint_control", []):
            print(
                f"  {row['label']:<2} kappa_mass={row['kappa_mass']:.6f} "
                f"tau_der/ref={row['tau_ratio_derived_over_ref']:.3f} "
                f"tau_mass_imprint/ref={row['tau_ratio_mass_imprint_over_ref']:.3f} "
                f"kappa_width_well={row['kappa_width_well_on_cluster']:.4f} "
                f"tau_closed/ref={row['tau_ratio_closed_over_ref']:.3f}"
            )
            print(f"      Q_nucleon_gap={row['endpoint_q_nucleon_gap_mev']:.4f} MeV  "
                  f"Q_atomic={row.get('endpoint_q_atomic_mev', 0)*1000:.2f} keV  "
                  f"Q_imprint={row.get('endpoint_q_with_per_isotope_mass_imprint_mev', 0)*1000:.2f} keV")


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV isotope benchmark vs reference data")
    parser.add_argument("--qualify-em-tipping", action="store_true")
    parser.add_argument("--lab-temperature-K", type=float, default=ish.CMB_TEMPERATURE_K)
    parser.add_argument("--neutrino-mass-mev", type=float, default=None)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    payload = build_payload(
        qualify_em_tipping=args.qualify_em_tipping,
        lab_temperature_K=args.lab_temperature_K,
        neutrino_mass_mev=args.neutrino_mass_mev,
    )
    print_report(payload)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()
