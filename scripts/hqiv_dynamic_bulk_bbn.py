#!/usr/bin/env python3
"""
HQIV dynamic bulk matter + BBN — per-shell integrator (v3).

Evolves QCD -> emergent lock-in as a discrete shell integrator:

- Inside/outside curvature and effective temperatures at each shell
- Dynamic vev / mass scale from inner--outer Casimir balance (Lean-aligned)
- Dynamic nuclear Q from inside/outside cluster binding (nucleon-binding paper)
- Incremental Omega_m / Omega_b accumulation (no window averages)
- Emergent lock-in event from inside/outside closure residual
- BBN cooling network with per-step dynamic Q values and shell opportunity

Physics primitives mirror Lean via ``hqiv_lean_physics_primitives``.
Legacy eta_paper (6.10e-10) appears only in the comparison branch.

Run:
  python3 scripts/hqiv_dynamic_bulk_bbn.py
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Callable

import hqiv_bbn_abundances as bbn
import hqiv_bbn_epoch_network as epoch_net
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_nuclear_outside_temperature_dynamics as nuclear

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "dynamic_bulk_bbn_v2.json"

ALPHA = lean.ALPHA
GAMMA = lean.GAMMA
QCD_SHELL = lean.QCD_SHELL
REFERENCE_M = lean.REFERENCE_M
PROTON_ANCHOR_MEV = 938.272
T13_OUTER_MODE_COUNT = lean.T13_OUTER_MODE_COUNT
XI_LOCKIN_LEAN = lean.XI_LOCKIN
STRONG_CHANNEL_FRACTION = lean.STRONG_CHANNEL_FRACTION
COLOR_SINGLET_FRACTION = 1.0 / 3.0
RADIATION_FLOOR = 1.0
MAX_SHELL_SCAN = 32

LEGACY_ETA_PAPER = lean.ETA_PAPER
DEFAULT_H0_KM_S_MPC = 67.4
T_CMB_K = 2.7255
ZETA_3 = 1.202056903159594
G_SI = 6.67430e-11
C_SI = 299_792_458.0
HBAR_SI = 1.054571817e-34
K_B_SI = 1.380649e-23
MPC_M = 3.0856775814913673e22
MEV_C2_KG = 1.7826619216278976e-30
# Binding curvature feedback is now derived in the Lean side
# (bbn_binding_curvature_efficiency = gamma * strong * bounded_slope).
# No separate BINDING_CURVATURE_KAPPA or CURV_CLOSURE_WEIGHT knobs remain
# for the core dynamic opportunity path.
CURVATURE_SEED_IMPRINT_SCALE = ALPHA * GAMMA * (1.0 + GAMMA + ALPHA)  # still used for early seed; review later


# ---------------------------------------------------------------------------
# Curvature / Casimir primitives (hqiv_lean_physics_primitives)
# ---------------------------------------------------------------------------

curvature_density = lean.curvature_density
shell_shape = lean.shell_shape
omega_k_at_xi = lean.omega_k_xi
t13_outer_suppression_at_xi = lean.t13_outer_suppression_at_xi
effective_casimir_scale_at_xi = lean.effective_casimir_scale_at_xi
heavy_lepton_gap_at_xi = lean.heavy_lepton_gap_at_xi
tuft_vev_factor_at_xi = lean.tuft_vev_factor_at_xi
eta_at_horizon = lean.eta_at_horizon
eta_at_horizon_dynamic = lean.eta_at_horizon_dynamic
xi_from_T_MeV = lean.xi_from_T_MeV
bbn_binding_release_factor = lean.bbn_binding_release_factor
bbn_shell_reaction_opportunity = lean.bbn_shell_reaction_opportunity


def effective_inside_temperature(xi: float) -> float:
    t_bg = 1.0 / xi
    trap = lean.trapping_selection_heavy(lean.ALPHA_HEAVY, omega_k_at_xi(xi))
    return t_bg / max(trap, 1e-30)


def effective_outside_temperature(xi: float) -> float:
    return (1.0 / xi) * t13_outer_suppression_at_xi(xi)


def inside_curvature_proxy(xi: float) -> float:
    trap = lean.trapping_selection_heavy(lean.ALPHA_HEAVY, omega_k_at_xi(xi))
    return shell_shape(int(xi) - 1) * trap


def outside_curvature_proxy(xi: float) -> float:
    return shell_shape(int(xi) - 1) * t13_outer_suppression_at_xi(xi)


def closed_curvature_balance(xi: float, xi_ref: float = XI_LOCKIN_LEAN) -> float:
    scale_ref = effective_casimir_scale_at_xi(xi_ref)
    scale = effective_casimir_scale_at_xi(xi) / max(scale_ref, 1e-30)
    return math.log(max(scale, 1e-30))


def dynamic_proton_mass_mev(xi: float) -> float:
    g = heavy_lepton_gap_at_xi(xi)
    g0 = heavy_lepton_gap_at_xi(XI_LOCKIN_LEAN)
    return PROTON_ANCHOR_MEV * (g / g0) if g0 > 0.0 else PROTON_ANCHOR_MEV


def dynamic_binding_q_at_shell(m: int, m_p: float, xi: float, xi_lock: float) -> tuple[float, float, float]:
    """Nuclear ledger shape at ξ; amplitudes anchored to lock-in valley witness."""
    return nuclear.binding_q_hybrid_at_xi(m, m_p, xi, xi_lock=xi_lock)


def dynamic_delta_m_mev(m: int, m_p: float, xi: float, xi_lock: float) -> float:
    """n-p gap scaled with dynamic proton mass at xi."""
    dm_anchor = float(bbn.load_witness().get("derivedDeltaM_MeV", 1.293))
    scale = dynamic_proton_mass_mev(xi) / PROTON_ANCHOR_MEV
    return dm_anchor * scale


# ---------------------------------------------------------------------------
# Per-shell integrator state
# ---------------------------------------------------------------------------


@dataclass
class DynamicShellStep:
    m: int
    xi: float
    shell_shape: float
    inside_curvature: float
    outside_curvature: float
    closure_residual: float
    omega_k_chart: float
    curvature_budget: float
    B_local_global: float
    curvature_seed_increment: float
    nuclear_cluster_binding_mev: float
    nuclear_binding_ratio_to_lockin: float
    vev_scale: float
    proton_mass_MeV: float
    Q_D_MeV: float
    Q_4He_MeV: float
    Q_3He_MeV: float
    delta_m_MeV: float
    binding_feedback: float
    source_increment: float
    cumulative_source: float
    omega_m: float
    omega_b: float
    is_lockin_event: bool = False


@dataclass
class DynamicShellIntegratorResult:
    xi_lock: float
    m_lock: int
    lockin_closure_residual: float
    lockin_vev_scale: float
    pre_hadronic_m: int
    pre_hadronic_xi: float
    pre_hadronic_closure_residual: float
    total_matter_fraction: float
    baryon_matter_fraction: float
    dark_matter_like_fraction: float
    final_cumulative_source: float
    steps: list[DynamicShellStep] = field(default_factory=list)


def find_hadronic_lockin_shell() -> tuple[int, float, float]:
    """Proton-anchor hadronic lock (referenceM); inner--outer Casimir at that shell."""
    m = REFERENCE_M
    xi = float(m + 1)
    return m, xi, closed_curvature_balance(xi)


def find_pre_hadronic_closure_shell() -> tuple[int, float, float]:
    """Best pre-hadronic Casimir closure before the proton anchor shell."""
    if REFERENCE_M <= QCD_SHELL:
        m = QCD_SHELL
        xi = float(m + 1)
        return m, xi, closed_curvature_balance(xi)
    best_m = QCD_SHELL
    best_abs = float("inf")
    best_residual = 0.0
    for m in range(QCD_SHELL, REFERENCE_M):
        xi = float(m + 1)
        residual = closed_curvature_balance(xi)
        mag = abs(residual)
        if mag < best_abs:
            best_abs = mag
            best_m = m
            best_residual = residual
    return best_m, float(best_m + 1), best_residual


def evolve_shell_integrator(
    *,
    m_start: int = QCD_SHELL,
    m_end: int | None = None,
    extend_to_anchor: bool = False,
) -> DynamicShellIntegratorResult:
    """
    Step integrator: accumulate matter and Q values shell-by-shell until
    emergent lock-in. By default evolution stops at ``m_lock``; set
    ``extend_to_anchor=True`` to continue through ``referenceM`` for witness
    comparison only (final Omega uses the lock-in step).
    """
    m_lock, xi_lock, lock_residual = find_hadronic_lockin_shell()
    pre_m, pre_xi, pre_res = find_pre_hadronic_closure_shell()
    if m_end is None:
        m_end = max(m_lock, REFERENCE_M) if extend_to_anchor else m_lock

    steps: list[DynamicShellStep] = []
    cumulative_baryon = 0.0
    cumulative_curvature_seed = 0.0
    lockin_recorded = False
    lockin_step: DynamicShellStep | None = None

    for m in range(m_start, m_end + 1):
        xi = float(m + 1)
        sh = shell_shape(m)
        inside = inside_curvature_proxy(xi)
        outside = outside_curvature_proxy(xi)
        residual = closed_curvature_balance(xi)
        omega_chart = omega_k_at_xi(xi)
        vev_factor = tuft_vev_factor_at_xi(xi)
        m_p = dynamic_proton_mass_mev(xi)
        Q_D, Q_4, Q_3 = dynamic_binding_q_at_shell(m, m_p, xi, xi_lock)
        dm = dynamic_delta_m_mev(m, m_p, xi, xi_lock)
        nuc_row = nuclear.shell_nuclear_binding_row(m, xi, xi_lock=xi_lock)
        own_bind = nuclear.nucleon_own_binding_mev(m, xi, bonded=True)
        own_bind_lock = nuclear.nucleon_own_binding_mev(m_lock, xi_lock, bonded=True)

        total_content_prev = cumulative_baryon + cumulative_curvature_seed + RADIATION_FLOOR
        omega_m_prev = (
            GAMMA * cumulative_baryon / max(total_content_prev, 1e-30)
            if steps
            else 0.0
        )
        B_local_global = lean.curvature_budget_local_global_at_xi(xi, xi_lock)
        shell_seed_budget = lean.curvature_budget_at_shell(
            m,
            m_lock=m_lock,
            m_start=m_start,
            xi=xi,
            omega_m_fraction=omega_m_prev,
        )
        # Combined: early pair/radiation seed × Casimir local/global (→1 at lock-in).
        curvature_budget = shell_seed_budget * B_local_global
        seed_excess = lean.curvature_seed_excess(curvature_budget)

        # Outside-modulated own binding: only sub-lock-in weakening feeds back (no super-lock boost).
        bind_ratio = min(own_bind / max(own_bind_lock, 1e-30), 1.0)
        binding_feedback = STRONG_CHANNEL_FRACTION * bind_ratio * vev_factor
        baryon_inc = sh * vev_factor + binding_feedback
        seed_inc = sh * vev_factor * CURVATURE_SEED_IMPRINT_SCALE * seed_excess
        if B_local_global < 1.0:
            seed_inc *= 1.0 + GAMMA * (1.0 / B_local_global - 1.0)
        cumulative_baryon += baryon_inc
        cumulative_curvature_seed += seed_inc

        total_content = cumulative_baryon + cumulative_curvature_seed + RADIATION_FLOOR
        omega_m = GAMMA * cumulative_baryon / max(total_content, 1e-30)
        omega_b = omega_m * STRONG_CHANNEL_FRACTION * COLOR_SINGLET_FRACTION

        is_lock = (m == m_lock) and not lockin_recorded
        if is_lock:
            lockin_recorded = True

        step = DynamicShellStep(
            m=m,
            xi=xi,
            shell_shape=sh,
            inside_curvature=inside,
            outside_curvature=outside,
            closure_residual=residual,
            omega_k_chart=omega_chart,
            curvature_budget=curvature_budget,
            B_local_global=B_local_global,
            curvature_seed_increment=seed_inc,
            nuclear_cluster_binding_mev=float(nuc_row["cluster_binding_mev"]),
            nuclear_binding_ratio_to_lockin=bind_ratio,
            vev_scale=vev_factor,
            proton_mass_MeV=m_p,
            Q_D_MeV=Q_D,
            Q_4He_MeV=Q_4,
            Q_3He_MeV=Q_3,
            delta_m_MeV=dm,
            binding_feedback=binding_feedback,
            source_increment=baryon_inc + seed_inc,
            cumulative_source=cumulative_baryon + cumulative_curvature_seed,
            omega_m=omega_m,
            omega_b=omega_b,
            is_lockin_event=is_lock,
        )
        steps.append(step)
        if is_lock:
            lockin_step = step

    final = lockin_step if lockin_step is not None else steps[-1]
    return DynamicShellIntegratorResult(
        xi_lock=xi_lock,
        m_lock=m_lock,
        lockin_closure_residual=lock_residual,
        lockin_vev_scale=tuft_vev_factor_at_xi(xi_lock),
        pre_hadronic_m=pre_m,
        pre_hadronic_xi=pre_xi,
        pre_hadronic_closure_residual=pre_res,
        total_matter_fraction=final.omega_m,
        baryon_matter_fraction=final.omega_b,
        dark_matter_like_fraction=max(0.0, final.omega_m - final.omega_b),
        final_cumulative_source=final.cumulative_source,
        steps=steps,
    )


# ---------------------------------------------------------------------------
# Comparison layer: Omega_b -> eta
# ---------------------------------------------------------------------------


def photon_number_density_m3(T_kelvin: float = T_CMB_K) -> float:
    return (2.0 * ZETA_3 / (math.pi**2)) * ((K_B_SI * T_kelvin) / (HBAR_SI * C_SI)) ** 3


def critical_density_kg_m3(H0_km_s_mpc: float) -> float:
    H0_s = H0_km_s_mpc * 1000.0 / MPC_M
    return 3.0 * H0_s * H0_s / (8.0 * math.pi * G_SI)


def eta_from_omega_b(omega_b: float, H0_km_s_mpc: float, T_kelvin: float = T_CMB_K) -> dict[str, float]:
    rho_crit = critical_density_kg_m3(H0_km_s_mpc)
    m_p = PROTON_ANCHOR_MEV * MEV_C2_KG
    n_b = omega_b * rho_crit / m_p
    n_gamma = photon_number_density_m3(T_kelvin)
    eta = n_b / n_gamma
    h = H0_km_s_mpc / 100.0
    return {
        "eta": eta,
        "eta10": eta * 1.0e10,
        "Omega_b_h2": omega_b * h * h,
        "n_b_m3": n_b,
        "n_gamma_m3": n_gamma,
        "rho_crit_kg_m3": rho_crit,
        "H0_km_s_Mpc": H0_km_s_mpc,
        "T_CMB_K": T_kelvin,
    }


# ---------------------------------------------------------------------------
# Dynamic BBN with per-step Q / shell-opportunity providers
# ---------------------------------------------------------------------------


def curvature_temperature_binding_factor(
    T_MeV: float,
    integrator: DynamicShellIntegratorResult,
) -> dict[str, float]:
    """Lean `bbnBindingReleaseFactor` and slope ingredients."""
    xi_epoch = xi_from_T_MeV(T_MeV)
    xi_lock = integrator.xi_lock
    slope = lean.bbn_curvature_temperature_slope(T_MeV, xi_lock)
    bounded = lean.bbn_bounded_curvature_temperature_slope(T_MeV, xi_lock)
    release_exponent = GAMMA * STRONG_CHANNEL_FRACTION * bounded
    binding_factor = bbn_binding_release_factor(T_MeV, xi_lock)
    return {
        "T_MeV": T_MeV,
        "xi_epoch": xi_epoch,
        "xi_lock": xi_lock,
        "omega_lock": omega_k_at_xi(xi_lock),
        "omega_epoch": omega_k_at_xi(xi_epoch),
        "log_temperature_gap": max(math.log(max(xi_epoch / xi_lock, 1.0)), 1e-30),
        "curvature_per_log_temperature": slope,
        "bounded_curvature_temperature_slope": bounded,
        "release_exponent": release_exponent,
        "binding_factor": binding_factor,
    }


def bbn_binding_curvature_perturbation(
    T_MeV: float,
    eta: float,
    integrator: DynamicShellIntegratorResult,
) -> float:
    """Derived version (matches Lean bbn_binding_curvature_perturbation).
    Efficiency = GAMMA * STRONG * bounded_slope; no free kappa.
    """
    bounded = lean.bbn_bounded_curvature_temperature_slope(T_MeV)
    efficiency = GAMMA * STRONG_CHANNEL_FRACTION * bounded
    lock_step = next((s for s in integrator.steps if s.is_lockin_event), integrator.steps[-1])
    binding_factor = curvature_temperature_binding_factor(T_MeV, integrator)["binding_factor"]
    binding_per_baryon = lock_step.Q_4He_MeV * binding_factor * 0.25
    return efficiency * max(0.0, binding_per_baryon / max(T_MeV, 1e-9))


def make_dynamic_bbn_providers(
    integrator: DynamicShellIntegratorResult,
) -> tuple[
    Callable[[float], tuple[float, ...]],
    Callable[[float, float, float], dict[str, Any]],
]:
    """Q values and shell reaction opportunity from lock-in dynamics + epoch temperature."""
    lock_step = next((s for s in integrator.steps if s.is_lockin_event), integrator.steps[-1])

    def q_provider(T_MeV: float) -> tuple[float, float, float, float]:
        xi_epoch = xi_from_T_MeV(T_MeV)
        m_p = dynamic_proton_mass_mev(integrator.xi_lock)
        dm = dynamic_delta_m_mev(integrator.m_lock, m_p, xi_epoch, integrator.xi_lock)
        Q_D, Q_4, Q_3 = dynamic_binding_q_at_shell(
            integrator.m_lock, m_p, xi_epoch, integrator.xi_lock
        )
        Q_7 = bbn.be7_binding_q(Q_4, m_shell=integrator.m_lock, m_nucleon=m_p)
        Q_li = bbn.li7_cluster_binding_q(m_shell=integrator.m_lock, m_nucleon=m_p)
        return dm, Q_D, Q_3, Q_4, Q_7, Q_li

    def opportunity_provider(T_MeV: float, T_next_MeV: float, eta: float) -> dict[str, Any]:
        base = bbn_shell_reaction_opportunity(T_MeV, T_next_MeV, integrator.xi_lock)
        delta = bbn_binding_curvature_perturbation(T_MeV, eta, integrator)
        c2_sup = lean.bbn_dynamic_c2_opportunity_suppression(
            T_MeV, eta=eta, m_nucleon=lock_step.proton_mass_MeV
        )
        xi_epoch = xi_from_T_MeV(T_MeV)
        c2_row = lean.bbn_dynamic_c2_readout_at_T(
            T_MeV, eta=eta, m_nucleon=lock_step.proton_mass_MeV
        )
        return {
            "mode": "shell_curvature_casimir_dynamic_C2",
            "reaction_opportunity": base * (1.0 + delta / 4.0) * c2_sup,
            "base_reaction_opportunity": base,
            "dynamic_C2_suppression": c2_sup,
            "log_shell_step": max(math.log(max(xi_from_T_MeV(T_next_MeV) / xi_epoch, 1.0)), 0.0),
            "log_lock_gap": max(math.log(max(xi_epoch / integrator.xi_lock, 1.0)), 0.0),
            "omega_k_epoch": omega_k_at_xi(xi_epoch),
            "curvature_opportunity_factor": lean.bbn_curvature_opportunity_factor(T_MeV),
            "C2": c2_row["C2"],
            "kappa6_over_ref": c2_row["kappa6_over_kappa6_ref"],
            "binding_curvature_delta": delta,
            "H_s_diagnostic_unperturbed": epoch_net.hubble_rate_s(T_MeV),
        }

    return q_provider, opportunity_provider


def lean_literal_q_values_at_T(
    T_MeV: float,
    lock_step: DynamicShellStep,
) -> dict[str, float]:
    """Literal Lean `*_at_xi` scaling with xi = T_Pl_MeV / T_MeV."""
    xi = bbn.T_PL_MEV / T_MeV
    factor = tuft_vev_factor_at_xi(xi)
    return {
        "T_MeV": T_MeV,
        "xi": xi,
        "tuft_vev_factor": factor,
        "delta_m_MeV": lock_step.delta_m_MeV * factor,
        "Q_D_MeV": lock_step.Q_D_MeV * factor,
        "Q_4He_MeV": lock_step.Q_4He_MeV * factor,
        "Q_3He_MeV": lock_step.Q_3He_MeV * factor,
    }


def lean_math_comparison(integrator: DynamicShellIntegratorResult) -> dict[str, Any]:
    """Compare calculator choices to executable Lean-side formulas."""
    lock_step = next((s for s in integrator.steps if s.is_lockin_event), integrator.steps[-1])
    shell_rows = []
    for m in range(QCD_SHELL, REFERENCE_M + 1):
        xi = float(m + 1)
        shell_rows.append(
            {
                "m": m,
                "xi": xi,
                "omegaK_xi_lean": omega_k_at_xi(xi),
                "effective_casimir_scale_at_xi": effective_casimir_scale_at_xi(xi),
                "heavy_lepton_gap_at_xi": heavy_lepton_gap_at_xi(xi),
                "tuft_vev_factor_at_xi": tuft_vev_factor_at_xi(xi),
            }
        )
    bbn_temperatures = [1.0, bbn.BBN_T_MID_MEV, bbn.BBN_T_LOW_MEV]
    return {
        "lean_modules_checked": [
            "Hqiv.Physics.ContinuousXiPath.omegaK_xi",
            "Hqiv.Physics.HopfShellBeltramiMassBridge.effective_casimir_scale_at_xi",
            "Hqiv.Physics.HopfShellBeltramiMassBridge.heavy_lepton_gap_at_xi",
            "Hqiv.Physics.HopfShellBeltramiMassBridge.tuftVevAtXi_MeV",
            "Hqiv.Physics.NuclearCurvatureBinding.nuclearClusterBindingCurvature",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics.nuclearClusterBindingAtXi",
            "Hqiv.Physics.NuclearOutsideTemperatureDynamics.localCurvatureNeutrinoOpacityBarn",
            "Hqiv.Physics.DynamicBBNBaryogenesis.bbnBindingReleaseFactor",
        ],
        "agreements_after_update": [
            "omegaK_xi is epoch-vs-lock-in chart ratio (diagnostic for seed amplitude).",
            "curvature_budget_at_shell: early pair/radiation seed, relaxes to 1 at lock-in.",
            "curvature seed imprint accumulates outside baryon track (lowers final Omega_b/eta).",
            "B_curv(ξ): Casimir gap (d∝1/ξ) on shell ladder; nuclear outside modulator at BBN ξ.",
            "κ₆ matter slot uses curvature_budget_at_xi (not ω_K chart ratio).",
            "heavy_lepton_gap_at_xi includes the explicit xi/5 temperature factor.",
            "tuft vev factor is heavy_lepton_gap_at_xi / heavy_lepton_gap_at_xi(5).",
            "t13_outer_suppression_at_xi matches Lean: ωK(ξ)/140, recovers 1/140 at ξ=5.",
            "effective_casimir_scale_at_xi uses dynamic inner and dynamic outer.",
            "shell source now uses the temperature-relative tuft vev factor, not a QCD-window average.",
            "nuclear binding: inside+outside ledger (papers/nucleon_binding); Q hybrid anchors lock-in to valley witness.",
            "local_curvature_neutrino_width: B_curv(ξ) relic-bath opacity OOM ~140^4 barn; free-branch weak-width catalysis (bonded clusters shielded).",
            "shell binding_feedback uses nucleon_own_binding_mev modulated by outside T(xi).",
        ],
        "nuclear_binding_Q_at_lockin": {
            "hybrid": dynamic_binding_q_at_shell(
                REFERENCE_M, lock_step.proton_mass_MeV, integrator.xi_lock, integrator.xi_lock
            ),
            "nuclear_raw": nuclear.binding_q_nuclear_at_xi(
                REFERENCE_M, lock_step.proton_mass_MeV, integrator.xi_lock
            ),
            "legacy_valley": bbn.lockin_binding_q(lock_step.proton_mass_MeV, REFERENCE_M),
        },
        "remaining_calculator_choice": (
            "BBN Q provider uses Lean bbnBindingReleaseFactor; literal *_at_xi rows kept for comparison."
        ),
        "shell_formula_rows": shell_rows,
        "literal_lean_BBN_Q_rows": [
            lean_literal_q_values_at_T(T, lock_step) for T in bbn_temperatures
        ],
        "curvature_temperature_binding_rows": [
            curvature_temperature_binding_factor(T, integrator) for T in bbn_temperatures
        ],
        "lean_bbn_binding_release": "bbnBindingReleaseFactor via hqiv_lean_physics_primitives",
    }


def run_dynamic_bbn_suite(
    eta: float,
    integrator: DynamicShellIntegratorResult,
    *,
    network_steps: int,
    use_dynamic_providers: bool,
) -> dict[str, Any]:
    witness = bbn.load_witness()
    lock_step = next((s for s in integrator.steps if s.is_lockin_event), integrator.steps[-1])
    m_p = lock_step.proton_mass_MeV
    dm = lock_step.delta_m_MeV
    Q_D, Q_4, Q_3 = lock_step.Q_D_MeV, lock_step.Q_4He_MeV, lock_step.Q_3He_MeV
    Q_7 = bbn.be7_binding_q(Q_4, m_shell=integrator.m_lock, m_nucleon=m_p)

    q_provider = None
    opportunity_provider = None
    if use_dynamic_providers:
        q_provider, opportunity_provider = make_dynamic_bbn_providers(integrator)

    final_state, net_meta = epoch_net.integrate_cooling_network(
        eta,
        dm,
        Q_D,
        Q_3,
        Q_4,
        n_steps=network_steps,
        q_provider=q_provider,
        opportunity_provider=opportunity_provider,
        history_stride=max(1, network_steps // 20),
    )
    network = {**epoch_net.readout_from_state(final_state, eta), **net_meta}

    mid_T = bbn.BBN_T_MID_MEV
    if q_provider is not None:
        q_mid_row = q_provider(mid_T)
        dm_mid, Q_D_mid, Q_3_mid, Q_4_mid = q_mid_row[0], q_mid_row[1], q_mid_row[2], q_mid_row[3]
        mid = bbn.abundances_at_epoch(eta, mid_T, m_p, dm_mid, Q_D_mid, Q_4_mid, Q_3_mid)
        q_mid = {
            "T_MeV": mid_T,
            "Q_D_MeV": Q_D_mid,
            "Q_4He_MeV": Q_4_mid,
            "Q_3He_MeV": Q_3_mid,
            "delta_m_MeV": dm_mid,
            "shell_opportunity": (
                opportunity_provider(mid_T, mid_T * 0.99, eta) if opportunity_provider else None
            ),
            "H_s_diagnostic": epoch_net.hubble_rate_s(mid_T),
        }
    else:
        mid = bbn.abundances_at_epoch(eta, mid_T, m_p, dm, Q_D, Q_4, Q_3)
        q_mid = {"T_MeV": mid_T, "Q_D_MeV": Q_D, "Q_4He_MeV": Q_4, "Q_3He_MeV": Q_3}

    return {
        "use_dynamic_providers": use_dynamic_providers,
        "lockin_shell_m": integrator.m_lock,
        "lockin_xi": integrator.xi_lock,
        "inputs_at_lockin": {
            "proton_mass_MeV": m_p,
            "delta_m_MeV": dm,
            "Q_D_MeV": Q_D,
            "Q_4He_MeV": Q_4,
            "Q_3He_MeV": Q_3,
        },
        "mid_epoch_T_0p1_MeV": mid,
        "mid_epoch_dynamic_Q_H": q_mid,
        "cooling_network": network,
    }


def run_legacy_bbn_suite(eta: float, *, network_steps: int) -> dict[str, Any]:
    witness = bbn.load_witness()
    m_p = float(witness["derivedProtonMass_MeV"])
    dm = float(witness["derivedDeltaM_MeV"])
    Q_D, Q_4, Q_3, _Q_7 = bbn.lockin_binding_q(m_p, REFERENCE_M)
    final_state, net_meta = epoch_net.integrate_cooling_network(
        eta, dm, Q_D, Q_3, Q_4, n_steps=network_steps
    )
    return {
        "eta": eta,
        "inputs": {"referenceM": REFERENCE_M, "Q_D_lockin_MeV": Q_D, "Q_4He_lockin_MeV": Q_4},
        "cooling_network": {**epoch_net.readout_from_state(final_state, eta), **net_meta},
    }


# Coc et al. / BBN+CMB comparison band (targets only, not fitted).
OBS_ETA10 = 6.10
OBS_ETA10_SIGMA = 0.06
OBS_OMEGA_B = 0.049
OBS_YP = 0.244
OBS_YP_SIGMA = 0.004
OBS_DH = 2.53e-5
OBS_DH_SIGMA = 0.04e-5
OBS_LI7H = 4.65e-10
OBS_LI7H_SIGMA = 1.5e-10


def observation_comparison_layer(
    eta_layer: dict[str, float],
    integrator: DynamicShellIntegratorResult,
    dynamic_bbn: dict[str, Any] | None,
) -> dict[str, Any]:
    """Model readouts vs observation bands (comparison layer only)."""
    bbn_net = (dynamic_bbn or {}).get("cooling_network", {})
    eta10 = float(eta_layer["eta10"])
    yp = float(bbn_net.get("Yp", float("nan")))
    dh = float(bbn_net.get("D_over_H", float("nan")))
    li7 = float(bbn_net.get("Li7_over_H", float("nan")))
    be7 = float(bbn_net.get("Be7_over_H", float("nan")))

    def z_score(model: float, central: float, sigma: float) -> float | None:
        if sigma <= 0.0 or math.isnan(model):
            return None
        return (model - central) / sigma

    return {
        "comparison_policy": "observation targets are not inputs to the integrator",
        "eta10": {
            "observed": OBS_ETA10,
            "sigma": OBS_ETA10_SIGMA,
            "model": eta10,
            "z_score": z_score(eta10, OBS_ETA10, OBS_ETA10_SIGMA),
            "relative_error": eta10 / OBS_ETA10 - 1.0,
        },
        "Omega_b": {
            "observed": OBS_OMEGA_B,
            "model": integrator.baryon_matter_fraction,
            "relative_error": integrator.baryon_matter_fraction / OBS_OMEGA_B - 1.0,
        },
        "Y_p": {
            "observed": OBS_YP,
            "sigma": OBS_YP_SIGMA,
            "model": yp,
            "z_score": z_score(yp, OBS_YP, OBS_YP_SIGMA),
        },
        "D_over_H": {
            "observed": OBS_DH,
            "sigma": OBS_DH_SIGMA,
            "model": dh,
            "z_score": z_score(dh, OBS_DH, OBS_DH_SIGMA),
        },
        "Be7_over_H": {
            "model": be7,
            "notes": "relic ⁷Be after capture (should be ≪ Li7/H in standard BBN)",
        },
        "Li7_over_H": {
            "observed": OBS_LI7H,
            "sigma": OBS_LI7H_SIGMA,
            "model": li7,
            "z_score": z_score(li7, OBS_LI7H, OBS_LI7H_SIGMA),
            "notes": "spite plateau / post-BBN depletion band; integrator is pre-destruction",
        },
        "nuclear_binding_paper": "papers/nucleon_binding/hqiv_nucleon_binding_from_composite_trace.tex",
        "baryogenesis_paper": "papers/baryogenesis_lockin/hqiv_baryogenesis_curvature_lockin.tex",
    }


def build_payload(H0_km_s_mpc: float, network_steps: int) -> dict[str, Any]:
    integrator = evolve_shell_integrator()
    integrator_anchor_extension = evolve_shell_integrator(extend_to_anchor=True)
    eta_layer = eta_from_omega_b(integrator.baryon_matter_fraction, H0_km_s_mpc)
    eta_lean = {
        "eta_at_horizon_lockin": eta_at_horizon(REFERENCE_M, REFERENCE_M),
        "eta_at_horizon_QCD_to_lockin": eta_at_horizon(QCD_SHELL, REFERENCE_M),
        "eta_at_horizon_dynamic_lockin": eta_at_horizon_dynamic(REFERENCE_M, REFERENCE_M),
        "binding_curvature_correction": lean.baryogenesis_binding_curvature_correction(),
    }
    dynamic_bbn = run_dynamic_bbn_suite(
        eta_layer["eta"],
        integrator,
        network_steps=network_steps,
        use_dynamic_providers=True,
    )
    legacy_bbn = run_legacy_bbn_suite(LEGACY_ETA_PAPER, network_steps=network_steps)
    legacy_eta_bbn = run_dynamic_bbn_suite(
        LEGACY_ETA_PAPER,
        integrator,
        network_steps=network_steps,
        use_dynamic_providers=False,
    )
    lock_step = next((s for s in integrator.steps if s.is_lockin_event), integrator.steps[-1])

    return {
        "source": "HQIV dynamic shell integrator — bulk matter + BBN v3",
        "python_script": "scripts/hqiv_dynamic_bulk_bbn.py",
        "integrator_mode": "per_shell_step (no window averages)",
        "lean_alignment": [
            "Hqiv.Geometry.OctonionicLightCone.shell_shape",
            "Hqiv.Physics.ContinuousXiCoupling.omegaKContinuous",
            "Hqiv.Physics.DynamicBBNBaryogenesis",
            "Hqiv.Physics.DynamicBBNBaryogenesis.bbnShellReactionOpportunity_dynamic_integrator",
            "Hqiv.Physics.DynamicBBNBaryogenesis.bbnDynamicC2OpportunitySuppression",
            "Hqiv.Physics.HopfShellBeltramiMassBridge.tuftLapseConcentrationAtXi",
            "Hqiv.Physics.BBNNetworkFromWeights",
            "Hqiv.Physics.BBNEpochEvolution",
        ],
        "curvature_budget_model": {
            "B_curv": "Casimir gap d∝1/ξ (power=1 on shell ladder) + nuclear bonded outside at BBN ξ",
            "seed_imprint_scale": CURVATURE_SEED_IMPRINT_SCALE,
            "kappa6_matter_slot": "eta_paper * curvature_budget_at_xi(xi)",
            "dynamic_C2": (
                "T_bottleneck = gamma*(4/8)*T_freeze(eta); "
                "w(T) = gamma*(4/8)*Q_D_eff(T)/Q_np; T_ref = T_freeze(eta); "
                "opportunity *= (kappa6_ref/kappa6)^w(T) in bottleneck"
            ),
        },
        "bbn_dynamic_C2_ladder": [
            lean.bbn_dynamic_c2_readout_at_T(
                T, eta=eta_layer["eta"], m_nucleon=lock_step.proton_mass_MeV
            )
            for T in (10.0, 1.0, 0.1, 0.01)
        ],
        "dynamic_inputs": {
            "alpha": ALPHA,
            "gamma": GAMMA,
            "qcd_shell": QCD_SHELL,
            "referenceM_anchor": REFERENCE_M,
            "t13_outer_mode_count": T13_OUTER_MODE_COUNT,
            "t13_outer_suppression_at_lockin": t13_outer_suppression_at_xi(XI_LOCKIN_LEAN),
            "strong_channel_fraction": STRONG_CHANNEL_FRACTION,
            "color_singlet_fraction": COLOR_SINGLET_FRACTION,
            "proton_anchor_MeV": PROTON_ANCHOR_MEV,
            "radiation_floor": RADIATION_FLOOR,
            "max_shell_scan": MAX_SHELL_SCAN,
        },
        "emergent_lockin": {
            "m_lock_hadronic": integrator.m_lock,
            "xi_lock_hadronic": integrator.xi_lock,
            "closure_residual_hadronic": integrator.lockin_closure_residual,
            "vev_scale_at_hadronic_lock": integrator.lockin_vev_scale,
            "pre_hadronic_closure_m": integrator.pre_hadronic_m,
            "pre_hadronic_closure_xi": integrator.pre_hadronic_xi,
            "pre_hadronic_closure_residual": integrator.pre_hadronic_closure_residual,
            "referenceM_anchor_m": REFERENCE_M,
        },
        "shell_integrator": {
            "total_matter_fraction": integrator.total_matter_fraction,
            "baryon_matter_fraction": integrator.baryon_matter_fraction,
            "dark_matter_like_fraction": integrator.dark_matter_like_fraction,
            "final_cumulative_source": integrator.final_cumulative_source,
            "steps": [asdict(s) for s in integrator.steps],
        },
        "anchor_extension_steps": [asdict(s) for s in integrator_anchor_extension.steps],
        "eta_from_dynamic_bulk": eta_layer,
        "eta_from_lean_curvature_laws": eta_lean,
        "kappa6_curvature_budget": {
            "casimir_power": 1.0,
            "B_at_shells": [
                {
                    "m": s.m,
                    "xi": s.xi,
                    "B_local_global": s.B_local_global,
                    "shell_seed_budget": s.curvature_budget / max(s.B_local_global, 1e-30),
                }
                for s in integrator.steps
            ],
            "B_at_bbn_T_0p1_MeV": lean.curvature_budget_local_global_at_xi(
                xi_from_T_MeV(bbn.BBN_T_MID_MEV), integrator.xi_lock
            ),
            "tuftMatterFraction_factor_at_lockin": lean.curvature_budget_at_xi(
                integrator.xi_lock, integrator.xi_lock
            ),
        },
        "nuclear_binding_conditions": nuclear.nuclear_binding_conditions_witness(
            m_start=QCD_SHELL, m_lock=integrator.m_lock, xi_lock=integrator.xi_lock
        ),
        "local_curvature_neutrino_width": nuclear.local_curvature_neutrino_width_witness(
            xi_lock=integrator.xi_lock
        ),
        "lean_math_comparison": lean_math_comparison(integrator),
        "dynamic_bbn": dynamic_bbn,
        "observation_comparison": observation_comparison_layer(eta_layer, integrator, dynamic_bbn),
        "legacy_eta_comparison": {
            "eta_paper": LEGACY_ETA_PAPER,
            "eta10_paper": LEGACY_ETA_PAPER * 1.0e10,
            "relative_eta_shift": eta_layer["eta"] / LEGACY_ETA_PAPER - 1.0,
            "fixed_Q_bbn": legacy_bbn,
            "dynamic_bulk_eta_fixed_Q": legacy_eta_bbn,
        },
        "notes": [
            "Shell integrator evolves QCD -> hadronic lock (m>=referenceM) with per-step vev, Q, and Omega accumulation.",
            "Pre-hadronic inside/outside closure can occur earlier (typically m=2, xi=3) before proton-anchor hadronic lock at m=4.",
            "Vev in the source term now follows Lean's temperature-relative tuftVevAtXi ratio, heavy_gap(xi)/heavy_gap(5).",
            "The stable BBN provider is tempered; literal Lean *_at_xi BBN Q rows are included under lean_math_comparison.",
            "Legacy eta_paper is comparison-only.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV dynamic shell integrator — bulk + BBN")
    parser.add_argument("--h0", type=float, default=DEFAULT_H0_KM_S_MPC)
    parser.add_argument("--network-steps", type=int, default=400)
    parser.add_argument("--out", type=Path, default=OUT)
    args = parser.parse_args()

    payload = build_payload(args.h0, args.network_steps)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n")

    lock = payload["emergent_lockin"]
    bulk = payload["shell_integrator"]
    eta_layer = payload["eta_from_dynamic_bulk"]
    bbn_dyn = payload["dynamic_bbn"]["cooling_network"]
    legacy = payload["legacy_eta_comparison"]

    print("HQIV dynamic shell integrator — bulk matter + BBN v3")
    print("=" * 60)
    print(f"Wrote {args.out}")
    print()
    print("Emergent lock-in:")
    print(f"  pre-hadronic closure  m={lock['pre_hadronic_closure_m']}  xi={lock['pre_hadronic_closure_xi']}")
    print(f"  hadronic lock         m={lock['m_lock_hadronic']}  xi={lock['xi_lock_hadronic']}")
    print(f"  referenceM anchor     m={lock['referenceM_anchor_m']}")
    print()
    print("Integrated bulk (final shell step):")
    print(f"  Omega_m,total = {bulk['total_matter_fraction']:.6f}")
    print(f"  Omega_b       = {bulk['baryon_matter_fraction']:.6f}")
    print(f"  Omega_dark    = {bulk['dark_matter_like_fraction']:.6f}")
    print()
    eta_lean = payload.get("eta_from_lean_curvature_laws", {})
    print("Eta from dynamic bulk (Omega_b path):")
    print(f"  eta10 = {eta_layer['eta10']:.6f}")
    print(f"  relative shift vs 6.10e-10 = {legacy['relative_eta_shift']:+.3%}")
    if eta_lean:
        print("Eta from Lean curvature laws (comparison):")
        print(f"  eta10 lock-in calibration = {eta_lean['eta_at_horizon_lockin'] * 1e10:.6f}")
        print(f"  eta10 dynamic lock-in     = {eta_lean['eta_at_horizon_dynamic_lockin'] * 1e10:.6f}")
        print(f"  binding corr factor       = {eta_lean['binding_curvature_correction']:+.6f}")
    print()
    print("BBN (dynamic Q + shell opportunity per step):")
    print(f"  Y_p = {bbn_dyn['Yp']:.6f}")
    print(f"  D/H = {bbn_dyn['D_over_H']:.6e}")
    print(f"  ⁷Be/H = {bbn_dyn.get('Be7_over_H', 0.0):.6e}")
    print(f"  ⁷Li/H = {bbn_dyn.get('Li7_over_H', 0.0):.6e}")
    obs = payload.get("observation_comparison", {})
    if obs:
        print()
        print("Observation comparison (model vs BBN+CMB band):")
        for key in ("eta10", "Omega_b", "Y_p", "D_over_H", "Li7_over_H", "Be7_over_H"):
            row = obs.get(key, {})
            rel = row.get("relative_error")
            rel_s = f"{rel:+.2%}" if rel is not None else f"z={row.get('z_score', 0):+.2f}"
            print(f"  {key:8} model={row.get('model')}  obs={row.get('observed')}  {rel_s}")
    k6 = payload.get("kappa6_curvature_budget", {})
    if k6.get("B_at_shells"):
        print()
        print("B_curv (Casimir local/global) on shells:", k6["B_at_shells"])
        print(f"  B_curv at BBN T=0.1 MeV: {k6.get('B_at_bbn_T_0p1_MeV')}")
    nu_w = payload.get("local_curvature_neutrino_width", {})
    lab = nu_w.get("lab_readout", {})
    if lab:
        print()
        print("Local curvature neutrino width (nucleon-binding paper):")
        print(f"  lab opacity = {lab.get('neutrino_opacity_barn', 0):.3e} barn")
        band = lab.get("width_factor_band", {})
        print(
            f"  free-branch width × = {band.get('central', 1):.4f} "
            f"({band.get('low', 1):.4f}–{band.get('high', 1):.4f})"
        )
        bbn0 = (nu_w.get("bbn_epochs") or [{}])[2] if len(nu_w.get("bbn_epochs") or []) > 2 else {}
        if bbn0:
            print(
                f"  BBN T=0.1 MeV: opacity={bbn0.get('neutrino_opacity_barn', 0):.3e} barn  "
                f"width×={bbn0.get('free_branch_width_factor', 1):.4f}"
            )


if __name__ == "__main__":
    main()
