#!/usr/bin/env python3
"""
LiH derivation scan (no empirical calibration).

Python mirror of the Lean-side scaffold:
  Hqiv/QuantumChemistry/LiH.lean
  Hqiv/QuantumChemistry/LiHDerivation.lean
  Hqiv/Geometry/Now.lean
  Hqiv/Physics/DerivedNucleonMass.lean

Derived indicator in dimensionless HQIV units:
  I = bond_horizon_surplus_dimless(4, 3, 1) + 3 * lattice_full_mode_energy(m_Li_p)

where:
  lattice_full_mode_energy(m) = 4 * (m + 2) * (m + 1)^2

For comparison to experiment (LiH D0 ~ 2.515 eV), we report two sign conventions:
  (a) surplus-as-energy:  E =  I * EV_PER_LAMBDA_UNIT
  (b) binding-depth:      E = -I * EV_PER_LAMBDA_UNIT

This script now also includes a "now-lapse target" branch mirroring the new
`Now.lean` terms:
  nowLapseTargetRatio(raw, anchor) = raw / anchor
  nowTimeForLapseTarget(Φ, raw, anchor) = ratio - (1 + Φ)
  nowHQVMLapse(Φ, t) = 1 + Φ + t
"""

from __future__ import annotations

from dataclasses import dataclass
import math

from bonded_horizon_casimir_float import bond_horizon_surplus_dimless
import cubic_phase_relax_probe as cpr
from nuclear_torus_casimir_float import DEFAULT_UUD_ANGLES_RAD, EV_PER_LAMBDA_UNIT


LIH_REFERENCE_EV = 2.515
HBAR_EV_S = 6.582119569e-16
PHASE_THETA = math.pi / 2.0
GAMMA_HQIV = 2.0 / 5.0
C_RINDLER_SHARED = GAMMA_HQIV / 2.0
REFERENCE_M = 4
BOSON_CLOSURE_SHELL = REFERENCE_M + 1
PROTON_DERIVED_RAW_MEV = 970.4
PROTON_ANCHOR_MEV = 938.272


def available_modes(m: int) -> float:
    return 4.0 * (m + 2) * (m + 1)


def phi_of_shell(m: int) -> float:
    return 2.0 * (m + 1)


def lattice_full_mode_energy(m: int) -> float:
    return available_modes(m) * (phi_of_shell(m) / 2.0)


def lih_bonded_surplus_dimless(
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> float:
    return bond_horizon_surplus_dimless(4, 3, 1, angles)


def lih_p_uplift_dimless(m_li_p: int) -> float:
    return 3.0 * lattice_full_mode_energy(m_li_p)


def lih_derived_indicator_dimless(
    m_li_p: int, angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD
) -> float:
    return lih_bonded_surplus_dimless(angles) + lih_p_uplift_dimless(m_li_p)


def shell_energy_ev(m: int) -> float:
    return lattice_full_mode_energy(m) * EV_PER_LAMBDA_UNIT


def omega_compton_from_energy_ev(energy_ev: float, hbar_ev_s: float = HBAR_EV_S) -> float:
    if hbar_ev_s <= 0.0:
        raise ValueError("hbar_ev_s must be positive")
    if energy_ev <= 0.0:
        raise ValueError("energy_ev must be positive")
    return energy_ev / hbar_ev_s


def t_ir_from_omega(omega: float) -> float:
    if omega <= 0.0:
        raise ValueError("omega must be positive")
    return PHASE_THETA / omega


def now_hqvm_lapse(phi_potential: float, t: float) -> float:
    """Mirror `Now.nowHQVMLapse_eq_one_add_Phi_add_t`."""
    return 1.0 + phi_potential + t


def now_lapse_target_ratio(raw: float, anchor: float) -> float:
    """Mirror `Now.nowLapseTargetRatio`."""
    if anchor == 0.0:
        raise ValueError("anchor must be nonzero")
    return raw / anchor


def now_time_for_lapse_target(phi_potential: float, raw: float, anchor: float) -> float:
    """Mirror `Now.nowTimeForLapseTarget`."""
    return now_lapse_target_ratio(raw, anchor) - (1.0 + phi_potential)


def lapse_corrected_energy_ev(energy_ev: float, lapse: float) -> float:
    """Apply controlled HQVM-lapse correction by division."""
    if lapse <= 0.0:
        raise ValueError("lapse must be positive for controlled correction")
    return energy_ev / lapse


@dataclass(frozen=True)
class ComptonAngleReport:
    angles_rad: tuple[float, float, float]
    omegas: tuple[float, float, float]
    t_irs: tuple[float, float, float]
    shared_time_s: float
    in_window: tuple[bool, bool, bool]


@dataclass(frozen=True)
class DetuningLapseReport:
    t_lockin: float
    surface_boson_closure: float
    outer_horizon_lapse_increment: float
    lambda_detuning: float
    delta_global: float
    rindler_den_reference_m: float
    lapse_fraction: float


@dataclass(frozen=True)
class NowLapseTargetReport:
    phi_potential: float
    raw_mev: float
    anchor_mev: float
    target_ratio: float
    solved_time: float
    lapse: float
    lapse_fraction: float


def shell_surface_hqiv(m: int) -> float:
    return float((m + 1) * (m + 2))


def t_lockin_hqiv(reference_m: int = REFERENCE_M) -> float:
    return 1.0 / float(reference_m + 1)


def outer_horizon_lapse_increment_hqiv(
    reference_m: int = REFERENCE_M, gamma_hqiv: float = GAMMA_HQIV
) -> float:
    # Mirrors Lean `vacuumExpectationValue = T_lockin * outerHorizonSurface(bosonClosureShell) * (1+gammaDerived)`.
    t_lockin = t_lockin_hqiv(reference_m)
    surface = shell_surface_hqiv(reference_m + 1)
    return t_lockin * surface * (1.0 + gamma_hqiv)


def detuning_lapse_fraction_from_hqiv_scalars(
    reference_m: int = REFERENCE_M,
    gamma_hqiv: float = GAMMA_HQIV,
    lambda_detuning: float = C_RINDLER_SHARED,
) -> DetuningLapseReport:
    t_lockin = t_lockin_hqiv(reference_m)
    surface = shell_surface_hqiv(reference_m + 1)
    obs = t_lockin * surface * (1.0 + gamma_hqiv)
    delta_global = lambda_detuning * obs
    rindler_den = 1.0 + (gamma_hqiv / 2.0) * float(reference_m) + delta_global
    if rindler_den <= 0.0:
        raise ValueError("detuning-derived Rindler denominator is non-positive")
    lapse_fraction = 1.0 / rindler_den
    if not (0.0 < lapse_fraction < 1.0):
        raise ValueError("detuning-derived lapse fraction is outside (0,1)")
    return DetuningLapseReport(
        t_lockin=t_lockin,
        surface_boson_closure=surface,
        outer_horizon_lapse_increment=obs,
        lambda_detuning=lambda_detuning,
        delta_global=delta_global,
        rindler_den_reference_m=rindler_den,
        lapse_fraction=lapse_fraction,
    )


def now_lapse_target_report(
    phi_potential: float = 0.0,
    raw_mev: float = PROTON_DERIVED_RAW_MEV,
    anchor_mev: float = PROTON_ANCHOR_MEV,
) -> NowLapseTargetReport:
    ratio = now_lapse_target_ratio(raw_mev, anchor_mev)
    t_solved = now_time_for_lapse_target(phi_potential, raw_mev, anchor_mev)
    lapse = now_hqvm_lapse(phi_potential, t_solved)
    if lapse <= 0.0:
        raise ValueError("computed now-lapse is non-positive")
    return NowLapseTargetReport(
        phi_potential=phi_potential,
        raw_mev=raw_mev,
        anchor_mev=anchor_mev,
        target_ratio=ratio,
        solved_time=t_solved,
        lapse=lapse,
        lapse_fraction=1.0 / lapse,
    )


def compton_window_angles_from_shells(
    shell_triplet: tuple[int, int, int] = (4, 3, 1),
    lapse_fraction: float = 0.90,
    hbar_ev_s: float = HBAR_EV_S,
) -> ComptonAngleReport:
    if not (0.0 < lapse_fraction < 1.0):
        raise ValueError("lapse_fraction must satisfy 0 < lapse_fraction < 1")
    energies = tuple(shell_energy_ev(m) for m in shell_triplet)
    omegas = tuple(omega_compton_from_energy_ev(e, hbar_ev_s) for e in energies)
    t_irs = tuple(t_ir_from_omega(w) for w in omegas)
    shared_time = lapse_fraction * min(t_irs)
    angles = tuple(w * shared_time for w in omegas)
    in_window = tuple((0.0 < a < PHASE_THETA) for a in angles)
    return ComptonAngleReport(
        angles_rad=(angles[0], angles[1], angles[2]),
        omegas=(omegas[0], omegas[1], omegas[2]),
        t_irs=(t_irs[0], t_irs[1], t_irs[2]),
        shared_time_s=shared_time,
        in_window=(in_window[0], in_window[1], in_window[2]),
    )


def compton_window_angles_from_detuning_lapse(
    shell_triplet: tuple[int, int, int] = (4, 3, 1),
    reference_m: int = REFERENCE_M,
    gamma_hqiv: float = GAMMA_HQIV,
    lambda_detuning: float = C_RINDLER_SHARED,
    hbar_ev_s: float = HBAR_EV_S,
) -> tuple[ComptonAngleReport, DetuningLapseReport]:
    det = detuning_lapse_fraction_from_hqiv_scalars(
        reference_m=reference_m,
        gamma_hqiv=gamma_hqiv,
        lambda_detuning=lambda_detuning,
    )
    angles = compton_window_angles_from_shells(
        shell_triplet=shell_triplet,
        lapse_fraction=det.lapse_fraction,
        hbar_ev_s=hbar_ev_s,
    )
    return angles, det


def content_layer_scales() -> tuple[float, float]:
    """
    Derive charged/color sector scaling from the improved spectrum model.
    Returns:
      charged_scale = e_improved / e_baseline
      color_scale = s_improved / s_baseline
    """
    base = cpr.build_content_layer_summary(
        cpr.ContentLayerParams(
            component_power=2.0,
            spin_coupling=1.0,
            charge_coupling=1.0,
            hypercharge_coupling=2.0,
            delta_global=0.0,
        )
    )
    improved = cpr.build_content_layer_summary(
        cpr.ContentLayerParams(
            component_power=3.0,
            spin_coupling=1.0,
            charge_coupling=4.0,
            hypercharge_coupling=4.0,
            delta_global=0.0,
        )
    )
    b = {r.particle: r.model_gev for r in base.rows}
    x = {r.particle: r.model_gev for r in improved.rows}
    return x["e"] / b["e"], x["s"] / b["s"]


def lih_derived_indicator_content_layer_coupled_dimless(
    m_li_p: int, angles: tuple[float, float, float]
) -> float:
    charged_scale, color_scale = content_layer_scales()
    bond = lih_bonded_surplus_dimless(angles)
    uplift = lih_p_uplift_dimless(m_li_p)
    return color_scale * bond + charged_scale * uplift


@dataclass(frozen=True)
class ScanRow:
    m_li_p: int
    indicator_dimless: float
    surplus_ev: float
    binding_ev: float
    surplus_err_pct: float
    binding_err_pct: float


@dataclass(frozen=True)
class OMaxwellResidualRow:
    m_li_p: int
    el_l2_norm: float
    el_max_abs: float


def _f_from_a(a_tensor: list[list[float]], a_idx: int, mu: int, nu: int) -> float:
    # Action.lean: F_from_A A a μ ν = A a ν - A a μ
    return a_tensor[a_idx][nu] - a_tensor[a_idx][mu]


def _f_divergence_sum(a_tensor: list[list[float]], a_idx: int, nu: int) -> float:
    # Action.lean: F_divergence_sum A a ν = sum_μ F_from_A A a μ ν
    return sum(_f_from_a(a_tensor, a_idx, mu, nu) for mu in range(4))


def _el_o_general(
    a_tensor: list[list[float]],
    j_tensor: list[list[float]],
    phi_val: float,
    a_idx: int,
    nu: int,
) -> float:
    # Action.lean (with grad_phi placeholder = 0 in current Lean):
    # EL_O_general = F_divergence_sum - 4π J_src - (if a=0 then α log(phi+1) grad_phi else 0)
    # => numeric mirror here uses grad_phi = 0, so only first two terms remain.
    _ = phi_val  # reserved for future nonzero grad_phi mirrors
    return _f_divergence_sum(a_tensor, a_idx, nu) - 4.0 * math.pi * j_tensor[a_idx][nu]


def lih_o_maxwell_ansatz_from_indicator(
    m_li_p: int,
    angles: tuple[float, float, float],
) -> tuple[list[list[float]], float]:
    """
    Build a concrete A(a,nu) ansatz from LiH-derived indicator components.
    Shape is [8][4] for (a in Fin 8, nu in Fin 4).
    """
    indicator = lih_derived_indicator_dimless(m_li_p, angles)
    uplift = lih_p_uplift_dimless(m_li_p)
    bonded = lih_bonded_surplus_dimless(angles)
    avg_angle = sum(angles) / 3.0
    phi_val = phi_of_shell(REFERENCE_M)

    # Keep a compact channel map:
    # - channel 0: composite LiH indicator profile
    # - channels 1..2: angle-coupled side channels
    # - others left at zero as baseline
    a_tensor = [[0.0 for _ in range(4)] for _ in range(8)]
    a_tensor[0][0] = 0.0
    a_tensor[0][1] = bonded
    a_tensor[0][2] = uplift / 3.0
    a_tensor[0][3] = indicator * avg_angle
    a_tensor[1][1] = angles[0]
    a_tensor[1][2] = angles[1]
    a_tensor[1][3] = angles[2]
    a_tensor[2][1] = indicator
    a_tensor[2][2] = bonded
    a_tensor[2][3] = uplift
    return a_tensor, phi_val


def run_o_maxwell_residual_scan(
    m_min: int = 0,
    m_max: int = 24,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> list[OMaxwellResidualRow]:
    rows: list[OMaxwellResidualRow] = []
    j_zero = [[0.0 for _ in range(4)] for _ in range(8)]  # source-free check
    for m_li_p in range(m_min, m_max + 1):
        a_tensor, phi_val = lih_o_maxwell_ansatz_from_indicator(m_li_p, angles)
        residuals = [
            _el_o_general(a_tensor, j_zero, phi_val, a_idx, nu)
            for a_idx in range(8)
            for nu in range(4)
        ]
        l2 = math.sqrt(sum(r * r for r in residuals))
        max_abs = max(abs(r) for r in residuals)
        rows.append(OMaxwellResidualRow(m_li_p=m_li_p, el_l2_norm=l2, el_max_abs=max_abs))
    return rows


def run_scan(
    m_min: int = 0,
    m_max: int = 24,
    angles: tuple[float, float, float] = DEFAULT_UUD_ANGLES_RAD,
) -> list[ScanRow]:
    rows: list[ScanRow] = []
    for m_li_p in range(m_min, m_max + 1):
        indicator = lih_derived_indicator_dimless(m_li_p, angles)
        surplus_ev = indicator * EV_PER_LAMBDA_UNIT
        binding_ev = -surplus_ev
        rows.append(
            ScanRow(
                m_li_p=m_li_p,
                indicator_dimless=indicator,
                surplus_ev=surplus_ev,
                binding_ev=binding_ev,
                surplus_err_pct=((surplus_ev - LIH_REFERENCE_EV) / LIH_REFERENCE_EV) * 100.0,
                binding_err_pct=((binding_ev - LIH_REFERENCE_EV) / LIH_REFERENCE_EV) * 100.0,
            )
        )
    return rows


def main() -> None:
    rows = run_scan()
    compton = compton_window_angles_from_shells()
    compton_detuning, detuning = compton_window_angles_from_detuning_lapse()
    now_target = now_lapse_target_report()
    rows_compton = run_scan(angles=compton.angles_rad)
    rows_compton_detuning = run_scan(angles=compton_detuning.angles_rad)
    bonded = lih_bonded_surplus_dimless()
    bonded_ev = bonded * EV_PER_LAMBDA_UNIT
    bonded_compton = lih_bonded_surplus_dimless(compton.angles_rad)
    bonded_compton_ev = bonded_compton * EV_PER_LAMBDA_UNIT
    bonded_compton_detuning = lih_bonded_surplus_dimless(compton_detuning.angles_rad)
    bonded_compton_detuning_ev = bonded_compton_detuning * EV_PER_LAMBDA_UNIT
    charged_scale, color_scale = content_layer_scales()

    rows_content_coupled = run_scan(
        angles=compton_detuning.angles_rad
    )
    rows_content_coupled = [
        ScanRow(
            m_li_p=r.m_li_p,
            indicator_dimless=lih_derived_indicator_content_layer_coupled_dimless(
                r.m_li_p, compton_detuning.angles_rad
            ),
            surplus_ev=lih_derived_indicator_content_layer_coupled_dimless(
                r.m_li_p, compton_detuning.angles_rad
            )
            * EV_PER_LAMBDA_UNIT,
            binding_ev=-lih_derived_indicator_content_layer_coupled_dimless(
                r.m_li_p, compton_detuning.angles_rad
            )
            * EV_PER_LAMBDA_UNIT,
            surplus_err_pct=(
                (
                    lih_derived_indicator_content_layer_coupled_dimless(
                        r.m_li_p, compton_detuning.angles_rad
                    )
                    * EV_PER_LAMBDA_UNIT
                    - LIH_REFERENCE_EV
                )
                / LIH_REFERENCE_EV
            )
            * 100.0,
            binding_err_pct=(
                (
                    -lih_derived_indicator_content_layer_coupled_dimless(
                        r.m_li_p, compton_detuning.angles_rad
                    )
                    * EV_PER_LAMBDA_UNIT
                    - LIH_REFERENCE_EV
                )
                / LIH_REFERENCE_EV
            )
            * 100.0,
        )
        for r in rows_content_coupled
    ]
    rows_content_coupled_now_lapse = [
        ScanRow(
            m_li_p=r.m_li_p,
            indicator_dimless=r.indicator_dimless,
            surplus_ev=lapse_corrected_energy_ev(r.surplus_ev, now_target.lapse),
            binding_ev=lapse_corrected_energy_ev(r.binding_ev, now_target.lapse),
            surplus_err_pct=(
                (lapse_corrected_energy_ev(r.surplus_ev, now_target.lapse) - LIH_REFERENCE_EV)
                / LIH_REFERENCE_EV
            )
            * 100.0,
            binding_err_pct=(
                (lapse_corrected_energy_ev(r.binding_ev, now_target.lapse) - LIH_REFERENCE_EV)
                / LIH_REFERENCE_EV
            )
            * 100.0,
        )
        for r in rows_content_coupled
    ]
    rows_omaxwell = run_o_maxwell_residual_scan(angles=compton_detuning.angles_rad)

    best_surplus = min(rows, key=lambda r: abs(r.surplus_ev - LIH_REFERENCE_EV))
    best_binding = min(rows, key=lambda r: abs(r.binding_ev - LIH_REFERENCE_EV))
    best_surplus_compton = min(rows_compton, key=lambda r: abs(r.surplus_ev - LIH_REFERENCE_EV))
    best_binding_compton = min(rows_compton, key=lambda r: abs(r.binding_ev - LIH_REFERENCE_EV))
    best_surplus_compton_detuning = min(rows_compton_detuning, key=lambda r: abs(r.surplus_ev - LIH_REFERENCE_EV))
    best_binding_compton_detuning = min(rows_compton_detuning, key=lambda r: abs(r.binding_ev - LIH_REFERENCE_EV))
    best_surplus_content_coupled = min(rows_content_coupled, key=lambda r: abs(r.surplus_ev - LIH_REFERENCE_EV))
    best_surplus_content_coupled_now_lapse = min(
        rows_content_coupled_now_lapse, key=lambda r: abs(r.surplus_ev - LIH_REFERENCE_EV)
    )
    best_omaxwell = min(rows_omaxwell, key=lambda r: r.el_l2_norm)

    print("LiH derivation scan (no calibration)")
    print("formula: I = bond_surplus(4,3,1) + 3*lattice_full_mode_energy(m_Li_p)")
    print(f"EV_PER_LAMBDA_UNIT = {EV_PER_LAMBDA_UNIT:.12f}")
    print(f"bond_surplus_dimless default angles = {bonded:.12f}")
    print(f"bond_surplus_eV default angles (surplus sign) = {bonded_ev:.12f}")
    print()
    print("Compton-window torus angles (shells 4,3,1; fixed shared lapse_fraction=0.90):")
    print(f"  theta = pi/2 = {PHASE_THETA:.12f} rad")
    print(f"  angles = ({compton.angles_rad[0]:.12f}, {compton.angles_rad[1]:.12f}, {compton.angles_rad[2]:.12f})")
    print(f"  in_window(0<x<theta) = {compton.in_window}")
    print(f"  shared_time_s = {compton.shared_time_s:.6e}")
    print(
        f"  t_IRs_s = ({compton.t_irs[0]:.6e}, {compton.t_irs[1]:.6e}, {compton.t_irs[2]:.6e})"
    )
    print(f"bond_surplus_dimless Compton angles = {bonded_compton:.12f}")
    print(f"bond_surplus_eV Compton angles (surplus sign) = {bonded_compton_ev:.12f}")
    print()
    print("Compton-window torus angles (detuning/lapse sourced):")
    print(
        "  HQIV scalars: "
        f"T_lockin={detuning.t_lockin:.12f}, "
        f"S(bosonClosure)={detuning.surface_boson_closure:.12f}, "
        f"gamma={GAMMA_HQIV:.12f}"
    )
    print(
        "  lapse increment obs = T_lockin*S*(1+gamma) = "
        f"{detuning.outer_horizon_lapse_increment:.12f}"
    )
    print(
        "  delta_global = lambda*obs with "
        f"lambda={detuning.lambda_detuning:.12f}: {detuning.delta_global:.12f}"
    )
    print(
        "  rindler_den(m_ref) = 1 + (gamma/2)*m_ref + delta = "
        f"{detuning.rindler_den_reference_m:.12f}"
    )
    print(f"  derived lapse_fraction = 1/rindler_den = {detuning.lapse_fraction:.12f}")
    print(
        f"  angles = ({compton_detuning.angles_rad[0]:.12f}, "
        f"{compton_detuning.angles_rad[1]:.12f}, "
        f"{compton_detuning.angles_rad[2]:.12f})"
    )
    print(f"  in_window(0<x<theta) = {compton_detuning.in_window}")
    print(f"  shared_time_s = {compton_detuning.shared_time_s:.6e}")
    print(
        f"  t_IRs_s = ({compton_detuning.t_irs[0]:.6e}, "
        f"{compton_detuning.t_irs[1]:.6e}, "
        f"{compton_detuning.t_irs[2]:.6e})"
    )
    print(f"bond_surplus_dimless Compton+detuning angles = {bonded_compton_detuning:.12f}")
    print(
        "bond_surplus_eV Compton+detuning angles (surplus sign) = "
        f"{bonded_compton_detuning_ev:.12f}"
    )
    print()
    print("Content-layer coupling factors (from improved spectrum model):")
    print(f"  charged_scale = {charged_scale:.12f}")
    print(f"  color_scale   = {color_scale:.12f}")
    print()
    print("Now-lapse target branch (mirrors Now.lean target-ratio terms):")
    print(f"  raw_mev / anchor_mev = {now_target.raw_mev:.6f} / {now_target.anchor_mev:.6f}")
    print(f"  target_ratio = {now_target.target_ratio:.12f}")
    print(f"  phi_potential = {now_target.phi_potential:.12f}")
    print(f"  solved_time = {now_target.solved_time:.12f}")
    print(f"  lapse = {now_target.lapse:.12f}")
    print(f"  lapse_fraction = {now_target.lapse_fraction:.12f}")
    print(f"LiH reference dissociation eV = {LIH_REFERENCE_EV:.6f}")
    print()
    print("[default-angle scan]")
    print("m_Li_p\tindicator_dimless\tsurplus_eV\tbinding_eV\tsurplus_err_%\tbinding_err_%")
    for r in rows:
        print(
            f"{r.m_li_p}\t{r.indicator_dimless:.9f}\t{r.surplus_ev:.9f}\t{r.binding_ev:.9f}\t"
            f"{r.surplus_err_pct:.6f}\t{r.binding_err_pct:.6f}"
        )
    print()
    print("[Compton-angle scan]")
    print("m_Li_p\tindicator_dimless\tsurplus_eV\tbinding_eV\tsurplus_err_%\tbinding_err_%")
    for r in rows_compton:
        print(
            f"{r.m_li_p}\t{r.indicator_dimless:.9f}\t{r.surplus_ev:.9f}\t{r.binding_ev:.9f}\t"
            f"{r.surplus_err_pct:.6f}\t{r.binding_err_pct:.6f}"
        )
    print()
    print("[Compton+detuning-lapse scan]")
    print("m_Li_p\tindicator_dimless\tsurplus_eV\tbinding_eV\tsurplus_err_%\tbinding_err_%")
    for r in rows_compton_detuning:
        print(
            f"{r.m_li_p}\t{r.indicator_dimless:.9f}\t{r.surplus_ev:.9f}\t{r.binding_ev:.9f}\t"
            f"{r.surplus_err_pct:.6f}\t{r.binding_err_pct:.6f}"
        )
    print()
    print("[Content-layer coupled scan (on Compton+detuning angles)]")
    print("m_Li_p\tindicator_dimless\tsurplus_eV\tbinding_eV\tsurplus_err_%\tbinding_err_%")
    for r in rows_content_coupled:
        print(
            f"{r.m_li_p}\t{r.indicator_dimless:.9f}\t{r.surplus_ev:.9f}\t{r.binding_ev:.9f}\t"
            f"{r.surplus_err_pct:.6f}\t{r.binding_err_pct:.6f}"
        )
    print()
    print("[Content-layer coupled + now-lapse corrected scan]")
    print("m_Li_p\tindicator_dimless\tsurplus_eV\tbinding_eV\tsurplus_err_%\tbinding_err_%")
    for r in rows_content_coupled_now_lapse:
        print(
            f"{r.m_li_p}\t{r.indicator_dimless:.9f}\t{r.surplus_ev:.9f}\t{r.binding_ev:.9f}\t"
            f"{r.surplus_err_pct:.6f}\t{r.binding_err_pct:.6f}"
        )
    print()
    print("[O-Maxwell EL residual scan on LiH ansatz, source-free J=0]")
    print("m_Li_p\tEL_L2_norm\tEL_max_abs")
    for r in rows_omaxwell:
        print(f"{r.m_li_p}\t{r.el_l2_norm:.9f}\t{r.el_max_abs:.9f}")
    print()
    print(
        "best default (surplus sign): "
        f"m_Li_p={best_surplus.m_li_p}, E={best_surplus.surplus_ev:.9f} eV, "
        f"err={best_surplus.surplus_err_pct:.6f}%"
    )
    print(
        "best default (binding sign): "
        f"m_Li_p={best_binding.m_li_p}, E={best_binding.binding_ev:.9f} eV, "
        f"err={best_binding.binding_err_pct:.6f}%"
    )
    print(
        "best Compton-angle (surplus sign): "
        f"m_Li_p={best_surplus_compton.m_li_p}, E={best_surplus_compton.surplus_ev:.9f} eV, "
        f"err={best_surplus_compton.surplus_err_pct:.6f}%"
    )
    print(
        "best Compton-angle (binding sign): "
        f"m_Li_p={best_binding_compton.m_li_p}, E={best_binding_compton.binding_ev:.9f} eV, "
        f"err={best_binding_compton.binding_err_pct:.6f}%"
    )
    print(
        "best Compton+detuning (surplus sign): "
        f"m_Li_p={best_surplus_compton_detuning.m_li_p}, "
        f"E={best_surplus_compton_detuning.surplus_ev:.9f} eV, "
        f"err={best_surplus_compton_detuning.surplus_err_pct:.6f}%"
    )
    print(
        "best Compton+detuning (binding sign): "
        f"m_Li_p={best_binding_compton_detuning.m_li_p}, "
        f"E={best_binding_compton_detuning.binding_ev:.9f} eV, "
        f"err={best_binding_compton_detuning.binding_err_pct:.6f}%"
    )
    print(
        "best content-layer coupled (surplus sign): "
        f"m_Li_p={best_surplus_content_coupled.m_li_p}, "
        f"E={best_surplus_content_coupled.surplus_ev:.9f} eV, "
        f"err={best_surplus_content_coupled.surplus_err_pct:.6f}%"
    )
    print(
        "best content-layer + now-lapse corrected (surplus sign): "
        f"m_Li_p={best_surplus_content_coupled_now_lapse.m_li_p}, "
        f"E={best_surplus_content_coupled_now_lapse.surplus_ev:.9f} eV, "
        f"err={best_surplus_content_coupled_now_lapse.surplus_err_pct:.6f}%"
    )
    print(
        "best O-Maxwell EL match (source-free ansatz): "
        f"m_Li_p={best_omaxwell.m_li_p}, "
        f"EL_L2={best_omaxwell.el_l2_norm:.9f}, "
        f"EL_max_abs={best_omaxwell.el_max_abs:.9f}"
    )


if __name__ == "__main__":
    main()

