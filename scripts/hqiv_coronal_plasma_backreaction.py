#!/usr/bin/env python3
"""
Self-consistent coronal heated-plasma back-reaction readout.

Lean mirrors:
  • Hqiv.Physics.CoronalHeatedPlasmaBackReaction
  • Hqiv.Physics.CoronalLongitudinalStress
  • Hqiv.Physics.SchematicPlasmaCurrent (J_O_plasma amplitude slot)

Closes the loop:
  primary HQIV heating → hot pressure/current → back-reaction E_∥ → E_self → q̇_self.

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_coronal_plasma_backreaction.py
  PYTHONPATH=scripts python3 scripts/hqiv_coronal_plasma_backreaction.py --json data/coronal_plasma_backreaction.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_lean_physics_primitives as lean
import hqiv_solar_dynamics as sd

E_CHARGE = 1.602176634e-19
K_B = 1.380649e-23
TARGET_CORONAL_FLUX_W_M2 = 1.0e3
PSP_PROTON_ENERGY_KEV = 400.0

LEAN_MODULES = [
    "Hqiv.Physics.CoronalHeatedPlasmaBackReaction",
    "Hqiv.Physics.CoronalLongitudinalStress",
    "Hqiv.Physics.SchematicPlasmaCurrent",
    "Hqiv.Physics.HQIVFluidClosureScaffold",
    "Hqiv.Physics.PlasmaZPinchFilament",
    "Hqiv.Physics.PspHcsReconnectionWitness",
]

GAMMA = lean.GAMMA
ALPHA = lean.ALPHA


def heated_energy_density(q_dot: float, tau_hot: float) -> float:
    return q_dot * tau_hot


def hot_pressure_from_energy(u_hot: float) -> float:
    return (2.0 / 3.0) * u_hot


def hot_pressure_back_reaction(nq: float, p_hot: float, l_grad: float) -> float:
    if nq == 0.0 or l_grad == 0.0:
        return 0.0
    return -p_hot / (nq * l_grad)


def hot_return_current(n_hot: float, q: float, v_hot: float) -> float:
    return n_hot * q * v_hot


def hot_electric_proxy(p_hot: float, nq: float) -> float:
    if nq <= 0.0:
        return 0.0
    return math.sqrt(max(p_hot / nq, 0.0))


def delta_theta_prime(e_prime: float) -> float:
    return math.atan(e_prime) * (math.pi / 2.0)


def hot_induced_dot_theta(p_hot: float, nq: float) -> float:
    return delta_theta_prime(hot_electric_proxy(p_hot, nq))


def hot_induced_vacuum_momentum_axial(phi: float, dphi_ds: float, p_hot: float, nq: float) -> float:
    dot = hot_induced_dot_theta(p_hot, nq)
    return -(GAMMA / 6.0) * (phi * 0.0 + dot * dphi_ds)


def plasma_radial_profile(r: float, lambda_debye: float = 1.0) -> float:
    r_pos = max(r, 0.0)
    return math.exp(-r / lambda_debye) / (1.0 + r_pos / lambda_debye)


def hot_plasma_coherence(kappa: float, j_hot: float, r: float, lambda_debye: float = 1.0) -> float:
    return min(1.0, kappa * abs(j_hot) * plasma_radial_profile(r, lambda_debye))


def single_pass_energy_j(charge: float, e_parallel: float, path_length: float) -> float:
    return abs(charge) * abs(e_parallel) * abs(path_length)


def linear_multi_pass_energy_ev(charge: float, e_parallel: float, path_length: float, n_passes: float) -> float:
    return n_passes * single_pass_energy_j(charge, e_parallel, path_length) / abs(charge)


def e_star_for_target_flux(
    target_flux: float,
    nq: float,
    v_parallel: float,
    phi_photo: float,
    phi_corona: float,
    coupling_log: float,
) -> float:
    delta_phi = phi_corona - phi_photo
    denom = nq * v_parallel * (3.0 / (20.0 * math.pi)) * coupling_log * delta_phi
    if denom <= 0.0:
        return 1.0
    return target_flux / denom


@dataclass(frozen=True)
class CoronalPlasmaBackReactionRow:
    label: str
    m_photo: int
    m_corona: int
    e_star: float
    target_flux_w_m2: float
    e_ohm: float
    e_hqiv_primary: float
    e_hot_back: float
    e_self: float
    q_dot_primary_w_m3: float
    q_dot_self_w_m3: float
    heating_flux_boundary_w_m2: float
    u_hot_j_m3: float
    p_hot_pa: float
    n_hot_m3: float
    j_hot_a_m2: float
    dot_theta_hot: float
    g_vac_hot_axial: float
    hot_coherence: float
    feedback_factor: float
    linear_pass_energy_ev: float
    linear_pass_energy_kev: float
    psp_proton_energy_kev: float
    psp_energy_ratio: float
    n_passes_for_psp_kev: float


def coronal_plasma_backreaction_readout(
    *,
    m_photo: int = sd.DEFAULT_M_PHOTO,
    m_corona: int = sd.DEFAULT_M_CORONA,
    j_parallel: float = 1.0e3,
    sigma: float = 1.0e7,
    nq: float = 1.0e20,
    v_parallel: float = 5.0e3,
    v_hot: float = 2.0e5,
    dphi_ds: float | None = None,
    tau_hot: float = 10.0,
    l_grad: float = 1.0e5,
    e_char: float = 100.0 * E_CHARGE,
    n_passes: float = 50.0,
    path_length_m: float = 1.0e6,
    target_flux: float = TARGET_CORONAL_FLUX_W_M2,
    kappa_coherence: float = 1.0e-22,
    proxy_radius: float = 1.0,
    lambda_debye: float = 1.0,
    max_iter: int = 12,
    label: str = "photosphere_corona_self_consistent",
) -> CoronalPlasmaBackReactionRow:
    """Self-consistent heated-plasma row with fixed-point hot back-reaction."""
    tube = sd.solar_flux_tube_readout(
        m_photo=m_photo,
        m_corona=m_corona,
        j_parallel=j_parallel,
        sigma=sigma,
        nq=nq,
        v_parallel=v_parallel,
        dphi_ds=dphi_ds,
        e_star=1.0,
        label=label,
    )
    e_star = e_star_for_target_flux(
        target_flux, nq, v_parallel, tube.phi_photo, tube.phi_corona, tube.coupling_log
    )
    tube = sd.solar_flux_tube_readout(
        m_photo=m_photo,
        m_corona=m_corona,
        j_parallel=j_parallel,
        sigma=sigma,
        nq=nq,
        v_parallel=v_parallel,
        dphi_ds=dphi_ds,
        e_star=e_star,
        label=label,
    )
    grad = tube.dphi_ds
    q_dot_primary = tube.force_density * v_parallel
    p_hot = 0.0
    e_hot_back = 0.0
    e_self = tube.e_eff
    for _ in range(max_iter):
        u_hot = heated_energy_density(q_dot_primary, tau_hot)
        p_hot = hot_pressure_from_energy(u_hot)
        e_hot_back = hot_pressure_back_reaction(nq, p_hot, l_grad)
        e_self = tube.e_ohm + tube.e_hqiv + e_hot_back
        q_dot_new = nq * v_parallel * e_self
        if abs(q_dot_new - q_dot_primary) <= 1.0e-6 * max(abs(q_dot_primary), 1.0):
            break
        q_dot_primary = q_dot_new
    u_hot = heated_energy_density(q_dot_primary, tau_hot)
    p_hot = hot_pressure_from_energy(u_hot)
    e_hot_back = hot_pressure_back_reaction(nq, p_hot, l_grad)
    e_self = tube.e_ohm + tube.e_hqiv + e_hot_back
    q_dot_self = nq * v_parallel * e_self
    n_hot = q_dot_primary / (e_char * v_parallel) if v_parallel != 0.0 else 0.0
    j_hot = hot_return_current(n_hot, E_CHARGE, v_hot)
    dot_theta = hot_induced_dot_theta(p_hot, nq)
    g_vac = hot_induced_vacuum_momentum_axial(tube.phi_corona, grad, p_hot, nq)
    coherence = hot_plasma_coherence(kappa_coherence, j_hot, proxy_radius, lambda_debye)
    feedback = q_dot_self / q_dot_primary if q_dot_primary != 0.0 else 1.0
    e_pass_ev = linear_multi_pass_energy_ev(E_CHARGE, e_self, path_length_m, n_passes)
    e_pass_kev = e_pass_ev / 1000.0
    n_for_psp = (
        (PSP_PROTON_ENERGY_KEV * 1000.0) / (single_pass_energy_j(E_CHARGE, e_self, path_length_m) / E_CHARGE)
        if e_self != 0.0
        else float("inf")
    )
    flux_boundary = sd.heating_flux_boundary(
        nq, v_parallel, tube.phi_photo, tube.phi_corona, e_star=e_star, coupling_log=tube.coupling_log
    )
    return CoronalPlasmaBackReactionRow(
        label=label,
        m_photo=m_photo,
        m_corona=m_corona,
        e_star=e_star,
        target_flux_w_m2=target_flux,
        e_ohm=tube.e_ohm,
        e_hqiv_primary=tube.e_hqiv,
        e_hot_back=e_hot_back,
        e_self=e_self,
        q_dot_primary_w_m3=q_dot_primary,
        q_dot_self_w_m3=q_dot_self,
        heating_flux_boundary_w_m2=flux_boundary,
        u_hot_j_m3=u_hot,
        p_hot_pa=p_hot,
        n_hot_m3=n_hot,
        j_hot_a_m2=j_hot,
        dot_theta_hot=dot_theta,
        g_vac_hot_axial=g_vac,
        hot_coherence=coherence,
        feedback_factor=feedback,
        linear_pass_energy_ev=e_pass_ev,
        linear_pass_energy_kev=e_pass_kev,
        psp_proton_energy_kev=PSP_PROTON_ENERGY_KEV,
        psp_energy_ratio=e_pass_kev / PSP_PROTON_ENERGY_KEV if PSP_PROTON_ENERGY_KEV else 0.0,
        n_passes_for_psp_kev=n_for_psp,
    )


def default_readout() -> dict[str, Any]:
    row = coronal_plasma_backreaction_readout()
    return {
        "lean_modules": LEAN_MODULES,
        "row": asdict(row),
        "notes": {
            "loop": "q_dot → u_hot → P_hot → E_hot_back → E_self → q_dot_self",
            "honesty": "Linear multi-pass stack is an upper-bound witness, not Fermi acceleration.",
            "psp_compare": "n_passes_for_psp_keV estimates passes needed at E_self without stochastic tail physics.",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV coronal heated-plasma back-reaction readout")
    parser.add_argument("--json", type=Path, help="Write JSON witness")
    args = parser.parse_args()
    payload = default_readout()
    text = json.dumps(payload, indent=2)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n")
        print(f"wrote {args.json}")
    else:
        print(text)


if __name__ == "__main__":
    main()
