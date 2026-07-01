#!/usr/bin/env python3
"""Pinch-local nonlinear feedback into the heated-plasma loop.

Closes: compression C → q̇_loc, n_loc → P_hot,loc → E_hot,back → E_self → q̇_self,loc
with fixed-point iteration (Python). Lean algebra in ``PlasmaZPinchFilament`` §7.

Also provides filament **intersection node** readouts (§6).

Run:
  PYTHONPATH=scripts python3 scripts/hqiv_pinch_heated_feedback.py
  PYTHONPATH=scripts python3 scripts/test_hqiv_pinch_heated_feedback.py
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from typing import Any

import hqiv_coronal_plasma_backreaction as back
import hqiv_plasma_pinch_filament as pinch

E_CHARGE = back.E_CHARGE


@dataclass(frozen=True)
class PinchHeatedFeedbackRow:
    label: str
    compression: float
    n_filaments: int | None
    site: str  # "spine" | "node"
    q_dot_bulk_w_m3: float
    q_dot_local_w_m3: float
    q_dot_self_local_w_m3: float
    n_local_m3: float
    p_hot_local_pa: float
    j_hot_local_a_m2: float
    e_self_v_m: float
    e_hot_back_v_m: float
    feedback_factor_local: float
    pinch_nonlinear_factor: float
    iterations: int
    converged: bool
    node_intensity: float | None
    phi_node_enhancement: float | None
    collapse_hypothesis: bool


def pinch_self_consistent_heating_once(
    *,
    compression: float,
    n_bulk: float,
    v_parallel: float,
    e_ohm: float,
    e_hqiv: float,
    q_dot_local: float,
    tau_hot: float,
    l_grad: float,
    v_hot: float,
) -> tuple[float, float, float, float, float, float]:
    """Single algebraic pass: pinch-local hot bath → E_self → q̇_self,loc."""
    n_local = compression * n_bulk
    u_hot = back.heated_energy_density(q_dot_local, tau_hot)
    p_hot = back.hot_pressure_from_energy(u_hot)
    e_hot_back = back.hot_pressure_back_reaction(n_local, p_hot, l_grad)
    e_self = e_ohm + e_hqiv + e_hot_back
    q_self_local = n_local * v_parallel * e_self
    n_hot = q_dot_local / (100.0 * E_CHARGE * v_hot) if v_hot > 0.0 else 0.0
    j_hot = back.hot_return_current(n_hot, E_CHARGE, v_hot) * compression
    return q_self_local, p_hot, e_self, e_hot_back, j_hot, n_local


def pinch_heated_feedback_fixed_point(
    *,
    compression: float | None = None,
    n_filaments: int | None = None,
    site: str = "spine",
    m_photo: int = 0,
    m_corona: int = 8,
    j_parallel: float = 1.0e3,
    sigma: float = 1.0e7,
    nq: float = 1.0e20,
    v_parallel: float = 5.0e3,
    v_hot: float = 2.0e5,
    tau_hot: float = 10.0,
    l_grad: float = 1.0e5,
    tube_radius_m: float = 1.0e5,
    R_bulk_m: float = 1.0e6,
    r_pinch_m: float | None = None,
    max_iter: int = 16,
    tol: float = 1.0e-6,
    collapse_threshold: float = 100.0,
    label: str = "pinch_heated_feedback",
) -> PinchHeatedFeedbackRow:
    """Fixed-point pinch-local heated-plasma feedback."""
    bulk = back.coronal_plasma_backreaction_readout(
        m_photo=m_photo,
        m_corona=m_corona,
        j_parallel=j_parallel,
        sigma=sigma,
        nq=nq,
        v_parallel=v_parallel,
        v_hot=v_hot,
        tau_hot=tau_hot,
        l_grad=l_grad,
        label=f"{label}_bulk",
    )
    if compression is None or compression <= 0.0:
        if site == "node" and n_filaments is not None and n_filaments >= 1:
            r_sp = r_pinch_m if r_pinch_m is not None else max(tube_radius_m * 0.1, 1.0e3)
            compression = pinch.node_localized_intensity(R_bulk_m, r_sp, n_filaments)
        elif r_pinch_m is not None:
            compression = pinch.pinch_compression_ratio(R_bulk_m, r_pinch_m)
        else:
            compression = 1.0

    node_intensity: float | None = None
    phi_node: float | None = None
    if site == "node" and n_filaments is not None and n_filaments >= 1:
        r_sp = r_pinch_m if r_pinch_m is not None else max(tube_radius_m * 0.1, 1.0e3)
        node_intensity = pinch.node_localized_intensity(R_bulk_m, r_sp, n_filaments)
        compression = node_intensity
        phi_node = pinch.whim_node_phi_enhancement(0, 1, R_bulk_m, r_sp, n_filaments)

    q = compression * bulk.q_dot_self_w_m3
    converged = False
    iters = 0
    p_hot = e_self = e_hot_back = j_hot = n_local = 0.0
    for iters in range(1, max_iter + 1):
        q_new, p_hot, e_self, e_hot_back, j_hot, n_local = pinch_self_consistent_heating_once(
            compression=compression,
            n_bulk=nq,
            v_parallel=v_parallel,
            e_ohm=bulk.e_ohm,
            e_hqiv=bulk.e_hqiv_primary,
            q_dot_local=q,
            tau_hot=tau_hot,
            l_grad=l_grad,
            v_hot=v_hot,
        )
        if abs(q_new - q) <= tol * max(abs(q), 1.0):
            q = q_new
            converged = True
            break
        q = q_new

    q_bulk = bulk.q_dot_self_w_m3
    fb_local = q / q_bulk if q_bulk != 0.0 else 1.0
    pinch_factor = fb_local / compression if compression != 0.0 else 1.0
    collapse = compression >= collapse_threshold

    return PinchHeatedFeedbackRow(
        label=label,
        compression=compression,
        n_filaments=n_filaments,
        site=site,
        q_dot_bulk_w_m3=q_bulk,
        q_dot_local_w_m3=compression * q_bulk,
        q_dot_self_local_w_m3=q,
        n_local_m3=n_local,
        p_hot_local_pa=p_hot,
        j_hot_local_a_m2=j_hot,
        e_self_v_m=e_self,
        e_hot_back_v_m=e_hot_back,
        feedback_factor_local=fb_local,
        pinch_nonlinear_factor=pinch_factor,
        iterations=iters,
        converged=converged,
        node_intensity=node_intensity,
        phi_node_enhancement=phi_node,
        collapse_hypothesis=collapse,
    )


def default_readout() -> dict[str, Any]:
    coronal_spine = pinch_heated_feedback_fixed_point(
        r_pinch_m=1.0e4,
        R_bulk_m=1.0e6,
        tube_radius_m=1.0e5,
        label="coronal_spine_pinch",
    )
    coronal_node = pinch_heated_feedback_fixed_point(
        site="node",
        n_filaments=3,
        r_pinch_m=1.0e4,
        R_bulk_m=1.0e6,
        tube_radius_m=1.0e5,
        label="coronal_triple_node",
    )
    whim_node = pinch_heated_feedback_fixed_point(
        site="node",
        n_filaments=4,
        R_bulk_m=3.086e22,
        r_pinch_m=1.543e20,
        compression=pinch.node_localized_intensity(3.086e22, 1.543e20, 4),
        label="whim_quad_node",
        collapse_threshold=100.0,
    )
    return {
        "lean_module": "Hqiv.Physics.PlasmaZPinchFilament",
        "loop": "C → q̇_loc, n_loc → P_hot → E_hot,back → E_self → q̇_self,loc (fixed point)",
        "coronal_spine": asdict(coronal_spine),
        "coronal_triple_node": asdict(coronal_node),
        "whim_quad_node": asdict(whim_node),
        "notes": {
            "node": "N-way junction: C_node = N·(R/(r_spine/√N))²; preferred collapse site.",
            "nonlinear": "pinch_nonlinear_factor = (q̇_self,loc/q̇_bulk)/C — hot-back-reaction gain beyond geometry.",
            "honesty": "Fixed point not proved unique in Lean; no Fermi tails or derived BH masses.",
        },
    }


if __name__ == "__main__":
    print(json.dumps(default_readout(), indent=2))
