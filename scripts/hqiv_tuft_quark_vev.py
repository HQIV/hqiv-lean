#!/usr/bin/env python3
"""
Vev-pinned quark family on the TUFT dynamic chart.

Mirrors the hadron pin (`tuftHadronGroundAtXi_MeV`) and Lean `QuarkMetaResonance`
internal ratios (`resonanceK_internal`, `resonanceK_internal_down`).

Ground anchors at ξ_lock:
  • top    ← τ(ξ) × (m_top / τ_lock)
  • bottom ← τ(ξ) × (m_bottom / τ_lock)

Light/mid generations follow geometric resonance steps on the quark shell triples
(same shell integers as `QuarkMetaResonance.lean`).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

import cubic_phase_relax_probe as cpr

# Lean `QuarkMetaResonance` readout shell triples
M_QUARK_UP_TOP_SHELL = 31382
M_QUARK_UP_CHARM_SHELL = 233
M_QUARK_UP_LIGHT_SHELL = 0
M_QUARK_DOWN_BOTTOM_SHELL = 5329
M_QUARK_DOWN_STRANGE_SHELL = 123
M_QUARK_DOWN_LIGHT_SHELL = 7

# Lock-in anchors (GeV) — same numerals as Lean `m_top_GeV` / `m_bottom_GeV`
M_TOP_GEV = 172.57
M_BOTTOM_GEV = 4.18

QuarkFlavor = Literal["t", "c", "u", "b", "s", "d"]
UpGen = Literal[2, 1, 0]  # top, charm, up
DownGen = Literal[2, 1, 0]  # bottom, strange, down


def resonance_k_up(step: int) -> float:
    """Lean `resonanceK_internal`."""
    if step == 0:
        return cpr.geometric_resonance_step(M_QUARK_UP_TOP_SHELL, M_QUARK_UP_CHARM_SHELL)
    if step == 1:
        return cpr.geometric_resonance_step(M_QUARK_UP_CHARM_SHELL, M_QUARK_UP_LIGHT_SHELL)
    raise ValueError(f"up resonance step must be 0 or 1, got {step}")


def resonance_k_down(step: int) -> float:
    """Lean `resonanceK_internal_down`."""
    if step == 0:
        return cpr.geometric_resonance_step(M_QUARK_DOWN_BOTTOM_SHELL, M_QUARK_DOWN_STRANGE_SHELL)
    if step == 1:
        return cpr.geometric_resonance_step(M_QUARK_DOWN_STRANGE_SHELL, M_QUARK_DOWN_LIGHT_SHELL)
    raise ValueError(f"down resonance step must be 0 or 1, got {step}")


def up_resonance_product(gen: UpGen) -> float:
    """Product of internal octave drops from top down to `gen`."""
    if gen == 2:
        return 1.0
    if gen == 1:
        return resonance_k_up(0)
    return resonance_k_up(0) * resonance_k_up(1)


def down_resonance_product(gen: DownGen) -> float:
    if gen == 2:
        return 1.0
    if gen == 1:
        return resonance_k_down(0)
    return resonance_k_down(0) * resonance_k_down(1)


def tuft_top_to_tau_pin_at_lockin(tau_lock_mev: float) -> float:
    """GeV per MeV of dynamic τ at lock-in (top calibration)."""
    return (M_TOP_GEV * 1000.0) / tau_lock_mev


def tuft_bottom_to_tau_pin_at_lockin(tau_lock_mev: float) -> float:
    return (M_BOTTOM_GEV * 1000.0) / tau_lock_mev


def tuft_quark_top_ground_at_xi_mev(xi: float, tau_at_xi_mev: float, tau_lock_mev: float) -> float:
    return tau_at_xi_mev * tuft_top_to_tau_pin_at_lockin(tau_lock_mev)


def tuft_quark_bottom_ground_at_xi_mev(xi: float, tau_at_xi_mev: float, tau_lock_mev: float) -> float:
    _ = xi
    return tau_at_xi_mev * tuft_bottom_to_tau_pin_at_lockin(tau_lock_mev)


def tuft_quark_up_type_at_xi_mev(
    gen: UpGen,
    *,
    tau_at_xi_mev: float,
    tau_lock_mev: float,
) -> float:
    top = tuft_quark_top_ground_at_xi_mev(0.0, tau_at_xi_mev, tau_lock_mev)
    return top / up_resonance_product(gen)


def tuft_quark_down_type_at_xi_mev(
    gen: DownGen,
    *,
    tau_at_xi_mev: float,
    tau_lock_mev: float,
) -> float:
    bottom = tuft_quark_bottom_ground_at_xi_mev(0.0, tau_at_xi_mev, tau_lock_mev)
    return bottom / down_resonance_product(gen)


@dataclass(frozen=True)
class QuarkSpectrumAtXi:
    t_mev: float
    c_mev: float
    u_mev: float
    b_mev: float
    s_mev: float
    d_mev: float

    def as_dict_gev(self) -> dict[str, float]:
        return {
            "t": self.t_mev / 1000.0,
            "c": self.c_mev / 1000.0,
            "u": self.u_mev / 1000.0,
            "b": self.b_mev / 1000.0,
            "s": self.s_mev / 1000.0,
            "d": self.d_mev / 1000.0,
        }


def tuft_quark_spectrum_at_xi_mev(tau_at_xi_mev: float, tau_lock_mev: float) -> QuarkSpectrumAtXi:
    kw = {"tau_at_xi_mev": tau_at_xi_mev, "tau_lock_mev": tau_lock_mev}
    return QuarkSpectrumAtXi(
        t_mev=tuft_quark_up_type_at_xi_mev(2, **kw),
        c_mev=tuft_quark_up_type_at_xi_mev(1, **kw),
        u_mev=tuft_quark_up_type_at_xi_mev(0, **kw),
        b_mev=tuft_quark_down_type_at_xi_mev(2, **kw),
        s_mev=tuft_quark_down_type_at_xi_mev(1, **kw),
        d_mev=tuft_quark_down_type_at_xi_mev(0, **kw),
    )
