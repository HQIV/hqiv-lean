#!/usr/bin/env python3
"""
Global TUFT hadron excitation readout — one formula, all sectors.

Single lock-in factorization (baryons + mesons, no per-particle operator menus):

  m(ξ, channel) = g_chart(ξ) · [ 1 + (R_in(ξ_split) − 1) · G_twist(ξ) ]

where
  g_chart(ξ)     = g_heavy(ξ) · (m_chart / m_heavy)     — vev ground on TUFT chart row
  G_twist        = channel twist / same (n,ℓ) at ξ_lock — unity at lock-in per mode
  Δ_Beltrami     = 1-jet detuned drum steps on m_chart (γ/2 slope, FanoResonance)
  w_content      = HadronMassReadout closure weight (1 for baryon; 8/27…1 for meson)
  ξ_split        = ξ_chart + invert(w · Δ_rad) + invert(w · Δ_orb) on trapped curve

Lean mirrors: `TuftGlobalHadronReadout.tuftExcitedMassGlobalAtXi_MeV`,
`HadronMassReadout.tuftContentExcitationWeight`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Literal

import hqiv_continuous_shell_mass as csm
import hqiv_coupling_linear_system as cpr
import hqiv_excited_states as hes
import hqiv_lean_physics_primitives as lean
import hqiv_tuft_shell_chart as tsc

TUFT_HEAVY_CHART_SHELL = tsc.TUFT_HEAVY_CHART_SHELL
TUFT_STRONG_CHART_SHELL = tsc.TUFT_STRONG_CHART_SHELL
XI_LOCKIN = lean.XI_LOCKIN
GAMMA = lean.GAMMA

# Lean `hadronIntrinsicScale_meson` · `valenceChannelFraction 2`
MESON_LIGHT_EXCITATION_WEIGHT = (4.0 / 9.0) * (2.0 / 3.0)


@dataclass(frozen=True)
class TuftExcitationChannel:
    """Canonical excitation tag: TUFT chart row + (n, ℓ) + valence content."""

    chart_shell: int
    n: int
    ell: int
    valence_quarks: int
    n_strange: int = 0
    isoscalar: bool = False
    negative_parity: bool = False
    pdg_key: str | None = None

    @property
    def tag(self) -> str:
        return self.pdg_key or f"(n={self.n}, ℓ={self.ell})"

    @property
    def is_meson(self) -> bool:
        return self.valence_quarks == 2

    @property
    def is_baryon(self) -> bool:
        return self.valence_quarks == 3

    @classmethod
    def baryon(
        cls,
        n: int,
        ell: int,
        pdg_key: str | None = None,
        *,
        negative_parity: bool = False,
    ) -> TuftExcitationChannel:
        return cls(TUFT_HEAVY_CHART_SHELL, n, ell, 3, 0, False, negative_parity, pdg_key)

    @classmethod
    def meson(
        cls,
        n: int,
        ell: int,
        n_strange: int = 0,
        pdg_key: str | None = None,
        *,
        isoscalar: bool = False,
    ) -> TuftExcitationChannel:
        return cls(TUFT_STRONG_CHART_SHELL, n, ell, 2, n_strange, isoscalar, False, pdg_key)


def mode_shell(ch: TuftExcitationChannel) -> int:
    return ch.chart_shell + ch.n + ch.ell


def radial_shell(ch: TuftExcitationChannel) -> int:
    return ch.chart_shell + ch.n


def orbital_shell(ch: TuftExcitationChannel) -> int:
    return ch.chart_shell + ch.ell


def omaxwell_fano_detuning1_jet(m: int) -> float:
    """Lean `omaxwellFanoDetuning1Jet`: 1 + (γ/2) · m."""
    return 1.0 + (GAMMA / 2.0) * float(m)


def tuft_content_excitation_weight(ch: TuftExcitationChannel) -> float:
    """
    Lean `HadronMassReadout.tuftContentExcitationWeight`.

    Baryon (3 valence, colorComposed): unity.
    Meson pair: hadronIntrinsicScale · valenceChannelFraction, lifted by strangeness.
    Light isoscalar (ω): isovector base × (1 + γ/2) — 1-jet Fano detuning on the pair.
    """
    if ch.is_baryon:
        return 1.0
    w_light = MESON_LIGHT_EXCITATION_WEIGHT
    if ch.n_strange >= ch.valence_quarks:
        return 1.0
    if ch.n_strange == 1:
        return math.sqrt(w_light)
    if ch.isoscalar and ch.n_strange == 0:
        return w_light * (1.0 + GAMMA / 2.0)
    return w_light


def tuft_excitation_coupling_weight(ch: TuftExcitationChannel) -> float:
    """
    Lean `HadronMassReadout.tuftExcitationCouplingWeight`.

    Mixed radial+orbital: 2 · hadronIntrinsicScale(.meson) = 8/9.
    Negative-parity pure orbital (ℓ≥2): 1 − γ/(2(ℓ+1)).
    Otherwise unity (incl. mesons).
    """
    n, ell = ch.n, ch.ell
    if n >= 1 and ell >= 1:
        return 2.0 * (4.0 / 9.0)
    if n == 0 and ell >= 2 and ch.negative_parity:
        return 1.0 - (GAMMA / 2.0) / float(ell + 1)
    return 1.0


def tuft_beltrami_weight(ch: TuftExcitationChannel) -> float:
    """Valence content weight × excitation Beltrami coupling."""
    return tuft_content_excitation_weight(ch) * tuft_excitation_coupling_weight(ch)


def tuft_ground_at_xi_mev(xi: float, chart_shell: int) -> float:
    """Vev-pinned ground on chart row `m_chart` (heavy = baryon anchor)."""
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    g_heavy = tmse.tuft_hadron_ground_at_xi_mev(xi)
    return g_heavy * float(chart_shell) / float(TUFT_HEAVY_CHART_SHELL)


def beltrami_radial_delta_mev(xi: float, ch: TuftExcitationChannel) -> float:
    """Radial Beltrami increment on chart drum (Lean `tuft*BeltramiRadialDeltaAtXi`)."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    m0 = float(ch.chart_shell)
    m1 = float(radial_shell(ch))
    s0 = cpr.shell_surface(int(m0))
    s1 = cpr.shell_surface(int(m1))
    return g * (s1 / s0 - 1.0)


def beltrami_orbital_delta_mev(xi: float, ch: TuftExcitationChannel) -> float:
    """Orbital Beltrami increment on chart drum (Lean `tuft*BeltramiOrbitalDeltaAtXi`)."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    step = cpr.geometric_resonance_step(float(orbital_shell(ch)), float(ch.chart_shell))
    return g * max(step - 1.0, 0.0)


def beltrami_radial_delta_1jet_mev(xi: float, ch: TuftExcitationChannel) -> float:
    """1-jet detuned radial step (Fano `detunedShellSurface`; used in channel twist only)."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    m0 = float(ch.chart_shell)
    m1 = float(radial_shell(ch))
    s0 = cpr.detuned_shell_surface(int(m0))
    s1 = cpr.detuned_shell_surface(int(m1))
    return g * (s1 / s0 - 1.0)


def beltrami_orbital_delta_1jet_mev(xi: float, ch: TuftExcitationChannel) -> float:
    """1-jet detuned orbital step (diagnostic; twist uses 1-jet Fano detuning)."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    step = cpr.geometric_resonance_step(float(orbital_shell(ch)), float(ch.chart_shell))
    return g * max(step - 1.0, 0.0)


def excited_channel_xi(ch: TuftExcitationChannel) -> float:
    return float(mode_shell(ch) + 1)


def excited_detuning_twist(ch: TuftExcitationChannel) -> float:
    shell = mode_shell(ch)
    return omaxwell_fano_detuning1_jet(shell) / omaxwell_fano_detuning1_jet(ch.chart_shell)


def excited_channel_twist_at_epoch(xi: float, ch: TuftExcitationChannel) -> float:
    xi_ch = excited_channel_xi(ch)
    return (lean.omega_k_xi(xi_ch) / lean.omega_k_xi(xi)) * excited_detuning_twist(ch)


def global_channel_twist_ratio(xi: float, ch: TuftExcitationChannel) -> float:
    """Lean `tuftGlobalChannelTwistRatio`: normalized to unity at ξ_lock per (n, ℓ)."""
    t = excited_channel_twist_at_epoch(xi, ch)
    t0 = excited_channel_twist_at_epoch(XI_LOCKIN, ch)
    return t / t0


def trapped_inside_ratio(ch: TuftExcitationChannel) -> float:
    return hes.meta_horizon_trapped_inside_ratio(mode_shell(ch), ch.chart_shell)


def effective_xi_split(xi: float, ch: TuftExcitationChannel) -> float:
    """Invert content-weighted Beltrami steps separately on the chart trapped curve."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    w = tuft_beltrami_weight(ch)
    return csm.effective_xi_split_on_chart(
        ch.n,
        ch.ell,
        chart_shell=ch.chart_shell,
        ground_mev=g,
        radial_delta_mev=w * beltrami_radial_delta_mev(xi, ch) if ch.n else 0.0,
        orbital_delta_mev=w * beltrami_orbital_delta_mev(xi, ch) if ch.ell else 0.0,
        trapped_to_increment_scale=1.0,
        mode=csm.ContinuousReadout.INTERP,
    )


def effective_xi_split_orbital_only(
    xi: float,
    ch: TuftExcitationChannel,
) -> float:
    """Split inversion using orbital Beltrami only (n forced to 0)."""
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    w = tuft_beltrami_weight(ch)
    return csm.effective_xi_split_on_chart(
        0,
        ch.ell,
        chart_shell=ch.chart_shell,
        ground_mev=g,
        radial_delta_mev=0.0,
        orbital_delta_mev=w * beltrami_orbital_delta_mev(xi, ch) if ch.ell else 0.0,
        trapped_to_increment_scale=1.0,
    )


def trapped_inside_ratio_global(xi: float, ch: TuftExcitationChannel) -> float:
    """
    Trapped inside factor for the global readout.

    One rule set for all sectors (no per-hadron menus):

    * Ground (n=ℓ=0): unity.
    * Partial meson closure (w<1): split inversion of w·Δ_Beltrami.
    * Full-closure mesons (φ): integer mode-shell sample (unchanged).
    * Baryons (w=1): excitation-type branch below; Beltrami split uses
      `tuftExcitationCouplingWeight` (8/9 mixed; 1−γ/(2(ℓ+1)) negative-parity orbital).
    * Higher pure orbital (n=0, ℓ≥2): split inversion on orbital Beltrami drum.
    * Pure radial (ℓ=0, n≥1): Compton phase readout.
    * Mixed (n≥1, ℓ≥1): split inversion on radial + orbital Beltrami separately.

    This breaks the n+ℓ degeneracy that collapsed N(1520)/N(1440) and N(1680)/N(1710).
    """
    n, ell = ch.n, ch.ell
    mref = ch.chart_shell
    if n == 0 and ell == 0:
        return 1.0

    w = tuft_content_excitation_weight(ch)
    if w < 1.0 - 1e-15:
        xi_ch = effective_xi_split(xi, ch)
        return trapped_inside_ratio_at_xi(xi_ch, mref)

    if not ch.is_baryon:
        return trapped_inside_ratio(ch)

    if n == 0 and ell == 1:
        m_eff = csm.effective_m_phase(0, 1, chart_shell=mref)
        return csm.inside_ratio_discrete(m_eff, float(mref))
    if n == 0 and ell >= 2:
        xi_ch = effective_xi_split_orbital_only(xi, ch)
        return trapped_inside_ratio_at_xi(xi_ch, mref)
    if ell == 0 and n >= 1:
        m_eff = csm.effective_m_phase(n, 0, chart_shell=mref)
        return csm.inside_ratio_discrete(m_eff, float(mref))
    xi_ch = effective_xi_split(xi, ch)
    return trapped_inside_ratio_at_xi(xi_ch, mref)


def trapped_inside_ratio_at_xi(xi_ch: float, chart_shell: int) -> float:
    return csm.inside_ratio_discrete(csm.m_from_xi(xi_ch), float(chart_shell))


def tuft_excited_mass_global_at_xi_mev(xi: float, ch: TuftExcitationChannel) -> float:
    """
    Lean `tuftExcitedMassGlobalAtXi_MeV` — the single global readout.

    m = g · [ 1 + (R_in(global) − 1) · G_twist ]

    G_twist uses 1-jet Fano detuning on the mode shell; Beltrami drum uses chart
    surface ratios; R_in is content-selected (discrete at w=1, split if w<1).
    """
    g = tuft_ground_at_xi_mev(xi, ch.chart_shell)
    twist = global_channel_twist_ratio(xi, ch)
    r = trapped_inside_ratio_global(xi, ch)
    return g * (1.0 + (r - 1.0) * twist)


# --- Canonical PDG grids (same global readout for every row) ---

MESON_EXCITED_CHANNELS: list[TuftExcitationChannel] = [
    TuftExcitationChannel.meson(0, 0),
    TuftExcitationChannel.meson(0, 1, 0, "rho", isoscalar=False),
    TuftExcitationChannel.meson(0, 1, 0, "omega", isoscalar=True),
    TuftExcitationChannel.meson(1, 0, 2, "phi(1020)"),
    TuftExcitationChannel.meson(1, 0, 1, "K*(892)"),
]

BARYON_EXCITED_CHANNELS: list[TuftExcitationChannel] = [
    TuftExcitationChannel.baryon(0, 0, "proton"),
    TuftExcitationChannel.baryon(0, 1, "Delta(1232)"),
    # J^P tags: parity selects orbital Beltrami coupling at fixed (n, ℓ)
    TuftExcitationChannel.baryon(0, 2, "N(1440)", negative_parity=False),
    TuftExcitationChannel.baryon(1, 1, "N(1520)", negative_parity=True),
    TuftExcitationChannel.baryon(0, 3, "N(1680)", negative_parity=True),
    TuftExcitationChannel.baryon(0, 3, "N(1710)", negative_parity=False),
]


def build_global_rows(xi: float, channels: list[TuftExcitationChannel], prefix: str):
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    rows = []
    for ch in channels:
        mass = tuft_excited_mass_global_at_xi_mev(xi, ch)
        rows.append(
            tmse._row(
                f"{prefix} {ch.tag} global",
                mass,
                ch.pdg_key,
                "tuftExcitedMassGlobalAtXi_MeV",
            )
        )
    return rows


if __name__ == "__main__":
    import hqiv_tuft_mass_spectrum_pdg_eval as tmse

    xi = XI_LOCKIN
    print(f"TUFT global hadron readout @ ξ={xi}")
    print(f"{'sector':<8} {'tag':<14} {'global MeV':>12} {'PDG':>10} {'ratio':>8}")
    print("-" * 56)
    for ch in MESON_EXCITED_CHANNELS:
        if ch.pdg_key is None:
            continue
        m = tuft_excited_mass_global_at_xi_mev(xi, ch)
        pdg = tmse.PDG_MEV.get(ch.pdg_key)
        ratio = m / pdg if pdg else float("nan")
        print(f"{'meson':<8} {ch.pdg_key:<14} {m:12.2f} {pdg:10.2f} {ratio:8.4f}")
    for ch in BARYON_EXCITED_CHANNELS:
        if ch.pdg_key is None:
            continue
        m = tuft_excited_mass_global_at_xi_mev(xi, ch)
        pdg = tmse.PDG_MEV.get(ch.pdg_key)
        ratio = m / pdg if pdg else float("nan")
        print(f"{'baryon':<8} {ch.pdg_key:<14} {m:12.2f} {pdg:10.2f} {ratio:8.4f}")
