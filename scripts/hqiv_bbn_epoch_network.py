#!/usr/bin/env python3
"""
HQIV BBN epoch network: integrate light-element abundances as the universe cools.

Cooling path: T from 1 MeV → 0.01 MeV (shell m grows via T_Pl/T − 1).

Fixed at lock-in: η, derivedDeltaM, Q_D, Q_4, Q_3 from composite-trace weights.
Epoch-varying: α_eff(m(T)), γ_eff(m(T)), shell reaction opportunity, exp(Q/T).

Reactions (baryon number per H):
  n + p ⇄ D + γ
  D + p → ³He + γ
  D + D → ⁴He + γ
  ³He + ⁴He → ⁷Be + γ
  ⁷Be + e⁻ → ⁷Li + ν_e
  n → p (weak, until freeze-out)

Run:
  python3 scripts/hqiv_bbn_epoch_network.py
"""

from __future__ import annotations

import json
import math
from collections.abc import Callable
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import hqiv_bbn_abundances as bbn
import hqiv_excited_states as hes

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "bbn_witnesses.json"

G_STAR = 10.75
M_PL_MEV = 1.2209e22
# H(1 MeV) ≈ 1.6×10⁻³ s⁻¹ (RD); Lean `bbnHubbleRate` uses same T²/M_Pl geometry
H_REF_S = 1.66e-3
# Rate geometry: T^n × exp(Q/T) × η × (α_eff(m)/α_eff(lockin))
# Calibrated to HQIV weak + composite-trace rates (no Coc input)
RATE_SCALE = 1.0e-2
WEAK_RATE_MULT = 400.0
DD_RATE_MULT = 8.0
# ³He dynamical branch stays off (D + p → ³He competes with ⁴He synthesis).
HE3_BRANCH_SCALE = 0.0
# ³He + ⁴He → ⁷Be uses a thermal ³He proxy; ⁷Be → ⁷Li is electron capture in the tail.
BE7_FORM_MULT = 0.25 * bbn.STRONG_CHANNEL_FRACTION
BE7_CAPTURE_MULT = 0.0012 * bbn.STRONG_CHANNEL_FRACTION
# Shell-opportunity integrator uses O(10²–10³) larger steps than legacy H·dt.
BE7_LEGACY_OPPORTUNITY_REF = 1.5


@dataclass
class NetworkState:
    n_n: float
    n_p: float
    n_D: float
    n_He3: float
    n_He4: float
    n_Be7: float = 0.0
    n_Li7: float = 0.0

    def baryon_sum(self) -> float:
        return (
            self.n_n
            + self.n_p
            + 2 * self.n_D
            + 3 * self.n_He3
            + 4 * self.n_He4
            + 7 * self.n_Be7
            + 7 * self.n_Li7
        )

    def clamp_nonneg(self) -> NetworkState:
        return NetworkState(
            n_n=max(0.0, self.n_n),
            n_p=max(0.0, self.n_p),
            n_D=max(0.0, self.n_D),
            n_He3=max(0.0, self.n_He3),
            n_He4=max(0.0, self.n_He4),
            n_Be7=max(0.0, self.n_Be7),
            n_Li7=max(0.0, self.n_Li7),
        )


def hubble_rate_s(T_mev: float) -> float:
    """H(T) s⁻¹, RD; matches Lean T²/M_Pl shape, calibrated at T=1 MeV."""
    return H_REF_S * math.sqrt(G_STAR / 10.75) * T_mev**2


def shell_nat_from_T(T_mev: float) -> int:
    m = int(bbn.T_PL_MEV / T_mev - 1.0)
    return max(hes.REFERENCE_M, min(m, hes.REFERENCE_M + 2000))


def alpha_eff_ratio_at_T(T_mev: float, c: float = 1.0) -> float:
    m = shell_nat_from_T(T_mev)
    ae = hes.alpha_eff_at_shell(m, c)
    ae0 = hes.alpha_eff_at_shell(hes.REFERENCE_M, c)
    return ae / ae0


def gamma_eff_at_T(T_mev: float) -> float:
    """γ_HQIV × T(m) with m from MeV shell map (natural-unit T = T_mev/T_Pl)."""
    m = shell_nat_from_T(T_mev)
    T_nat = T_mev / bbn.T_PL_MEV
    return bbn.GAMMA_HQIV * T_nat


def formation_weight(Q_mev: float, T_mev: float) -> float:
    if T_mev <= 0:
        return 0.0
    x = Q_mev / T_mev
    if x > 700:
        return math.exp(700)
    if x < -700:
        return 0.0
    return math.exp(x)


def weak_equilibrium_xn(T_mev: float, Q_np: float) -> float:
    x = math.exp(-Q_np / T_mev)
    return x / (1.0 + x)


def rate_np_to_D(eta: float, T_mev: float, Q_D: float) -> float:
    return RATE_SCALE * eta * alpha_eff_ratio_at_T(T_mev) * formation_weight(Q_D, T_mev) * T_mev**1.5


def photodissociation_boost(T_mev: float) -> float:
    """Enhance D destruction in the MeV tail (bottleneck competition)."""
    if T_mev >= 0.2:
        return 1.0
    return min(1.0e6, (0.12 / max(T_mev, 0.04)) ** 2)


def rate_D_destroy(T_mev: float, Q_D: float) -> float:
    return RATE_SCALE * photodissociation_boost(T_mev) * formation_weight(-Q_D, T_mev) * T_mev**3


def rate_Dp_to_He3(eta: float, T_mev: float, Q_D: float, Q_3: float) -> float:
    Q = max(0.01, Q_3 - Q_D)  # D + p → ³He: Q = B(³He) − B(D)
    return (
        RATE_SCALE
        * HE3_BRANCH_SCALE
        * eta
        * alpha_eff_ratio_at_T(T_mev)
        * formation_weight(Q, T_mev)
        * T_mev**1.5
    )


def dd_fusion_gate(T_mev: float) -> float:
    """Fade 2D→⁴He below ~0.04 MeV (deuterium bottleneck tail)."""
    return min(1.0, max(0.0, (T_mev - 0.035) / 0.06))


def he3_thermal_proxy_per_h(T_mev: float, eta: float, Q_3: float, Q_4: float) -> float:
    """Schematic ³He/H from HQIV thermal sink (enables ⁷Be without a large D + p branch)."""
    sink = bbn.thermal_sink(Q_3, Q_4, T_mev)
    return eta * math.sqrt(max(sink, 0.0))


def be7_fusion_gate(T_mev: float) -> float:
    """Turn on ³He + ⁴He → ⁷Be below ~0.3 MeV (after α synthesis)."""
    return min(1.0, max(0.0, (0.30 - T_mev) / 0.12))


def rate_He3_He4_to_Be7(
    eta: float, T_mev: float, Q_7: float, Q_3: float, Q_4: float, Q_np: float
) -> float:
    """³He + ⁴He → ⁷Be: barrier scaled by weak channel (not raw 7 MeV tail)."""
    Q_barrier = bbn.be7_electron_capture_q(Q_7, Q_np)
    return (
        RATE_SCALE
        * BE7_FORM_MULT
        * eta
        * alpha_eff_ratio_at_T(T_mev)
        * formation_weight(Q_barrier, T_mev)
        * T_mev**1.5
        * be7_fusion_gate(T_mev)
    )


def be7_capture_gate(T_mev: float) -> float:
    """⁷Be electron capture active in the MeV tail."""
    return min(1.0, max(0.0, (0.20 - T_mev) / 0.08))


def rate_Be7_to_Li7(
    T_mev: float,
    Q_be: float,
    Q_li: float,
    Q_np: float,
) -> float:
    """⁷Be + e⁻ → ⁷Li: MeV-tail capture; Q from Be vs Li cluster wells."""
    if T_mev <= 0.0:
        return 0.0
    Q_ec = bbn.be7_to_li7_capture_q(Q_be, Q_li)
    if Q_ec <= 0.0:
        Q_ec = bbn.be7_electron_capture_q(Q_be, Q_np)
    return (
        RATE_SCALE
        * BE7_CAPTURE_MULT
        * formation_weight(Q_ec, T_mev)
        * be7_capture_gate(T_mev)
        / max(T_mev, 0.02) ** 0.5
    )


def rate_DD_to_He4(eta: float, T_mev: float, Q_D: float, Q_4: float) -> float:
    # 2D → ⁴He: Q = M(⁴He) − 2M(D) = Q_4 − 2 Q_D (lock-in composite trace)
    Q = max(0.01, Q_4 - 2.0 * Q_D)
    return (
        RATE_SCALE
        * DD_RATE_MULT
        * eta
        * alpha_eff_ratio_at_T(T_mev)
        * formation_weight(Q, T_mev)
        * T_mev**1.5
        * dd_fusion_gate(T_mev)
    )


def weak_relax_rate(T_mev: float, Q_np: float) -> float:
    """n ↔ p relaxation toward equilibrium (before freeze-out)."""
    return RATE_SCALE * WEAK_RATE_MULT * formation_weight(-Q_np, T_mev) * T_mev**5


def be7_lithium_opportunity_scale(reaction_opportunity: float) -> tuple[float, float]:
    """Scale A = 7 channels when shell opportunity ≫ legacy H·dt."""
    ref = BE7_LEGACY_OPPORTUNITY_REF
    opp = max(reaction_opportunity, ref)
    prod = min(1.0, ref / opp)
    cap = min(1.0, (20.0 * ref) / opp)
    return prod, cap


def dstate_dt(
    T_mev: float,
    s: NetworkState,
    *,
    eta: float,
    Q_np: float,
    Q_D: float,
    Q_3: float,
    Q_4: float,
    Q_7: float,
    Q_li: float,
    T_freeze: float,
    be7_prod_scale: float = 1.0,
    be7_cap_scale: float = 1.0,
    reaction_opportunity: float = 1.0,
) -> NetworkState:
    """d(species)/dt [s⁻¹] for abundances per H (comoving; no H dilution)."""
    s = s.clamp_nonneg()
    x_eq = weak_equilibrium_xn(T_mev, Q_np)

    if T_mev > T_freeze:
        target_n = eta * x_eq / (1.0 + x_eq)
        target_p = eta - target_n
        dn = weak_relax_rate(T_mev, Q_np) * (target_n - s.n_n)
        dp = weak_relax_rate(T_mev, Q_np) * (target_p - s.n_p)
    else:
        dn = 0.0
        dp = 0.0

    r_form = rate_np_to_D(eta, T_mev, Q_D) * s.n_n * s.n_p
    r_destroy = rate_D_destroy(T_mev, Q_D) * s.n_D
    dD = r_form - r_destroy

    r_Dp = rate_Dp_to_He3(eta, T_mev, Q_D, Q_3) * s.n_D * s.n_p
    r_DD = rate_DD_to_He4(eta, T_mev, Q_D, Q_4) * s.n_D * s.n_D
    n_he3_src = max(s.n_He3, he3_thermal_proxy_per_h(T_mev, eta, Q_3, Q_4))
    r_Be7_raw = (
        be7_prod_scale
        * rate_He3_He4_to_Be7(eta, T_mev, Q_7, Q_3, Q_4, Q_np)
        * n_he3_src
        * s.n_He4
    )
    opp = max(reaction_opportunity, 1e-30)
    be7_frac = 0.02 if opp <= BE7_LEGACY_OPPORTUNITY_REF else 1e-5
    r_Be7 = min(r_Be7_raw, be7_frac * max(s.n_He4, 0.0) / opp)
    r_Li7 = min(
        be7_cap_scale * rate_Be7_to_Li7(T_mev, Q_7, Q_li, Q_np) * s.n_Be7,
        max(s.n_Be7, 0.0) / opp,
    )

    return NetworkState(
        n_n=dn - r_form,
        n_p=dp - r_form - r_Dp,
        n_D=dD - r_Dp - 2.0 * r_DD,
        n_He3=r_Dp,
        n_He4=r_DD - r_Be7,
        n_Be7=r_Be7 - r_Li7,
        n_Li7=r_Li7,
    )


def integrate_cooling_network(
    eta: float,
    Q_np: float,
    Q_D: float,
    Q_3: float,
    Q_4: float,
    *,
    T_high: float = bbn.BBN_T_HIGH_MEV,
    T_low: float = bbn.BBN_T_LOW_MEV,
    n_steps: int = 200,
    q_provider: Callable[[float], tuple[float, ...]] | None = None,
    opportunity_provider: Callable[[float, float, float], dict[str, Any]] | None = None,
    h_provider: Callable[[float, float], float] | None = None,
    history_stride: int = 1,
) -> tuple[NetworkState, dict[str, Any]]:
    """Cooling integration with optional per-temperature Q and shell-opportunity providers.

    ``q_provider(T_MeV)`` returns ``(Q_np, Q_D, Q_3, Q_4[, Q_7[, Q_Li]])`` at that epoch.
    ``opportunity_provider(T_MeV, T_next_MeV, eta)`` returns a dimensionless
    shell reaction opportunity. ``h_provider`` is retained only for legacy
    comparison mode when no shell opportunity provider is supplied.
    """
    q_np0 = Q_np if q_provider is None else q_provider(T_high)[0]
    T_freeze = bbn.freezeout_temperature_mev(q_np0, eta)
    temps = [T_high * (T_low / T_high) ** (i / n_steps) for i in range(n_steps + 1)]

    x0 = weak_equilibrium_xn(T_high, q_np0)
    n_n0 = eta * x0 / (1.0 + x0)
    s = NetworkState(n_n=n_n0, n_p=eta - n_n0, n_D=0.0, n_He3=0.0, n_He4=0.0, n_Be7=0.0, n_Li7=0.0)

    history: list[dict[str, Any]] = []
    weak_locked = False
    for i in range(n_steps):
        T = temps[i]
        if q_provider is not None:
            q_row = q_provider(T)
            q_np, Q_D, Q_3, Q_4 = float(q_row[0]), float(q_row[1]), float(q_row[2]), float(q_row[3])
            if len(q_row) > 4:
                Q_7 = float(q_row[4])
            else:
                Q_7 = bbn.be7_binding_q(Q_4, m_nucleon=None)
            if len(q_row) > 5:
                Q_li = float(q_row[5])
            else:
                Q_li = bbn.li7_cluster_binding_q()
        else:
            q_np, Q_D, Q_3, Q_4 = Q_np, Q_D, Q_3, Q_4
            Q_7 = bbn.be7_binding_q(Q_4)
            Q_li = bbn.li7_cluster_binding_q()

        if not weak_locked and T <= T_freeze:
            x_f = weak_equilibrium_xn(T_freeze, q_np)
            n_n_f = eta * x_f / (1.0 + x_f)
            s = NetworkState(
                n_n=n_n_f,
                n_p=eta - n_n_f,
                n_D=0.0,
                n_He3=0.0,
                n_He4=0.0,
                n_Be7=0.0,
                n_Li7=0.0,
            )
            weak_locked = True
        T_next = temps[i + 1]
        dT = T_next - T
        legacy_H = max(
            h_provider(T, eta) if h_provider is not None else hubble_rate_s(T),
            1e-30,
        )
        if opportunity_provider is None:
            opportunity_row = {
                "reaction_opportunity": -dT / (T * legacy_H),
                "mode": "legacy_H_cooling",
            }
        else:
            opportunity_row = opportunity_provider(T, T_next, eta)
        reaction_opportunity = max(float(opportunity_row["reaction_opportunity"]), 0.0)
        be7_prod_scale, be7_cap_scale = be7_lithium_opportunity_scale(reaction_opportunity)
        ds = dstate_dt(
            T,
            s,
            eta=eta,
            Q_np=q_np,
            Q_D=Q_D,
            Q_3=Q_3,
            Q_4=Q_4,
            Q_7=Q_7,
            Q_li=Q_li,
            T_freeze=T_freeze,
            be7_prod_scale=be7_prod_scale,
            be7_cap_scale=be7_cap_scale,
            reaction_opportunity=reaction_opportunity,
        )
        s = NetworkState(
            n_n=s.n_n + ds.n_n * reaction_opportunity,
            n_p=s.n_p + ds.n_p * reaction_opportunity,
            n_D=s.n_D + ds.n_D * reaction_opportunity,
            n_He3=s.n_He3 + ds.n_He3 * reaction_opportunity,
            n_He4=s.n_He4 + ds.n_He4 * reaction_opportunity,
            n_Be7=s.n_Be7 + ds.n_Be7 * reaction_opportunity,
            n_Li7=s.n_Li7 + ds.n_Li7 * reaction_opportunity,
        ).clamp_nonneg()
        total = s.baryon_sum()
        if total > 0 and abs(total - eta) > 1e-12 * eta:
            scale = eta / total
            s = NetworkState(
                n_n=s.n_n * scale,
                n_p=s.n_p * scale,
                n_D=s.n_D * scale,
                n_He3=s.n_He3 * scale,
                n_He4=s.n_He4 * scale,
                n_Be7=s.n_Be7 * scale,
                n_Li7=s.n_Li7 * scale,
            )
        if i % max(1, history_stride) == 0:
            history.append(
                {
                    "T_MeV": T,
                    "shell": bbn.shell_index_from_mev(T),
                    "Q_D_MeV": Q_D,
                    "Q_4He_MeV": Q_4,
                    "Q_np_MeV": q_np,
                    "alpha_eff_ratio": alpha_eff_ratio_at_T(T),
                    "gamma_eff": gamma_eff_at_T(T),
                    "reaction_opportunity": reaction_opportunity,
                    "opportunity_mode": opportunity_row.get("mode", "shell_opportunity"),
                    "H_s_diagnostic": legacy_H,
                    **{
                        k: v
                        for k, v in opportunity_row.items()
                        if k not in {"reaction_opportunity", "mode"}
                    },
                    "Q_7Be_MeV": Q_7,
                    "n_n": s.n_n,
                    "n_D": s.n_D,
                    "n_He3": s.n_He3,
                    "n_He4": s.n_He4,
                    "n_Be7": s.n_Be7,
                    "n_Li7": s.n_Li7,
                }
            )

    meta: dict[str, Any] = {
        "T_freeze_MeV": T_freeze,
        "T_high_MeV": T_high,
        "T_low_MeV": T_low,
        "n_steps": n_steps,
        "final_baryon_sum": s.baryon_sum(),
        "eta": eta,
        "dynamic_q_provider": q_provider is not None,
        "dynamic_opportunity_provider": opportunity_provider is not None,
        "dynamic_h_provider": h_provider is not None and opportunity_provider is None,
        "history_stride": history_stride,
        "history": history,
    }
    return s, meta


def readout_from_state(s: NetworkState, eta: float) -> dict[str, float]:
    # Mass fraction Y_p = 4 n(⁴He)/η_baryon (³He contributes 3/4 of its number)
    Yp = (4.0 * s.n_He4 + 3.0 * s.n_He3) / eta if eta > 0 else 0.0
    return {
        "Yp": Yp,
        "D_over_H": s.n_D / eta if eta > 0 else 0.0,
        "He3_over_H": s.n_He3 / eta if eta > 0 else 0.0,
        "Be7_over_H": s.n_Be7 / eta if eta > 0 else 0.0,
        "Li7_over_H": s.n_Li7 / eta if eta > 0 else 0.0,
        "n_n_relic": s.n_n / eta if eta > 0 else 0.0,
    }


def main() -> None:
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    dm = float(w["derivedDeltaM_MeV"])
    eta = bbn.ETA_PAPER
    Q_D, Q_4, Q_3, Q_7 = bbn.lockin_binding_q(m_p, hes.REFERENCE_M)

    final, meta = integrate_cooling_network(eta, dm, Q_D, Q_3, Q_4, n_steps=400)
    abund = readout_from_state(final, eta)
    partition = bbn.integrate_bbn_window(eta, m_p, dm, Q_D, Q_4, Q_3)
    tail = bbn.abundances_at_epoch(eta, bbn.BBN_T_MID_MEV, m_p, dm, Q_D, Q_4, Q_3)
    coc = bbn.coc2015_abundances(eta)

    payload = {
        "source": "HQIV BBN epoch network (cooling integration in T)",
        "lean_modules": [
            "Hqiv.Physics.BBNNetworkFromWeights",
            "Hqiv.Physics.BBNEpochEvolution",
            "Hqiv.Physics.BBNEpochNetwork",
        ],
        "python_scripts": [
            "scripts/hqiv_bbn_abundances.py",
            "scripts/hqiv_bbn_epoch_network.py",
        ],
        "hqiv_inputs": {
            "eta_paper": eta,
            "derivedDeltaM_MeV": dm,
            "Q_D_lockin_MeV": Q_D,
            "Q_4He_lockin_MeV": Q_4,
            "Q_3He_binding_MeV": Q_3,
            "Q_7Be_binding_MeV": Q_7,
            "rate_scale": RATE_SCALE,
            "weak_rate_mult": WEAK_RATE_MULT,
            "dd_rate_mult": DD_RATE_MULT,
            "he3_branch_scale": HE3_BRANCH_SCALE,
            "be7_form_mult": BE7_FORM_MULT,
            "be7_capture_mult": BE7_CAPTURE_MULT,
        },
        "epoch_network_integration": {**abund, **meta},
        "hqiv_weight_readout_at_T_0p1_MeV": tail,
        "partition_average_legacy": partition,
        "comparison_coc2015": coc,
        "observed_comparison_layer": {
            "Yp": "0.244 ± 0.004",
            "D_over_H": "(2.53 ± 0.04)×10⁻⁵",
            "He3_over_H": "≈10⁻⁵",
        },
    }

    if OUT.is_file():
        existing = json.loads(OUT.read_text())
        existing.update(payload)
        payload = existing

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")

    print(f"Wrote {OUT}")
    print("\nEpoch network (cooling T: 1 → 0.01 MeV):")
    print(f"  T_freeze     = {meta['T_freeze_MeV']:.4f} MeV")
    print(f"  Y_p          = {abund['Yp']:.5f}")
    print(f"  D/H (kinetic)= {abund['D_over_H']:.4e}")
    print(f"  ³He/H        = {abund['He3_over_H']:.4e}")
    print(f"  ⁷Be/H        = {abund['Be7_over_H']:.4e}")
    print(f"  ⁷Li/H        = {abund['Li7_over_H']:.4e}")
    print(f"  n_n relic/H  = {abund['n_n_relic']:.4e}")
    print("\nHQIV weights at T=0.1 MeV (D, ³He, ⁷Li):")
    print(f"  D/H          = {tail['D_over_H']:.4e}")
    print(f"  ³He/H        = {tail['He3_over_H']:.4e}")
    print("\nPartition average (legacy):")
    print(f"  D/H          = {partition['D_over_H']:.4e}")
    print("\nCoc2015:")
    print(f"  D/H          = {coc['D_over_H']:.4e}")


if __name__ == "__main__":
    main()
