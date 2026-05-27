#!/usr/bin/env python3
"""
HQIV BBN epoch network: integrate light-element abundances as the universe cools.

Cooling path: T from 1 MeV → 0.01 MeV (shell m grows via T_Pl/T − 1).

Fixed at lock-in: η, derivedDeltaM, Q_D, Q_4, Q_3 from composite-trace weights.
Epoch-varying: α_eff(m(T)), γ_eff(m(T)), H(T), exp(Q/T).

Reactions (baryon number per H):
  n + p ⇄ D + γ
  D + p → ³He + γ
  D + D → ⁴He + γ
  n → p (weak, until freeze-out)

Run:
  python3 scripts/hqiv_bbn_epoch_network.py
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

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
# ³He channel subdominant in standard BBN
HE3_BRANCH_SCALE = 0.0


@dataclass
class NetworkState:
    n_n: float
    n_p: float
    n_D: float
    n_He3: float
    n_He4: float

    def baryon_sum(self) -> float:
        return self.n_n + self.n_p + 2 * self.n_D + 3 * self.n_He3 + 4 * self.n_He4

    def clamp_nonneg(self) -> NetworkState:
        return NetworkState(
            n_n=max(0.0, self.n_n),
            n_p=max(0.0, self.n_p),
            n_D=max(0.0, self.n_D),
            n_He3=max(0.0, self.n_He3),
            n_He4=max(0.0, self.n_He4),
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


def dstate_dt(
    T_mev: float,
    s: NetworkState,
    *,
    eta: float,
    Q_np: float,
    Q_D: float,
    Q_3: float,
    Q_4: float,
    T_freeze: float,
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

    return NetworkState(
        n_n=dn - r_form,
        n_p=dp - r_form - r_Dp,
        n_D=dD - r_Dp - 2.0 * r_DD,
        n_He3=r_Dp,
        n_He4=r_DD,
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
) -> tuple[NetworkState, dict]:
    T_freeze = bbn.freezeout_temperature_mev(Q_np, eta)
    temps = [T_high * (T_low / T_high) ** (i / n_steps) for i in range(n_steps + 1)]

    x0 = weak_equilibrium_xn(T_high, Q_np)
    n_n0 = eta * x0 / (1.0 + x0)
    s = NetworkState(n_n=n_n0, n_p=eta - n_n0, n_D=0.0, n_He3=0.0, n_He4=0.0)

    history: list[dict] = []
    weak_locked = False
    for i in range(n_steps):
        T = temps[i]
        if not weak_locked and T <= T_freeze:
            x_f = weak_equilibrium_xn(T_freeze, Q_np)
            n_n_f = eta * x_f / (1.0 + x_f)
            # Weak sector locks n/p; nuclear synthesis starts from free nucleons only.
            s = NetworkState(
                n_n=n_n_f,
                n_p=eta - n_n_f,
                n_D=0.0,
                n_He3=0.0,
                n_He4=0.0,
            )
            weak_locked = True
        dT = temps[i + 1] - temps[i]  # negative (cooling)
        H = max(hubble_rate_s(T), 1e-30)
        dt = -dT / (T * H)  # RD: dT/dt = −T H  ⇒  dt > 0
        ds = dstate_dt(T, s, eta=eta, Q_np=Q_np, Q_D=Q_D, Q_3=Q_3, Q_4=Q_4, T_freeze=T_freeze)
        s = NetworkState(
            n_n=s.n_n + ds.n_n * dt,
            n_p=s.n_p + ds.n_p * dt,
            n_D=s.n_D + ds.n_D * dt,
            n_He3=s.n_He3 + ds.n_He3 * dt,
            n_He4=s.n_He4 + ds.n_He4 * dt,
        ).clamp_nonneg()
        # Enforce baryon budget n_n + n_p + 2 n_D + 3 n_He3 + 4 n_He4 = η
        total = s.baryon_sum()
        if total > 0 and abs(total - eta) > 1e-12 * eta:
            scale = eta / total
            s = NetworkState(
                n_n=s.n_n * scale,
                n_p=s.n_p * scale,
                n_D=s.n_D * scale,
                n_He3=s.n_He3 * scale,
                n_He4=s.n_He4 * scale,
            )
        history.append(
            {
                "T_MeV": T,
                "shell": bbn.shell_index_from_mev(T),
                "alpha_eff_ratio": alpha_eff_ratio_at_T(T),
                "gamma_eff": gamma_eff_at_T(T),
                "H_s": hubble_rate_s(T),
                "n_n": s.n_n,
                "n_D": s.n_D,
                "n_He4": s.n_He4,
            }
        )

    meta = {
        "T_freeze_MeV": T_freeze,
        "T_high_MeV": T_high,
        "T_low_MeV": T_low,
        "n_steps": n_steps,
        "final_baryon_sum": s.baryon_sum(),
        "eta": eta,
    }
    return s, meta


def readout_from_state(s: NetworkState, eta: float) -> dict[str, float]:
    # Mass fraction Y_p = 4 n(⁴He)/η_baryon (³He contributes 3/4 of its number)
    Yp = (4.0 * s.n_He4 + 3.0 * s.n_He3) / eta if eta > 0 else 0.0
    return {
        "Yp": Yp,
        "D_over_H": s.n_D / eta if eta > 0 else 0.0,
        "He3_over_H": s.n_He3 / eta if eta > 0 else 0.0,
        "Li7_over_H": 0.0,  # not in this network yet
        "n_n_relic": s.n_n / eta if eta > 0 else 0.0,
    }


def main() -> None:
    w = bbn.load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    dm = float(w["derivedDeltaM_MeV"])
    eta = bbn.ETA_PAPER
    Q_D, Q_4, Q_3 = bbn.lockin_binding_q(m_p, hes.REFERENCE_M)

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
            "rate_scale": RATE_SCALE,
            "weak_rate_mult": WEAK_RATE_MULT,
            "dd_rate_mult": DD_RATE_MULT,
            "he3_branch_scale": HE3_BRANCH_SCALE,
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
