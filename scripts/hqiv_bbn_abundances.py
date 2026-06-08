#!/usr/bin/env python3
"""
HQIV BBN from network weights **as a cosmological epoch** on the temperature ladder.

Key point: abundances depend on universe age / shell, not only on lock-in η.

  • Lock-in (m ≈ 4): baryogenesis η, nucleon masses, nuclear Q's from composite trace.
  • BBN epoch (m ≈ 10²², T ≈ 0.01–1 MeV): synthesis — integrate over this window.
  • Today (m ≈ nowShell, T ≈ T_CMB): relic abundances; no active nucleosynthesis.

Mirrors `Hqiv.Physics.BBNNetworkFromWeights` + `Hqiv.Physics.BBNEpochEvolution`.

Run:
  python3 scripts/hqiv_bbn_abundances.py
  python3 scripts/hqiv_bbn_abundances.py --epoch-sweep
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import hqiv_excited_states as hes

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "bbn_witnesses.json"
WITNESS_JSON = ROOT / "data" / "hqiv_witnesses.json"

ETA_PAPER = 6.10e-10
T_PL_MEV = 1.2209e19 * 1000.0
T_CMB_NATURAL = 1.9e-32  # T_CMB / T_Pl (Now.lean)
REFERENCE_M = hes.REFERENCE_M
GAMMA_HQIV = 2.0 / 5.0
VALLEY_COUNT = {1: 0, 2: 2, 3: 4, 4: 6}
VALLEY_HE4 = 6
ALPHA_CORE_Z = 2
PROTON_FACET_VERTEX_CONTACTS = 3
STRONG_CHANNEL_FRACTION = 4.0 / 8.0

BBN_T_LOW_MEV = 0.01
BBN_T_HIGH_MEV = 1.0
BBN_T_MID_MEV = 0.1


def load_witness() -> dict:
    if WITNESS_JSON.is_file():
        return json.loads(WITNESS_JSON.read_text())
    return {
        "derivedProtonMass_MeV": 938.272,
        "derivedDeltaM_MeV": 1.293,
        "referenceM": REFERENCE_M,
    }


def eta10(eta: float) -> float:
    return eta * 1e10


def shell_index_from_mev(T_mev: float) -> float:
    """Lean `bbnShellIndexFromMeV`: m + 1 = T_Pl_MeV / T."""
    return T_PL_MEV / T_mev - 1.0


def lockin_temperature_mev() -> float:
    return T_PL_MEV / (REFERENCE_M + 1)


def cmb_temperature_mev() -> float:
    return T_CMB_NATURAL * T_PL_MEV


def valley_count(A: int, Z: int = 0) -> int:
    """Lean `postAlphaOutsideValleyCount` via sphere-touch facet chart when A > 4."""
    if A <= 4:
        return VALLEY_COUNT.get(A, 0)
    from hqiv_post_alpha_sphere_touching import post_alpha_outside_valley_count

    return post_alpha_outside_valley_count(A, Z)


def spin_stability_participation(A: int, Z: int) -> float:
    """Lean `spinStabilityParticipation`: feasible facet touches, not isospin inequality."""
    if A <= 4:
        return 1.0
    from hqiv_post_alpha_sphere_touching import spin_stability_participation as _spin

    return _spin(A, Z)


def valley_binding_factor(A: int, Z: int = 0) -> float:
    if A <= 4:
        return 1.0 + valley_count(A) / VALLEY_HE4
    from hqiv_post_alpha_sphere_touching import (
        CONSTRUCTIVE_VALLEY_CAP,
        bbn_proton_facet_touches,
        far_neutron_weighted_contact_sum,
        proton_facet_touch_contact_sum,
    )

    cap = CONSTRUCTIVE_VALLEY_CAP / VALLEY_HE4
    touch = (
        proton_facet_touch_contact_sum(bbn_proton_facet_touches(A, Z))
        / VALLEY_HE4
        * spin_stability_participation(A, Z)
    )
    far = far_neutron_weighted_contact_sum(A, Z) / VALLEY_HE4
    return 1.0 + cap + touch + far


def cluster_binding_mev(m: int, A: int, c: float = 1.0, *, Z: int = 0) -> float:
    return float(A) * hes.e_bind_from_nucleon_trace_mev(m, c) * valley_binding_factor(A, Z)


def cluster_mass_mev(
    m: int, A: int, m_nucleon: float, c: float = 1.0, *, Z: int = 0
) -> float:
    return float(A) * m_nucleon - cluster_binding_mev(m, A, c, Z=Z)


def be7_binding_q(
    Q_4: float,
    *,
    m_shell: int | None = None,
    m_nucleon: float | None = None,
    c: float = 1.0,
) -> float:
    """⁷Be (`Z=4`): α + 2×3 proton contacts — `bbnBe7BindingQ`."""
    m_shell = m_shell if m_shell is not None else REFERENCE_M
    if m_nucleon is not None:
        return cluster_binding_mev(m_shell, 7, c, Z=4)
    return (7.0 / 4.0) * Q_4


def li7_cluster_binding_q(
    m_shell: int | None = None,
    m_nucleon: float | None = None,
    c: float = 1.0,
) -> float:
    """⁷Li (`Z=3`): facet proton + far-neutron touches at (4/8) weight."""
    m_shell = m_shell if m_shell is not None else REFERENCE_M
    return cluster_binding_mev(m_shell, 7, c, Z=3)


def be7_formation_q(Q_7: float, Q_3: float, Q_4: float) -> float:
    """³He + ⁴He → ⁷Be: `Q_7 − Q_3 − Q_4` (same gap pattern as 2D → ⁴He)."""
    return max(0.01, Q_7 - Q_3 - Q_4)


def be7_electron_capture_q(Q_7: float, Q_np: float) -> float:
    """Legacy weak-scale placeholder (prefer `be7_to_li7_capture_q` with both wells)."""
    return GAMMA_HQIV * STRONG_CHANNEL_FRACTION * Q_np


def be7_to_li7_capture_q(
    Q_be: float,
    Q_li: float,
) -> float:
    """⁷Be + e⁻ → ⁷Li: release from Be well minus weaker Li far-neutron well."""
    from hqiv_post_alpha_sphere_touching import be7_to_li7_capture_q as _q

    return _q(Q_be, Q_li)


def lockin_binding_q(
    m_nucleon: float, m_shell: int | None = None, c: float = 1.0
) -> tuple[float, float, float, float]:
    """Q_D, Q_4, Q_3, Q_7 at lock-in shell (nuclear-scale network witness)."""
    m_shell = m_shell if m_shell is not None else REFERENCE_M
    Q_D = 2.0 * m_nucleon - cluster_mass_mev(m_shell, 2, m_nucleon, c)
    Q_4 = 4.0 * m_nucleon - cluster_mass_mev(m_shell, 4, m_nucleon, c)
    Q_3 = cluster_binding_mev(m_shell, 3, c)
    Q_7 = be7_binding_q(Q_4, m_shell=m_shell, m_nucleon=m_nucleon, c=c)
    return Q_D, Q_4, Q_3, Q_7


def lockin_li7_be7_q(
    m_nucleon: float, m_shell: int | None = None, c: float = 1.0
) -> tuple[float, float]:
    """⁷Be and ⁷Li cluster binding Q at lock-in (distinct post-α valley geometry)."""
    m_shell = m_shell if m_shell is not None else REFERENCE_M
    Q_be = cluster_binding_mev(m_shell, 7, c, Z=4)
    Q_li = li7_cluster_binding_q(m_shell, m_nucleon, c)
    return Q_be, Q_li


def neutron_proton_ratio(T_mev: float, Q_np: float) -> float:
    x = math.exp(-Q_np / T_mev)
    return x / (1.0 + x)


def y_p_from_neutron_fraction(x_n: float) -> float:
    return 2.0 * x_n / (1.0 + x_n)


def thermal_sink(Q_light: float, Q_alpha: float, T_mev: float) -> float:
    """exp((Q_light − Q_α)/T); returns 0 if T is below BBN (relic / CMB epoch)."""
    if T_mev < 1e-6:
        return 0.0
    arg = (Q_light - Q_alpha) / T_mev
    if arg > 700:
        return math.inf
    if arg < -700:
        return 0.0
    return math.exp(arg)


def eta_exponent_dh(Q_D: float, Q_4: float, Q_np: float) -> float:
    return -((Q_4 - Q_D) / Q_np)


def eta_exponent_he3(Q_3: float, Q_D: float, Q_np: float) -> float:
    return -((Q_3 - Q_D) / Q_np)


def eta_exponent_li7(Q_4: float, Q_D: float, Q_np: float) -> float:
    return -(((7.0 / 4.0) * Q_4 - Q_D) / Q_np)


def freezeout_temperature_mev(Q_np: float, eta: float) -> float:
    """Weak freeze-out: T ≈ Q_np / log(η₁₀) (epoch when n↔p rates decouple)."""
    return Q_np / math.log(eta10(eta))


def abundances_at_epoch(
    eta: float,
    T_mev: float,
    m_nucleon: float,
    Q_np: float,
    Q_D: float,
    Q_4: float,
    Q_3: float,
    *,
    T_freeze_mev: float | None = None,
) -> dict[str, float]:
    """Lock-in Q's; thermal factors at epoch T; Y_p from single freeze-out temperature."""
    T_f = T_freeze_mev if T_freeze_mev is not None else freezeout_temperature_mev(Q_np, eta)
    x_n = neutron_proton_ratio(T_f, Q_np)
    Yp = y_p_from_neutron_fraction(x_n)
    e10 = eta10(eta)
    DH = e10 ** eta_exponent_dh(Q_D, Q_4, Q_np) * thermal_sink(Q_D, Q_4, T_mev)
    He3H = e10 ** eta_exponent_he3(Q_3, Q_D, Q_np) * thermal_sink(Q_3, Q_4, T_mev)
    Li7H = e10 ** eta_exponent_li7(Q_4, Q_D, Q_np) * thermal_sink(1.75 * Q_4, Q_4, T_mev)
    return {
        "T_MeV": T_mev,
        "shell_index": shell_index_from_mev(T_mev),
        "Yp": Yp,
        "D_over_H": DH,
        "He3_over_H": He3H,
        "Li7_over_H": Li7H,
        "xn": x_n,
        "T_freeze_MeV": T_f,
    }


def integrate_bbn_window(
    eta: float,
    m_nucleon: float,
    Q_np: float,
    Q_D: float,
    Q_4: float,
    Q_3: float,
    *,
    n_steps: int = 40,
    T_high: float = BBN_T_HIGH_MEV,
    T_low: float = BBN_T_LOW_MEV,
) -> dict[str, float]:
    """
    Log-spaced average over the BBN temperature window (universe aging: T drops, shell grows).

    Weights ∝ dT/T (order-of-magnitude RD bookkeeping).
    """
    temps = [T_high * (T_low / T_high) ** (i / (n_steps - 1)) for i in range(n_steps)]
    weights: list[float] = []
    rows: list[dict[str, float]] = []
    for i, T in enumerate(temps):
        if i == 0:
            w = abs(math.log(temps[1] / temps[0]))
        elif i == n_steps - 1:
            w = abs(math.log(temps[-1] / temps[-2]))
        else:
            w = abs(math.log(temps[i + 1] / temps[i - 1]) / 2.0)
        weights.append(w)
        rows.append(abundances_at_epoch(eta, T, m_nucleon, Q_np, Q_D, Q_4, Q_3))
    total_w = sum(weights)
    out: dict[str, float] = {}
    for key in ("Yp", "D_over_H", "He3_over_H", "Li7_over_H"):
        vals = [r[key] for r in rows]
        if any(math.isinf(v) for v in vals):
            out[key] = float("nan")
        else:
            out[key] = sum(v * w for v, w in zip(vals, weights)) / total_w
    out["T_window_low_MeV"] = T_low
    out["T_window_high_MeV"] = T_high
    out["n_steps"] = float(n_steps)
    return out


def coc2015_abundances(eta: float) -> dict[str, float]:
    e10 = eta10(eta)
    anchor = 6.10
    return {
        "Yp": 0.24703 * (e10 / anchor) ** (-0.039),
        "D_over_H": 2.579e-5 * (anchor / e10) ** 1.61,
        "He3_over_H": 0.9996e-5 * (anchor / e10) ** 1.40,
        "Li7_over_H": 4.648e-10 * (anchor / e10) ** 2.50,
    }


@dataclass
class EpochRow:
    label: str
    T_MeV: float
    shell_index: float
    Yp: float
    D_over_H: float
    He3_over_H: float
    Li7_over_H: float


def build_epoch_table(
    eta: float, m_nucleon: float, Q_np: float, Q_D: float, Q_4: float, Q_3: float
) -> list[EpochRow]:
    rows = []
    for label, T in [
        ("lockin_shell_m4_QCD_scale", lockin_temperature_mev()),
        ("bbn_T_1_MeV", 1.0),
        ("bbn_mid_T_0.1_MeV", BBN_T_MID_MEV),
        ("bbn_T_0.01_MeV", BBN_T_LOW_MEV),
        ("cmb_today", cmb_temperature_mev()),
    ]:
        a = abundances_at_epoch(eta, T, m_nucleon, Q_np, Q_D, Q_4, Q_3)
        rows.append(
            EpochRow(
                label=label,
                T_MeV=T,
                shell_index=a["shell_index"],
                Yp=a["Yp"],
                D_over_H=a["D_over_H"],
                He3_over_H=a["He3_over_H"],
                Li7_over_H=a["Li7_over_H"],
            )
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description="HQIV BBN from network weights (epoch-aware)")
    parser.add_argument("--epoch-sweep", action="store_true", help="Print epoch comparison table")
    parser.add_argument(
        "--integrate-network",
        action="store_true",
        help="Run cooling-path reaction network (hqiv_bbn_epoch_network.py)",
    )
    args = parser.parse_args()

    if args.integrate_network:
        import hqiv_bbn_epoch_network as net

        net.main()
        return

    w = load_witness()
    m_p = float(w["derivedProtonMass_MeV"])
    dm = float(w["derivedDeltaM_MeV"])
    eta = ETA_PAPER
    Q_D, Q_4, Q_3, _Q_7 = lockin_binding_q(m_p, REFERENCE_M)

    mid = abundances_at_epoch(eta, BBN_T_MID_MEV, m_p, dm, Q_D, Q_4, Q_3)
    integrated = integrate_bbn_window(eta, m_p, dm, Q_D, Q_4, Q_3)
    epoch_table = build_epoch_table(eta, m_p, dm, Q_D, Q_4, Q_3)
    coc = coc2015_abundances(eta)

    payload = {
        "source": "HQIV BBN: lock-in η + network Q at referenceM; abundances at cosmological T",
        "lean_modules": [
            "Hqiv.Physics.BBNNetworkFromWeights",
            "Hqiv.Physics.BBNEpochEvolution",
        ],
        "python_script": "scripts/hqiv_bbn_abundances.py",
        "hqiv_inputs": {
            "referenceM": REFERENCE_M,
            "eta_paper": eta,
            "derivedProtonMass_MeV": m_p,
            "derivedDeltaM_MeV": dm,
            "Q_D_lockin_MeV": Q_D,
            "Q_4He_lockin_MeV": Q_4,
            "lockin_T_MeV": lockin_temperature_mev(),
            "cmb_T_MeV": cmb_temperature_mev(),
        },
        "bbn_window_integrated": integrated,
        "bbn_mid_epoch": mid,
        "epoch_comparison": [asdict(r) for r in epoch_table],
        "comparison_coc2015": coc,
        "observed_comparison_layer": {
            "Yp": "0.244 ± 0.004",
            "D_over_H": "(2.53 ± 0.04)×10⁻⁵",
            "He3_over_H": "≈10⁻⁵",
            "Li7_over_H": "(1.6–4.5)×10⁻¹⁰ (astrophysical depletion)",
            "note": "Observed values are relics from the BBN epoch, not CMB-today synthesis.",
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")

    print(f"Wrote {OUT}")
    print("\nIntegrated BBN window (T = 1 → 0.01 MeV, log weights):")
    print(f"  Y_p   = {integrated['Yp']:.5f}")
    print(f"  D/H   = {integrated['D_over_H']:.4e}")
    print(f"  ³He/H = {integrated['He3_over_H']:.4e}")
    print(f"  ⁷Li/H = {integrated['Li7_over_H']:.4e}")
    print("\nMid-epoch (T = 0.1 MeV):")
    print(f"  Y_p   = {mid['Yp']:.5f}  |  D/H = {mid['D_over_H']:.4e}")

    if args.epoch_sweep:
        print("\nEpoch sweep (same lock-in Q's; T and shell vary with age):")
        print(f"{'label':<28} {'T_MeV':>12} {'shell':>12} {'Y_p':>8} {'D/H':>12}")
        for r in epoch_table:
            print(
                f"{r.label:<28} {r.T_MeV:12.4e} {r.shell_index:12.3e} "
                f"{r.Yp:8.5f} {r.D_over_H:12.4e}"
            )
        print("\n  lock-in m≈4 is QCD/baryogenesis — not the BBN synthesis shell.")
        print("  CMB today: thermal factors → 0; no active light-element production.")


if __name__ == "__main__":
    main()
