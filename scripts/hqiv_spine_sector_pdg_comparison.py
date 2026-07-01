#!/usr/bin/env python3
"""
Unified PDG comparison: HqivSpine structure + TUFT MeV discharge + PDG quarantine.

Columns:
  • spine_dim — Lean-proved lock-in readout (dimensionless; `GenerationResonanceLadder`)
  • discharge — TUFT MeV path (witness-anchored; comparison layer only)
  • PDG — comparison numerals only

Run:
  python3 scripts/hqiv_spine_sector_pdg_comparison.py
  python3 scripts/hqiv_spine_sector_pdg_comparison.py --json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass

import hqiv_spine_mev_discharge_bridge as bridge
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

PDG = {
    **tmse.PDG_MEV,
    "m_u_MeV": 2.16,
    "m_d_MeV": 4.67,
    "m_s_MeV": 93.4,
    "m_c_MeV": 1270.0,
    "m_b_MeV": 4180.0,
    "m_t_MeV": 172570.0,
    "m_pi0_MeV": 134.9768,
    "m_rho_MeV": 775.26,
    "sum_mnu_cap_eV": 0.12,
    "dm21_sq_eV2": 7.53e-5,
    "dm31_sq_eV2": 2.453e-3,
}


@dataclass(frozen=True)
class CompareRow:
    label: str
    spine_dim: float | None
    discharge: float | None
    discharge_unit: str
    pdg: float | None
    pdg_unit: str
    note: str = ""


def pct(pred: float | None, ref: float | None) -> float | None:
    if pred is None or ref is None or ref == 0:
        return None
    return 100.0 * (pred - ref) / ref


def ratio(pred: float | None, ref: float | None) -> float | None:
    if pred is None or ref is None or ref == 0:
        return None
    return pred / ref


def fermion_rows() -> list[CompareRow]:
    lep = bridge.discharge_leptons_mev()
    quark = bridge.discharge_quarks_mev()
    had = bridge.discharge_hadron_mev()
    lep_mev = bridge.lepton_by_generation(lep)
    rows: list[CompareRow] = []

    for gen in bridge.GENERATIONS:
        w = bridge.WINDING[gen]
        pdg_key = {"electron": "e", "muon": "mu", "tau": "tau"}[gen]
        rows.append(
            CompareRow(
                f"charged lepton {gen}",
                bridge.spine_lepton_readout(w),
                lep_mev[gen],
                "MeV",
                PDG[pdg_key],
                "MeV",
                "spine: massUnit·generationResonanceMassFactor; discharge: vev→T8",
            )
        )

    quark_map = [
        ("u (gen-1)", quark.u_mev, PDG["m_u_MeV"], 1),
        ("d (gen-1)", quark.d_mev, PDG["m_d_MeV"], 1),
        ("s (gen-2)", quark.s_mev, PDG["m_s_MeV"], 2),
        ("c (gen-2)", quark.c_mev, PDG["m_c_MeV"], 2),
        ("b (gen-3)", quark.b_mev, PDG["m_b_MeV"], 3),
        ("t (gen-3)", quark.t_mev, PDG["m_t_MeV"], 3),
    ]
    for label, mev, pdg_val, w in quark_map:
        rows.append(
            CompareRow(
                label,
                bridge.spine_quark_readout(w),
                mev,
                "MeV",
                pdg_val,
                "MeV",
                "spine: 9·generationResonanceMassFactor/4; discharge: resonance ladder",
            )
        )

    nu = bridge.discharge_neutrinos_mev()
    for gen, idx in [("electron", 0), ("muon", 1), ("tau", 2)]:
        w = bridge.WINDING[gen]
        nu_mev = [nu.m1_mev, nu.m2_mev, nu.m3_mev][idx] if nu else None
        nu_ev = nu_mev * 1.0e6 if nu_mev is not None else None
        rows.append(
            CompareRow(
                f"neutrino {gen}",
                bridge.spine_neutrino_absolute(w),
                nu_ev,
                "eV",
                None,
                "eV",
                "spine: m_ℓ/140 dim; discharge: outer T8+T10",
            )
        )

    rows.append(
        CompareRow(
            "proton",
            bridge.spine_proton_readout(),
            had["proton_mev"],
            "MeV",
            PDG["proton"],
            "MeV",
            "spine dim; discharge: τ×proton/τ pin",
        )
    )
    pi_rho = 0.5 * (PDG["m_pi0_MeV"] + PDG["m_rho_MeV"])
    rows.append(
        CompareRow(
            "meson vector ground",
            (2.0 / 3.0) * bridge.spine_proton_readout(),
            had["meson_vector_ground_mev"],
            "MeV",
            pi_rho,
            "MeV",
            "spine 2/3·proton dim; discharge 3/4·baryon (strong/heavy)",
        )
    )
    return rows


def hopf_fibration_shape(winding: int) -> float:
    return winding / (winding + 2)


def lattice_simplex_count(m: int) -> int:
    """Lean `latticeSimplexCount m = (m+2)(m+1)`."""
    return (m + 2) * (m + 1)


def binding_rows() -> list[CompareRow]:
    """Hopf-weighted binding — dimensionless spine; MeV only via hadronic discharge scale."""
    rows: list[CompareRow] = []
    proton_bind_dim = (
        hopf_fibration_shape(3)
        * 3
        * lattice_simplex_count(4)
        * (1.0 / (42.0 * (1.0 + 0.6 * math.log(10.0))))
    )
    proton_bind_mev = proton_bind_dim * (PDG["proton"] / bridge.spine_proton_readout())
    rows.append(
        CompareRow(
            "E_bind nucleon @ Hopf n=3 (heavy)",
            proton_bind_dim,
            proton_bind_mev,
            "MeV",
            None,
            "MeV",
            "Hopf (3/5)·3·count·α_eff; MeV col = hadronic dim map only",
        )
    )
    return rows


def spine_ratio_summary() -> dict[str, float]:
    lep = {g: bridge.spine_lepton_readout(bridge.WINDING[g]) for g in bridge.GENERATIONS}
    return {
        "spine_mu_over_e": lep["muon"] / lep["electron"],
        "spine_tau_over_mu": lep["tau"] / lep["muon"],
        "lean_resonance_mu_over_e": bridge.RESONANCE_MU_OVER_E,
        "lean_resonance_tau_over_mu": bridge.RESONANCE_TAU_OVER_MU,
        "spine_quark_over_lepton_gen1": bridge.spine_quark_readout(1) / lep["electron"],
        "spine_nu_over_lepton_gen1": bridge.spine_neutrino_absolute(1) / lep["electron"],
        "target_C_A_over_C_F": 9.0 / 4.0,
        "target_nu_suppression": bridge.NEUTRINO_SUPPRESSION,
    }


def discharge_ratio_summary() -> dict[str, float]:
    lep = bridge.discharge_leptons_mev()
    return {
        "discharge_mu_over_e": lep.mu_mev / lep.e_mev,
        "discharge_tau_over_mu": lep.tau_mev / lep.mu_mev,
        "pdg_mu_over_e": PDG["mu"] / PDG["e"],
        "pdg_tau_over_mu": PDG["tau"] / PDG["mu"],
    }


def fmt(x: float | None, w: int = 11) -> str:
    if x is None:
        return f"{'—':>{w}s}"
    if abs(x) >= 1000 or (0 < abs(x) < 1e-4):
        return f"{x:>{w}.4g}"
    return f"{x:>{w}.6g}"


def print_table(title: str, rows: list[CompareRow]) -> None:
    print(title)
    hdr = (
        f"{'Observable':<26} {'spine':>8} {'discharge':>12} {'PDG':>12} "
        f"{'ratio':>8} {'Δ%':>8}  note"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        rat = ratio(r.discharge, r.pdg)
        dlt = pct(r.discharge, r.pdg)
        disp = fmt(r.discharge)
        if r.discharge is not None and r.discharge_unit != "MeV":
            disp += f" {r.discharge_unit}"
        print(
            f"{r.label:<26} {fmt(r.spine_dim, 8)} {disp:>12} {fmt(r.pdg):>12} "
            f"{fmt(rat, 8)} {fmt(dlt, 8)}  {r.note}"
        )
    print()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    nu = bridge.discharge_neutrinos_mev()
    payload = {
        "policy": (
            "Spine = dimensionless Lean structure; MeV = TUFT discharge witnesses "
            "(proton pin + vev→T8 + quark resonance + outer ν); PDG = comparison only"
        ),
        "mis_map_warning": (
            "Do not use spine_dim × (938.272/20) for leptons — that is the legacy "
            "shell-quotient failure mode"
        ),
        "fermions": [asdict(r) for r in fermion_rows()],
        "binding": [asdict(r) for r in binding_rows()],
        "spine_ratios": spine_ratio_summary(),
        "discharge_ratios": discharge_ratio_summary(),
        "neutrino_discharge_sum_eV": nu.sum_mev * 1e6 if nu else None,
        "neutrino_cosmo_cap_eV": PDG["sum_mnu_cap_eV"],
    }

    if args.json:
        print(json.dumps(payload, indent=2))
        return

    print("HQIV unified comparison — spine structure + TUFT MeV discharge + PDG\n")
    print(payload["policy"])
    print(f"ξ_lock = {tmse.XI_LOCKIN}, massUnit = {bridge.MASS_UNIT_LOCKIN}\n")

    print_table("Fermions and hadron ground", fermion_rows())

    print("Ratios — spine (structural) vs discharge (PDG-like MeV)")
    for k, v in spine_ratio_summary().items():
        print(f"  {k:<32} {v:.6g}")
    for k, v in discharge_ratio_summary().items():
        print(f"  {k:<32} {v:.6g}")
    print()

    if nu:
        print(
            f"Neutrino outer discharge: Σm_ν = {nu.sum_mev * 1e6:.4g} eV  "
            f"(cosmo cap {PDG['sum_mnu_cap_eV']} eV, ratio "
            f"{nu.sum_mev * 1e6 / PDG['sum_mnu_cap_eV']:.3f})"
        )
        print(
            f"Spine ν abs dims @ lock-in — e={bridge.spine_neutrino_absolute(1):.6g}, "
            f"μ={bridge.spine_neutrino_absolute(2):.6g}, τ={bridge.spine_neutrino_absolute(3):.6g}; "
            f"MeV/eV via outer discharge, not proton/20 map\n"
        )

    e_wrong = bridge.mis_map_proton_only_mev(bridge.spine_lepton_readout(1))
    lep = bridge.discharge_leptons_mev()
    print("Calibration sanity")
    print(f"  WRONG  e via proton/20 map: {e_wrong:.1f} MeV  (Δ vs PDG {pct(e_wrong, PDG['e']):+.0f}%)")
    print(f"  RIGHT  e via TUFT discharge:  {lep.e_mev:.4f} MeV  (ratio {lep.e_mev/PDG['e']:.4f})")
    print()
    print_table("Binding (hadronic scale)", binding_rows())


if __name__ == "__main__":
    main()
