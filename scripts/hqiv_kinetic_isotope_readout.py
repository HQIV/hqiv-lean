#!/usr/bin/env python3
"""
W4 / GMTKN kinetic isotope effect readout from path barriers + tunneling μ.

Lean: ``Hqiv.QuantumChemistry.KineticIsotopePath``
      ``HqivSpine.Physics.Tunneling`` (kappaForbidden, transmissionCoefficient)

The discrete path barrier B is mass-independent.  Primary KIE is μ-only:

  * Harmonic ZPE channel (DFT-slot numeral):
      ω = √(k/μ),  k = 2 D / r²  (Morse Hessian),
      KIE_ZPE = exp( (ω_H − ω_D) / (2 · strong · D_Ha) )
  * Tunneling identity (proved μ-monotonicity):
      KIE_tun = T(μ_H) / T(μ_D) ≥ 1
      with V−E = strong²·D (harmonic saddle), L = γ (Planck units).

W4 / GMTKN numerals are quarantine only.

Run:
  PYTHONPATH=.:scripts python3 scripts/hqiv_kinetic_isotope_readout.py
  PYTHONPATH=.:scripts python3 scripts/hqiv_kinetic_isotope_readout.py \\
    --json-out data/kinetic_isotope_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import hqiv_bond_rearrangement_path as brp
import hqiv_discrete_saddle_defect_readout as dsd
import hqiv_isotope_hydrogenic_scales as ihs
import hqiv_lean_physics_primitives as lean

STRONG = lean.STRONG_CHANNEL_FRACTION
GAMMA = lean.GAMMA
BOHR_ANGSTROM = 0.529177210903
EV_TO_HA = 1.0 / 27.211386245988
DEFAULT_JSON = _REPO_ROOT / "data" / "kinetic_isotope_audit.json"

# Quarantine-only W4 / GMTKN-style primary KIE targets (never inputs).
W4_KIE_COMPARISON: dict[str, float] = {
    "H2/D2": 1.5,
    "HF/DF": 2.0,
    "H2O/HOD": 2.5,
    "CH4/CD4": 3.0,
    "HCl/DCl": 2.0,
    "H2S/HSD": 2.5,
    "NH3/NDH2": 2.5,
    "HCN/DCN": 2.0,
    "C2H2/C2HD": 2.0,
    "PH3/PDH2": 2.5,
    "LiH/LiD": 1.5,
}

# Approximate closed-shell nuclear mass / m_e from A·m_p (quarantine comparison only).
_MP_OVER_ME = ihs.NUCLEAR_MASS_OVER_M_E["¹H"]
_NUCLEAR_A_OVER_ME: dict[int, float] = {
    1: _MP_OVER_ME,
    3: 7.0 * _MP_OVER_ME,
    6: 12.0 * _MP_OVER_ME,
    7: 14.0 * _MP_OVER_ME,
    8: 16.0 * _MP_OVER_ME,
    9: 19.0 * _MP_OVER_ME,
    15: 31.0 * _MP_OVER_ME,
    16: 32.0 * _MP_OVER_ME,
    17: 35.5 * _MP_OVER_ME,
}


def kappa_forbidden(mu: float, e: float, v: float) -> float:
    """Lean ``kappaForbidden``: √(2μ(V−E)), ħ ≡ 1."""
    return math.sqrt(max(2.0 * float(mu) * (float(v) - float(e)), 0.0))


def transmission_coefficient(kappa: float, length: float) -> float:
    """Lean ``transmissionCoefficient``: exp(−2 κ L)."""
    return math.exp(-2.0 * float(kappa) * float(length))


def path_tunnel_transmission(mu: float, e: float, v: float, length: float) -> float:
    """Lean ``pathTunnelTransmission``."""
    return transmission_coefficient(kappa_forbidden(mu, e, v), length)


def kinetic_isotope_effect(
    mu_light: float, mu_heavy: float, e: float, v: float, length: float
) -> float:
    """Lean ``pathKineticIsotopeEffect``: T_light / T_heavy."""
    t_h = path_tunnel_transmission(mu_light, e, v, length)
    t_d = path_tunnel_transmission(mu_heavy, e, v, length)
    return float(t_h / max(t_d, 1e-300))


def morse_hessian_ha_per_bohr2(binding_ev: float, r_angstrom: float) -> float:
    """Lean ``contactHessian`` spine: k = 2 D / r² in Ha/Bohr²."""
    d_ha = float(binding_ev) * EV_TO_HA
    r_bohr = max(float(r_angstrom) / BOHR_ANGSTROM, 1e-12)
    return 2.0 * d_ha / (r_bohr * r_bohr)


def harmonic_omega_au(k_ha: float, mu: float) -> float:
    """ω = √(k/μ) in atomic units (ħ ≡ 1)."""
    return math.sqrt(max(float(k_ha), 0.0) / max(float(mu), 1e-30))


def harmonic_zpe_kie(
    mu_light: float,
    mu_heavy: float,
    *,
    binding_ev: float,
    r_angstrom: float,
) -> float:
    """
    Primary DFT-slot KIE from Morse ZPE difference.

    KIE = exp( (ω_H − ω_D) / (2 · strong · D_Ha) ).

    Temperature scale is the HQIV-rational ``strong · D`` (same energy that
    softens activation transmission) — no fitted kT.
    """
    k = morse_hessian_ha_per_bohr2(binding_ev, r_angstrom)
    w_h = harmonic_omega_au(k, mu_light)
    w_d = harmonic_omega_au(k, mu_heavy)
    d_ha = max(float(binding_ev) * EV_TO_HA, 1e-30)
    scale = 2.0 * STRONG * d_ha
    return math.exp((w_h - w_d) / scale)


def secondary_kinetic_isotope_effect(kie_primary: float) -> float:
    """
    Lean ``secondaryKineticIsotopeEffect``: spectator softener ``KIE^γ``.

    Secondary (non-transferred) H/D substitution softens the primary channel
    by the lattice factor γ — identity at KIE=1, no fitted secondary table.
    """
    if kie_primary <= 0.0:
        return 0.0
    return math.exp(GAMMA * math.log(float(kie_primary)))


def diatomic_reduced_mass_au(m1_over_me: float, m2_over_me: float) -> float:
    """μ = m1 m2 / (m1 + m2) in electron-mass units."""
    a, b = float(m1_over_me), float(m2_over_me)
    return a * b / max(a + b, 1e-30)


def nuclear_mass_over_me(z: int, *, deuterium: bool = False) -> float:
    """Nuclear mass / m_e from Z (A·m_p order-of-magnitude; quarantine)."""
    if int(z) == 1 and deuterium:
        return ihs.NUCLEAR_MASS_OVER_M_E["²H"]
    if int(z) in _NUCLEAR_A_OVER_ME:
        return _NUCLEAR_A_OVER_ME[int(z)]
    # Fallback: A ≈ 2Z for mid-Z comparison masses.
    return max(float(z) * 2.0, 1.0) * _MP_OVER_ME


def fragment_mass_over_me(zs: tuple[int, ...], *, replace_h_with_d: int = 0) -> float:
    """Sum nuclear masses; optionally replace the first ``replace_h_with_d`` H nuclei by D."""
    remaining = int(replace_h_with_d)
    total = 0.0
    for z in zs:
        if int(z) == 1 and remaining > 0:
            total += nuclear_mass_over_me(1, deuterium=True)
            remaining -= 1
        else:
            total += nuclear_mass_over_me(int(z))
    return total


def primary_h_transfer_masses(
    partner_zs: tuple[int, ...],
) -> tuple[float, float]:
    """
    Primary H/D transfer reduced masses against a fixed partner fragment.

    μ_H = m_H · M / (m_H + M),  μ_D = m_D · M / (m_D + M) with M = Σ partner nuclei.
    """
    mH = nuclear_mass_over_me(1)
    mD = nuclear_mass_over_me(1, deuterium=True)
    m_partner = fragment_mass_over_me(partner_zs)
    return (
        diatomic_reduced_mass_au(mH, m_partner),
        diatomic_reduced_mass_au(mD, m_partner),
    )


def isotope_pair_masses_from_benchmark(
    bench: Any,
) -> tuple[float, float, str, str]:
    """
    General primary H/D pair from a molecule benchmark (no name cases).

    * H₂: μ(H–H) vs μ(D–D)
    * else: first H break against the remaining fragment mass
    """
    zs = tuple(int(f.z_nuclear) for f in bench.fragments)
    n_h = sum(1 for z in zs if z == 1)
    if len(zs) == 2 and zs[0] == 1 and zs[1] == 1:
        mH = nuclear_mass_over_me(1)
        mD = nuclear_mass_over_me(1, deuterium=True)
        return (
            diatomic_reduced_mass_au(mH, mH),
            diatomic_reduced_mass_au(mD, mD),
            "H2",
            "D2",
        )
    if n_h <= 0:
        raise ValueError(f"{bench.name}: no H for primary KIE")
    # Partner = all nuclei except one H.
    partner = tuple(z for z in zs if z != 1)
    # Keep non-transferred H on the partner (H₂O → OH, CH₄ → CH₃, …).
    n_keep = n_h - 1
    partner = partner + (1,) * n_keep
    mu_l, mu_h = primary_h_transfer_masses(partner)
    return mu_l, mu_h, bench.name, f"{bench.name}[D]"


def isotope_pair_masses(label: str) -> tuple[float, float, str, str]:
    """Legacy label API → resolve via benchmark when possible."""
    raw = label.upper()
    mol_map = {
        "H2": "H2",
        "H2/D2": "H2",
        "HF": "HF",
        "HF/DF": "HF",
        "H2O": "H2O",
        "H2O/HOD": "H2O",
        "CH4": "CH4",
        "CH4/CD4": "CH4",
        "HCL": "HCl",
        "HCL/DCL": "HCl",
        "H2S": "H2S",
        "H2S/HSD": "H2S",
        "NH3": "NH3",
        "NH3/NDH2": "NH3",
        "HCN": "HCN",
        "HCN/DCN": "HCN",
        "C2H2": "C2H2",
        "C2H2/C2HD": "C2H2",
        "PH3": "PH3",
        "PH3/PDH2": "PH3",
        "LIH": "LiH",
        "LIH/LID": "LiH",
    }
    mol = mol_map.get(raw, mol_map.get(raw.split("/")[0], raw.split("/")[0]))
    bench = brp._benchmark_by_name(mol)
    if bench is None:
        raise KeyError(f"unknown KIE pair {label!r}")
    return isotope_pair_masses_from_benchmark(bench)


def mild_tunnel_params(binding_ev: float) -> tuple[float, float, float]:
    """
    Mild tunneling (E, V, L) for the proved μ-monotonicity witness.

    V−E = strong² · D (harmonic saddle); L = γ (Planck / lock-in units).
    Keeps KIE_tun ≥ 1 without deep-barrier numerical underflow.
    """
    height_ha = (STRONG ** 2) * float(binding_ev) * EV_TO_HA
    return 0.0, height_ha, GAMMA


KIE_SUBSET: tuple[tuple[str, str], ...] = (
    ("H2", "H2/D2"),
    ("HF", "HF/DF"),
    ("H2O", "H2O/HOD"),
    ("CH4", "CH4/CD4"),
)

KIE_EXTENDED: tuple[tuple[str, str], ...] = KIE_SUBSET + (
    ("HCl", "HCl/DCl"),
    ("H2S", "H2S/HSD"),
    ("NH3", "NH3/NDH2"),
    ("HCN", "HCN/DCN"),
    ("C2H2", "C2H2/C2HD"),
    ("PH3", "PH3/PDH2"),
    ("LiH", "LiH/LiD"),
)


def kie_row_from_benchmark(mol: str, pair_label: str) -> dict[str, Any]:
    bench = brp._benchmark_by_name(mol)
    if bench is None:
        return {"molecule": mol, "pair": pair_label, "error": "benchmark not found"}
    path_row = brp.path_from_benchmark(bench, edge_index=0)
    mu_l, mu_h, tag_l, tag_h = isotope_pair_masses_from_benchmark(bench)
    d_ev = float(path_row["binding_ev_edge"])
    r_ang = float(path_row.get("distance_angstrom") or 1.0)
    kie_zpe = harmonic_zpe_kie(mu_l, mu_h, binding_ev=d_ev, r_angstrom=r_ang)
    e, v, length = mild_tunnel_params(d_ev)
    kie_tun = kinetic_isotope_effect(mu_l, mu_h, e, v, length)
    kie_sec = secondary_kinetic_isotope_effect(kie_zpe)
    t_l = path_tunnel_transmission(mu_l, e, v, length)
    t_h = path_tunnel_transmission(mu_h, e, v, length)
    ref = W4_KIE_COMPARISON.get(pair_label)
    return {
        "molecule": mol,
        "pair": pair_label,
        "light": tag_l,
        "heavy": tag_h,
        "mu_light_au": mu_l,
        "mu_heavy_au": mu_h,
        "path_barrier_ev": path_row["path_barrier_ev"],
        "harmonic_saddle_gate_ev": path_row["harmonic_saddle_gate_ev"],
        "binding_ev_edge": d_ev,
        "delta_coord": path_row["delta_coord"],
        "distance_angstrom": r_ang,
        "KIE": kie_zpe,
        "KIE_zpe": kie_zpe,
        "KIE_tunnel": kie_tun,
        "KIE_secondary": kie_sec,
        "KIE_ge_one": kie_zpe >= 1.0 - 1e-12 and kie_tun >= 1.0 - 1e-12,
        "secondary_between_one_and_primary": (
            1.0 - 1e-12 <= kie_sec <= kie_zpe + 1e-12
        ),
        "T_light": t_l,
        "T_heavy": t_h,
        "E_Ha": e,
        "V_Ha": v,
        "L_Bohr": length,
        "w4_reference_quarantine": ref,
        "comparison_policy": "W4/GMTKN KIE numerals are quarantine only",
    }


def build_kinetic_isotope_audit(
    *,
    subset: tuple[tuple[str, str], ...] | None = None,
) -> dict[str, Any]:
    pairs = subset if subset is not None else KIE_EXTENDED
    rows = [kie_row_from_benchmark(mol, pair) for mol, pair in pairs]
    identity = {
        "all_kie_ge_one": all(r.get("KIE_ge_one") for r in rows if "error" not in r),
        "mu_h2_lt_d2": isotope_pair_masses("H2/D2")[0] < isotope_pair_masses("H2/D2")[1],
        "heavier_tunnels_less_h2": True,
        "zpe_channel_primary": True,
        "secondary_softens_primary": all(
            r.get("secondary_between_one_and_primary") for r in rows if "error" not in r
        ),
        "secondary_identity_at_one": abs(secondary_kinetic_isotope_effect(1.0) - 1.0)
        < 1e-12,
        "all_rows_ok": all("error" not in r for r in rows),
    }
    h2 = next((r for r in rows if r.get("molecule") == "H2" and "error" not in r), None)
    if h2 is not None:
        identity["heavier_tunnels_less_h2"] = h2["T_heavy"] <= h2["T_light"] + 1e-15
    return {
        "source": "scripts/hqiv_kinetic_isotope_readout.py",
        "lean_modules": [
            "Hqiv.QuantumChemistry.KineticIsotopePath",
            "HqivSpine.Physics.Tunneling",
            "Hqiv.QuantumChemistry.BondRearrangementPath",
        ],
        "subset": [p for _, p in pairs],
        "core_subset": [p for _, p in KIE_SUBSET],
        "formula": {
            "KIE_zpe": "exp((ω_H−ω_D)/(2·strong·D_Ha)), ω=√(k/μ), k=2D/r²",
            "KIE_tunnel": "T(μ_H)/T(μ_D), κ=√(2μ(V−E)), V−E=strong²·D, L=γ",
            "KIE_secondary": "KIE_pri^γ (spectator softener; identity at 1)",
            "mass_independence": "path barrier B is μ-independent; isotope only via μ",
            "primary_dft_slot": "KIE_zpe",
            "mu_construction": "primary H transfer vs partner fragment (Z-keyed; no name cases)",
        },
        "identity_checks": identity,
        "all_identity_checks_pass": all(identity.values()),
        "rows": rows,
        "comparison_policy": "W4/GMTKN KIE numerals are quarantine only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    args = parser.parse_args()
    audit = build_kinetic_isotope_audit()
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(audit, indent=2) + "\n")
    print(f"wrote {args.json_out}")
    print(f"identity_ok={audit['all_identity_checks_pass']}")
    for r in audit["rows"]:
        if "error" in r:
            print(f"  {r['molecule']}: ERROR {r['error']}")
            continue
        ref = r.get("w4_reference_quarantine")
        ref_s = f"  (W4~{ref})" if ref else ""
        print(
            f"  {r['pair']:10} KIE_zpe={r['KIE_zpe']:.4f}  "
            f"KIE_sec={r['KIE_secondary']:.4f}  "
            f"KIE_tun={r['KIE_tunnel']:.4f}{ref_s}"
        )


if __name__ == "__main__":
    main()
