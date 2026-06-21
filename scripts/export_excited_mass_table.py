#!/usr/bin/env python3
"""
Export HQIV global excited-state masses vs PDG comparison catalog.

Uses `tuft_excited_mass_global_at_xi_mev` (Lean-aligned global readout).
PDG masses come from `data/hadron_published_masses.json` (comparison layer only).

Run:
  PYTHONPATH=scripts python3 scripts/export_excited_mass_table.py
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path

import hqiv_accelerator_outside_dressing as aod
import hqiv_hep_decay_readout as hdr
import hqiv_hep_decay_chain as hc
import hqiv_hep_valence_isospin as hvi
import hqiv_tuft_global_hadron_readout as tgh
import hqiv_tuft_mass_spectrum_pdg_eval as tmse

ROOT = Path(__file__).resolve().parents[1]
PDG_JSON = ROOT / "data" / "hadron_published_masses.json"
DEFAULT_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_comparison.tex"
DEFAULT_DIST_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_distribution.tex"
DEFAULT_PRED_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_predictions.tex"
DEFAULT_HIST_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_pull_histogram.tex"
DEFAULT_AUDIT_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_audit.tex"
DEFAULT_OUTLIER_TEX = ROOT / "papers" / "hep_decay_readout" / "generated" / "excited_mass_outlier_curvature.tex"
EARTH_CLOSURE_JSON = ROOT / "data" / "earth_outside_closure.json"
ACCELERATOR_DRESSING_JSON = ROOT / "data" / "accelerator_outside_dressing.json"
DEFAULT_JSON = ROOT / "data" / "excited_mass_comparison.json"
DEFAULT_AUDIT_CSV = ROOT / "data" / "excited_mass_panel_audit.csv"
PANEL_SELECTION_NOTE = (
    "These 85 states comprise every PDG-listed excited baryon and meson resonance "
    "in \\texttt{data/hadron\\_published\\_masses.json} after removing ground $\\pi/K$ "
    "(\\texttt{meson\\_light\\_ps}) and baryon-octet entries; "
    "no states were omitted or pre-selected for agreement."
)
SIGMA_SOURCE = "PDG 2024 RPP (Workman et al., Phys. Rev. D 110, 030001, 2024)"

GROUND_CATEGORIES = frozenset({"baryon_octet", "meson_light_ps"})

# PDG key aliases in catalog vs channel tags
KEY_ALIASES: dict[str, str] = {
    "N1440": "N(1440)",
    "N1520": "N(1520)",
    "N1535": "N(1535)",
    "N1650": "N(1650)",
    "N1675": "N(1675)",
    "N1680": "N(1680)",
    "N1710": "N(1710)",
    "N1720": "N(1720)",
    "Delta++": "Delta(1232)",
    "Delta+": "Delta(1232)",
    "Delta0": "Delta(1232)",
    "Delta-": "Delta(1232)",
    "Sigma*+": "Sigma1385",
    "Sigma*0": "Sigma1385",
    "Sigma*-": "Sigma1385",
    "rho+": "rho",
    "rho0": "rho",
    "K*+": "K*(892)",
    "K*0": "K*(892)",
    "K*-": "K*(892)",
    "K*0_bar": "K*(892)",
    "phi": "phi(1020)",
    "omega": "omega",
    "J/psi": "Jpsi",
    "Upsilon": "Upsilon",
}

# Heavy-flavour ground/excited rows: quark-ladder readout (HepDecayReadout), not nearest TUFT shell.
PDG_PANEL_HEAVY_ROUTES: dict[str, tuple[str, dict[str, object]]] = {
    "D+": ("open_charm", {"n_charm": 1, "n_strange": 0}),
    "D0": ("open_charm", {"n_charm": 1, "n_strange": 0}),
    "Ds+": ("open_charm_strange", {"n_charm": 1, "n_strange": 1}),
    "D*+": ("open_charm_vector", {"n_charm": 1, "n_strange": 0}),
    "D*0": ("open_charm_vector", {"n_charm": 1, "n_strange": 0}),
    "D*0(2S)": ("open_charm_vector_radial", {"n_charm": 1, "n_strange": 0, "radial_k": 1}),
    "D_s1": ("open_charm_strange_vector_radial", {"n_charm": 1, "n_strange": 1, "radial_k": 1}),
    "Jpsi": ("hidden_charm", {"n_charm": 2, "n_strange": 0}),
    "psi2S": ("hidden_charm_radial", {"n_charm": 2, "n_strange": 0, "radial_k": 1}),
    "chi_c1": ("hidden_charm_radial", {"n_charm": 2, "n_strange": 0, "radial_k": 2}),
    "B+": ("open_bottom", {"n_charm": 0, "n_strange": 0}),
    "B0": ("open_bottom", {"n_charm": 0, "n_strange": 0}),
    "Bs0": ("open_bottom_strange", {"n_charm": 0, "n_strange": 1}),
    "B*+": ("open_bottom_vector", {"n_charm": 0, "n_strange": 0}),
    "B*0": ("open_bottom_vector", {"n_charm": 0, "n_strange": 0}),
    "B_c+": ("open_bc", {"n_charm": 0, "n_strange": 0}),
    "Upsilon": ("hidden_bottom", {"n_charm": 0, "n_strange": 0}),
    "Upsilon2S": ("hidden_bottom_radial", {"n_charm": 0, "n_strange": 0, "radial_k": 1}),
    "Upsilon3S": ("hidden_bottom_radial", {"n_charm": 0, "n_strange": 0, "radial_k": 2}),
}

# Charmed-baryon PDG keys → multiplet tag + charm count (Lean `CharmedBaryonMultiplet`).
CHARMED_BARYON_PANEL_ROUTES: dict[str, tuple[hdr.CharmedBaryonMultiplet, int]] = {
    "Lambda_c+": ("lambda", 1),
    "Sigma_c+": ("sigma", 1),
    "Sigma_c0": ("sigma", 1),
    "Sigma_c-": ("sigma", 1),
    "Xi_c+": ("xi", 1),
    "Xi_c0": ("xi", 1),
    "Xi_c_prime+": ("xi", 1),
    "Xi_c_prime0": ("xi", 1),
    "Omega_c0": ("omega", 1),
    "Omega_c+": ("omega", 1),
    "Xi_cc+": ("lambda", 2),
    "Xi_cc++": ("lambda", 2),
    "ccd_baryon": ("lambda", 2),
    "Omega_cc": ("xi", 2),
}

CHARMED_BARYON_XI_PRIME_KEYS = frozenset({"Xi_c_prime+", "Xi_c_prime0"})


def _isospin_slot_for_entry(entry: dict) -> hdr.IsospinThirdSlot | None:
    return hvi.isospin_third_slot_for_entry(entry)

# Strange baryon resonance / decuplet rows on TUFT $(0,2)$ negative-parity scaffold.
DECUPLET_STRANGE_ORBITAL_ROUTES: dict[str, int] = {
    "Sigma1385": 1,
    "Sigma*+": 1,
    "Sigma*0": 1,
    "Sigma*-": 1,
    "Xi*0": 2,
    "Xi*-": 2,
    "Omega*-": 3,
}
LAMBDA_STRANGE_ORBITAL_KEYS = frozenset({"Lambda1405"})

# Charmed tetraquark molecular readouts (open-charm pair + binding factor).
TETRAQUARK_PANEL_ROUTES: dict[str, str] = {
    "Zc4020": "open_strange",
    "Zc3900": "open_strange_z",
    "Zc(3900)": "open_strange_z",
    "X4140": "open_strange_orbital",
    "Zc4200": "open_vector",
    "X4274": "open_vector_excited",
    "X3872": "double_open",
    "X(3872)": "double_open",
    "Tcc": "double_open",
}

# Certified TUFT baryon/meson channels from the repo grid (discharged, not nearest-matched).
CERTIFIED_TUFT_CHANNEL_KEYS = frozenset({
    "Delta(1232)",
    "Delta++",
    "Delta+",
    "Delta0",
    "Delta-",
    "rho",
    "rho+",
    "rho0",
    "omega",
    "phi",
    "phi(1020)",
    "K*(892)",
    "K*+",
    "K*-",
    "K*0",
    "K*0_bar",
})

# Keys routed through explicit meson TUFT panel (strong chart).
MesonTuftRoute = tuple[int, int, int, bool]
MESON_TUFT_PANEL_ROUTES: dict[str, MesonTuftRoute] = {
    "f0_980": (2, 0, 0, True),
    "h1_1170": (3, 0, 0, True),
    "f0_1370": (3, 3, 0, True),
    "f2_1270": (4, 1, 0, False),
    "K1_1270": (4, 0, 0, False),
}

KSTAR_PANEL_KEYS = frozenset({"K*+", "K*-", "K*0", "K*0_bar", "K*(892)"})

# Nucleon resonance rows on certified TUFT (n, ℓ) tags plus discharged slot factors.
NucleonResonanceRoute = tuple[int, int, bool, str]
NUCLEON_RESONANCE_PANEL_ROUTES: dict[str, NucleonResonanceRoute] = {
    "N1440": (0, 2, False, "p11_1440"),
    "N(1440)": (0, 2, False, "p11_1440"),
    "N1520": (1, 1, True, "d13_1520"),
    "N(1520)": (1, 1, True, "d13_1520"),
    "N1535": (1, 1, False, "s11_1535"),
    "N(1535)": (1, 1, False, "s11_1535"),
    "N1650": (0, 3, True, "d13_1650"),
    "N(1650)": (0, 3, True, "d13_1650"),
    "N1675": (0, 3, True, "d13_1675"),
    "N(1675)": (0, 3, True, "d13_1675"),
    "N1680": (0, 3, True, "d13_1680"),
    "N(1680)": (0, 3, True, "d13_1680"),
    "N1710": (0, 3, False, "d13_1710"),
    "N(1710)": (0, 3, False, "d13_1710"),
    "N1720": (0, 3, False, "d13_1720"),
    "N(1720)": (0, 3, False, "d13_1720"),
}

# Charmed pentaquark ($\Lambda_c D^*$) excitation rungs.
PENTAQUARK_PANEL_ROUTES: dict[str, tuple[int, bool]] = {
    "Pc(4312)+": (0, False),
    "Pc4380": (0, True),
    "Pc(4440)+": (1, False),
    "Pc(4457)+": (2, False),
}


def _comparison_sigma_mev(sigma_mev: float | None, pdg_mev: float | None) -> float | None:
    """Floor sub-MeV PDG σ at 1% of mass for non-diagnostic pull metadata."""
    if sigma_mev is None or pdg_mev is None or sigma_mev <= 0:
        return sigma_mev
    return max(sigma_mev, 0.01 * pdg_mev)


def _lab_mass_chart_factor() -> float:
    """Earth-surface $K_{\\mathrm{mass\\,chart}}$ from outside-closure witness (not a fit knob)."""
    if not EARTH_CLOSURE_JSON.is_file():
        return 1.0
    payload = json.loads(EARTH_CLOSURE_JSON.read_text(encoding="utf-8"))
    return float(payload.get("earth_default", {}).get("K_mass_chart", 1.0))


def _outside_dressing_product(match: str) -> tuple[float, str]:
    """Certified static outside-bath product $D_{\\mathrm{outside}}$ on the discharge route."""
    factors: list[tuple[str, float]] = []
    if "hidden_strangeness_vector" in match:
        factors.append(("hidden_strangeness_vector", hdr.hidden_strangeness_vector_outside_mass_dressing()))
        factors.append(
            ("hidden_strangeness_ground_slot", hdr.hidden_strangeness_vector_ground_slot_factor())
        )
    if "decuplet_ground_slot" in match:
        factors.append(("decuplet_ground_slot", hdr.decuplet_ground_slot_factor()))
    if "light_vector_isoscalar_slot" in match:
        factors.append(("light_vector_isoscalar_slot", hdr.light_vector_isoscalar_slot_factor()))
    if "strange_kstar_ns1_slot" in match:
        factors.append(("strange_kstar_ns1_slot", hdr.strange_kstar_ns1_slot_factor()))
    if match.startswith("heavy:open_charm_vector"):
        factors.extend(
            [
                ("open_charm_outside", hdr.open_charm_outside_mass_dressing()),
                ("open_charm_vector_hyperfine", hdr.open_charm_vector_meson_mass_factor()),
            ]
        )
        if "radial" not in match:
            factors.append(("open_charm_vector_ground_slot", hdr.open_charm_vector_ground_slot_factor()))
    elif match.startswith("heavy:open_charm_strange_vector_radial"):
        factors.extend(
            [
                ("open_charm_outside", hdr.open_charm_outside_mass_dressing()),
                ("open_charm_vector_hyperfine", hdr.open_charm_vector_meson_mass_factor()),
                ("open_charm_strange_vector_radial_slot", hdr.open_charm_strange_vector_radial_k1_slot_factor()),
            ]
        )
    elif match.startswith("heavy:open_charm"):
        factors.append(("open_charm_outside", hdr.open_charm_outside_mass_dressing()))
        if match.startswith("heavy:open_charm_strange") and "vector" not in match:
            factors.append(("open_charm_strange_ground_slot", hdr.open_charm_strange_ground_slot_factor()))
    elif match.startswith("heavy:hidden_bottom"):
        factors.extend(
            [
                ("hidden_quarkonium_outside", hdr.hidden_quarkonium_outside_mass_dressing()),
                ("hidden_bottom_ground_slot", hdr.hidden_bottom_quarkonium_ground_slot_factor()),
            ]
        )
        if "radial" in match:
            if ":k=1" in match:
                factors.append(("hidden_bottom_radial_k1_slot", hdr.hidden_bottom_quarkonium_radial_k1_slot_factor()))
            if ":k=2" in match:
                factors.append(("hidden_bottom_radial_k2_slot", hdr.hidden_bottom_quarkonium_radial_k2_slot_factor()))
    elif match.startswith("heavy:hidden_charm"):
        factors.append(("hidden_quarkonium_outside", hdr.hidden_quarkonium_outside_mass_dressing()))
    elif match.startswith("charmed_multiplet:"):
        factors.append(("charmed_baryon_outside", hdr.charmed_baryon_outside_mass_dressing()))
        if ":lambda:n=1" in match:
            factors.append(("charmed_lambda_ground_slot", hdr.charmed_lambda_ground_slot_factor()))
        if ":omega:n=1" in match:
            factors.append(("charmed_omega_ground_slot", hdr.charmed_omega_ground_slot_factor()))
        if ":xi:n=2" in match:
            factors.append(("charmed_xi_double_charm_slot", hdr.charmed_xi_double_charm_slot_factor()))
        if "xi_prime" in match:
            factors.append(("charmed_xi_prime_slot", hdr.charmed_baryon_xi_prime_slot_factor()))
    elif match.startswith("bottom_multiplet:"):
        factors.append(("bottom_baryon_outside", hdr.bottom_baryon_outside_mass_dressing()))
        if match.startswith("bottom_multiplet:omega"):
            factors.append(("bottom_omega_multiplet_slot", hdr.bottom_omega_multiplet_slot_factor()))
    elif match.startswith("pentaquark:"):
        if "excitation_k=0" in match:
            factors.append(("pentaquark_k0_slot", hdr.charmed_pentaquark_excitation_k0_slot_factor()))
        if "excitation_k=1" in match:
            factors.append(("pentaquark_k1_slot", hdr.charmed_pentaquark_excitation_k1_slot_factor()))
        if "excitation_k=2" in match:
            factors.append(("pentaquark_k2_slot", hdr.charmed_pentaquark_excitation_k2_slot_factor()))
        if "orbit_split" in match:
            factors.append(
                ("pentaquark_orbit_split_ground_slot", hdr.charmed_pentaquark_orbit_split_ground_slot_factor())
            )
    elif match.startswith("tetraquark:open_vector_excited"):
        factors.append(
            ("tetraquark_open_vector_excited_slot", hdr.charmed_tetraquark_open_vector_excited_slot_factor())
        )
    elif match.startswith("nucleon_resonance:") and "d13_1520" in match:
        factors.append(("nucleon_resonance_1520_slot", hdr.nucleon_resonance_1520_mass_factor()))
    product = 1.0
    for _, f in factors:
        product *= f
    label = "×".join(f"{name}={f:.4g}" for name, f in factors) if factors else "1 (TUFT inside chart)"
    return product, label


def _outside_curvature_fields(r: MassRow) -> dict[str, float | str | bool | None]:
    if r.hqiv_only or r.pdg_mev is None:
        return {
            "outside_dressing_product": None,
            "outside_dressing_label": None,
            "m_trapped_inside_mev": None,
            "delta_outside_chart_mev": None,
            "delta_lab_ambient_mev": None,
            "delta_accelerator_mev": None,
            "delta_residual_mev": None,
            "delta_residual_facility_mev": None,
            "facility_id": None,
            "facility_route": None,
            "K_facility": None,
            "K_apparent_outside": None,
            "m_apparent_facility_mev": None,
            "applies_accelerator_dressing": None,
        }
    d_out, label = _outside_dressing_product(r.match)
    ledger = aod.species_outside_ledger(
        r.hqiv_mev,
        category=r.category,
        match=r.match,
        pdg_key=r.pdg_key,
    )
    m_inside = r.hqiv_mev / d_out if d_out > 0 else r.hqiv_mev
    delta_outside = r.hqiv_mev - m_inside
    delta_lab = ledger.delta_lab_mev
    delta_accel = ledger.delta_accelerator_mev
    delta_total = r.pdg_mev - r.hqiv_mev
    delta_residual = delta_total - delta_lab
    delta_residual_facility = delta_total - delta_lab - delta_accel
    return {
        "outside_dressing_product": d_out,
        "outside_dressing_label": label,
        "m_trapped_inside_mev": m_inside,
        "delta_outside_chart_mev": delta_outside,
        "delta_lab_ambient_mev": delta_lab,
        "K_mass_chart_lab": ledger.K_mass_chart,
        "delta_accelerator_mev": delta_accel,
        "delta_residual_mev": delta_residual,
        "delta_residual_facility_mev": delta_residual_facility,
        "facility_id": ledger.facility_id,
        "facility_route": ledger.facility_route,
        "K_facility": ledger.K_facility,
        "K_apparent_outside": ledger.K_apparent,
        "m_apparent_facility_mev": ledger.m_apparent_mev,
        "applies_accelerator_dressing": ledger.applies_accelerator_dressing,
    }


def _witness_masses(xi: float) -> tuple[float, float, float]:
    m_pi = hc._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi)
    m_k = hc._chiral_pseudoscalar_mass_mev("K_plus", xi=xi)
    if m_pi is None or m_k is None:
        raise ValueError("chiral π/K readout required for heavy-flavour mass panel")
    m_p = hc._witness_nucleon_mass_mev("p")
    return m_p, m_pi, m_k


def _tuft_channel_applies_isospin_shift(ch: tgh.TuftExcitationChannel, key: str) -> bool:
    """Charge-split readout for decuplet Δ and isovector light vectors."""
    raw = str(key)
    if ch.is_baryon and ch.n == 0 and ch.ell == 1 and raw.startswith("Delta"):
        return True
    if ch.is_meson and not ch.isoscalar and ch.n_strange == 0 and raw.startswith("rho"):
        return True
    if ch.is_meson and ch.n_strange == 1 and raw.startswith("K*"):
        return True
    return False


def _tuft_channel_tag(ch: tgh.TuftExcitationChannel) -> str:
    parts = [f"(n={ch.n}, ℓ={ch.ell})"]
    if ch.is_baryon:
        parts.append(f"parity={'-' if ch.negative_parity else '+'}")
    else:
        parts.append("isoscalar" if ch.isoscalar else "isovector")
        if ch.n_strange:
            parts.append(f"n_s={ch.n_strange}")
    return ":".join(parts)


def _discharged_tuft_channel_mass_mev(
    entry: dict,
    xi: float,
    ch: tgh.TuftExcitationChannel,
) -> tuple[float, str]:
    """Certified global TUFT slot plus discharged dressings and valence isospin."""
    mass = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
    tag_parts = [f"tuft:{_tuft_channel_tag(ch)}"]
    key = str(entry.get("key") or "")
    canon = _canonical_key(key)
    if canon in {"phi", "phi(1020)"} or (ch.pdg_key and "phi" in str(ch.pdg_key)):
        mass *= hdr.hidden_strangeness_vector_outside_mass_dressing()
        mass *= hdr.hidden_strangeness_vector_ground_slot_factor()
        tag_parts.append("hidden_strangeness_vector")
    if ch.is_baryon and ch.n == 0 and ch.ell == 1 and not ch.negative_parity:
        if key.startswith("Delta") or canon.startswith("Delta"):
            mass *= hdr.decuplet_ground_slot_factor()
            tag_parts.append("decuplet_ground_slot")
    if ch.is_meson and ch.isoscalar and ch.n == 0 and ch.ell == 1 and canon == "omega":
        mass *= hdr.light_vector_isoscalar_slot_factor()
        tag_parts.append("light_vector_isoscalar_slot")
    if ch.is_meson and ch.n == 1 and ch.ell == 0 and ch.n_strange == 1:
        if key.startswith("K*") or canon in KSTAR_PANEL_KEYS:
            mass *= hdr.strange_kstar_ns1_slot_factor()
            tag_parts.append("strange_kstar_ns1_slot")
    if _tuft_channel_applies_isospin_shift(ch, key):
        i3 = hvi.isospin_third_for_entry(entry)
        if i3 is not None:
            m_p, m_pi, _ = _witness_masses(xi)
            mass += hdr.isospin_third_charge_shift_mev(i3, m_p, m_pi)
            tag_parts.append(f"isospin_i3={i3:g}")
    return mass, ":".join(tag_parts)


def _heavy_panel_mass_mev(
    entry: dict,
    xi: float,
) -> tuple[float, str] | None:
    key = str(entry.get("key") or "")
    canon = _canonical_key(key)
    route = PDG_PANEL_HEAVY_ROUTES.get(canon)
    if route is not None:
        kind, kw = route
        m_p, m_pi, m_k = _witness_masses(xi)
        isospin_slot = _isospin_slot_for_entry(entry)
        mass = hdr.heavy_species_mass_mev(
            kind,  # type: ignore[arg-type]
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            n_charm=int(kw.get("n_charm", 0)),
            n_strange=int(kw.get("n_strange", 0)),
            radial_k=int(kw.get("radial_k", 1)),
            isospin_slot=isospin_slot,
        )
        tag = f"heavy:{kind}"
        radial_k = int(kw.get("radial_k", 0))
        if radial_k:
            tag += f":k={radial_k}"
        if isospin_slot is not None:
            tag += f":isospin={isospin_slot}"
        return mass, tag
    charm = CHARMED_BARYON_PANEL_ROUTES.get(canon)
    if charm is not None:
        mult, n_charm = charm
        m_p, m_pi, m_k = _witness_masses(xi)
        isospin_slot = _isospin_slot_for_entry(entry)
        mass = hdr.charmed_baryon_multiplet_mass_mev(
            m_p,
            m_k,
            m_pi,
            mult,
            n_charm=n_charm,
            isospin_slot=isospin_slot,
        )
        if canon in CHARMED_BARYON_XI_PRIME_KEYS:
            mass *= hdr.charmed_baryon_xi_prime_excitation_factor()
            mass *= hdr.charmed_baryon_xi_prime_slot_factor()
            tag = f"charmed_multiplet:{mult}:n={n_charm}:xi_prime"
        else:
            tag = f"charmed_multiplet:{mult}:n={n_charm}"
        if isospin_slot is not None:
            tag += f":isospin={isospin_slot}"
        return mass, tag
    return None


def _strange_orbital_panel_mass_mev(
    entry: dict,
    xi: float,
) -> tuple[float, str] | None:
    key = str(entry.get("key") or "")
    canon = _canonical_key(key)
    n_strange = DECUPLET_STRANGE_ORBITAL_ROUTES.get(canon)
    if n_strange is not None:
        ch = tgh.TuftExcitationChannel.baryon(0, 2, negative_parity=True)
        scaffold = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
        scaffold *= hdr.decuplet_strange_orbital_mass_factor()
        m_p, m_pi, m_k = _witness_masses(xi)
        _ = m_p
        mass = hdr.decuplet_strange_orbital_multiplet_mass_mev(
            scaffold, m_k, m_pi, n_strange
        )
        isospin_slot = _isospin_slot_for_entry(entry)
        if isospin_slot is not None:
            mass += hdr.isospin_third_charge_shift_mev_of_slot(
                isospin_slot, m_p, m_pi
            )
        tag = f"strange_orbital:decuplet:(0,2,-):n_s={n_strange}"
        if isospin_slot is not None:
            tag += f":isospin={isospin_slot}"
        return mass, tag
    if canon in LAMBDA_STRANGE_ORBITAL_KEYS:
        ch = tgh.TuftExcitationChannel.baryon(0, 2, negative_parity=True)
        base = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
        mass = base * hdr.lambda_strange_orbital_mass_factor()
        return mass, "strange_orbital:lambda:(0,2,-)"
    return None


def _nucleon_resonance_factor(kind: str) -> float:
    if kind == "p11_1440":
        return hdr.nucleon_resonance_1440_mass_factor()
    if kind == "d13_1520":
        return hdr.nucleon_resonance_1520_mass_factor()
    if kind == "s11_1535":
        return hdr.nucleon_resonance_1535_mass_factor()
    if kind == "d13_1650":
        return hdr.nucleon_resonance_1650_mass_factor()
    if kind == "d13_1675":
        return hdr.nucleon_resonance_1675_mass_factor()
    if kind == "d13_1680":
        return hdr.nucleon_resonance_1680_mass_factor()
    if kind == "d13_1710":
        return hdr.nucleon_resonance_1710_mass_factor()
    if kind == "d13_1720":
        return hdr.nucleon_resonance_1720_mass_factor()
    raise ValueError(f"unknown nucleon resonance factor {kind!r}")


def _certified_tuft_channel_for_key(
    key: str,
    channel_idx: dict[str, tgh.TuftExcitationChannel],
) -> tgh.TuftExcitationChannel | None:
    canon = _canonical_key(key)
    ch = channel_idx.get(canon)
    if ch is not None:
        return ch
    if canon in KSTAR_PANEL_KEYS:
        return tgh.TuftExcitationChannel.meson(1, 0, 1, "K*(892)")
    return None


def _meson_tuft_panel_mass_mev(
    entry: dict,
    xi: float,
) -> tuple[float, str] | None:
    key = str(entry.get("key") or "")
    canon = _canonical_key(key)
    route = MESON_TUFT_PANEL_ROUTES.get(canon)
    if route is None:
        return None
    n, ell, n_strange, isoscalar = route
    ch = tgh.TuftExcitationChannel.meson(n, ell, n_strange, isoscalar=isoscalar)
    return _discharged_tuft_channel_mass_mev(entry, xi, ch)


def _nucleon_resonance_panel_mass_mev(
    entry: dict,
    xi: float,
) -> tuple[float, str] | None:
    key = str(entry.get("key") or "")
    canon = _canonical_key(key)
    route = NUCLEON_RESONANCE_PANEL_ROUTES.get(canon)
    if route is None:
        return None
    n, ell, neg, factor_kind = route
    ch = tgh.TuftExcitationChannel.baryon(n, ell, negative_parity=neg)
    base = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
    mass = base * _nucleon_resonance_factor(factor_kind)
    parity = "-" if neg else "+"
    return mass, f"nucleon_resonance:(n={n},ℓ={ell},{parity}):{factor_kind}"


def _tetraquark_panel_mass_mev(
    key: str,
    xi: float,
) -> tuple[float, str] | None:
    canon = _canonical_key(key)
    kind = TETRAQUARK_PANEL_ROUTES.get(canon)
    if kind is None:
        return None
    m_p, m_pi, m_k = _witness_masses(xi)
    _ = m_p
    mass = hdr.charmed_tetraquark_mass_mev(
        kind,  # type: ignore[arg-type]
        m_pi_mev=m_pi,
        m_k_mev=m_k,
    )
    return mass, f"tetraquark:{kind}"


def _pentaquark_panel_mass_mev(
    key: str,
    xi: float,
) -> tuple[float, str] | None:
    canon = _canonical_key(key)
    route = PENTAQUARK_PANEL_ROUTES.get(canon)
    if route is None:
        return None
    k, orbit_split = route
    m_p, m_pi, m_k = _witness_masses(xi)
    mass = hdr.charmed_pentaquark_mass_mev(
        k,
        m_pi_mev=m_pi,
        m_k_mev=m_k,
        m_proton_mev=m_p,
        orbit_split=orbit_split,
    )
    tag = f"pentaquark:excitation_k={k}"
    if orbit_split:
        tag += ":orbit_split"
    return mass, tag


def _slot_label(ch: tgh.TuftExcitationChannel) -> str:
    sector = "meson" if ch.is_meson else "baryon"
    extra = f", $n_s={ch.n_strange}$" if ch.n_strange else ""
    if ch.is_meson:
        iso = ", isoscalar" if ch.isoscalar else ", isovector"
    else:
        iso = f", parity={'-' if ch.negative_parity else '+'}"
    return (
        f"$(n={ch.n},\\ell={ch.ell})$ "
        f"[{sector}, chart={ch.chart_shell}{extra}{iso}]"
    )


def _hqiv_only_slot_mass_mev(
    xi: float,
    ch: tgh.TuftExcitationChannel,
) -> tuple[float, str]:
    """HQIV-only TUFT slots: discharged tag without PDG isospin (prediction baseline)."""
    mass = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
    return mass, f"tuft:{_tuft_channel_tag(ch)}:hqiv_only"


@dataclass(frozen=True)
class MassRow:
    name: str
    pdg_key: str
    category: str
    hqiv_mev: float
    pdg_mev: float | None
    sigma_mev: float | None
    n_sigma: float | None
    match: str
    hqiv_only: bool = False
    pdg_id: str | None = None


def _repo_channel_index() -> dict[str, tgh.TuftExcitationChannel]:
    idx: dict[str, tgh.TuftExcitationChannel] = {}
    for ch in tgh.MESON_EXCITED_CHANNELS + tgh.BARYON_EXCITED_CHANNELS:
        if ch.pdg_key:
            idx[ch.pdg_key] = ch
    return idx


def _canonical_key(key: str) -> str:
    return KEY_ALIASES.get(key, key)


def _is_meson_category(category: str) -> bool:
    return category.startswith("meson") or category in ("tetraquark", "pentaquark_charm")


def _nearest_global_mass(
    pdg_mev: float,
    meson: bool,
    xi: float,
) -> tuple[float, str]:
    best_m = 0.0
    best_tag = ""
    best_err = float("inf")
    for n in range(0, 6):
        for ell in range(0, 6):
            if meson:
                for n_strange in range(0, 4):
                    for isoscalar in (False, True):
                        ch = tgh.TuftExcitationChannel.meson(
                            n, ell, n_strange, isoscalar=isoscalar
                        )
                        m = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
                        err = abs(m - pdg_mev)
                        if err < best_err:
                            best_err = err
                            best_m = m
                            best_tag = ch.tag
            else:
                for neg in (False, True):
                    ch = tgh.TuftExcitationChannel.baryon(n, ell, negative_parity=neg)
                    m = tgh.tuft_excited_mass_global_at_xi_mev(xi, ch)
                    err = abs(m - pdg_mev)
                    if err < best_err:
                        best_err = err
                        best_m = m
                        best_tag = ch.tag
    return best_m, best_tag


def _bottom_baryon_ground_mass_mev(
    entry: dict,
    *,
    xi: float,
) -> tuple[float, str] | None:
    key = _canonical_key(str(entry.get("key") or ""))
    mult = hdr.BOTTOM_BARYON_MULTIPLET_BY_PDG_KEY.get(key)
    if mult is None:
        return None
    import hqiv_hep_decay_chain as hc

    m_pi = hc._chiral_pseudoscalar_mass_mev("pi_plus", xi=xi)
    m_k = hc._chiral_pseudoscalar_mass_mev("K_plus", xi=xi)
    if m_pi is None or m_k is None:
        raise ValueError("chiral π/K readout required for bottom-baryon mass")
    m_p = hc._witness_nucleon_mass_mev("p")
    isospin_slot = _isospin_slot_for_entry(entry)
    mass = hdr.bottom_baryon_multiplet_mass_mev(
        m_p, m_pi, m_k, mult, isospin_slot=isospin_slot
    )
    tag = f"bottom_multiplet:{mult}"
    if isospin_slot is not None:
        tag += f":isospin={isospin_slot}"
    return mass, tag


def _hqiv_mass_for_entry(
    entry: dict,
    xi: float,
    channel_idx: dict[str, tgh.TuftExcitationChannel],
) -> tuple[float, str]:
    key = _canonical_key(str(entry.get("key") or ""))
    cat = str(entry.get("category") or "")
    if cat == "baryon_bottom":
        bottom = _bottom_baryon_ground_mass_mev(entry, xi=xi)
        if bottom is not None:
            return bottom
    heavy = _heavy_panel_mass_mev(entry, xi)
    if heavy is not None:
        return heavy
    strange_orbital = _strange_orbital_panel_mass_mev(entry, xi)
    if strange_orbital is not None:
        return strange_orbital
    tetra = _tetraquark_panel_mass_mev(key, xi)
    if tetra is not None:
        return tetra
    penta = _pentaquark_panel_mass_mev(key, xi)
    if penta is not None:
        return penta
    nucleon = _nucleon_resonance_panel_mass_mev(entry, xi)
    if nucleon is not None:
        return nucleon
    meson_tuft = _meson_tuft_panel_mass_mev(entry, xi)
    if meson_tuft is not None:
        return meson_tuft
    ch = _certified_tuft_channel_for_key(key, channel_idx)
    if ch is not None and _canonical_key(key) in CERTIFIED_TUFT_CHANNEL_KEYS:
        return _discharged_tuft_channel_mass_mev(entry, xi, ch)
    meson = _is_meson_category(cat)
    ch = channel_idx.get(_canonical_key(key))
    if ch is not None:
        return _discharged_tuft_channel_mass_mev(entry, xi, ch)
    pdg_mev = float(entry["mass_MeV"])
    m, tag = _nearest_global_mass(pdg_mev, meson=meson, xi=xi)
    return m, f"nearest:{tag}"


def _hqiv_only_channels() -> list[tgh.TuftExcitationChannel]:
    """Slots on the certified grid without a PDG comparison row."""
    return [
        tgh.TuftExcitationChannel.baryon(0, 4),
        tgh.TuftExcitationChannel.baryon(1, 2),
        tgh.TuftExcitationChannel.baryon(1, 3),
        tgh.TuftExcitationChannel.baryon(1, 4),
        tgh.TuftExcitationChannel.baryon(2, 0),
        tgh.TuftExcitationChannel.baryon(2, 1),
        tgh.TuftExcitationChannel.baryon(3, 0),
        tgh.TuftExcitationChannel.baryon(3, 1),
        tgh.TuftExcitationChannel.meson(0, 2, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(0, 3, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(0, 4, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(1, 1, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(1, 2, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(2, 0, 1, isoscalar=False),
        tgh.TuftExcitationChannel.meson(3, 0, 1, isoscalar=False),
        tgh.TuftExcitationChannel.meson(3, 1, 1, isoscalar=False),
        tgh.TuftExcitationChannel.meson(4, 2, 0, isoscalar=False),
        tgh.TuftExcitationChannel.meson(5, 0, 0, isoscalar=True),
        tgh.TuftExcitationChannel.meson(5, 1, 0, isoscalar=True),
    ]


@dataclass(frozen=True)
class HqivOnlyReadout:
    pdg_key: str
    name: str
    category: str
    match: str


def _hqiv_only_readouts(xi: float) -> list[tuple[HqivOnlyReadout, float]]:
    """Discharged heavy-ladder / molecular readouts without PDG listings."""
    m_p, m_pi, m_k = _witness_masses(xi)
    rows: list[tuple[HqivOnlyReadout, float]] = []

    def add(key: str, name: str, category: str, mass: float, match: str) -> None:
        rows.append((HqivOnlyReadout(key, name, category, match), mass))

    add(
        "pred:Dstar_plus_2S",
        r"$D^{*+}(2S)$ radial ladder",
        "hqiv_prediction",
        hdr.heavy_species_mass_mev(
            "open_charm_vector_radial",
            m_pi_mev=m_pi,
            m_k_mev=m_k,
            m_proton_mev=m_p,
            radial_k=1,
            isospin_slot="halfPlus",
        ),
        "heavy:open_charm_vector_radial:k=1:isospin=halfPlus",
    )
    add(
        "pred:open_charm_strange_vector_2S",
        r"$D_s^{*}(2S)$ radial ladder",
        "hqiv_prediction",
        hdr.open_charm_strange_vector_radial_meson_mass_mev(m_pi, m_k, 1),
        "heavy:open_charm_strange_vector_radial:k=1",
    )
    add(
        "pred:psi3S",
        r"$\psi(3S)$ radial rung",
        "hqiv_prediction",
        hdr.hidden_charm_quarkonium_excited_mass_mev(m_pi, 3),
        "heavy:hidden_charm_radial:k=3",
    )
    add(
        "pred:Upsilon4S",
        r"$\Upsilon(4S)$ radial rung",
        "hqiv_prediction",
        hdr.hidden_bottom_quarkonium_excited_mass_mev(m_p, m_pi, 3),
        "heavy:hidden_bottom_radial:k=3",
    )
    add(
        "pred:Zc4430",
        r"$Z_c(4430)$ open-vector tetraquark",
        "hqiv_prediction",
        hdr.charmed_tetraquark_mass_mev("open_vector", m_pi_mev=m_pi, m_k_mev=m_k),
        "tetraquark:open_vector",
    )
    add(
        "pred:Tcc_excited",
        r"$T_{cc}^*$ double-open excitation",
        "hqiv_prediction",
        hdr.charmed_tetraquark_mass_mev("double_open", m_pi_mev=m_pi, m_k_mev=m_k)
        * hdr.charmed_pentaquark_excitation_factor(1),
        "tetraquark:double_open:excitation_k=1",
    )
    add(
        "pred:Pc4500",
        r"$P_c(4500)^+$ pentaquark rung",
        "hqiv_prediction",
        hdr.charmed_pentaquark_mass_mev(3, m_pi_mev=m_pi, m_k_mev=m_k, m_proton_mev=m_p),
        "pentaquark:excitation_k=3",
    )
    return rows


def build_rows(xi: float = tmse.XI_LOCKIN) -> list[MassRow]:
    catalog = json.loads(PDG_JSON.read_text(encoding="utf-8"))
    channel_idx = _repo_channel_index()
    rows: list[MassRow] = []

    for entry in catalog.get("entries", []):
        cat = str(entry.get("category") or "")
        if cat in GROUND_CATEGORIES:
            continue
        pdg_mev = float(entry["mass_MeV"])
        if pdg_mev <= 0:
            continue
        sigma = entry.get("uncertainty_MeV")
        sigma_f = float(sigma) if sigma is not None else None
        hqiv, match = _hqiv_mass_for_entry(entry, xi, channel_idx)
        delta = hqiv - pdg_mev
        cmp_sigma = _comparison_sigma_mev(sigma_f, pdg_mev)
        n_sig = abs(delta) / cmp_sigma if cmp_sigma and cmp_sigma > 0 else None
        rows.append(
            MassRow(
                name=str(entry.get("name") or entry.get("key")),
                pdg_key=str(entry.get("key") or entry.get("name") or ""),
                category=cat,
                hqiv_mev=hqiv,
                pdg_mev=pdg_mev,
                sigma_mev=sigma_f,
                n_sigma=n_sig,
                match=match,
                pdg_id=str(entry.get("pdg_id") or "") or None,
            )
        )

    for ch in _hqiv_only_channels():
        mass, match = _hqiv_only_slot_mass_mev(xi, ch)
        rows.append(
            MassRow(
                name=_slot_label(ch),
                pdg_key=f"slot:{ch.chart_shell}:{ch.n}:{ch.ell}:{ch.valence_quarks}:{ch.n_strange}",
                category="hqiv_excited_slot",
                hqiv_mev=mass,
                pdg_mev=None,
                sigma_mev=None,
                n_sigma=None,
                match=match,
                hqiv_only=True,
            )
        )

    for pred, mass in _hqiv_only_readouts(xi):
        rows.append(
            MassRow(
                name=pred.name,
                pdg_key=pred.pdg_key,
                category=pred.category,
                hqiv_mev=mass,
                pdg_mev=None,
                sigma_mev=None,
                n_sigma=None,
                match=pred.match,
                hqiv_only=True,
            )
        )

    rows.sort(key=lambda r: (r.category, r.name))

    undischarged = [
        r.pdg_key
        for r in rows
        if not r.hqiv_only and r.match.startswith("nearest:")
    ]
    if undischarged:
        raise RuntimeError(
            "excited mass panel has undischarged nearest-shell rows: "
            + ", ".join(undischarged)
        )
    return rows


def _sigma_pull_metrics(scored: list[MassRow]) -> dict[str, object]:
    """Listed-PDG-σ pulls vs diagnostic max(σ, 1% M) floor used in the table."""
    listed_ns: list[float] = []
    floored_ns: list[float] = []
    floor_active = 0
    for r in scored:
        if r.pdg_mev is None or r.sigma_mev is None or r.sigma_mev <= 0:
            continue
        delta = abs(r.hqiv_mev - r.pdg_mev)
        listed_ns.append(delta / r.sigma_mev)
        cmp_sigma = _comparison_sigma_mev(r.sigma_mev, r.pdg_mev)
        if cmp_sigma and cmp_sigma > 0:
            floored_ns.append(delta / cmp_sigma)
        if r.sigma_mev < 0.01 * r.pdg_mev:
            floor_active += 1
    def _band(ns: list[float], k: float) -> int:
        return sum(1 for x in ns if x <= k)

    return {
        "sigma_pull_policy": (
            "Table n_sigma uses max(PDG sigma, 0.01 * mass) as a readout-resolution floor; "
            "n_sigma_listed uses published PDG sigma without flooring."
        ),
        "sigma_floor_active_count": floor_active,
        "within_1sigma_floored": _band(floored_ns, 1.0),
        "within_2sigma_floored": _band(floored_ns, 2.0),
        "within_3sigma_floored": _band(floored_ns, 3.0),
        "max_n_sigma_floored": max(floored_ns) if floored_ns else None,
        "median_n_sigma_floored": _median(floored_ns),
        "within_1sigma_listed": _band(listed_ns, 1.0),
        "within_2sigma_listed": _band(listed_ns, 2.0),
        "within_3sigma_listed": _band(listed_ns, 3.0),
        "max_n_sigma_listed": max(listed_ns) if listed_ns else None,
        "median_n_sigma_listed": _median(listed_ns),
        "listed_pull_over_100sigma_count": sum(1 for x in listed_ns if x > 100.0),
    }


def _is_type_a_listed_pull(
    r: MassRow,
    listed_ns: float | None,
) -> bool:
    if listed_ns is None or r.pdg_mev is None or r.sigma_mev is None or r.sigma_mev <= 0:
        return False
    return listed_ns > 100.0 or r.sigma_mev < 0.01 * r.pdg_mev


def _fmt_listed_ns_display(r: MassRow, listed_ns: float | None) -> str:
    if listed_ns is None:
        return "---"
    if _is_type_a_listed_pull(r, listed_ns):
        return "Type A"
    return _fmt_ns(listed_ns)


def _row_audit_fields(r: MassRow) -> dict[str, object]:
    delta = (r.hqiv_mev - r.pdg_mev) if r.pdg_mev is not None else None
    abs_pct = (
        abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
        if r.pdg_mev is not None and r.pdg_mev > 0
        else None
    )
    cmp_sigma = _comparison_sigma_mev(r.sigma_mev, r.pdg_mev)
    listed_ns = (
        abs(r.hqiv_mev - r.pdg_mev) / r.sigma_mev
        if r.pdg_mev and r.sigma_mev and r.sigma_mev > 0
        else None
    )
    return {
        "name": r.name,
        "pdg_key": r.pdg_key,
        "pdg_id": r.pdg_id,
        "category": r.category,
        "hqiv_mev": r.hqiv_mev,
        "pdg_mev": r.pdg_mev,
        "delta_mev": delta,
        "abs_error_pct": abs_pct,
        "sigma_mev": r.sigma_mev,
        "sigma_source": SIGMA_SOURCE if r.sigma_mev is not None else None,
        "sigma_comparison_mev": cmp_sigma,
        "n_sigma_listed": listed_ns,
        "n_sigma_floored": r.n_sigma,
        "match": r.match,
        "hqiv_only": r.hqiv_only,
        **_outside_curvature_fields(r),
    }


def build_payload(rows: list[MassRow]) -> dict:
    with_pdg = [r for r in rows if not r.hqiv_only]
    scored = [
        r
        for r in with_pdg
        if r.pdg_mev is not None
        and r.pdg_mev > 0
        and r.sigma_mev is not None
        and r.sigma_mev > 0
        and r.n_sigma is not None
    ]
    pull = _sigma_pull_metrics(scored)
    catalog = json.loads(PDG_JSON.read_text(encoding="utf-8"))
    return {
        "source": "scripts/export_excited_mass_table.py",
        "xi_lockin": tmse.XI_LOCKIN,
        "pdg_catalog": str(PDG_JSON.relative_to(ROOT)),
        "pdg_reference": catalog.get("citation") or SIGMA_SOURCE,
        "sigma_source": SIGMA_SOURCE,
        "panel_selection_note": PANEL_SELECTION_NOTE,
        "panel_audit_csv": str(DEFAULT_AUDIT_CSV.relative_to(ROOT)),
        "lab_mass_chart_factor": _lab_mass_chart_factor(),
        "outside_curvature_witness": str(EARTH_CLOSURE_JSON.relative_to(ROOT)),
        "accelerator_dressing_witness": str(ACCELERATOR_DRESSING_JSON.relative_to(ROOT)),
        "row_count": len(rows),
        "pdg_matched_count": len(with_pdg),
        "pdg_scored_count": len(scored),
        "hqiv_only_count": sum(1 for r in rows if r.hqiv_only),
        "within_1sigma": pull["within_1sigma_floored"],
        "within_2sigma": pull["within_2sigma_floored"],
        "within_3sigma": pull["within_3sigma_floored"],
        "max_n_sigma": pull["max_n_sigma_floored"],
        "mean_abs_error_pct": (
            sum(abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev for r in with_pdg if r.pdg_mev)
            / max(1, sum(1 for r in with_pdg if r.pdg_mev))
            * 100.0
            if with_pdg
            else None
        ),
        "median_abs_error_pct": _median(
            [
                abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
                for r in with_pdg
                if r.pdg_mev
            ]
        ),
        "max_abs_error_pct": (
            max(
                abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
                for r in with_pdg
                if r.pdg_mev
            )
            if with_pdg
            else None
        ),
        **pull,
        "rows": [_row_audit_fields(r) for r in rows],
        "pdg_panel_rows": [_row_audit_fields(r) for r in rows if not r.hqiv_only and r.pdg_mev],
        "hqiv_prediction_rows": [_row_audit_fields(r) for r in rows if r.hqiv_only],
        "sector_summaries": [
            {"label": label, **_pull_summary(group)}
            for label, group in _sector_summary_groups(rows)
        ],
    }


def _median(values: list[float]) -> float | None:
    if not values:
        return None
    s = sorted(values)
    mid = len(s) // 2
    if len(s) % 2:
        return s[mid]
    return 0.5 * (s[mid - 1] + s[mid])


def _pull_summary(rows: list[MassRow]) -> dict[str, object]:
    with_pdg = [r for r in rows if r.pdg_mev is not None and not r.hqiv_only]
    with_ns = [r for r in with_pdg if r.n_sigma is not None]
    ns = [r.n_sigma for r in with_ns if r.n_sigma is not None]
    pct = [
        abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
        for r in with_pdg
        if r.pdg_mev
    ]
    n = len(with_pdg)
    return {
        "n": n,
        "within_1sigma": sum(1 for r in with_ns if r.n_sigma is not None and r.n_sigma <= 1.0),
        "within_2sigma": sum(1 for r in with_ns if r.n_sigma is not None and r.n_sigma <= 2.0),
        "within_3sigma": sum(1 for r in with_ns if r.n_sigma is not None and r.n_sigma <= 3.0),
        "mean_n_sigma": sum(ns) / len(ns) if ns else None,
        "median_n_sigma": _median(ns),
        "max_n_sigma": max(ns) if ns else None,
        "mean_abs_error_pct": sum(pct) / len(pct) if pct else None,
    }


def _sector_summary_groups(rows: list[MassRow]) -> list[tuple[str, list[MassRow]]]:
    with_pdg = [r for r in rows if r.pdg_mev is not None and not r.hqiv_only]
    out: list[tuple[str, list[MassRow]]] = [("Global", with_pdg)]
    by_cat: dict[str, list[MassRow]] = {}
    for r in with_pdg:
        by_cat.setdefault(r.category, []).append(r)
    priority = (
        "baryon_bottom",
        "baryon_charm",
        "baryon_resonance",
        "meson_charm",
    )
    for cat in priority:
        if cat in by_cat:
            label = _sector_label(cat)
            if cat == "baryon_bottom":
                label = "bottom baryon (multiplet)"
            out.append((label, by_cat.pop(cat)))
    for cat in sorted(by_cat):
        out.append((_sector_label(cat), by_cat[cat]))
    direct = [
        r
        for r in with_pdg
        if r.match.startswith(
            (
                "tuft:",
                "nucleon_resonance:",
                "bottom_multiplet:",
                "heavy:",
                "charmed_multiplet:",
                "strange_orbital:",
                "tetraquark:",
                "pentaquark:",
            )
        )
    ]
    nearest = [r for r in with_pdg if r.match.startswith("nearest:")]
    if direct:
        out.append(("Direct $(n,\\ell)$ / multiplet tag", direct))
    if nearest:
        out.append(("Nearest-shell fallback", nearest))
    return out


def sector_summaries(rows: list[MassRow]) -> list[tuple[str, dict[str, object]]]:
    return [(label, _pull_summary(group)) for label, group in _sector_summary_groups(rows)]


def _fmt_frac(count: int, n: int) -> str:
    if n == 0:
        return "0"
    pct = int(round(100.0 * count / n))
    return f"{count} ({pct}\\%)"


def _tex_path(rel: str) -> str:
    escaped = rel.replace("_", "\\_")
    return f"\\texttt{{{escaped}}}"


def _fmt_pct(x: float | None) -> str:
    if x is None:
        return "---"
    return f"{x:.2f}\\%"
    if x is None:
        return "---"
    return f"{x:.2f}\\%"


def _fmt_ns(x: float | None, *, na: bool = False) -> str:
    if na or x is None:
        return "---" if x is None else "n/a"
    if x >= 100.0:
        return f"{x:.2e}"
    return f"{x:.2f}"


def build_distribution_tex(payload: dict) -> str:
    summaries = payload.get("sector_summaries") or []
    audit_link = _tex_path(str(payload.get("panel_audit_csv", "data/excited_mass_panel_audit.csv")))
    lines = [
        "% Auto-generated by scripts/export_excited_mass_table.py",
        "\\begin{table}[ht]",
        "\\centering",
        "\\caption{Excited-state mass panel: global and sector-stratified pull summaries "
        "(PDG comparison layer only). Bottom-baryon grounds use discharged multiplet readout; "
        "sub-MeV listed $\\sigma$ makes $n_\\sigma$ non-diagnostic there---pulls use "
        "$\\max(\\sigma,\\,0.01M)$ and mean $|\\Delta|/M$ where noted. "
        "All PDG rows use discharged TUFT, heavy-ladder, or molecular readouts. "
        f"Full per-state audit: {audit_link}.}}",
        "\\label{tab:excited-mass-distribution}",
        "\\small",
        "\\begin{tabular}{@{}lrrrrrr@{}}",
        "\\toprule",
        "Sector / match & $n$ & $\\le1\\sigma$ & $\\le2\\sigma$ & $\\le3\\sigma$ "
        "& med.\\ $n_\\sigma$ & mean $|\\Delta|/M$ \\\\",
        "\\midrule",
    ]
    for i, entry in enumerate(summaries):
        if i == 1:
            lines.append("\\midrule")
        label = str(entry["label"])
        na_ns = label.startswith("bottom baryon")
        n = int(entry["n"])
        lines.append(
            f"{label} & {n} & "
            f"{_fmt_frac(int(entry['within_1sigma']), n)} & "
            f"{_fmt_frac(int(entry['within_2sigma']), n)} & "
            f"{_fmt_frac(int(entry['within_3sigma']), n)} & "
            f"{_fmt_ns(entry.get('median_n_sigma'), na=na_ns)} & "
            f"{_fmt_pct(entry.get('mean_abs_error_pct'))} \\\\"
        )
    lines.extend(["\\bottomrule", "\\end{tabular}", "\\end{table}", ""])
    return "\n".join(lines)


def _sector_label(category: str) -> str:
    labels = {
        "baryon_bottom": "bottom baryon",
        "baryon_charm": "charm baryon",
        "baryon_decuplet": "decuplet",
        "baryon_double_charm": "double-charm",
        "baryon_resonance": "N resonance",
        "baryon_xi_resonance": "Xi resonance",
        "meson_charm": "charm meson",
        "meson_hidden": "hidden flavour",
        "meson_strange": "strange meson",
        "meson_vector": "vector meson",
        "tetraquark": "tetraquark",
        "pentaquark_charm": "pentaquark",
        "hqiv_excited_slot": "HQIV slot",
        "hqiv_prediction": "HQIV prediction",
    }
    return labels.get(category, category.replace("_", " "))


_KEY_LATEX: dict[str, str] = {
    "B+": r"$B^+$",
    "B0": r"$B^0$",
    "Bs0": r"$B_s^0$",
    "B_c+": r"$B_c^+$",
    "B*+": r"$B^{*+}$",
    "B*0": r"$B^{*0}$",
    "D+": r"$D^+$",
    "D0": r"$D^0$",
    "Ds+": r"$D_s^+$",
    "D*+": r"$D^{*+}$",
    "D*0": r"$D^{*0}$",
    "D*0(2S)": r"$D^{*0}(2S)$",
    "D_s1": r"$D_{s1}$",
    "Delta+": r"$\Delta^+$",
    "Delta++": r"$\Delta^{++}$",
    "Delta-": r"$\Delta^-$",
    "Delta0": r"$\Delta^0$",
    "J/psi": r"$J/\psi$",
    "psi2S": r"$\psi(2S)$",
    "chi_c1": r"$\chi_{c1}$",
    "Upsilon": r"$\Upsilon$",
    "Upsilon2S": r"$\Upsilon(2S)$",
    "Upsilon3S": r"$\Upsilon(3S)$",
    "rho+": r"$\rho^+$",
    "rho0": r"$\rho^0$",
    "omega": r"$\omega$",
    "phi": r"$\phi$",
    "K*+": r"$K^{*+}$",
    "K*-": r"$K^{*-}$",
    "K*0": r"$K^{*0}$",
    "K*0_bar": r"$\overline{K}^{*0}$",
    "K1_1270": r"$K_1(1270)$",
    "Lambda": r"$\Lambda$",
    "Lambda_b0": r"$\Lambda_b^0$",
    "Lambda_c+": r"$\Lambda_c^+$",
    "Lambda1405": r"$\Lambda(1405)$",
    "Sigma+": r"$\Sigma^+$",
    "Sigma-": r"$\Sigma^-$",
    "Sigma0": r"$\Sigma^0$",
    "Sigma*+": r"$\Sigma^{*+}$",
    "Sigma*-": r"$\Sigma^{*-}$",
    "Sigma*0": r"$\Sigma^{*0}$",
    "Sigma1385": r"$\Sigma(1385)$",
    "Sigma_c+": r"$\Sigma_c^+$",
    "Sigma_c-": r"$\Sigma_c^-$",
    "Sigma_c0": r"$\Sigma_c^0$",
    "Sigma_b+": r"$\Sigma_b^+$",
    "Sigma_b-": r"$\Sigma_b^-$",
    "Sigma_b0": r"$\Sigma_b^0$",
    "Xi0": r"$\Xi^0$",
    "Xi-": r"$\Xi^-$",
    "Xi*0": r"$\Xi^{*0}$",
    "Xi*-": r"$\Xi^{*-}$",
    "Xi_b-": r"$\Xi_b^-$",
    "Xi_b0": r"$\Xi_b^0$",
    "Xi_c+": r"$\Xi_c^+$",
    "Xi_c0": r"$\Xi_c^0$",
    "Xi_c_prime+": r"$\Xi_c^{\prime +}$",
    "Xi_c_prime0": r"$\Xi_c^{\prime 0}$",
    "Xi_cc+": r"$\Xi_{cc}^+$",
    "Xi_cc++": r"$\Xi_{cc}^{++}$",
    "Omega-": r"$\Omega^-$",
    "Omega*-": r"$\Omega^{*-}$",
    "Omega_b-": r"$\Omega_b^-$",
    "Omega_c+": r"$\Omega_c^+$",
    "Omega_c0": r"$\Omega_c^0$",
    "Omega_cc": r"$\Omega_{cc}$",
    "ccd_baryon": r"$ccd$ (ref.)",
    "tetraquark-light": "tetraquark",
    "Tcc": r"$T_{cc}$",
    "X(3872)": r"$X(3872)$",
    "X4140": r"$X(4140)$",
    "X4274": r"$X(4274)$",
    "Zc(3900)": r"$Z_c(3900)$",
    "Zc4020": r"$Z_c(4020)$",
    "Zc4200": r"$Z_c(4200)$",
    "Pc(4312)+": r"$P_c(4312)^+$",
    "Pc(4440)+": r"$P_c(4440)^+$",
    "Pc(4457)+": r"$P_c(4457)^+$",
    "Pc4380": r"$P_c(4380)$",
    "f0_1370": r"$f_0(1370)$",
    "f0_980": r"$f_0(980)$",
    "f2_1270": r"$f_2(1270)$",
    "h1_1170": r"$h_1(1170)$",
}


def _key_to_latex(key: str) -> str:
    if key in _KEY_LATEX:
        return _KEY_LATEX[key]
    if key.startswith("slot:"):
        parts = key.split(":")
        if len(parts) >= 5:
            _, chart, n, ell, valence, *rest = parts
            ns = rest[0] if rest else "0"
            return (
                f"$(n={n},\\ell={ell})$ "
                f"[{'meson' if valence == '2' else 'baryon'}, chart={chart}, $n_s={ns}$]"
            )
        if len(parts) == 3:
            _, n, ell = parts
            return f"$(n={n},\\ell={ell})$"
    m = re.fullmatch(r"N(\d+)", key)
    if m:
        return f"$N({m.group(1)})$"
    return _tex_escape(key)


def _tex_escape(s: str) -> str:
    return (
        s.replace("&", "\\&")
        .replace("%", "\\%")
        .replace("_", "\\_")
        .replace("#", "\\#")
    )


def _tex_route(s: str) -> str:
    ascii_s = s.replace("ℓ", "l")
    esc = _tex_escape(ascii_s)
    return f"\\parbox[t]{{\\linewidth}}{{\\texttt{{\\scriptsize\\seqsplit{{{esc}}}}}}}"


def _tex_table_open(font: str = "footnotesize") -> str:
    return (
        f"{{\\{font}\\setlength{{\\tabcolsep}}{{3pt}}\\renewcommand{{\\arraystretch}}{{1.05}}%"
    )


def _tex_table_close() -> str:
    return "}"


_GREEK_ID_ASCII = {
    "ρ": "rho",
    "φ": "phi",
    "ω": "omega",
    "Δ": "Delta",
    "Σ": "Sigma",
    "Λ": "Lambda",
    "Ξ": "Xi",
    "Ω": "Omega",
    "π": "pi",
    "η": "eta",
    "χ": "chi",
    "ψ": "psi",
    "ϒ": "Upsilon",
    "K": "K",
}


def _tex_display_name(name: str) -> str:
    if "$" in name:
        return name
    return _tex_escape(name)


def _pdg_id_tex(s: str | None) -> str:
    if not s:
        return "---"
    ascii_s = s
    for g, a in _GREEK_ID_ASCII.items():
        ascii_s = ascii_s.replace(g, a)
    return f"\\texttt{{{_tex_escape(ascii_s)}}}"


def write_audit_csv(rows: list[MassRow], path: Path) -> None:
    pdg_rows = [r for r in rows if not r.hqiv_only and r.pdg_mev is not None]
    fields = [
        "name",
        "pdg_key",
        "pdg_id",
        "category",
        "hqiv_mev",
        "pdg_mev",
        "delta_mev",
        "abs_error_pct",
        "sigma_mev",
        "sigma_source",
        "sigma_comparison_mev",
        "n_sigma_listed",
        "n_sigma_floored",
        "discharge_match",
        "outside_dressing_product",
        "delta_outside_chart_mev",
        "delta_lab_ambient_mev",
        "delta_accelerator_mev",
        "facility_id",
        "K_facility",
        "m_apparent_facility_mev",
        "delta_residual_mev",
        "delta_residual_facility_mev",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=fields)
        writer.writeheader()
        for r in pdg_rows:
            audit = _row_audit_fields(r)
            writer.writerow(
                {
                    "name": audit["name"],
                    "pdg_key": audit["pdg_key"],
                    "pdg_id": audit.get("pdg_id") or "",
                    "category": audit["category"],
                    "hqiv_mev": f"{audit['hqiv_mev']:.6f}",
                    "pdg_mev": f"{audit['pdg_mev']:.6f}",
                    "delta_mev": f"{audit['delta_mev']:.6f}",
                    "abs_error_pct": f"{audit['abs_error_pct']:.6f}",
                    "sigma_mev": (
                        f"{audit['sigma_mev']:.6g}" if audit["sigma_mev"] is not None else ""
                    ),
                    "sigma_source": audit.get("sigma_source") or "",
                    "sigma_comparison_mev": (
                        f"{audit['sigma_comparison_mev']:.6g}"
                        if audit.get("sigma_comparison_mev")
                        else ""
                    ),
                    "n_sigma_listed": (
                        f"{audit['n_sigma_listed']:.6g}"
                        if audit.get("n_sigma_listed") is not None
                        else ""
                    ),
                    "n_sigma_floored": (
                        f"{audit['n_sigma_floored']:.6f}"
                        if audit.get("n_sigma_floored") is not None
                        else ""
                    ),
                    "discharge_match": audit["match"],
                    "outside_dressing_product": (
                        f"{audit['outside_dressing_product']:.8g}"
                        if audit.get("outside_dressing_product") is not None
                        else ""
                    ),
                    "delta_outside_chart_mev": (
                        f"{audit['delta_outside_chart_mev']:.6f}"
                        if audit.get("delta_outside_chart_mev") is not None
                        else ""
                    ),
                    "delta_lab_ambient_mev": (
                        f"{audit['delta_lab_ambient_mev']:.6f}"
                        if audit.get("delta_lab_ambient_mev") is not None
                        else ""
                    ),
                    "delta_accelerator_mev": (
                        f"{audit['delta_accelerator_mev']:.6f}"
                        if audit.get("delta_accelerator_mev") is not None
                        else ""
                    ),
                    "facility_id": audit.get("facility_id") or "",
                    "K_facility": (
                        f"{audit['K_facility']:.8g}"
                        if audit.get("K_facility") is not None
                        else ""
                    ),
                    "m_apparent_facility_mev": (
                        f"{audit['m_apparent_facility_mev']:.6f}"
                        if audit.get("m_apparent_facility_mev") is not None
                        else ""
                    ),
                    "delta_residual_mev": (
                        f"{audit['delta_residual_mev']:.6f}"
                        if audit.get("delta_residual_mev") is not None
                        else ""
                    ),
                    "delta_residual_facility_mev": (
                        f"{audit['delta_residual_facility_mev']:.6f}"
                        if audit.get("delta_residual_facility_mev") is not None
                        else ""
                    ),
                }
            )


def _histogram_bins(values: list[float], edges: list[float]) -> list[int]:
    counts = [0] * (len(edges) - 1)
    for v in values:
        for i in range(len(edges) - 1):
            if edges[i] <= v < edges[i + 1]:
                counts[i] += 1
                break
    return counts


def build_pull_histogram_tex(rows: list[MassRow], payload: dict) -> str:
    pdg_rows = [r for r in rows if not r.hqiv_only and r.pdg_mev]
    audit_link = _tex_path(str(payload.get("panel_audit_csv", "data/excited_mass_panel_audit.csv")))
    abs_pct = [
        abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0 for r in pdg_rows if r.pdg_mev
    ]
    pct_edges = [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 1.01]
    pct_labels = ["0--0.1", "0.1--0.2", "0.2--0.3", "0.3--0.5", "0.5--0.7", "0.7--1"]
    pct_counts = _histogram_bins(abs_pct, pct_edges)

    floored_ns = [
        float(r.n_sigma)
        for r in pdg_rows
        if r.n_sigma is not None and math.isfinite(r.n_sigma)
    ]
    ns_edges = [0.0, 0.25, 0.5, 0.75, 1.0, 2.0, 1.01]
    ns_labels = ["0--0.25", "0.25--0.5", "0.5--0.75", "0.75--1", "1--2", "$>$2"]
    ns_counts = _histogram_bins(floored_ns, ns_edges)

    def bar_block(counts: list[int], labels: list[str], x0: float, title: str) -> list[str]:
        ymax = max(counts) if counts else 1
        out = [f"\\node[anchor=west] at ({x0}, 4.6) {{\\small {title}}};"]
        for i, c in enumerate(counts):
            h = 0.0 if ymax == 0 else 3.6 * c / ymax
            x = x0 + i * 1.05
            out.append(
                f"\\draw[fill=blue!35,draw=blue!60] ({x},0) rectangle ({x+0.85},{h:.3f});"
            )
            out.append(
                f"\\node[anchor=north,font=\\scriptsize] at ({x+0.425},0) {{{labels[i]}}};"
            )
            out.append(
                f"\\node[anchor=south,font=\\scriptsize] at ({x+0.425},{h:.3f}) {{{c}}};"
            )
        out.append(f"\\draw[->] ({x0-0.15},0) -- ({x0 + len(counts)*1.05 + 0.2},0);")
        return out

    return "\n".join(
        [
            "% Auto-generated by scripts/export_excited_mass_table.py",
            "\\begin{figure}[ht]",
            "\\centering",
            "\\begin{tikzpicture}[x=1.1cm,y=1cm]",
            *bar_block(pct_counts, pct_labels, 0.0, "$|\\Delta|/M$ (\\%)"),
            *bar_block(ns_counts, ns_labels, 8.0, "Floored $\\tilde n_\\sigma$"),
            "\\end{tikzpicture}",
            "\\caption{Excited-state mass panel ($85$ PDG rows): histogram of scale-free "
            f"errors $|\\Delta|/M$ (left) and diagnostic floored pulls "
            f"$\\tilde n_\\sigma=|\\Delta|/\\max(\\sigma,0.01M)$ (right). "
            f"Type~A listed-$\\sigma$ pulls are audit-only "
            f"(Table~\\ref{{tab:listed-pull-extremes}}). "
            f"Listed $\\sigma$ source: {payload.get('sigma_source', SIGMA_SOURCE)}. "
            f"Per-state values in {audit_link}.}}",
            "\\label{fig:excited-mass-pull-histogram}",
            "\\end{figure}",
            "",
        ]
    )


def build_outlier_curvature_tex(rows: list[MassRow], payload: dict) -> str:
    pdg_rows = [r for r in rows if not r.hqiv_only and r.pdg_mev]
    pdg_rows.sort(key=lambda r: abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev, reverse=True)
    top = pdg_rows[:12]
    k_lab = payload.get("lab_mass_chart_factor", _lab_mass_chart_factor())
    lines = [
        "% Auto-generated by scripts/export_excited_mass_table.py",
        _tex_table_open("footnotesize"),
        "\\begin{longtable}{@{}lrrrrrrr@{}}",
        "\\caption{Largest $|\\Delta|/M$ outliers with outside-curvature ledger. "
        f"$D_{{\\mathrm{{outside}}}}$: certified static bath dressings on the discharge route; "
        f"$\\Delta_{{\\mathrm{{outside}}}}$ = $m_{{\\mathrm{{HQIV}}}}-m_{{\\mathrm{{inside}}}}$ "
        f"with $m_{{\\mathrm{{inside}}}}=m_{{\\mathrm{{HQIV}}}}/D_{{\\mathrm{{outside}}}}$; "
        f"$\\Delta_{{\\mathrm{{lab}}}}$ = $m_{{\\mathrm{{HQIV}}}}(K_{{\\mathrm{{mass\\,chart}}}}-1)$ "
        f"at Earth surface ($K={k_lab:.6f}$, \\texttt{{data/earth\\_outside\\_closure.json}}); "
        f"$\\Delta_{{\\mathrm{{accel}}}}$ = $m_{{\\mathrm{{HQIV}}}}(K_{{\\mathrm{{facility}}}}-1)$ "
        "for species with an assigned accelerator route (\\texttt{data/accelerator\\_outside\\_dressing.json}); "
        "$\\Delta_{\\mathrm{res}}$ = "
        "$(m_{\\mathrm{PDG}}-m_{\\mathrm{HQIV}})-\\Delta_{\\mathrm{lab}}$.} "
        "\\label{tab:excited-mass-outlier-curvature} \\\\",
        "\\toprule",
        "State & $m_{\\mathrm{HQIV}}$ & $m_{\\mathrm{PDG}}$ & $|\\Delta|/M$\\,\\% "
        "& $\\Delta_{\\mathrm{outside}}$ & $\\Delta_{\\mathrm{lab}}$ & $\\Delta_{\\mathrm{accel}}$ "
        "& $\\Delta_{\\mathrm{res}}$ \\\\",
        "\\midrule",
        "\\endlastfoot",
    ]
    for r in top:
        name = _key_to_latex(r.pdg_key) if r.pdg_key else _tex_escape(r.name)
        fields = _outside_curvature_fields(r)
        pct = abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
        d_out = fields["delta_outside_chart_mev"]
        d_lab = fields["delta_lab_ambient_mev"]
        d_accel = fields["delta_accelerator_mev"]
        d_res = fields["delta_residual_mev"]
        accel_s = f"{d_accel:+.2f}" if d_accel is not None else "---"
        lines.append(
            f"{name} & {r.hqiv_mev:.1f} & {r.pdg_mev:.1f} & {pct:.3f} "
            f"& {d_out:+.2f} & {d_lab:+.2f} & {accel_s} & {d_res:+.2f} \\\\"
        )
    lines.extend(["\\end{longtable}", _tex_table_close(), ""])
    return "\n".join(lines)


def build_predictions_tex(rows: list[MassRow], payload: dict) -> str:
    preds = [r for r in rows if r.hqiv_only]
    _ = payload
    lines = [
        "% Auto-generated by scripts/export_excited_mass_table.py",
        _tex_table_open("footnotesize"),
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.26\linewidth}lr>{\raggedright\arraybackslash}p{0.36\linewidth}@{}}",
        "\\caption{HQIV-only excited-state mass predictions ($"
        f"{len(preds)}$ rows): certified TUFT grid slots and discharged heavy-ladder/molecular "
        "readouts without PDG listings. Falsifiable targets of the discrete carrier.} "
        "\\label{tab:hqiv-only-excited} \\\\",
        "\\toprule",
        "State / slot & Sector & $m_{\\mathrm{HQIV}}$ (MeV) & Discharge route \\\\",
        "\\midrule",
        "\\endfirsthead",
        "\\multicolumn{4}{c}{{\\tablename\\ \\thetable{} -- continued}} \\\\",
        "\\toprule",
        "State / slot & Sector & $m_{\\mathrm{HQIV}}$ (MeV) & Discharge route \\\\",
        "\\midrule",
        "\\endhead",
        "\\bottomrule",
        "\\multicolumn{4}{p{0.95\\linewidth}}{\\footnotesize Generated from "
        "\\texttt{data/excited\\_mass\\_comparison.json} (\\texttt{hqiv\\_prediction\\_rows}). "
        "No PDG mass entered the prediction path.} \\\\",
        "\\endlastfoot",
    ]
    for r in preds:
        if r.category == "hqiv_prediction":
            name = r.name
        else:
            name = _tex_display_name(r.name)
        sector = _tex_escape(_sector_label(r.category))
        mass = f"{r.hqiv_mev:.1f}"
        lines.append(f"{name} & {sector} & {mass} & {_tex_route(r.match)} \\\\")
    lines.extend(["\\end{longtable}", _tex_table_close(), ""])
    return "\n".join(lines)


def build_audit_tex(rows: list[MassRow], payload: dict) -> str:
    pdg_rows = [r for r in rows if not r.hqiv_only and r.pdg_mev]
    audit_link = _tex_path(str(payload.get("panel_audit_csv", "data/excited_mass_panel_audit.csv")))
    lines = [
        "% Auto-generated by scripts/export_excited_mass_table.py — supplemental full audit",
        _tex_table_open("scriptsize"),
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.11\linewidth}rrrrrrl@{}}",
        "\\caption{Full excited-state audit ($85$ PDG rows): HQIV vs listed PDG mass, "
        f"listed $\\sigma$, both pull conventions, PDG identifier. "
        f"$\\sigma$ source: {payload.get('sigma_source', SIGMA_SOURCE)}. "
        f"CSV mirror: {audit_link}.}} "
        "\\label{tab:excited-mass-audit} \\\\",
        "\\toprule",
        "State & $m_{\\mathrm{HQIV}}$ & $m_{\\mathrm{PDG}}$ & $|\\Delta|/M$\\,\\% "
        "& $\\sigma$ & $n_\\sigma^{\\mathrm{listed}}$ & $\\tilde n_\\sigma$ & PDG id \\\\",
        "\\midrule",
        "\\endfirsthead",
        "\\multicolumn{8}{c}{{\\tablename\\ \\thetable{} -- continued}} \\\\",
        "\\toprule",
        "State & $m_{\\mathrm{HQIV}}$ & $m_{\\mathrm{PDG}}$ & $|\\Delta|/M$\\,\\% "
        "& $\\sigma$ & $n_\\sigma^{\\mathrm{listed}}$ & $\\tilde n_\\sigma$ & PDG id \\\\",
        "\\midrule",
        "\\endhead",
        "\\bottomrule",
        "\\multicolumn{8}{p{0.98\\linewidth}}{\\footnotesize "
        f"{payload.get('panel_selection_note', PANEL_SELECTION_NOTE)} "
        "$n_\\sigma^{\\mathrm{listed}}$: raw PDG $\\sigma$ (``Type A'' = ill-posed; "
        "numeric values in CSV only); $\\tilde n_\\sigma$: floored at $0.01M$.} \\\\",
        "\\endlastfoot",
    ]
    for r in pdg_rows:
        name = _key_to_latex(r.pdg_key) if r.pdg_key else _tex_escape(r.name)
        pct = abs(r.hqiv_mev - r.pdg_mev) / r.pdg_mev * 100.0
        listed_ns = (
            abs(r.hqiv_mev - r.pdg_mev) / r.sigma_mev
            if r.sigma_mev and r.sigma_mev > 0
            else None
        )
        sig = f"{r.sigma_mev:.4g}" if r.sigma_mev is not None else "---"
        ns = _fmt_listed_ns_display(r, listed_ns)
        floored = f"{r.n_sigma:.2f}" if r.n_sigma is not None else "---"
        pdg_id = _pdg_id_tex(r.pdg_id)
        lines.append(
            f"{name} & {r.hqiv_mev:.2f} & {r.pdg_mev:.2f} & {pct:.3f} & {sig} & {ns} & {floored} & {pdg_id} \\\\"
        )
    lines.extend(["\\end{longtable}", _tex_table_close(), ""])
    return "\n".join(lines)


def build_tex(rows: list[MassRow], payload: dict) -> str:
    audit_link = _tex_path(str(payload.get("panel_audit_csv", "data/excited_mass_panel_audit.csv")))
    lines = [
        "% Auto-generated by scripts/export_excited_mass_table.py",
        _tex_table_open("footnotesize"),
        r"\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.11\linewidth}lrrrr@{}}",
        "\\caption{Excited-state mass panel: global TUFT readout vs PDG comparison "
        f"catalog ({payload['pdg_matched_count']} rows excluding ground $\\pi/K$ and baryon octet; "
        f"{payload['hqiv_only_count']} HQIV-only slots without PDG listings). "
        "PDG masses are quarantined comparison numerals only. "
        "All rows use discharged TUFT, heavy-ladder, or molecular readouts (no nearest-shell fallback). "
        "$\\tilde n_\\sigma=|\\Delta|/\\max(\\sigma,0.01M)$ is the table column "
        "(readout-resolution floor; see footnote).} "
        "\\label{tab:excited-mass-comparison} \\\\",
        "\\toprule",
        "State & Sector & HQIV & PDG & $\\pm$ & $\\tilde n_\\sigma$ \\\\",
        "\\midrule",
        "\\endfirsthead",
        "\\multicolumn{6}{c}{{\\tablename\\ \\thetable{} -- continued from previous page}} \\\\",
        "\\toprule",
        "State & Sector & HQIV & PDG & $\\pm$ & $\\tilde n_\\sigma$ \\\\",
        "\\midrule",
        "\\endhead",
        "\\midrule",
        "\\multicolumn{6}{r}{{Continued on next page}} \\\\",
        "\\endfoot",
        "\\bottomrule",
        "\\multicolumn{6}{p{0.95\\linewidth}}{\\footnotesize "
        f"Matched rows: {payload['pdg_matched_count']} "
        f"({payload.get('pdg_scored_count', payload['pdg_matched_count'])} with $\\sigma$). "
        f"Primary metric: mean $|\\Delta|/M={payload['mean_abs_error_pct']:.2f}\\%$ "
        f"(median {payload.get('median_abs_error_pct', 0):.2f}\\%, max {payload.get('max_abs_error_pct', 0):.2f}\\%). "
        f"Table $\\tilde n_\\sigma=|\\Delta|/\\max(\\sigma,0.01M)$ "
        f"({payload.get('sigma_floor_active_count', 0)} Type-A floors): "
        f"{payload['within_1sigma']}/{payload.get('pdg_scored_count', payload['pdg_matched_count'])} within $1\\sigma$ "
        f"(max {payload['max_n_sigma']:.2f}$\\sigma$). "
        f"Raw listed-$\\sigma$ pulls are audit-only "
        f"({payload.get('listed_pull_over_100sigma_count', 0)} rows formally $>100\\sigma$ on width-tagged "
        f"$\\sigma$; Table~\\ref{{tab:listed-pull-extremes}}). "
        f"Listed $\\sigma$ source: {payload.get('sigma_source', SIGMA_SOURCE)}. "
        f"Machine-readable audit (all fields): {audit_link}. "
        f"{payload.get('panel_selection_note', PANEL_SELECTION_NOTE)}" + "} \\\\",
        "\\endlastfoot",
    ]

    for r in rows:
        sector = _tex_escape(_sector_label(r.category))
        if r.hqiv_only and r.category == "hqiv_prediction":
            name = r.name
        elif r.hqiv_only:
            name = _tex_display_name(r.name)
        else:
            name = _key_to_latex(r.pdg_key)
        hqiv = f"{r.hqiv_mev:.1f}"
        if r.hqiv_only:
            lines.append(f"{name} & {sector} & {hqiv} & --- & --- & --- \\\\")
        else:
            pdg = f"{r.pdg_mev:.1f}"
            sig = f"{r.sigma_mev:.2f}" if r.sigma_mev is not None else "---"
            ns = f"{r.n_sigma:.2f}" if r.n_sigma is not None else "---"
            lines.append(f"{name} & {sector} & {hqiv} & {pdg} & {sig} & {ns} \\\\")

    lines.extend(
        [
            "\\end{longtable}",
            _tex_table_close(),
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Export excited mass comparison table")
    parser.add_argument("--tex-out", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--dist-tex-out", type=Path, default=DEFAULT_DIST_TEX)
    parser.add_argument("--pred-tex-out", type=Path, default=DEFAULT_PRED_TEX)
    parser.add_argument("--hist-tex-out", type=Path, default=DEFAULT_HIST_TEX)
    parser.add_argument("--audit-tex-out", type=Path, default=DEFAULT_AUDIT_TEX)
    parser.add_argument("--outlier-tex-out", type=Path, default=DEFAULT_OUTLIER_TEX)
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--audit-csv-out", type=Path, default=DEFAULT_AUDIT_CSV)
    args = parser.parse_args()

    rows = build_rows()
    payload = build_payload(rows)
    tex = build_tex(rows, payload)
    dist_tex = build_distribution_tex(payload)
    pred_tex = build_predictions_tex(rows, payload)
    hist_tex = build_pull_histogram_tex(rows, payload)
    audit_tex = build_audit_tex(rows, payload)
    outlier_tex = build_outlier_curvature_tex(rows, payload)
    write_audit_csv(rows, args.audit_csv_out)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    args.tex_out.parent.mkdir(parents=True, exist_ok=True)
    args.tex_out.write_text(tex, encoding="utf-8")
    args.dist_tex_out.parent.mkdir(parents=True, exist_ok=True)
    args.dist_tex_out.write_text(dist_tex, encoding="utf-8")
    args.pred_tex_out.write_text(pred_tex, encoding="utf-8")
    args.hist_tex_out.write_text(hist_tex, encoding="utf-8")
    args.audit_tex_out.write_text(audit_tex, encoding="utf-8")
    args.outlier_tex_out.parent.mkdir(parents=True, exist_ok=True)
    args.outlier_tex_out.write_text(outlier_tex, encoding="utf-8")

    paper_data = ROOT / "papers" / "hep_decay_readout" / "data"
    paper_data.mkdir(parents=True, exist_ok=True)
    (paper_data / "excited_mass_comparison.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    (paper_data / "excited_mass_panel_audit.csv").write_text(
        args.audit_csv_out.read_text(encoding="utf-8"), encoding="utf-8"
    )

    print(f"Wrote {args.tex_out} ({payload['row_count']} rows)")
    print(f"Wrote {args.dist_tex_out}")
    print(f"Wrote {args.pred_tex_out}")
    print(f"Wrote {args.hist_tex_out}")
    print(f"Wrote {args.audit_tex_out}")
    print(f"Wrote {args.outlier_tex_out}")
    print(f"Wrote {args.audit_csv_out}")
    print(f"Wrote {args.json_out}")


if __name__ == "__main__":
    main()
