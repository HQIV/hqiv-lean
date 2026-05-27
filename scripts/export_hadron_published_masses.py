#!/usr/bin/env python3
"""
Export PDG / literature hadron masses for the mass-spectrum calculator comparison layer.

NOT HQIV inputs — comparison only (see AGENTS/MASS_DERIVATION_ROADMAP.md).

Writes: data/hadron_published_masses.json

Run:
  python3 scripts/export_hadron_published_masses.py
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "hadron_published_masses.json"
OUT_JS = ROOT / "web" / "hqiv-mass-spectrum-calculator" / "hadron-published-data.js"

# (config_id or None, pdg_key, name, mass_MeV, uncertainty_MeV, pdg_id, category)
# config_id links to hadron-catalog.js HadronConfig.id when applicable.
ENTRIES: list[tuple] = [
    # --- Light baryon octet ---
    ("p", "proton", "p", 938.272088, 0.00000029, "p", "baryon_octet"),
    ("n", "neutron", "n", 939.565421, 0.00000028, "n", "baryon_octet"),
    ("lambda", "Lambda", "Λ", 1115.683, 0.006, "Λ", "baryon_octet"),
    ("sigma_plus", "Sigma+", "Σ⁺", 1189.37, 0.07, "Σ+", "baryon_octet"),
    ("sigma_zero", "Sigma0", "Σ⁰", 1192.642, 0.024, "Σ0", "baryon_octet"),
    ("sigma_minus", "Sigma-", "Σ⁻", 1197.449, 0.030, "Σ-", "baryon_octet"),
    ("xi_zero", "Xi0", "Ξ⁰", 1314.86, 0.20, "Ξ0", "baryon_octet"),
    ("xi_minus", "Xi-", "Ξ⁻", 1321.71, 0.07, "Ξ-", "baryon_octet"),
    ("omega", "Omega-", "Ω⁻", 1672.45, 0.29, "Ω-", "baryon_octet"),
    # --- Decuplet (Δ, Σ*, Ξ*, Ω*) ---
    ("delta_pp", "Delta++", "Δ⁺⁺", 2321.0, 2.1, "Δ(1232)++", "baryon_decuplet"),
    ("delta_p", "Delta+", "Δ⁺", 2452.0, 1.0, "Δ(1232)+", "baryon_decuplet"),
    ("delta_0", "Delta0", "Δ⁰", 2452.0, 1.0, "Δ(1232)0", "baryon_decuplet"),
    ("delta_m", "Delta-", "Δ⁻", 2452.0, 1.0, "Δ(1232)-", "baryon_decuplet"),
    ("sigma_star_p", "Sigma*+", "Σ*⁺", 1384.60, 0.60, "Σ(1385)+", "baryon_decuplet"),
    ("sigma_star_0", "Sigma*0", "Σ*⁰", 1383.7, 1.0, "Σ(1385)0", "baryon_decuplet"),
    ("sigma_star_m", "Sigma*-", "Σ*⁻", 1387.2, 0.5, "Σ(1385)-", "baryon_decuplet"),
    ("xi_star_0", "Xi*0", "Ξ*⁰", 1531.80, 0.30, "Ξ(1530)0", "baryon_decuplet"),
    ("xi_star_m", "Xi*-", "Ξ*⁻", 1535.0, 0.6, "Ξ(1530)-", "baryon_decuplet"),
    ("omega_star", "Omega*-", "Ω*⁻", 1672.45, 0.29, "Ω(1650)-", "baryon_decuplet"),
    # --- Charmed baryons ---
    ("lambda_c", "Lambda_c+", "Λ⁺_c", 2286.46, 0.14, "Λ+c", "baryon_charm"),
    ("sigma_c", "Sigma_c+", "Σ⁺_c", 2453.97, 0.31, "Σc(2455)++", "baryon_charm"),
    (None, "Sigma_c0", "Σ⁰_c", 2453.75, 0.34, "Σc(2455)0", "baryon_charm"),
    (None, "Sigma_c-", "Σ⁻_c", 2452.86, 0.27, "Σc(2455)-", "baryon_charm"),
    ("xi_c", "Xi_c0", "Ξ⁰_c", 2467.71, 0.30, "Ξc0", "baryon_charm"),
    (None, "Xi_c+", "Ξ⁺_c", 2468.05, 0.27, "Ξc+", "baryon_charm"),
    ("omega_c", "Omega_c0", "Ω⁰_c", 2695.2, 0.6, "Ωc0", "baryon_charm"),
    (None, "Xi_c_prime+", "Ξ′_c+", 2575.6, 0.6, "Ξc(2645)+", "baryon_charm"),
    (None, "Xi_c_prime0", "Ξ′_c⁰", 2578.2, 0.5, "Ξc(2645)0", "baryon_charm"),
    (None, "Omega_c+", "Ω⁺_c", 2698.0, 0.8, "Ωc+", "baryon_charm"),
    # --- Bottom baryons ---
    ("lambda_b", "Lambda_b0", "Λ⁰_b", 5619.60, 0.17, "Λb0", "baryon_bottom"),
    ("xi_b", "Xi_b-", "Ξ⁻_b", 5797.0, 0.6, "Ξb-", "baryon_bottom"),
    (None, "Xi_b0", "Ξ⁰_b", 5791.9, 0.5, "Ξb0", "baryon_bottom"),
    (None, "Sigma_b+", "Σ⁺_b", 5816.2, 0.5, "Σb+", "baryon_bottom"),
    (None, "Sigma_b0", "Σ⁰_b", 5815.2, 0.4, "Σb0", "baryon_bottom"),
    (None, "Sigma_b-", "Σ⁻_b", 5815.4, 0.4, "Σb-", "baryon_bottom"),
    (None, "Omega_b-", "Ω⁻_b", 6046.1, 0.6, "Ωb-", "baryon_bottom"),
    # --- Doubly charmed (published where known) ---
    ("xi_cc_plus", "Xi_cc+", "Ξcc+", 3621.2, 0.7, "Ξcc+", "baryon_double_charm"),
    (None, "Xi_cc++", "Ξcc++", 3621.55, 0.23, "Ξcc++", "baryon_double_charm"),
    ("omega_cc", "Omega_cc", "Ωcc", 3621.2, 2.0, "Ωcc", "baryon_double_charm"),
    (None, "Xi_cc+", "Ξcc+", 3621.2, 0.7, "Ξcc+", "baryon_double_charm"),
    # ccd: no stable PDG entry; use Ξcc++-like doubly-charmed reference for comparison only
    ("ccd", "ccd_baryon", "ccd (ref.)", 3621.55, 0.23, "Ξcc++ (proxy)", "baryon_double_charm"),
    # --- Light pseudoscalar mesons ---
    ("pi_plus", "pi+", "π⁺", 139.57039, 0.00018, "π+", "meson_light_ps"),
    ("pi_minus", "pi-", "π⁻", 139.57039, 0.00018, "π-", "meson_light_ps"),
    ("K_plus", "K+", "K⁺", 493.677, 0.013, "K+", "meson_light_ps"),
    ("K_minus", "K-", "K⁻", 493.677, 0.013, "K-", "meson_light_ps"),
    ("K0", "K0", "K⁰", 497.611, 0.013, "K0", "meson_light_ps"),
    (None, "K0_L", "K⁰_L", 497.614, 0.018, "K0L", "meson_light_ps"),
    (None, "K0_S", "K⁰_S", 497.611, 0.013, "K0S", "meson_light_ps"),
    ("eta", "eta", "η", 547.862, 0.018, "η", "meson_light_ps"),
    (None, "eta_prime", "η′", 957.78, 0.06, "η′(958)", "meson_light_ps"),
    # --- Light vector mesons ---
    ("rho_plus", "rho+", "ρ⁺", 775.26, 0.15, "ρ(770)+", "meson_light_vector"),
    ("rho_zero", "rho0", "ρ⁰", 775.26, 0.15, "ρ(770)0", "meson_light_vector"),
    ("omega", "omega", "ω", 782.65, 0.12, "ω(782)", "meson_light_vector"),
    ("phi", "phi", "φ", 1019.461, 0.016, "φ(1020)", "meson_light_vector"),
    (None, "K*+", "K*⁺", 891.67, 0.26, "K*(892)+", "meson_light_vector"),
    (None, "K*0", "K*⁰", 896.10, 0.06, "K*(892)0", "meson_light_vector"),
    (None, "K*-", "K*⁻", 891.67, 0.26, "K*(892)-", "meson_light_vector"),
    (None, "K*0_bar", "K*⁰", 896.10, 0.06, "K*(892)0", "meson_light_vector"),
    # --- Charmed mesons ---
    ("D_plus", "D+", "D⁺", 1869.66, 0.05, "D+", "meson_charm"),
    ("D0", "D0", "D⁰", 1864.84, 0.05, "D0", "meson_charm"),
    ("Ds_plus", "Ds+", "D⁺_s", 1968.35, 0.07, "Ds+", "meson_charm"),
    (None, "D*+", "D*⁺", 2010.26, 0.17, "D*+", "meson_charm"),
    (None, "D*0", "D*⁰", 2006.85, 0.10, "D*0", "meson_charm"),
    (None, "D*0(2S)", "D*⁰(2S)", 2400.0, 25.0, "D*0(2400)0", "meson_charm"),
    ("Jpsi", "J/psi", "J/ψ", 3096.900, 0.006, "J/ψ(3097)", "meson_charm"),
    (None, "psi2S", "ψ(2S)", 3686.097, 0.025, "ψ(3686)", "meson_charm"),
    (None, "chi_c1", "χc1", 3510.71, 0.04, "χc1(3510)", "meson_charm"),
    (None, "D_s1", "D_s1(2536)+", 2536.29, 0.20, "Ds1(2536)+", "meson_charm"),
    # --- Bottom mesons ---
    ("B_plus", "B+", "B⁺", 5279.34, 0.12, "B+", "meson_bottom"),
    ("B0", "B0", "B⁰", 5279.66, 0.12, "B0", "meson_bottom"),
    ("Bs", "Bs0", "B⁰_s", 5366.92, 0.10, "Bs0", "meson_bottom"),
    (None, "B_c+", "B⁺_c", 6274.47, 0.27, "Bc+", "meson_bottom"),
    (None, "B*+", "B*⁺", 5324.71, 0.20, "B*+", "meson_bottom"),
    (None, "B*0", "B*⁰", 5324.83, 0.18, "B*0", "meson_bottom"),
    ("Upsilon", "Upsilon", "ϒ(1S)", 9460.30, 0.26, "ϒ(1S)", "meson_bottom"),
    (None, "Upsilon2S", "ϒ(2S)", 10023.26, 0.05, "ϒ(2S)", "meson_bottom"),
    (None, "Upsilon3S", "ϒ(3S)", 10355.2, 0.1, "ϒ(3S)", "meson_bottom"),
    # --- Tetraquark / exotic (where listed in PDG) ---
    ("X3872", "X(3872)", "X(3872)", 3871.69, 0.17, "X(3872)", "tetraquark"),
    ("Zc3900", "Zc(3900)", "Zc(3900)", 3886.7, 2.0, "Zc(3900)+", "tetraquark"),
    ("Tcc", "Tcc", "Tcc", 3875.0, 2.0, "Tcc", "tetraquark"),
    (None, "Zc4020", "Zc(4020)", 4020.4, 1.8, "Zc(4020)0", "tetraquark"),
    (None, "Zc4200", "Zc(4200)", 4198.0, 13.0, "Zc(4200)0", "tetraquark"),
    (None, "X4140", "X(4140)", 4146.8, 1.4, "X(4140)", "tetraquark"),
    (None, "X4274", "X(4274)", 4273.3, 1.2, "X(4274)", "tetraquark"),
    # --- Pentaquarks ---
    ("Pc4312", "Pc(4312)+", "Pc(4312)⁺", 4311.9, 0.7, "Pc(4312)+", "pentaquark_charm"),
    ("Pc4440", "Pc(4440)+", "Pc(4440)⁺", 4440.3, 1.3, "Pc(4440)+", "pentaquark_charm"),
    ("Pc4457", "Pc(4457)+", "Pc(4457)⁺", 4457.3, 2.3, "Pc(4457)+", "pentaquark_charm"),
    (None, "Pc4380", "Pc(4380)⁺", 4380.0, 29.0, "Pc(4380)+", "pentaquark_charm"),
    # --- Additional established hadrons (fill toward ~80+) ---
    (None, "N1440", "N(1440)", 1440.0, 30.0, "N(1440)1/2", "baryon_resonance"),
    (None, "N1520", "N(1520)", 1515.0, 20.0, "N(1520)3/2", "baryon_resonance"),
    (None, "N1535", "N(1535)", 1523.0, 10.0, "N(1535)1/2", "baryon_resonance"),
    (None, "N1650", "N(1650)", 1650.0, 30.0, "N(1650)1/2", "baryon_resonance"),
    (None, "N1675", "N(1675)", 1675.0, 5.0, "N(1675)5/2", "baryon_resonance"),
    (None, "N1680", "N(1680)", 1680.0, 5.0, "N(1680)5/2", "baryon_resonance"),
    (None, "N1710", "N(1710)", 1710.0, 30.0, "N(1710)1/2", "baryon_resonance"),
    (None, "N1720", "N(1720)", 1720.0, 20.0, "N(1720)3/2", "baryon_resonance"),
    (None, "Lambda1405", "Λ(1405)", 1405.1, 0.3, "Λ(1405)", "baryon_resonance"),
    (None, "Sigma1385", "Σ(1385)", 1385.0, 5.0, "Σ(1385)", "baryon_resonance"),
    (None, "K1_1270", "a1(1260)", 1270.0, 20.0, "a1(1260)", "meson_resonance"),
    (None, "f0_980", "f0(980)", 980.0, 30.0, "f0(980)", "meson_resonance"),
    (None, "f0_1370", "f0(1370)", 1370.0, 50.0, "f0(1370)", "meson_resonance"),
    (None, "f2_1270", "f2(1270)", 1275.0, 25.0, "f2(1270)", "meson_resonance"),
    (None, "h1_1170", "h1(1170)", 1170.0, 40.0, "h1(1170)", "meson_resonance"),
]


def main() -> None:
    entries = []
    by_config_id: dict[str, dict] = {}
    by_key: dict[str, dict] = {}

    for row in ENTRIES:
        config_id, key, name, mass, err, pdg_id, category = row
        rec = {
            "config_id": config_id,
            "key": key,
            "name": name,
            "mass_MeV": mass,
            "uncertainty_MeV": err,
            "pdg_id": pdg_id,
            "category": category,
            "mass_GeV": mass / 1000.0,
        }
        entries.append(rec)
        by_key[key] = rec
        if config_id:
            by_config_id[config_id] = rec

    payload = {
        "source": "PDG 2024 Review of Particle Physics (RPP) — comparison layer only; not HQIV inputs",
        "citation": "Workman et al. (PDG), Phys. Rev. D 110, 030001 (2024)",
        "unit": "MeV",
        "count": len(entries),
        "entries": entries,
        "by_config_id": by_config_id,
        "by_key": by_key,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    OUT_JS.parent.mkdir(parents=True, exist_ok=True)
    OUT_JS.write_text(
        "/* Auto-generated — run scripts/export_hadron_published_masses.py */\n"
        "(function () {\n"
        "  if (typeof HQIVPublishedHadrons !== 'undefined') {\n"
        f"    HQIVPublishedHadrons.setPublishedMasses({json.dumps(payload)});\n"
        "  }\n})();\n",
        encoding="utf-8",
    )
    print(f"Wrote {OUT} ({len(entries)} entries, {len(by_config_id)} catalog-linked)")
    print(f"Wrote {OUT_JS}")


if __name__ == "__main__":
    main()
