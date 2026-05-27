#!/usr/bin/env python3
"""
Map HQIV Fano coupling solve → Standard Model parameter dashboard (~26 inputs).

The 7×7 solver fixes c_v on the Fano plane; each vertex carries an O–Maxwell readout
  1/α_v = 42·(1 + c_v·(α/5)·ln(φ(m_v)+1))
with exactly one CODATA brace on the EM axis (continuous ξ_G or discrete Gauss→EW ratio).

This script does **not** claim all 26 SM numbers come from that linear system alone.
It classifies each PDG-style parameter by HQIV tier:

  A  fixed by lattice axioms (α, γ, 1/α_GUT)
  B  predicted from solved c_v + sector shells (7 effective couplings)
  C  brace / σ(ξ) geometry (α_EM after Gauss→EW imprint)
  D  triality / monogamy split (g_SU2, g_U1 — not solved, imported from Lean)
  E  mass ladder / outer closure (fermion & boson masses — separate modules)
  W  witness literals in Lean (comparison only)
  O  open (CKM, θ_QCD, …)

Run:
  python3 scripts/hqiv_sm_constants_explorer.py
  python3 scripts/hqiv_sm_constants_explorer.py --continuous-xi --json
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(_ROOT / "scripts"))

import hqiv_coupling_linear_system as hcls  # noqa: E402

# PDG / CODATA centrals for comparison (GeV where noted; dimensionless otherwise)
PDG = {
    "inv_alpha_em": hcls.CODATA_INV_ALPHA,
    "alpha_s_mz": 0.1180,
    "sin2theta_w": 0.23122,
    "G_F_GeV2": 1.1663787e-5,
    "m_W_GeV": 80.379,
    "m_Z_GeV": 91.1876,
    "m_H_GeV": 125.10,
    "m_e_MeV": 0.51099895,
    "m_mu_MeV": 105.6583755,
    "m_tau_MeV": 1776.86,
    "m_u_MeV": 2.16,
    "m_d_MeV": 4.67,
    "m_s_MeV": 93.4,
    "m_c_MeV": 1270,
    "m_b_MeV": 4180,
    "m_t_GeV": 172.57,
    "lambda_CKM": 0.22650,
    "A_CKM": 0.790,
    "rho_bar_CKM": 0.141,
    "eta_bar_CKM": 0.357,
    "theta12_PMNS_deg": 33.44,
    "theta23_PMNS_deg": 49.0,
    "theta13_PMNS_deg": 8.57,
    "delta_CP_PMNS_deg": 197.0,
    "dm21_sq_eV2": 7.53e-5,
    "dm31_sq_eV2": 2.453e-3,
}

# Lean outer-closure witnesses (GeV) — DerivedGaugeAndLeptonSector closed forms
LEAN_BOSON_W_GeV = 392 / 5
LEAN_BOSON_Z_GeV = 2744 / 25
LEAN_BOSON_H_GeV = 588 / 5

Tier = Literal["A", "B", "C", "D", "E", "W", "O"]


@dataclass(frozen=True)
class SMConstantSlot:
    id: str
    name: str
    tier: Tier
    unit: str
    hqiv_source: str
    predicted: float | None
    pdg: float | None
    note: str


def alpha_from_inv(inv_a: float) -> float:
    return 1.0 / inv_a if inv_a != 0 else float("nan")


def sin2_from_g(g2: float, g1: float) -> float:
    """Weinberg angle proxy: g1²/(g1²+g2²) with HQIV g_SU2=g2, g_U1=g1."""
    return (g1 * g1) / (g1 * g1 + g2 * g2)


def sin2_from_report(report: hcls.CoherenceReport) -> float | None:
    if report.mixing_geometry is None:
        return None
    return report.mixing_geometry.sin2_solved_c3_over_c0


def g_f_from_alpha_mw_sin2(alpha_em: float, m_w_gev: float, sin2: float) -> float:
    """Fermi constant [GeV⁻²] from Forces.lean: G_F = π α / (√2 M_W² sin²θ_W)."""
    return math.pi * alpha_em / (math.sqrt(2) * m_w_gev * m_w_gev * sin2)


def build_dashboard(
    report: hcls.CoherenceReport,
    *,
    use_lean_bosons: bool = True,
) -> list[SMConstantSlot]:
    c = report.c
    shells = report.shells
    g2 = report.factor_g_su2
    g1 = report.factor_g_u1
    sin2_proxy = sin2_from_g(g2, g1)

    inv_by_vertex = {
        v: hcls.one_over_alpha_eff(shells[v], float(c[v])) for v in range(7)
    }
    inv_braced = None
    if report.continuous_xi is not None:
        inv_braced = report.continuous_xi.inv_alpha_braced_at_xi_g
    else:
        inv_braced = hcls.shell_brace_inv_alpha(float(c[0]))

    alpha_em = alpha_from_inv(inv_braced)
    m_w = LEAN_BOSON_W_GeV if use_lean_bosons else PDG["m_W_GeV"]
    m_z = LEAN_BOSON_Z_GeV if use_lean_bosons else PDG["m_Z_GeV"]
    m_h = LEAN_BOSON_H_GeV if use_lean_bosons else PDG["m_H_GeV"]
    g_f = g_f_from_alpha_mw_sin2(alpha_em, m_w, sin2_proxy)

    vertex_roles = [
        (0, "α_EM (braced)", inv_braced),
        (1, "up g0 coupling", inv_by_vertex[1]),
        (2, "up g1 coupling", inv_by_vertex[2]),
        (3, "up g2 / weak slot", inv_by_vertex[3]),
        (4, "down g0 / strong slot", inv_by_vertex[4]),
        (5, "down g1 coupling", inv_by_vertex[5]),
        (6, "Higgs / down g2 slot", inv_by_vertex[6]),
    ]

    slots: list[SMConstantSlot] = []

    # --- Tier A: axioms ---
    slots.extend(
        [
            SMConstantSlot(
                "alpha_lattice",
                "α (curvature imprint)",
                "A",
                "—",
                "OctonionicLightCone.alpha",
                hcls.ALPHA,
                None,
                "Not α_EM; fixes O–Maxwell log slope",
            ),
            SMConstantSlot(
                "gamma_lattice",
                "γ (monogamy)",
                "A",
                "—",
                "gamma_HQIV = 1−α",
                hcls.GAMMA,
                None,
                "Feeds Rindler detuning γ/2",
            ),
            SMConstantSlot(
                "inv_alpha_gut",
                "1/α_GUT",
                "A",
                "—",
                "6×7 octonion / cubeDirections",
                hcls.INV_ALPHA_GUT,
                None,
                "Bare O–Maxwell prefactor 42",
            ),
        ]
    )

    # --- Tier C: EM fine structure (the one scale setter) ---
    slots.append(
        SMConstantSlot(
            "inv_alpha_em",
            "1/α_EM(M_Z)",
            "C",
            "—",
            "continuous brace σ(ξ_G)/σ(ξ_EW) or discrete shell brace",
            inv_braced,
            PDG["inv_alpha_em"],
            f"c₀≈{c[0]:.4f}; ξ_G={report.continuous_xi.xi_g:.4f}"
            if report.continuous_xi
            else f"c₀≈{c[0]:.4f}",
        )
    )
    slots.append(
        SMConstantSlot(
            "alpha_em",
            "α_EM(M_Z)",
            "C",
            "—",
            "1 / braced inverse",
            alpha_em,
            1.0 / PDG["inv_alpha_em"],
            "Only parameter pinned to CODATA in solve",
        )
    )

    # --- Tier B: seven Fano effective couplings (same c_v, not all compared to α) ---
    for v, label, inv_a in vertex_roles:
        slots.append(
            SMConstantSlot(
                f"inv_alpha_v{v}",
                f"1/α_eff @ {label}",
                "B",
                "—",
                f"vertex {v}, m={shells[v]}, c_v={c[v]:.4f}",
                inv_a,
                None,
                "Structural; not fitted to PDG α",
            )
        )

    # --- Tier D: gauge couplings from triality (not from linear solve) ---
    slots.extend(
        [
            SMConstantSlot(
                "g_SU2",
                "g_SU2 (triality)",
                "D",
                "—",
                "DerivedGaugeAndLeptonSector / triality 1/3",
                g2,
                None,
                "Hard-coded in coherence report, not solved",
            ),
            SMConstantSlot(
                "g_U1",
                "g_U1 (triality)",
                "D",
                "—",
                "γ/3 monogamy split",
                g1,
                None,
                "Hard-coded in coherence report",
            ),
            SMConstantSlot(
                "sin2theta_w_proxy",
                "sin²θ_W (g₁²/(g₁²+g₂²) proxy)",
                "D",
                "—",
                "Forces.G_F_from_beta chain",
                sin2_proxy,
                PDG["sin2theta_w"],
                "Triality bare; mixing rows tighten c₃/c₀",
            ),
            SMConstantSlot(
                "sin2theta_w_geometric",
                "sin²θ_W (Fano weak/EM row)",
                "B",
                "—",
                "sin2_theta_w_geometric + mixing solve",
                sin2_from_report(report),
                PDG["sin2theta_w"],
                "From extended linear system when --mixing-rows",
            ),
            SMConstantSlot(
                "alpha_s_geometric",
                "α_s(M_Z) φ-slope geometric",
                "B",
                "—",
                "alpha_s_geometric(ξ₄, ξ_EW)",
                report.mixing_geometry.alpha_s_geometric
                if report.mixing_geometry
                else hcls.alpha_s_geometric(
                    report.holonomy_xi_vertices[4]
                    if report.holonomy_xi_vertices
                    else float(hcls.XI_EW - 2)
                ),
                PDG["alpha_s_mz"],
                "Strong slot row when --mixing-rows",
            ),
            SMConstantSlot(
                "alpha_s_proxy_v4",
                "α_s(M_Z) proxy 1/α_eff(v4)",
                "B",
                "—",
                "legacy inverse-coupling mis-map",
                alpha_from_inv(inv_by_vertex[4]),
                PDG["alpha_s_mz"],
                "Superseded by alpha_s_geometric slot",
            ),
        ]
    )

    # --- Tier E: masses (outside 7×7 solve; Lean ladders) ---
    mass_slots = [
        ("m_W", "M_W", LEAN_BOSON_W_GeV, PDG["m_W_GeV"], "outerClosureScale × g_SU2 × vev"),
        ("m_Z", "M_Z", LEAN_BOSON_Z_GeV, PDG["m_Z_GeV"], "(g_SU2+g_U1)×vev; no PDG mixing"),
        ("m_H", "m_H", LEAN_BOSON_H_GeV, PDG["m_H_GeV"], "2× scalar vev lift"),
        ("m_e", "m_e", None, PDG["m_e_MeV"] / 1000, "m_tau_Pl / resonanceProduct"),
        ("m_mu", "m_μ", None, PDG["m_mu_MeV"] / 1000, "resonance ladder"),
        ("m_tau", "m_τ", None, PDG["m_tau_MeV"] / 1000, "τ anchor / resonance"),
        ("m_u", "m_u", None, PDG["m_u_MeV"] / 1000, "quark shell tables (witness)"),
        ("m_d", "m_d", None, PDG["m_d_MeV"] / 1000, "quark shell tables"),
        ("m_s", "m_s", None, PDG["m_s_MeV"] / 1000, "quark shell tables"),
        ("m_c", "m_c", None, PDG["m_c_MeV"] / 1000, "quark shell tables"),
        ("m_b", "m_b", None, PDG["m_b_MeV"] / 1000, "quark shell tables"),
        ("m_t", "m_t", None, PDG["m_t_GeV"], "lock-in shell / meta-horizon"),
    ]
    for sid, name, pred, pdg, src in mass_slots:
        slots.append(
            SMConstantSlot(
                sid,
                name,
                "E",
                "GeV",
                src,
                pred,
                pdg,
                "Not output of hqiv_coupling_linear_system.py",
            )
        )

    slots.append(
        SMConstantSlot(
            "G_F",
            "G_F (from α, M_W, sin² proxy)",
            "E",
            "GeV⁻²",
            "Forces.G_F_from_beta",
            g_f,
            PDG["G_F_GeV2"],
            "Uses Tier C α + Tier D sin² + Tier E M_W",
        )
    )

    # --- Tier W: Lean witnesses (not from solve) ---
    slots.append(
        SMConstantSlot(
            "sin2theta_w_witness",
            "sin²θ_W (Lean witness)",
            "W",
            "—",
            "SM_GR_Unification.sin2thetaW_at_MZ",
            0.23122,
            PDG["sin2theta_w"],
            "Decimal witness, not derived from c_v",
        )
    )
    slots.append(
        SMConstantSlot(
            "alpha_s_witness",
            "α_s (Lean witness)",
            "W",
            "—",
            "SM_GR_Unification.alpha_s_at_MZ",
            0.1180,
            PDG["alpha_s_mz"],
            "Decimal witness",
        )
    )

    # --- Tier O: mixing / CP ---
    open_slots = [
        ("CKM_lambda", "CKM λ", PDG["lambda_CKM"]),
        ("CKM_A", "CKM A", PDG["A_CKM"]),
        ("CKM_rho", "CKM ρ̄", PDG["rho_bar_CKM"]),
        ("CKM_eta", "CKM η̄", PDG["eta_bar_CKM"]),
        ("theta12_PMNS", "PMNS θ₁₂", PDG["theta12_PMNS_deg"]),
        ("theta23_PMNS", "PMNS θ₂₃", PDG["theta23_PMNS_deg"]),
        ("theta13_PMNS", "PMNS θ₁₃", PDG["theta13_PMNS_deg"]),
        ("delta_CP_PMNS", "PMNS δ_CP", PDG["delta_CP_PMNS_deg"]),
        ("dm21_sq", "Δm²₂₁", PDG["dm21_sq_eV2"]),
        ("dm31_sq", "Δm³₁", PDG["dm31_sq_eV2"]),
        ("theta_QCD", "θ_QCD", 0.0),
    ]
    for sid, name, pdg in open_slots:
        slots.append(
            SMConstantSlot(
                sid,
                name,
                "O",
                "varies",
                "Fano axis angles / PMNS scaffold (partial Lean)",
                None,
                pdg,
                "Not in coupling linear system",
            )
        )

    return slots


def print_dashboard(slots: list[SMConstantSlot], report: hcls.CoherenceReport) -> None:
    print("HQIV Standard Model constants explorer")
    print("=" * 78)
    print(
        f"Coupling solve: ||Ac-b||={report.residual:.4e}  "
        f"setter={report.scale_setter_used}  shells={report.shells}"
    )
    if report.holonomy_xi_vertices:
        print(f"  ξ_v = {[round(x, 3) for x in report.holonomy_xi_vertices]}")
    print()
    print("Tier key: A=axiom  B=Fano 1/α_v  C=CODATA brace  D=triality  E=mass ladder  W=witness  O=open")
    print()

    by_tier: dict[Tier, list[SMConstantSlot]] = {}
    for s in slots:
        by_tier.setdefault(s.tier, []).append(s)

    for tier in ("A", "B", "C", "D", "E", "W", "O"):
        group = by_tier.get(tier, [])
        if not group:
            continue
        print(f"--- Tier {tier} ({len(group)} slots) ---")
        for s in group:
            pred = "—" if s.predicted is None else f"{s.predicted:.6g}"
            pdg = "—" if s.pdg is None else f"{s.pdg:.6g}"
            rel = ""
            if s.predicted is not None and s.pdg is not None and s.pdg != 0:
                rel = f"  rel_err={(s.predicted - s.pdg) / abs(s.pdg):+.2%}"
            print(f"  {s.name:32s}  pred={pred:>12s}  PDG={pdg:>12s}{rel}")
            print(f"      {s.hqiv_source}")
            if s.note:
                print(f"      → {s.note}")
        print()

    n_b = len(by_tier.get("B", []))
    n_c = len(by_tier.get("C", []))
    n_e = len(by_tier.get("E", []))
    n_o = len(by_tier.get("O", []))
    print("Summary (how the ~26 SM inputs split across the script)")
    print(f"  • Coupling script directly constrains: 1 CODATA scale (Tier C) + {n_b} vertex 1/α_eff (Tier B)")
    print(f"  • Triality gives 2–3 gauge slots (Tier D); masses ({n_e}) need mass/closure modules (Tier E)")
    print(f"  • Mixing & CP ({n_o}) remain open until Fano/axis-angle derivation lands (Tier O)")
    print()
    print("To close the gap:")
    print("  1. Map v3,v4,v6 → sin²θ_W, α_s via proved Fano→gauge (not 1/α_eff identity)")
    print("  2. Feed Ω_k(ξ) row + outerClosureScale for M_W,M_Z,m_H without extra GeV anchors")
    print("  3. Replace quark GeV tables with resonanceProduct at continuous ξ_v")


def main() -> None:
    p = argparse.ArgumentParser(description="HQIV SM constants dashboard")
    p.add_argument("--continuous-xi", action="store_true")
    p.add_argument("--mixing-rows", action="store_true")
    p.add_argument("--mixing-weight", type=float, default=10.0)
    p.add_argument("--json", action="store_true")
    p.add_argument("--shell-chart", default="sector")
    p.add_argument("--m-global", type=int, default=hcls.REFERENCE_M)
    args = p.parse_args()

    report = hcls.run_coherence(
        args.shell_chart,
        args.m_global,
        use_brace_instead_of_setter=True,
        continuous_xi=args.continuous_xi,
        density_holonomy=args.continuous_xi,
        holonomy_k_mode="sigma",
        mixing_rows=getattr(args, "mixing_rows", False),
        mixing_weight=getattr(args, "mixing_weight", 10.0),
        include_two_objective=False,
    )
    slots = build_dashboard(report)

    if args.json:
        out = {
            "coherence": asdict(report),
            "sm_constants": [asdict(s) for s in slots],
        }
        print(json.dumps(out, indent=2, default=str))
    else:
        print_dashboard(slots, report)


if __name__ == "__main__":
    main()
