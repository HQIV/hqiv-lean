#!/usr/bin/env python3
"""
ARCHIVE — phenomenological PDG shell witness (not first-principles HQIV proof).

This script mirrors **Lean modules that still live under `Hqiv/Physics/` for build wiring**
(`LeptonGenerationLockin`, `ChargedLeptonResonance`, `QuarkMetaResonance`) but whose **explicit
ℕ shell numerals** are PDG-alignment / placeholder tables, **not** theorems from the discrete
null-lattice axiom. See `archive/abandoned/MASS_LADDER_PHENOMENOLOGY.md`.

For **geometry-only** checks (zeta, eff, Fano residue), use modules like `OctonionicZeta` / proofs
in-repo — not this table.

Run from repo root:
  python3 archive/scripts/check_mass_ladder_pdg_witness.py
  python3 archive/scripts/check_mass_ladder_pdg_witness.py --show-fano-lines

Former path: `scripts/check_fano_mass_coherence.py` (removed from active `scripts/`).
"""

from __future__ import annotations

import argparse
import math
import sys
from dataclasses import dataclass
from typing import List, Tuple

# --- HQIV constants (match Lean `gamma_eq_2_5`, `c_rindler_shared`) ---
GAMMA_HQIV = 2.0 / 5.0
C_RINDLER = GAMMA_HQIV / 2.0  # 1/5

# --- Shell indices (Lean: LeptonGenerationLockin, QuarkMetaResonance) ---
M_TAU_SHELL = 4  # referenceM / leptonHeavyVertexShell
M_MU_SHELL = 81
M_E_SHELL = 16336

M_QUARK_UP_TOP = 31382
M_QUARK_UP_CHARM = 233
M_QUARK_UP_LIGHT = 0

M_QUARK_DOWN_BOTTOM = 5329
M_QUARK_DOWN_STRANGE = 123
M_QUARK_DOWN_LIGHT = 7

# Anchors (GeV where noted; τ in GeV via 1776.86 MeV)
M_TAU_GEV = 1776.86e-3
M_TOP_GEV = 172.57
M_BOTTOM_GEV = 4.18


def shell_surface(m: int) -> float:
    return float(m + 1) * float(m + 2)


def rindler_detuning_shared(x: float) -> float:
    return 1.0 + C_RINDLER * x


def detuned_shell_surface(m: int) -> float:
    return shell_surface(m) / rindler_detuning_shared(float(m))


def geometric_resonance_step(m_from: int, m_to: int) -> float:
    """Lean `geometricResonanceStep m_from m_to` = detuned(from) / detuned(to)."""
    return detuned_shell_surface(m_from) / detuned_shell_surface(m_to)


def fano_prime_line(m: int) -> int:
    """One-based Fano line label 1..7 matching shell residue (Lean `fano_prime` story)."""
    return (m % 7) + 1


def rel_err(model: float, ref: float) -> float:
    if ref == 0.0:
        return math.inf if model != 0.0 else 0.0
    return abs(model - ref) / abs(ref)


@dataclass
class Row:
    name: str
    shell_m: int
    model_mass_gev: float
    ref_mass_gev: float
    note: str = ""


def lepton_masses_from_tau_anchor() -> Tuple[float, float, float, float, float]:
    k_tau_mu = geometric_resonance_step(M_MU_SHELL, M_TAU_SHELL)
    k_mu_e = geometric_resonance_step(M_E_SHELL, M_MU_SHELL)
    m_mu = M_TAU_GEV / k_tau_mu
    m_e = m_mu / k_mu_e
    return k_tau_mu, k_mu_e, M_TAU_GEV, m_mu, m_e


def up_quark_masses() -> Tuple[float, float, float]:
    k_tc = geometric_resonance_step(M_QUARK_UP_TOP, M_QUARK_UP_CHARM)
    k_cu = geometric_resonance_step(M_QUARK_UP_CHARM, M_QUARK_UP_LIGHT)
    m_charm = M_TOP_GEV / k_tc
    m_up = m_charm / k_cu
    return m_charm, m_up, k_tc * k_cu


def down_quark_masses() -> Tuple[float, float, float]:
    k_bs = geometric_resonance_step(M_QUARK_DOWN_BOTTOM, M_QUARK_DOWN_STRANGE)
    k_sd = geometric_resonance_step(M_QUARK_DOWN_STRANGE, M_QUARK_DOWN_LIGHT)
    m_strange = M_BOTTOM_GEV / k_bs
    m_down = m_strange / k_sd
    return m_strange, m_down, k_bs * k_sd


LEGACY_K_TAU_MU_TARGET = 17.0
LEGACY_K_MU_E_TARGET = 207.0


def collect_rows(tol: float, strict_leptons: bool) -> Tuple[List[Row], List[str], List[str]]:
    failures: List[str] = []
    warnings: List[str] = []
    rows: List[Row] = []

    k_tm, k_me, m_tau, m_mu, m_e = lepton_masses_from_tau_anchor()
    rows.append(Row("τ (anchor)", M_TAU_SHELL, m_tau, 1.77686, "PDG mass as Lean anchor"))
    rows.append(Row("μ (from ladder)", M_MU_SHELL, m_mu, 0.1056583755, "PDG 2024"))
    rows.append(Row("e (from ladder)", M_E_SHELL, m_e, 0.0005109989461, "PDG 2024"))

    m_charm, m_up, _ = up_quark_masses()
    m_strange, m_down, _ = down_quark_masses()
    rows.append(Row("top (anchor)", M_QUARK_UP_TOP, M_TOP_GEV, M_TOP_GEV, "Lean anchor"))
    rows.append(Row("charm (ladder)", M_QUARK_UP_CHARM, m_charm, 1.27, "Lean `light_quark` ref"))
    rows.append(Row("up (ladder)", M_QUARK_UP_LIGHT, m_up, 0.0022, "Lean `light_quark` ref"))
    rows.append(Row("bottom (anchor)", M_QUARK_DOWN_BOTTOM, M_BOTTOM_GEV, M_BOTTOM_GEV, "Lean anchor"))
    rows.append(Row("strange (ladder)", M_QUARK_DOWN_STRANGE, m_strange, 0.095, "Lean `light_quark` ref"))
    rows.append(Row("down (ladder)", M_QUARK_DOWN_LIGHT, m_down, 0.0047, "Lean `light_quark` ref"))

    rows.append(
        Row(
            "(diag) k_τμ",
            -1,
            k_tm,
            LEGACY_K_TAU_MU_TARGET,
            "vs legacy 17 ratio (Lean δ_rindler_tau_muon)",
        )
    )
    rows.append(
        Row(
            "(diag) k_μe",
            -1,
            k_me,
            LEGACY_K_MU_E_TARGET,
            "vs legacy 207 ratio (Lean δ_rindler_muon_e)",
        )
    )

    quark_names = {
        "charm (ladder)",
        "up (ladder)",
        "strange (ladder)",
        "down (ladder)",
    }
    lepton_pdg_names = {"μ (from ladder)", "e (from ladder)"}

    for r in rows:
        if r.shell_m < 0:
            continue
        err = rel_err(r.model_mass_gev, r.ref_mass_gev)
        if r.name in ("τ (anchor)", "top (anchor)", "bottom (anchor)"):
            continue
        if r.name in quark_names and err > tol:
            failures.append(f"{r.name}: rel_err={err:.4g} (tol={tol}) model={r.model_mass_gev} ref={r.ref_mass_gev}")
        if r.name in lepton_pdg_names:
            if err > tol:
                msg = f"{r.name}: rel_err={err:.4g} vs PDG — placeholder shells {M_MU_SHELL}/{M_E_SHELL} in Lean"
                warnings.append(msg)
                if strict_leptons:
                    failures.append(msg)

    return rows, failures, warnings


def mass_scaling_ansatz_ratios() -> None:
    m = M_TAU_SHELL
    eff = detuned_shell_surface(m)
    for l, label in [(1, "ν sector l=1"), (2, "charged ℓ l=2"), (3, "quark l=3")]:
        print(f"  {label}: l²·eff(m={m}) = {l * l * eff:.6g}  (eff={eff:.6g})")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--tol", type=float, default=1.0 / 500.0)
    p.add_argument("--strict-leptons", action="store_true")
    p.add_argument("--show-fano-lines", action="store_true")
    args = p.parse_args()

    rows, failures, warnings = collect_rows(args.tol, args.strict_leptons)

    print("[ARCHIVE] PDG-tuned shell table witness (not axiom output)")
    print("=" * 60)
    print(f"γ_HQIV = {GAMMA_HQIV}, c_rindler = γ/2 = {C_RINDLER}")
    print(f"relative tolerance = {args.tol} (~{100 * args.tol:.3f}%)")
    print()

    print(f"{'particle':<22} {'shell m':>8} {'fano line':>10} {'model (GeV)':>14} {'ref (GeV)':>12} {'rel err':>10}")
    print("-" * 80)
    for r in rows:
        if r.shell_m < 0:
            fp, sm = "—", "—"
        else:
            fp = str(fano_prime_line(r.shell_m))
            sm = str(r.shell_m)
        if r.shell_m >= 0:
            err = rel_err(r.model_mass_gev, r.ref_mass_gev)
            err_s = f"{err * 100:.3f}%"
        else:
            err = rel_err(r.model_mass_gev, r.ref_mass_gev)
            err_s = f"{err * 100:.3f}% (vs target)"
        print(
            f"{r.name:<22} {sm:>8} {fp:>10} {r.model_mass_gev:>14.6g} {r.ref_mass_gev:>12.6g} {err_s:>10}"
        )

    print()
    print("massScalingAnsatz-style l² weight at fixed shell (illustration):")
    mass_scaling_ansatz_ratios()

    if args.show_fano_lines:
        print()
        print("Sample: Fano line (m % 7) + 1 for ladder shells")
        for m in [
            M_TAU_SHELL,
            M_MU_SHELL,
            M_E_SHELL,
            M_QUARK_UP_TOP,
            M_QUARK_UP_CHARM,
            M_QUARK_UP_LIGHT,
            M_QUARK_DOWN_BOTTOM,
            M_QUARK_DOWN_STRANGE,
            M_QUARK_DOWN_LIGHT,
        ]:
            print(f"  m={m:6d}  →  fano line {fano_prime_line(m)}")

    print()
    if warnings:
        print("WARN:")
        for w in warnings:
            print(f"  - {w}")
        print()
    if failures:
        print("FAIL (outside tolerance):")
        for f in failures:
            print(f"  - {f}")
        sys.exit(1)
    print("PASS (within script tolerance for quark rows).")
    print()
    print(
        "Fano lines 1–7 = shell residue mod 7; generation split = triality / resonance products "
        "(separate from this PDG shell table)."
    )


if __name__ == "__main__":
    main()
