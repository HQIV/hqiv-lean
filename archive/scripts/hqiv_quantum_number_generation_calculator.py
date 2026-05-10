#!/usr/bin/env python3
"""
Calculator for the narrative: lepton number → +charge → +color ramps the mass **proxy**,
while triality gives **three generations** with the **heavy (3rd) slot** tied to the **lock-in
shell** in the Lean lepton picture.

**Lean hooks (names only):**
  - `FermionContentClass` / `conservedTripleCount`: ν → 1, charged ℓ → 2, quark → 3
    (`ConservedContentMassBridge`).
  - `massScalingAnsatz k δ l m = k * l² * effCorrected δ m` — we set `k = 1` and use one δ, `m`.
  - `effCorrected` / `c_rindler_shared = γ/2` (`GlobalDetuning`).
  - Charged-lepton shells: τ at `referenceM = 4`, μ at `81`, e at `16336` (`LeptonGenerationLockin`);
    resonance factors = ratios of detuned surfaces (`ChargedLeptonResonance`).

**What this shows (illustration, not a proof):**
  1. At fixed `(δ, m)`, increasing “closed quantum numbers” (l = 1,2,3) **multiplies** the proxy by
     `l²` — same `eff`, stiffer effective scale for quarks than for ν.
  2. **Third generation (heavy)** in `Fin 3` is the τ slot: **smallest ℕ shell** among e,μ,τ in the
     current table — lock-in aligned with `referenceM`. Lighter generations sit at **larger** `m`
     (outer shells in that ℕ ordering). “Most relaxed” is read here as **settled at the anchor**
     after the resonance ladder (heavy = reference surface), not “smallest mass.”

**Not claimed:** unique ground state of a full Mexican-hat functional in continuum; no PDG fit.

Run from repo root:
  python3 archive/scripts/hqiv_quantum_number_generation_calculator.py
"""

from __future__ import annotations

import math
from typing import List, Tuple

GAMMA_HQIV = 2.0 / 5.0
C_RINDLER = GAMMA_HQIV / 2.0

REFERENCE_M = 4  # Lean referenceM / lepton τ shell
M_MU = 81
M_E = 16336


def eff_corrected(delta: float, m: int) -> float:
    m = int(m)
    return (m + 1) * (m + 2) / (1.0 + C_RINDLER * m + delta)


def delta_auxiliary(phi: float, t: float, beta_cum: float, delta_global: float = 0.0) -> float:
    return delta_global + beta_cum * phi * t


def mass_scaling_proxy(l: int, delta: float, m: int, k: float = 1.0) -> float:
    """`massScalingAnsatz` with k, l, δ, m (ℝ)."""
    return k * float(l * l) * eff_corrected(delta, m)


def geometric_step(m_from: int, m_to: int, delta: float) -> float:
    return eff_corrected(delta, m_from) / eff_corrected(delta, m_to)


def sector_table(delta: float, shells: List[int]) -> None:
    sectors: Tuple[Tuple[str, int], ...] = (
        ("ν  (lepton # only, l=1)", 1),
        ("ℓ  (+ electric charge, l=2)", 2),
        ("q  (+ colour, l=3)", 3),
    )
    print(f"δ = {delta:.6g}  (same for all rows)\n")
    hdr = f"{'sector':<32}"
    for m in shells:
        hdr += f"  m={m:<5}"
    print(hdr)
    print("-" * len(hdr))
    for name, l in sectors:
        row = f"{name:<32}"
        for m in shells:
            val = mass_scaling_proxy(l, delta, m)
            row += f"  {val:10.4f}"
        print(row)
    print("\nInterpretation: at fixed shell, **l²** ordering is ν < ℓ < q (same eff, larger l²).")


def generation_lepton_table(delta: float) -> None:
    """
    Resonance-style mass **ratios** from τ anchor (gen 2 = heavy = 1.0 scale divisor).
    Matches Lean pattern: m_τ / (k_τμ * k_μe) for electron, etc.
    """
    k_tm = geometric_step(M_MU, REFERENCE_M, delta)
    k_me = geometric_step(M_E, M_MU, delta)
    # Heavy generation (3rd family, τ): normalized mass scale 1
    m_scale_tau = 1.0
    m_scale_mu = 1.0 / k_tm
    m_scale_e = 1.0 / (k_tm * k_me)
    print("Charged-lepton **generation** factors (τ = heavy gen @ m=4, proxy normalized to 1.0):")
    print(f"  k_τμ = eff(μ)/eff(τ) = geometric_step({M_MU},{REFERENCE_M}) = {k_tm:.6f}")
    print(f"  k_μe = eff(e)/eff(μ) = geometric_step({M_E},{M_MU}) = {k_me:.6f}")
    print()
    print(f"  gen 2 (τ, 3rd family):  relative scale = {m_scale_tau:.6f}  (shell m = {REFERENCE_M})")
    print(f"  gen 1 (μ):               relative scale = {m_scale_mu:.6f}  (shell m = {M_MU})")
    print(f"  gen 0 (e):               relative scale = {m_scale_e:.6e}  (shell m = {M_E})")
    print()
    print(
        "Narrative: **highest** relative scale at the **heavy** generation (lock-in shell); "
        "lighter generations are **smaller** mass factors at **larger** ℕ shells in this table."
    )


def main() -> None:
    print("HQIV quantum-number / generation calculator (archive illustration)\n")
    print(f"γ = {GAMMA_HQIV},  c_rindler = γ/2 = {C_RINDLER}\n")

    # Readable δ so eff is O(1)–O(10)
    phi, t, beta = 1.0, 1.0, 0.05
    delta = delta_auxiliary(phi, t, beta, 0.0)
    shells = [0, 1, REFERENCE_M, 8]
    sector_table(delta, shells)
    print()
    generation_lepton_table(delta)

    print()
    print(
        "Colour / charge are **not** separate δ here — only the **l²** factor distinguishes sectors. "
        "A richer model would tie δ or shell to gauge closure; this script is the minimal Lean-aligned "
        "proxy (`massScalingAnsatz` + detuned `eff`)."
    )


if __name__ == "__main__":
    main()
