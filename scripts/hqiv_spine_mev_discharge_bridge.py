#!/usr/bin/env python3
"""
Bridge HqivSpine dimensionless readouts → TUFT MeV discharge (comparison layer).

Two layers (do not conflate):

1. **Spine (Lean `HqivSpine.Physics.*`)** — proved structure on the lock-in now slice:
   `massUnit · generationResonanceMassFactor(n)` (resonance descent from heavy hopf anchor),
   Hopf-weighted `E_bind`, neutrino absolute mass = charged anchor `/140` via carrier monogamy.
   Dimensionless only; no electroweak vev literal in the spine modules.

2. **MeV discharge (legacy `Hqiv.*` + Python TUFT mirror)** — attaches physical units via
   witness anchors that are *quarantined comparison inputs*, not spine axioms:
   • hadronic ground — proton lock-in 938.272 MeV via `proton/τ` pin at ξ_lock
   • charged leptons — `T → vev → √(2π)·v·κ₆ · geometric_scalar · T8` at ξ_lock
   • quarks — vev-pinned τ/top/bottom + `QuarkMetaResonance` ladder
   • neutrino MeV — outer T8+T10 Casimir dressing (not spine `m_ℓ/140` MeV map)

**Anti-pattern:** `MeV = spine_dim × (938.272 / 20)` — that mis-identifies Beltrami labels
with MeV; legacy TUFT labels this the "shell quotient" path (~842× off on e).

Run:
  python3 scripts/hqiv_spine_mev_discharge_bridge.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Literal

import hqiv_tuft_mass_spectrum_pdg_eval as tmse
import hqiv_tuft_quark_vev as tqv

try:
    import hqiv_tuft_neutrino_bridge as nu_bridge
except ImportError:
    nu_bridge = None  # type: ignore[assignment,misc]

# --- spine pins (match Lean ClosureAction / MassLadder / NowSliceFromLattice) ---
REFERENCE_M = tmse.REFERENCE_M
XI_LOCKIN = tmse.XI_LOCKIN
MASS_UNIT_LOCKIN = 5.0
PROTON_BELTRAMI = 4
PROTON_MEV = tmse.PROTON_MEV
ALPHA = 3.0 / 5.0
GAMMA = 2.0 / 5.0
INV_ALPHA_GUT = 42.0
NEUTRINO_SUPPRESSION = GAMMA / (7 * 8)  # carrier monogamy γ/(imaginaryDim·carrierMultiplicity) = 1/140

# Lean `GenerationResonanceLadder` lock-in factors (massUnit=5 readouts in parentheses)
GENERATION_MASS_FACTOR: dict[int, float] = {
    1: 759696.0 / 784700.0,  # e readout ≈ 4.84 @ massUnit=5
    2: 304.0 / 175.0,        # μ readout ≈ 8.69
    3: 4.0,                  # τ readout 20
}

# Legacy resonance ratios (proved in GenerationResonanceLadder)
RESONANCE_MU_OVER_E = 4484.0 / 2499.0
RESONANCE_TAU_OVER_MU = 175.0 / 76.0

Generation = Literal["electron", "muon", "tau"]
WINDING: dict[Generation, int] = {"electron": 1, "muon": 2, "tau": 3}
GENERATIONS: tuple[Generation, ...] = ("electron", "muon", "tau")


def spine_lepton_readout(winding: int, mass_unit: float = MASS_UNIT_LOCKIN) -> float:
    return mass_unit * GENERATION_MASS_FACTOR[winding]


def spine_quark_readout(winding: int, mass_unit: float = MASS_UNIT_LOCKIN) -> float:
    return mass_unit * 9.0 * GENERATION_MASS_FACTOR[winding] / 4.0


def spine_neutrino_readout(winding: int, mass_unit: float = MASS_UNIT_LOCKIN) -> float:
    return mass_unit * GENERATION_MASS_FACTOR[winding] / 4.0


def spine_neutrino_absolute(winding: int, mass_unit: float = MASS_UNIT_LOCKIN) -> float:
    return spine_lepton_readout(winding, mass_unit) / 140.0


def spine_proton_readout(mass_unit: float = MASS_UNIT_LOCKIN) -> float:
    return mass_unit * PROTON_BELTRAMI


def mis_map_proton_only_mev(spine_dim: float) -> float:
    """Diagnostic only — wrong calibration used in early spine PDG script."""
    return spine_dim * (PROTON_MEV / spine_proton_readout())


@dataclass(frozen=True)
class DischargeLeptons:
    tau_mev: float
    mu_mev: float
    e_mev: float
    source: str = "leptonMassSpectrum_at_xi_from_vev_T8_MeV"


@dataclass(frozen=True)
class DischargeQuarks:
    t_mev: float
    c_mev: float
    u_mev: float
    b_mev: float
    s_mev: float
    d_mev: float


@dataclass(frozen=True)
class DischargeNeutrinos:
    m1_mev: float
    m2_mev: float
    m3_mev: float
    sum_mev: float
    source: str


def discharge_leptons_mev(xi: float = XI_LOCKIN) -> DischargeLeptons:
    tau, mu, e = tmse.lepton_mass_spectrum_at_xi_mev(xi)
    return DischargeLeptons(tau, mu, e)


def discharge_quarks_mev(xi: float = XI_LOCKIN) -> DischargeQuarks:
    q = tmse.tuft_quark_spectrum_at_xi_mev(xi)
    return DischargeQuarks(q.t_mev, q.c_mev, q.u_mev, q.b_mev, q.s_mev, q.d_mev)


def discharge_neutrinos_mev(xi: float = XI_LOCKIN) -> DischargeNeutrinos | None:
    if nu_bridge is None:
        return None
    nu = nu_bridge.model_tuft_outer_t8_t10(xi)
    s = nu.m1_mev + nu.m2_mev + nu.m3_mev
    return DischargeNeutrinos(nu.m1_mev, nu.m2_mev, nu.m3_mev, s, "tuftOuterCasimirDressingAtXi")


def discharge_hadron_mev(xi: float = XI_LOCKIN) -> dict[str, float]:
    g = tmse.tuft_hadron_ground_at_xi_mev(xi)
    meson_vec = tmse.tuft_meson_vector_ground_at_xi_mev(xi)
    meson_spine_ratio = (2.0 / 3.0) * spine_proton_readout()
    return {
        "proton_mev": g,
        "meson_vector_ground_mev": meson_vec,
        "meson_spine_2over3_dim_only_mev": mis_map_proton_only_mev(meson_spine_ratio),
    }


def lepton_by_generation(d: DischargeLeptons) -> dict[Generation, float]:
    return {"tau": d.tau_mev, "muon": d.mu_mev, "electron": d.e_mev}


def ratio(pred: float, ref: float) -> float:
    return pred / ref if ref else float("nan")


def pct(pred: float, ref: float) -> float:
    return 100.0 * (pred - ref) / ref if ref else float("nan")


def main() -> None:
    pdg_mev = tmse.PDG_MEV
    pdg_quark = {
        "u": 2.16,
        "d": 4.67,
        "s": 93.4,
        "c": 1270.0,
        "b": 4180.0,
        "t": 172570.0,
    }
    lep = discharge_leptons_mev()
    quark = discharge_quarks_mev()
    had = discharge_hadron_mev()
    nu = discharge_neutrinos_mev()

    print("HQIV spine ↔ TUFT MeV discharge bridge\n")
    print("Layer 1 — spine (dimensionless @ lock-in massUnit=5)")
    for gen in GENERATIONS:
        w = WINDING[gen]
        print(
            f"  ℓ {gen:8s}  readout={spine_lepton_readout(w):g}   "
            f"q-scale={spine_quark_readout(w):g}   "
            f"ν_abs={spine_neutrino_absolute(w):.6g}"
        )
    print(f"  proton readout dim = {spine_proton_readout():g}\n")

    print("Layer 2 — TUFT MeV discharge @ ξ_lock (witness-anchored, PDG-free formulas)")
    print(f"  {'species':<10} {'discharge MeV':>14} {'PDG MeV':>14} {'ratio':>8}")
    print("  " + "-" * 50)
    for gen in GENERATIONS:
        mev = lepton_by_generation(lep)[gen]
        key = {"electron": "e", "muon": "mu", "tau": "tau"}[gen]
        ref = pdg_mev[key]
        print(f"  ℓ {gen:<7} {mev:14.6g} {ref:14.6g} {ratio(mev, ref):8.4f}")
    print(f"  proton     {had['proton_mev']:14.6g} {pdg_mev['proton']:14.6g} {ratio(had['proton_mev'], pdg_mev['proton']):8.4f}")
    print(
        f"  meson vec  {had['meson_vector_ground_mev']:14.6g} "
        f"{'(π,ρ diag)':>14} {'—':>8}"
    )
    for label in ("u", "d", "s", "c", "b", "t"):
        val = getattr(quark, f"{label}_mev")
        ref = pdg_quark[label]
        print(f"  q {label:<8} {val:14.6g} {ref:14.6g} {ratio(val, ref):8.4f}")

    if nu is not None:
        print(f"\n  ν outer discharge Σm_ν = {nu.sum_mev * 1e6:.4g} eV  (cap 0.12 eV)")
    print()

    print("Mis-map diagnostic (do NOT use for PDG)")
    e_dim = spine_lepton_readout(1)
    print(f"  spine e dim {e_dim:g} × proton/20 → {mis_map_proton_only_mev(e_dim):.1f} MeV  "
          f"(PDG {pdg_mev['e']:.4f}; factor ~{mis_map_proton_only_mev(e_dim)/pdg_mev['e']:.0e}× high)")
    print(f"  discharge e → {lep.e_mev:.4f} MeV  (ratio {ratio(lep.e_mev, pdg_mev['e']):.4f})")


if __name__ == "__main__":
    main()
