import Hqiv.Physics.ChargedLeptonResonance

/-!
# Quark sector: τ-resonance mass functional (geometry-first track)

The **color-resonance / MeV nucleon** export ladder in `QuarkMetaResonance.lean` uses explicit GeV
anchors (`m_top_GeV`, `m_bottom_GeV`) and natural-number readout coordinates for detuned-surface
ratios; the module header there states this witness honestly.

A **separate** track already exists in `SM_GR_Unification.lean`: quark labels use the same
`smMassFromGeometry` template as charged leptons,
`m_tau_Pl * (1 / resonanceProduct ρ)` for `ρ : Hqiv.Algebra.So8RepIndex` (triality generation slots).
Generation ratios are therefore the **same** Fano / detuned-surface objects as the lepton ladder,
with **no** top/bottom numerals in that definition chain.

The only dimensionful Planck-ratio input reused from `ChargedLeptonResonance` is `m_tau_Pl` (tau
mass in Planck units), exactly as for the lepton sector normalization.

This file exposes that functional **without** importing the heavy `SM_GR_Unification` cone, so
future work can attempt to re-wire nucleon **constituent** bookkeeping from GeV anchors to this
functional plus a **single** electroweak-derived unit conversion (not proved here — open hook).

For a **blank-slate quark sector** using the outer gauge VEV `vacuumExpectationValueGauge` with the
same `resonanceProduct` ratios (and optional φ(lock-in) dressing), see
`Hqiv.Physics.QuarkSectorFromEWGauge`.

For electroweak-scale certificates on the outer-horizon ladder, see
`Hqiv.Physics.WeakDoubletCarrierGaugeQuadratic` and `Hqiv.Physics.DerivedGaugeAndLeptonSector`.
-/

namespace Hqiv.Physics

open Hqiv.Algebra

/-- Planck-unit mass assignment parallel to `SM_GR_Unification.smMassFromGeometry` (quark labels). -/
noncomputable def quarkLikeMassFromTauResonance (ρ : So8RepIndex) : ℝ :=
  m_tau_Pl * (1 / resonanceProduct ρ)

theorem resonanceProduct_pos (ρ : So8RepIndex) : 0 < resonanceProduct ρ := by
  fin_cases ρ
  · simpa [resonanceProduct] using mul_pos resonance_k_tau_mu_pos resonance_k_mu_e_pos
  · simpa [resonanceProduct] using resonance_k_tau_mu_pos
  · simp [resonanceProduct]

theorem quarkLikeMassFromTauResonance_pos (ρ : So8RepIndex) :
    0 < quarkLikeMassFromTauResonance ρ := by
  unfold quarkLikeMassFromTauResonance
  refine mul_pos ?_ ?_
  · norm_num [m_tau_Pl]
  · exact div_pos zero_lt_one (resonanceProduct_pos ρ)

theorem quarkLikeMassFromTauResonance_eq_m_tau_div (ρ : So8RepIndex) :
    quarkLikeMassFromTauResonance ρ = m_tau_Pl / resonanceProduct ρ := by
  simp [quarkLikeMassFromTauResonance, div_eq_mul_inv]

end Hqiv.Physics
