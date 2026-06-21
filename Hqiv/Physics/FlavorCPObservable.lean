import Hqiv.Physics.RareDecayReadout
import Hqiv.Physics.CkmHolonomyReadout
import Hqiv.Physics.PMNSHolonomyReadout
import Hqiv.Physics.HepExtendedAnomalyDischarge
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ChargedLeptonResonance

/-!
# Flavor CP and differential observables

LFU ratios, angular moments, and CP asymmetry routing on top of the
CKM/PMNS holonomy theorem packages.
-/

namespace Hqiv.Physics

/-! ## LFU ratios -/

/-- R_K slot: mu/e phase-space ratio at fixed parent mass (form-factor independent skeleton). -/
noncomputable def lfuRKSlot (mB mK : ℝ) : ℝ :=
  lfuRatioFromPhaseSpace (m_mu_from_lockin_surface_candidate) (m_e_from_lockin_surface_candidate) mB

/-- R_K* slot uses the same lepton mass phase space with K* parent mass proxy. -/
noncomputable def lfuRKstarSlot (mB mKstar : ℝ) : ℝ :=
  lfuRatioFromPhaseSpace (m_mu_from_lockin_surface_candidate) (m_e_from_lockin_surface_candidate) mB

/-! ## Angular observables -/

/-- P_5' differential moment on b→sℓℓ (from extended anomaly discharge). -/
noncomputable def bToSllP5Prime : ℝ := bsllP5PrimeMoment

theorem bToSllP5Prime_eq :
    bToSllP5Prime = cpOddFanoHolonomySkew - gamma_HQIV * ckmSlotCD2 := rfl

/-! ## CP asymmetries -/

/-- CP asymmetry slot for B_s → J/ψ φ from Jarlskog orientation. -/
noncomputable def cpAsymmetryBsJpsiPhi : ℝ :=
  2 * ckmJarlskog / (ckmMagnitude 1 2 ^ 2 + ckmMagnitude 2 2 ^ 2)

/-- CP asymmetry slot for B → K* γ from holonomy skew. -/
noncomputable def cpAsymmetryBToKstarGamma : ℝ :=
  cpOddFanoHolonomySkew / ckmSlotUS2

theorem cpAsymmetryBToKstarGamma_eq_three_over_four :
    cpAsymmetryBToKstarGamma = (3 : ℝ) / 4 := by
  simp [cpAsymmetryBToKstarGamma, cpOddFanoHolonomySkew_eq_three_over_eighty,
    ckmSlotUS2, gamma_eq_2_5]
  norm_num

/-! ## LFV and EDM phase-lift bounds -/

/-- μ → eγ: double monogamy exclusion on flavour-changing holonomy (finite patch). -/
noncomputable def lfvMuToEgGammaBound : ℝ :=
  doubleMonogamyExclusionFactor * fanoSecondOrderPhaseSkew

/-- Neutron EDM slot from phase-lift holonomy at lock-in. -/
noncomputable def edmNeutronSlot : ℝ :=
  fanoHolonomyCPPhase / Real.pi * gamma_HQIV

/-- Electron EDM slot: outer-shell suppression relative to neutron. -/
noncomputable def edmElectronSlot : ℝ :=
  edmNeutronSlot * outerHorizonNeutrinoSuppression

structure FlavorCPObservableCertificate where
  rk_universal_contact : ∀ l, visibleChargedLeptonWeakContact l = (1 : ℝ) / 10
  p5_prime : bToSllP5Prime = cpOddFanoHolonomySkew - gamma_HQIV * ckmSlotCD2
  jarlskog_pos : 0 < ckmJarlskog
  pmns_delta_cp : assemblePMNSHolonomyReadout.deltaCP = Real.pi / 5

def flavorCPObservableCertificate_holds : FlavorCPObservableCertificate where
  rk_universal_contact := visibleChargedLeptonWeakContact_universal
  p5_prime := bToSllP5Prime_eq
  jarlskog_pos := ckmJarlskog_pos
  pmns_delta_cp := assemblePMNSHolonomyReadout_deltaCP

end Hqiv.Physics
