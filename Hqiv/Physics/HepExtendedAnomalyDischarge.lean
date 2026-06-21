import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.ChargedLeptonResonance

/-!
# Extended heavy-flavour anomaly discharge (LFU, angular, FCNC)

Three anomaly classes previously marked out-of-scope are discharged here on the
finite three-ledger patch:

1. **LFU ratios** — universal visible-lepton weak contact plus helicity phase space
   from the lock-in resonance ladder (`ChargedLeptonResonance`).
2. **Angular observables** — differential `b→sℓℓ` moment registry (`P_5'` slot).
3. **Rare FCNC** — second-order weak-operator registry on fixed CKM / OZI slots.

Python mirror: `scripts/hqiv_hep_anomaly_discharge.py`.
-/

namespace Hqiv.Physics

/-! ## I. LFU ratio ledger -/

/-- Visible charged leptons on the weak discharge ledger. -/
inductive VisibleChargedLepton where
  | e
  | mu
  | tau
  deriving DecidableEq, Repr, Inhabited

/--
Every visible charged lepton occupies the same weak outlet aperture; LFU violation
must enter only through lepton-mass phase space, not a fitted contact table.
-/
noncomputable def visibleChargedLeptonWeakContact (_ : VisibleChargedLepton) : ℝ :=
  leptonNeutrinoPairAperture

theorem visibleChargedLeptonWeakContact_universal (l : VisibleChargedLepton) :
    visibleChargedLeptonWeakContact l = (1 : ℝ) / 10 :=
  leptonNeutrinoPairAperture_eq_one_tenth

/-- Helicity phase-space factor `(1 - m_ℓ²/m_parent²)²` on the finite patch. -/
noncomputable def semileptonicHelicityPhaseSpace (mLepton mParent : ℝ) : ℝ :=
  if mParent ≤ 0 then 0
  else if mLepton ≥ mParent then 0
  else (1 - (mLepton / mParent) ^ 2) ^ 2

/--
LFU ratio from phase space alone: e.g. $R_{D^{(*)}} = \Gamma(B\to D^{(*)}\tau\nu)/
\Gamma(B\to D^{(*)}\mu\nu)$ when the weak contact is flavour-universal.
-/
noncomputable def lfuRatioFromPhaseSpace (mHeavy mLight mParent : ℝ) : ℝ :=
  if semileptonicHelicityPhaseSpace mLight mParent = 0 then 0
  else
    semileptonicHelicityPhaseSpace mHeavy mParent /
      semileptonicHelicityPhaseSpace mLight mParent

/-- Lock-in μ/τ mass ratio from the proved surface resonance step. -/
noncomputable def lfuTauMuMassRatio : ℝ :=
  m_mu_from_lockin_surface_candidate / m_tau_from_lockin_surface_candidate

theorem lfuTauMuMassRatio_eq_seventysix_over_onehundredseventyfive :
    lfuTauMuMassRatio = (76 : ℝ) / 175 := by
  rw [lfuTauMuMassRatio, m_mu_from_lockin_surface_candidate_eq_tau_over_resonance,
    m_tau_from_lockin_surface_candidate_eq_four_fifths, resonance_k_tau_mu_eq_rat]
  norm_num

/--
Open-bottom $R_{D^{(*)}}$ suppression when the heavy $c$-quark leg competes with
the open-bottom production aperture on the same weak outlet: double monogamy on the
charm leg times the bottom/charm production ratio.
-/
noncomputable def lfuOpenBottomTauMuSuppression : ℝ :=
  doubleMonogamyExclusionFactor * openBottomProductionWeight / openCharmProductionWeight

theorem lfuOpenBottomTauMuSuppression_eq_twentyone_fiftieths :
    lfuOpenBottomTauMuSuppression = (21 : ℝ) / 50 := by
  simp [lfuOpenBottomTauMuSuppression, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive,
    openBottomProductionWeight_eq, openCharmProductionWeight_eq, gamma_eq_2_5]
  norm_num

/--
Vector-daughter LFU slot on $B\to D^*\ell\nu$: pseudoscalar-to-vector mass ratio
squared times a second double-monogamy pass on the excited charm leg.
Mass arguments are HQIV readout inputs, not PDG imports.
-/
noncomputable def lfuOpenBottomVectorDaughterFactor (mPseudoscalar mVector : ℝ) : ℝ :=
  if mVector = 0 then 0 else (mPseudoscalar / mVector) ^ 2 * doubleMonogamyExclusionFactor

theorem lfuOpenBottomVectorDaughterFactor_unit_mass :
    lfuOpenBottomVectorDaughterFactor 1 1 = doubleMonogamyExclusionFactor := by
  simp [lfuOpenBottomVectorDaughterFactor]

structure LfuRatiosDischarged where
  contact_universal : ∀ l, visibleChargedLeptonWeakContact l = (1 : ℝ) / 10
  tau_mu_mass_ratio : lfuTauMuMassRatio = (76 : ℝ) / 175
  resonance_step : resonance_k_tau_mu = (175 : ℝ) / 76
  open_bottom_tau_mu_suppression : lfuOpenBottomTauMuSuppression = (21 : ℝ) / 50

noncomputable def lfuRatiosDischarged : LfuRatiosDischarged where
  contact_universal := visibleChargedLeptonWeakContact_universal
  tau_mu_mass_ratio := lfuTauMuMassRatio_eq_seventysix_over_onehundredseventyfive
  resonance_step := resonance_k_tau_mu_eq_rat
  open_bottom_tau_mu_suppression := lfuOpenBottomTauMuSuppression_eq_twentyone_fiftieths

/-! ## II. Angular differential registry (`P_5'` slot) -/

/--
Differential forward-backward moment on the $b\to s\ell^+\ell^-$ registry.
Built from the CP-odd Fano skew minus the $c\to d$ second-order rung return.
-/
noncomputable def bsllP5PrimeMoment : ℝ :=
  cpOddFanoHolonomySkew - gamma_HQIV * ckmSlotCD2

theorem bsllP5PrimeMoment_eq_eleven_fourhundred :
    bsllP5PrimeMoment = (11 : ℝ) / 400 := by
  simp [bsllP5PrimeMoment, cpOddFanoHolonomySkew, ckmSlotUS2, ckmSlotCB2, ckmSlotCD2,
    gamma_eq_2_5]
  norm_num

theorem bsllP5PrimeMoment_pos : 0 < bsllP5PrimeMoment := by
  rw [bsllP5PrimeMoment_eq_eleven_fourhundred]
  norm_num

/--
Angular observable registry: moments are multiplicative weights on the weak
ledger before inclusive normalization.
-/
structure AngularObservablesRegistry where
  p5_prime : ℝ

noncomputable def angularObservablesRegistry : AngularObservablesRegistry where
  p5_prime := bsllP5PrimeMoment

/--
Low-$q^2$ promotion of the $P_5'$ moment on the $b\to s\ell^+\ell^-$ registry:
CP-odd Fano skew times the charged open-bottom spectator ladder
(`2 × spectatorHalfMonogamyContact`).
-/
noncomputable def bsllP5PrimeLowQ2Readout : ℝ :=
  cpOddFanoHolonomySkew * (2 * spectatorHalfMonogamyContact)

theorem bsllP5PrimeLowQ2Readout_eq_nine_hundredths :
    bsllP5PrimeLowQ2Readout = (9 : ℝ) / 100 := by
  simp [bsllP5PrimeLowQ2Readout, cpOddFanoHolonomySkew_eq_three_over_eighty,
    spectatorHalfMonogamyContact_eq_six_fifths, gamma_eq_2_5]
  norm_num

theorem bsllP5PrimeLowQ2Readout_eq_moment_times_thirtysix_elevenths :
    bsllP5PrimeLowQ2Readout = bsllP5PrimeMoment * (36 : ℝ) / 11 := by
  rw [bsllP5PrimeLowQ2Readout_eq_nine_hundredths, bsllP5PrimeMoment_eq_eleven_fourhundred]
  norm_num

structure AngularObservablesDischarged where
  registry : AngularObservablesRegistry
  p5_prime_value : registry.p5_prime = (11 : ℝ) / 400
  p5_prime_pos : 0 < registry.p5_prime
  p5_prime_low_q2 : bsllP5PrimeLowQ2Readout = (9 : ℝ) / 100

noncomputable def angularObservablesDischarged : AngularObservablesDischarged where
  registry := angularObservablesRegistry
  p5_prime_value := bsllP5PrimeMoment_eq_eleven_fourhundred
  p5_prime_pos := bsllP5PrimeMoment_pos
  p5_prime_low_q2 := bsllP5PrimeLowQ2Readout_eq_nine_hundredths

/-! ## III. Rare FCNC operator registry -/

/-- Curated rare FCNC modes on the finite weak patch. -/
inductive RareFcncMode where
  | Bsll
  | BsGamma
  | BsMuMu
  deriving DecidableEq, Repr, Inhabited

def allRareFcncModes : List RareFcncMode := [.Bsll, .BsGamma, .BsMuMu]

/--
Second-order FCNC operator weights: products of discharged CKM / OZI / monogamy
slots — no loop integral tables and no fitted Wilson coefficients.
-/
noncomputable def rareFcncOperatorWeight : RareFcncMode → ℝ
  | .Bsll => ckmSlotUS2 * cpOddFanoHolonomySkew
  | .BsGamma => oziSuppressedStrongContact * ckmSlotUS2
  | .BsMuMu => ckmSlotCB2 ^ 2 * doubleMonogamyExclusionFactor

theorem rareFcncOperatorWeight_Bsll_eq_three_sixteenhundredths :
    rareFcncOperatorWeight .Bsll = (3 : ℝ) / 1600 := by
  simp [rareFcncOperatorWeight, cpOddFanoHolonomySkew, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem rareFcncOperatorWeight_BsGamma_eq_one_twohundredth :
    rareFcncOperatorWeight .BsGamma = (1 : ℝ) / 200 := by
  simp [rareFcncOperatorWeight, oziSuppressedStrongContact, ckmSlotUS2, gamma_eq_2_5]
  norm_num

theorem rareFcncOperatorWeight_BsMuMu_eq_twentyone_onehundredsixtythousands :
    rareFcncOperatorWeight .BsMuMu = (21 : ℝ) / 160000 := by
  simp [rareFcncOperatorWeight, ckmSlotCB2, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive,
    gamma_eq_2_5]
  norm_num

theorem rareFcncOperatorWeight_pos (m : RareFcncMode) : 0 < rareFcncOperatorWeight m := by
  cases m
  · rw [rareFcncOperatorWeight_Bsll_eq_three_sixteenhundredths]; norm_num
  · rw [rareFcncOperatorWeight_BsGamma_eq_one_twohundredth]; norm_num
  · rw [rareFcncOperatorWeight_BsMuMu_eq_twentyone_onehundredsixtythousands]; norm_num

theorem rareFcncRegistry_covers_three_modes :
    allRareFcncModes.length = 3 := by native_decide

/--
Comparison-layer FCNC contact readout: operator weights on the weak ledger directly
(no extra open-charm aperture divisor — that was a Python comparison bug).
-/
noncomputable def rareFcncComparisonContact (m : RareFcncMode) : ℝ :=
  rareFcncOperatorWeight m

theorem rareFcncComparisonContact_Bsll_eq :
    rareFcncComparisonContact .Bsll = (3 : ℝ) / 1600 := by
  simp [rareFcncComparisonContact, rareFcncOperatorWeight_Bsll_eq_three_sixteenhundredths]

theorem rareFcncComparisonContact_BsGamma_eq :
    rareFcncComparisonContact .BsGamma = (1 : ℝ) / 200 := by
  simp [rareFcncComparisonContact, rareFcncOperatorWeight_BsGamma_eq_one_twohundredth]

structure RareFcncDischarged where
  bsll_weight : rareFcncOperatorWeight .Bsll = (3 : ℝ) / 1600
  bsgamma_weight : rareFcncOperatorWeight .BsGamma = (1 : ℝ) / 200
  bsmumu_weight : rareFcncOperatorWeight .BsMuMu = (21 : ℝ) / 160000
  all_pos : ∀ m, 0 < rareFcncOperatorWeight m
  comparison_contact_bsll : rareFcncComparisonContact .Bsll = (3 : ℝ) / 1600
  comparison_contact_bsgamma : rareFcncComparisonContact .BsGamma = (1 : ℝ) / 200

noncomputable def rareFcncDischarged : RareFcncDischarged where
  bsll_weight := rareFcncOperatorWeight_Bsll_eq_three_sixteenhundredths
  bsgamma_weight := rareFcncOperatorWeight_BsGamma_eq_one_twohundredth
  bsmumu_weight := rareFcncOperatorWeight_BsMuMu_eq_twentyone_onehundredsixtythousands
  all_pos := rareFcncOperatorWeight_pos
  comparison_contact_bsll := rareFcncComparisonContact_Bsll_eq
  comparison_contact_bsgamma := rareFcncComparisonContact_BsGamma_eq

#check lfuRatiosDischarged
#check angularObservablesDischarged
#check rareFcncDischarged

end Hqiv.Physics
