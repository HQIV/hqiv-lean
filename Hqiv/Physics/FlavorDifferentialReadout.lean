import Hqiv.Physics.FlavorCPObservable
import Hqiv.Physics.CkmHolonomyReadout
import Hqiv.Physics.RareDecayReadout

/-!
# Differential and angular flavor readouts

Form-factor-independent angular skeletons for rare and semileptonic channels,
built on the CKM holonomy and extended anomaly discharge ledger.
-/

namespace Hqiv.Physics

/-! ## Angular distributions (finite patch) -/

/-- Forward-backward asymmetry slot for B → K* μμ: `2P_5'/(1+P_5'²)` skeleton. -/
noncomputable def bToKstarMuMuForwardBackward : ℝ :=
  2 * bToSllP5Prime / (1 + bToSllP5Prime ^ 2)

theorem bToKstarMuMuForwardBackward_eq :
    bToKstarMuMuForwardBackward =
      2 * (cpOddFanoHolonomySkew - gamma_HQIV * ckmSlotCD2) /
        (1 + (cpOddFanoHolonomySkew - gamma_HQIV * ckmSlotCD2) ^ 2) := by
  simp [bToKstarMuMuForwardBackward, bToSllP5Prime_eq]

theorem bToKstarMuMuForwardBackward_eq_eight_thousand_eight_hundred_over_160121 :
    bToKstarMuMuForwardBackward = (8800 : ℝ) / 160121 := by
  dsimp [bToKstarMuMuForwardBackward, bToSllP5Prime]
  rw [bsllP5PrimeMoment_eq_eleven_fourhundred]
  field_simp
  norm_num

/-- Flatness / isotropic slot for Bs → μμ (no hadronic spin; Jarlskog-weighted). -/
noncomputable def bsToMuMuAngularFlatness : ℝ :=
  1 / (1 + ckmJarlskog ^ 2)

theorem bsToMuMuAngularFlatness_eq :
    bsToMuMuAngularFlatness = 1 / (1 + cpOddFanoHolonomySkew ^ 2) := by
  simp [bsToMuMuAngularFlatness, ckmJarlskog_eq_cp_odd_skew]

theorem bsToMuMuAngularFlatness_eq_one_over_one_plus_nine_sixtyfour_hundred :
    bsToMuMuAngularFlatness = 1 / (1 + (9 : ℝ) / 6400) := by
  rw [bsToMuMuAngularFlatness_eq, cpOddFanoHolonomySkew_eq_three_over_eighty]
  norm_num

/-- Differential weight for B → K* μμ at cos θ = 0 (transverse slot). -/
noncomputable def bToKstarMuMuTransverseWeight : ℝ :=
  1 - bToKstarMuMuForwardBackward ^ 2

theorem bToKstarMuMuTransverseWeight_eq :
    bToKstarMuMuTransverseWeight = 1 - bToKstarMuMuForwardBackward ^ 2 := rfl

structure FlavorDifferentialReadout where
  p5_prime : ℝ
  forward_backward : ℝ
  bs_flatness : ℝ
  transverse_weight : ℝ

noncomputable def assembleFlavorDifferentialReadout : FlavorDifferentialReadout where
  p5_prime := bToSllP5Prime
  forward_backward := bToKstarMuMuForwardBackward
  bs_flatness := bsToMuMuAngularFlatness
  transverse_weight := bToKstarMuMuTransverseWeight

theorem assembleFlavorDifferentialReadout_p5_eq_eleven_fourhundred :
    assembleFlavorDifferentialReadout.p5_prime = (11 : ℝ) / 400 :=
  bsllP5PrimeMoment_eq_eleven_fourhundred

structure FlavorDifferentialReadoutCertificate where
  p5_prime : assembleFlavorDifferentialReadout.p5_prime = (11 : ℝ) / 400
  forward_backward :
    assembleFlavorDifferentialReadout.forward_backward = (8800 : ℝ) / 160121

def flavorDifferentialReadoutCertificate_holds : FlavorDifferentialReadoutCertificate where
  p5_prime := assembleFlavorDifferentialReadout_p5_eq_eleven_fourhundred
  forward_backward := bToKstarMuMuForwardBackward_eq_eight_thousand_eight_hundred_over_160121

end Hqiv.Physics
