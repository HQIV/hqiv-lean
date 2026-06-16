import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.DynamicNucleonPN
import Hqiv.Physics.NuclearOutsideTemperatureDynamics

/-!
# Proton mass decomposition: inner anchor vs outside curvature slot

The scale witness pins the **inner** composite-trace mass (`derivedProtonMass`).
Outside temperature / gravity modulators book an additive increment on the nucleon
own-binding trace without re-feeding the anchor.

Python mirror: `scripts/hqiv_proton_mass_decomposition.py`.
-/

namespace Hqiv.Physics

noncomputable section

/-- Inner (meta-horizon) proton mass: constituent minus shared composite-trace binding. -/
noncomputable def protonInnerRawMass : ℝ := derivedProtonMass

/-- Shared nucleon trace at the lock-in shell (MeV). -/
noncomputable def protonBindingTraceAtLockin (c : ℝ := 1) : ℝ :=
  bbnNucleonTraceBinding referenceM c

/-- Outside increment on own-binding from the release factor alone (zero at ξ_lock). -/
noncomputable def nucleonOutsideReleaseIncrementAtXi (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  protonBindingTraceAtLockin c * (outsideCurvatureReleaseFactor ξ - 1)

/-- Outside increment from weak-field gravity via `G_eff(1+ε)`. -/
noncomputable def nucleonOutsideGravityIncrement (trace : ℝ) (φ : ℝ) : ℝ :=
  trace * (outsideGravityGeffModulator ⟨φ⟩ - 1)

/-- Named decomposition of the proton mass budget at `(ξ, φ)`. -/
structure ProtonMassDecomposition where
  innerRaw : ℝ
  outsideReleaseIncrement : ℝ
  outsideGravityIncrement : ℝ
  observedDynamic : ℝ
  inner_eq_derived : innerRaw = derivedProtonMass
  observed_eq_inner_minus_outside :
    observedDynamic =
      innerRaw - outsideReleaseIncrement - outsideGravityIncrement

/-- Decomposition at `(ξ, φ)` using the nucleon trace at lock-in. -/
noncomputable def protonMassDecompositionAt (ξ : ℝ) (φ : ℝ) (c : ℝ := 1) :
    ProtonMassDecomposition where
  innerRaw := derivedProtonMass
  outsideReleaseIncrement := nucleonOutsideReleaseIncrementAtXi ξ c
  outsideGravityIncrement := nucleonOutsideGravityIncrement (protonBindingTraceAtLockin c) φ
  observedDynamic :=
    derivedProtonMass -
      nucleonOutsideReleaseIncrementAtXi ξ c -
        nucleonOutsideGravityIncrement (protonBindingTraceAtLockin c) φ
  inner_eq_derived := rfl
  observed_eq_inner_minus_outside := by ring_nf

theorem protonOutsideReleaseIncrement_zero_at_lockin (c : ℝ) :
    nucleonOutsideReleaseIncrementAtXi xiLockin c = 0 := by
  unfold nucleonOutsideReleaseIncrementAtXi
  rw [outsideCurvatureLockinCalibrated_holds]
  ring

theorem protonOutsideGravityIncrement_zero_at_neutral (c : ℝ) :
    nucleonOutsideGravityIncrement (protonBindingTraceAtLockin c) 0 = 0 := by
  unfold nucleonOutsideGravityIncrement outsideGravityGeffModulator
  simp

theorem protonMassDecompositionAt_lockin_neutral_observed_eq_inner (c : ℝ) :
    (protonMassDecompositionAt xiLockin 0 c).observedDynamic = derivedProtonMass := by
  dsimp [protonMassDecompositionAt]
  rw [protonOutsideReleaseIncrement_zero_at_lockin, protonOutsideGravityIncrement_zero_at_neutral]
  ring

theorem protonInnerRawMass_eq_derived : protonInnerRawMass = derivedProtonMass := rfl

/-- Dynamic free-branch mass matches inner raw at lock-in when trace equals shared binding. -/
theorem protonMassAtXi_freeLockin_eq_inner
    (c : ℝ)
    (htrace :
      bbnNucleonTraceBinding referenceM c = nucleonSharedBinding_MeV) :
    protonMassAtXi freeLockinNucleonEnvironment c = derivedProtonMass := by
  unfold protonMassAtXi nucleonMassAtXi derivedProtonMass sharedBindingEnergy
    nucleonOwnBindingInEnvironment nucleonWellContribution nucleonOwnBindingAtXi
    freeLockinNucleonEnvironment
  simp only [nucleonConstituentEnergy, Bool.false_eq_true, if_false]
  rw [outsideCurvatureLockinCalibrated_holds, htrace]
  ring

end

end Hqiv.Physics
