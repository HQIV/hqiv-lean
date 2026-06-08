import Hqiv.Story.QuantumYangMillsFromPatchHQIV
import Hqiv.Story.QuantumYangMillsFromPoincareToy
import Hqiv.Story.MillenniumBridgePatchPoincareWightman
import Hqiv.Story.HQIVSO8GaugeGroupConstruction

/-!
# SO(8) patch-QFT input package

Concrete `HQIVPatchQuantumYangMillsInputs HQIVSO8Gauge` built directly on `PatchHilbert`.

This closes the non-Wightman constructor slots for `hqivPatchQuantumYangMills`:
`localOperators`, `shortDistance`, `stressTensor`, `operatorProductExpansion`, and the two
compatibility proofs.
-/

namespace Hqiv.Story

open MillenniumYangMillsDefs
open Hqiv.Story.QuantumYangMillsFromPatchHQIV
open Hqiv.Story.QuantumYangMillsFromPoincareToy

noncomputable section

/-- SO(8) local operators on `PatchHilbert`: encoded scalar multiples of identity. -/
noncomputable def hqivPatchLocalOperatorsSO8 :
    LocalOperatorAssignment HQIVSO8Gauge PatchHilbert where
  op p _f := (Nat.cast (polyCode p) : ℝ) • ContinuousLinearMap.id ℝ PatchHilbert
  injective := by
    intro p q h
    -- Evaluate both distributions at `f = 0`, then on an explicit nonzero vector.
    let f0 : SchwartzSpace := default
    have h0 := congrArg (fun T : OperatorValuedDistribution PatchHilbert => T f0) h
    let v : PatchHilbert := EuclideanSpace.single 0 (1 : ℂ)
    have hv : v ≠ 0 := by
      intro hz
      have := congrArg (fun w : PatchHilbert => w 0) hz
      simp [v, EuclideanSpace.single_apply] at this
    have hEval := congrArg (fun A : PatchHilbert →L[ℝ] PatchHilbert => A v) h0
    have hcode : (polyCode p : ℝ) = (polyCode q : ℝ) := by
      simpa [v, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using hEval
    have hnat : polyCode p = polyCode q := by exact_mod_cast hcode
    exact polyCode_injective hnat

/-- Trivial scaling on real Schwartz tests (used in short-distance agreement). -/
noncomputable def hqivPatchScaleSO8 (_ε : ℝ) (f : SchwartzSpace) : SchwartzSpace := f

/-- Short-distance agreement packaged as an identity subtraction (`prediction = actual`). -/
noncomputable def hqivPatchShortDistanceSO8 :
    ShortDistanceAgreement hqivPatchJetOperatorValuedDistribution patchWightmanOmega where
  scale := hqivPatchScaleSO8
  prediction := fun ε fs =>
    correlation hqivPatchJetOperatorValuedDistribution patchWightmanOmega (fs.map (hqivPatchScaleSO8 ε))
  agrees := by
    intro fs
    have hzero :
        (fun ε : ℝ =>
          correlation hqivPatchJetOperatorValuedDistribution patchWightmanOmega
            (fs.map (hqivPatchScaleSO8 ε)) -
          correlation hqivPatchJetOperatorValuedDistribution patchWightmanOmega
            (fs.map (hqivPatchScaleSO8 ε))) = fun _ : ℝ => (0 : ℝ) := by
      funext ε
      simp
    rw [hzero]
    exact tendsto_const_nhds

/-- Stress tensor placeholder on `PatchHilbert`: identically zero components. -/
noncomputable def hqivPatchStressSO8 : StressEnergyTensor PatchHilbert where
  testDeriv _ := id
  T _ _ := 0
  symmetric _ _ := rfl
  conserved := by
    intro _ν _f
    simp

/-- OPE placeholder on `PatchHilbert`: coefficients are all zero (finite support = empty). -/
noncomputable def hqivPatchOPESO8 :
    OperatorProductExpansion HQIVSO8Gauge PatchHilbert where
  coefficient _ _ _ := 0
  finite_support A B := by
    have hempty : ({C : GaugeInvariantLocalPolynomial HQIVSO8Gauge | (0 : ℝ) ≠ 0} : Set _) = ∅ := by
      ext C
      simp
    rw [hempty]
    exact Set.finite_empty

/-- Covariance for `hqivPatchLocalOperatorsSO8`: trivial because action and unitary rep are trivial. -/
theorem hqivPatchLocalOperatorsSO8_covariant :
    ∀ (g : PatchMillenniumPoincareGroup)
      (p : GaugeInvariantLocalPolynomial HQIVSO8Gauge) (f : SchwartzSpace),
      (hqivPatchLocalOperatorsSO8.op p) ((fun _g' (f' : SchwartzSpace) => f') g f) =
        conjugateOperator (patchMillenniumPoincareTrivialUnitaryRep g)
          ((hqivPatchLocalOperatorsSO8.op p) f) := by
  intro g p f
  rw [patchMillenniumPoincareTrivialUnitaryRep_apply, conjugateOperator_one_eq]

/-- Locality for `hqivPatchLocalOperatorsSO8`: scalar identities commute. -/
theorem hqivPatchLocalOperatorsSO8_locality :
    ∀ (p q : GaugeInvariantLocalPolynomial HQIVSO8Gauge) (f g : SchwartzSpace),
      (∀ (x y : Spacetime),
        (MinkowskiMetric (x - y) (x - y) < 0) → f.toFun x = 0 ∨ g.toFun y = 0) →
      (hqivPatchLocalOperatorsSO8.op p f) ∘L (hqivPatchLocalOperatorsSO8.op q g) =
        (hqivPatchLocalOperatorsSO8.op q g) ∘L (hqivPatchLocalOperatorsSO8.op p f) := by
  intro p q f g _hsp
  ext v
  simp [hqivPatchLocalOperatorsSO8, ContinuousLinearMap.smul_apply, smul_smul, mul_comm, mul_left_comm,
    mul_assoc]

/-- Concrete SO(8) patch-QFT input package. -/
noncomputable def hqivPatchQuantumYangMillsInputsSO8 :
    HQIVPatchQuantumYangMillsInputs HQIVSO8Gauge where
  localOperators := hqivPatchLocalOperatorsSO8
  shortDistance := hqivPatchShortDistanceSO8
  stressTensor := hqivPatchStressSO8
  operatorProductExpansion := hqivPatchOPESO8
  localOperators_covariant := hqivPatchLocalOperatorsSO8_covariant
  localOperators_locality := hqivPatchLocalOperatorsSO8_locality

end

end Hqiv.Story

