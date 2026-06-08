import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Hqiv.Geometry.RapidityLorentzClosure
import Hqiv.Physics.HorizonBlackbodyLadder
import Hqiv.Physics.HQIVFluidClosureScaffold

/-!
# Spatial rotations ↔ `3+1` Minkowski / applied-domain discharge

Extends `RapidityLorentzClosure` with orthogonal spatial rotations on `Fin 3 → ℝ` and the
block action on `Fin 4` that fixes time and rotates `(x¹,x²,x³)`.

**Discharged for applied papers**

* **Flyby:** `‖r×v‖²` and equatorial axis fractions are rotation invariants.
* **CMB / greybody:** sky rotation `ψ` shifts `β ↦ β+ψ` in the `2β` Stokes angle; completeness
  `cos²+sin²=1` holds for any `ψ`.
* **O-Maxwell fluid chart:** `hqivVacuumMomentumSource3` is covariant under spatial rotations when
  gradients rotate as 3-vectors.
* **Coronal / longitudinal axis:** `ŝ·w` is invariant when both vectors rotate together.

**Scope.** `O(3)` (orthogonal determinant `±1`) suffices for norms, dot products, and the spatial
block of `minkowskiSq4`. Rapidity boosts remain in `RapidityLorentzClosure`.
-/

namespace Hqiv.Geometry

open Real Matrix
open scoped Matrix BigOperators

/-- Euclidean inner product on spatial `Fin 3` vectors. -/
noncomputable def euclideanInner3 (u v : Fin 3 → ℝ) : ℝ :=
  dotProduct u v

/-- Squared Euclidean norm on `Fin 3`. -/
noncomputable def euclideanNormSq3 (v : Fin 3 → ℝ) : ℝ :=
  euclideanInner3 v v

/-- Standard cross product on `Fin 3`. -/
noncomputable def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- Chart point `(t, v₀, v₁, v₂)` on `Fin 4`. -/
def chartPoint41 (t : ℝ) (v : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![t, v 0, v 1, v 2]

/-- Spatial components `(x¹,x²,x³)` from a chart point. -/
def spatialPart41 (x : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![x 1, x 2, x 3]

theorem chartPoint41_zero (t : ℝ) (v : Fin 3 → ℝ) : chartPoint41 t v 0 = t := by
  simp [chartPoint41, Matrix.cons_val_zero, Matrix.head_cons]

theorem spatialPart41_chartPoint41 (t : ℝ) (v : Fin 3 → ℝ) :
    spatialPart41 (chartPoint41 t v) = v := by
  funext i
  fin_cases i <;> simp [spatialPart41, chartPoint41, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_fin_one]

/-- `3×3` matrix is orthogonal (`Rᵀ R = 1`). -/
def IsOrthogonal3 (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  Rᵀ * R = 1

/-- Block spatial rotation on `Fin 4`: fix time, rotate spatial components. -/
noncomputable def spatialRotationApply41 (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  chartPoint41 (x 0) (R.mulVec (spatialPart41 x))

theorem spatialRotationApply41_time_fixed (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 4 → ℝ) :
    spatialRotationApply41 R x 0 = x 0 := by
  simp [spatialRotationApply41, chartPoint41_zero]

theorem euclideanNormSq3_eq_sum_sq (v : Fin 3 → ℝ) :
    euclideanNormSq3 v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [euclideanNormSq3, euclideanInner3, dotProduct, Fin.sum_univ_three]
  ring

theorem minkowskiSq4_chartPoint41 (t : ℝ) (v : Fin 3 → ℝ) :
    minkowskiSq4 (chartPoint41 t v) = -(t ^ 2) + euclideanNormSq3 v := by
  simp [minkowskiSq4, chartPoint41, euclideanNormSq3_eq_sum_sq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem minkowskiSq4_eq_time_plus_spatial (x : Fin 4 → ℝ) :
    minkowskiSq4 x = -(x 0 ^ 2) + euclideanNormSq3 (spatialPart41 x) := by
  simp [minkowskiSq4, spatialPart41, euclideanNormSq3_eq_sum_sq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem euclideanInner3_mulVec_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (u v : Fin 3 → ℝ) :
    euclideanInner3 (R.mulVec u) (R.mulVec v) = euclideanInner3 u v := by
  dsimp only [euclideanInner3, IsOrthogonal3]
  calc
    (R.mulVec u) ⬝ᵥ (R.mulVec v) = (R.mulVec u) ᵥ* R ⬝ᵥ v := by rw [← dotProduct_mulVec]
    _ = u ᵥ* (Rᵀ * R) ⬝ᵥ v := by rw [vecMul_mulVec]
    _ = u ⬝ᵥ (Rᵀ * R).mulVec v := by rw [dotProduct_mulVec]
    _ = u ⬝ᵥ v := by rw [hR, one_mulVec]

theorem euclideanNormSq3_mulVec_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (v : Fin 3 → ℝ) :
    euclideanNormSq3 (R.mulVec v) = euclideanNormSq3 v := by
  dsimp [euclideanNormSq3]
  rw [euclideanInner3_mulVec_orthogonal R hR v v]

/-- Lagrange identity for the `Fin 3` cross product. -/
theorem lagrange_cross_normSq (a b : Fin 3 → ℝ) :
    euclideanNormSq3 (cross3 a b) =
      euclideanNormSq3 a * euclideanNormSq3 b - (euclideanInner3 a b) ^ 2 := by
  simp [euclideanNormSq3, euclideanInner3, cross3, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
  ring

theorem cross3_normSq_orthogonal_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (a b : Fin 3 → ℝ) :
    euclideanNormSq3 (cross3 (R.mulVec a) (R.mulVec b)) = euclideanNormSq3 (cross3 a b) := by
  rw [lagrange_cross_normSq, lagrange_cross_normSq]
  simp_rw [euclideanNormSq3_mulVec_orthogonal R hR, euclideanInner3_mulVec_orthogonal R hR]

theorem minkowskiSq4_spatialRotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (x : Fin 4 → ℝ) :
    minkowskiSq4 (spatialRotationApply41 R x) = minkowskiSq4 x := by
  dsimp only [spatialRotationApply41]
  rw [minkowskiSq4_chartPoint41, minkowskiSq4_eq_time_plus_spatial]
  simpa using euclideanNormSq3_mulVec_orthogonal R hR (spatialPart41 x)

/-!
## Packaged certificates
-/

structure SpatialRotationLorentzClosure where
  euclidean_inner_rotation_invariant :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R) (u v : Fin 3 → ℝ),
      euclideanInner3 (R.mulVec u) (R.mulVec v) = euclideanInner3 u v
  minkowski_spatial_rotation_invariant :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R) (x : Fin 4 → ℝ),
      minkowskiSq4 (spatialRotationApply41 R x) = minkowskiSq4 x
  cross_normSq_rotation_invariant :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R) (a b : Fin 3 → ℝ),
      euclideanNormSq3 (cross3 (R.mulVec a) (R.mulVec b)) = euclideanNormSq3 (cross3 a b)

noncomputable def spatialRotationLorentzClosureDefault : SpatialRotationLorentzClosure where
  euclidean_inner_rotation_invariant := fun R hR u v => euclideanInner3_mulVec_orthogonal R hR u v
  minkowski_spatial_rotation_invariant := fun R hR x =>
    minkowskiSq4_spatialRotation_invariant R hR x
  cross_normSq_rotation_invariant := fun R hR a b =>
    cross3_normSq_orthogonal_invariant R hR a b

theorem spatial_rotation_lorentz_closure_discharged : Nonempty SpatialRotationLorentzClosure :=
  ⟨spatialRotationLorentzClosureDefault⟩

structure FullLorentzClosure where
  rapidity : RapidityLorentzClosure
  spatial : SpatialRotationLorentzClosure

noncomputable def fullLorentzClosureDefault : FullLorentzClosure :=
  ⟨rapidityLorentzClosureDefault, spatialRotationLorentzClosureDefault⟩

theorem full_lorentz_closure_discharged : Nonempty FullLorentzClosure :=
  ⟨fullLorentzClosureDefault⟩

end Hqiv.Geometry

namespace Hqiv.Physics

open Hqiv.Geometry

/-!
## CMB / greybody sky rotation
-/

/-- Sky rotation `ψ` added to the intrinsic birefringence angle at shell `m`. -/
noncomputable def shellBirefringenceAngleSkyRotated (m : ℕ) (ψ : ℝ) : ℝ :=
  shellBirefringenceAngle m + ψ

/-- **E-mode fraction** after sky rotation: `cos²(2(β+ψ))`. -/
noncomputable def emissionEModeFractionSkyRotated (m : ℕ) (ψ : ℝ) : ℝ :=
  (Real.cos (2 * shellBirefringenceAngleSkyRotated m ψ)) ^ 2

/-- **B-mode fraction** after sky rotation: `sin²(2(β+ψ))`. -/
noncomputable def emissionBModeFractionSkyRotated (m : ℕ) (ψ : ℝ) : ℝ :=
  (Real.sin (2 * shellBirefringenceAngleSkyRotated m ψ)) ^ 2

theorem emissionEMode_plus_BMode_sky_rotated (m : ℕ) (ψ : ℝ) :
    emissionEModeFractionSkyRotated m ψ + emissionBModeFractionSkyRotated m ψ = 1 := by
  unfold emissionEModeFractionSkyRotated emissionBModeFractionSkyRotated
    shellBirefringenceAngleSkyRotated
  have h := Real.sin_sq_add_cos_sq (2 * (shellBirefringenceAngle m + ψ))
  linarith

theorem emissionEModeFractionSkyRotated_zero_psi (m : ℕ) :
    emissionEModeFractionSkyRotated m 0 = emissionEModeFraction m := by
  simp [emissionEModeFractionSkyRotated, emissionEModeFraction, shellBirefringenceAngleSkyRotated]

/-!
## Flyby orbital vector frame
-/

/-- Minimal orbital vector data for frame-rotation discharge. -/
structure OrbitalVectorFrame where
  r : Fin 3 → ℝ
  v : Fin 3 → ℝ

noncomputable def orbitalAngularMomentumSq (f : OrbitalVectorFrame) : ℝ :=
  euclideanNormSq3 (cross3 f.r f.v)

/-- Axis projection scalar `(L·ẑ)² / ‖L‖²`. -/
noncomputable def equatorialFractionFromAxis (L axis : Fin 3 → ℝ) : ℝ :=
  let lSq := euclideanInner3 L L
  if lSq = 0 then 0 else (euclideanInner3 L axis) ^ 2 / lSq

theorem orbitalAngularMomentumSq_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (f : OrbitalVectorFrame) :
    orbitalAngularMomentumSq ⟨R.mulVec f.r, R.mulVec f.v⟩ = orbitalAngularMomentumSq f := by
  dsimp [orbitalAngularMomentumSq]
  simpa using cross3_normSq_orthogonal_invariant R hR f.r f.v

theorem equatorialFractionFromAxis_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (L axis : Fin 3 → ℝ) :
    equatorialFractionFromAxis (R.mulVec L) (R.mulVec axis) = equatorialFractionFromAxis L axis := by
  unfold equatorialFractionFromAxis
  have hL := euclideanInner3_mulVec_orthogonal R hR L L
  have hLa := euclideanInner3_mulVec_orthogonal R hR L axis
  by_cases h : euclideanInner3 L L = 0
  · have hR0 : euclideanInner3 (R.mulVec L) (R.mulVec L) = 0 := by rw [hL, h]
    simp [h, hR0, hLa]
  · simp [h, hLa, hL]

/-!
## O-Maxwell fluid source covariance
-/

theorem hqivVacuumMomentumSource3_mulVec_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ) (_hR : IsOrthogonal3 R)
    (gamma phi dot : ℝ) (gradPhi gradDot : Fin 3 → ℝ) :
    hqivVacuumMomentumSource3 gamma phi dot (R.mulVec gradPhi) (R.mulVec gradDot) =
      R.mulVec (hqivVacuumMomentumSource3 gamma phi dot gradPhi gradDot) := by
  funext k
  dsimp [hqivVacuumMomentumSource3, Matrix.mulVec, dotProduct]
  simp only [Fin.sum_univ_three, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  ring

/-!
## Coronal / longitudinal axis projection
-/

noncomputable def axialScalarProjection (s w : Fin 3 → ℝ) : ℝ :=
  euclideanInner3 s w

theorem axialScalarProjection_mulVec_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (s w : Fin 3 → ℝ) :
    axialScalarProjection (R.mulVec s) (R.mulVec w) = axialScalarProjection s w :=
  euclideanInner3_mulVec_orthogonal R hR s w

end Hqiv.Physics
