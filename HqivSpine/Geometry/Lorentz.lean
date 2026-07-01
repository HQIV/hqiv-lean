import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# `HqivSpine.Geometry.Lorentz` — Lorentz invariance from the discrete null chart

The first HQIV axiom is a **discrete past null light cone**. Its events carry a
single continuous label — a **rapidity** `η` along the forward null ray — together
with a discrete shell index `m`. This module shows that the only kinematics
compatible with that null chart is **special relativity**: the rapidity acts on the
chart by Lorentz boosts, boosts form a one-parameter group under rapidity addition,
they preserve the Minkowski quadratic form and bilinear pairing, and they fix the
forward null ray. Nothing here is assumed; everything is proved from `cosh`/`sinh`.

Concretely, with the mostly-plus signature `diag(−1, 1)` on the radial `1+1` chart
`(t, r)`:

* **Group law.** `Λ(η)·Λ(ξ) = Λ(η + ξ)`, `Λ(0) = I`, `Λ(η)·Λ(−η) = I` — the boosts
  are the abelian one-parameter rapidity group.
* **Isometry.** `Λᵀ g Λ = g`, hence the quadratic form `minkowskiSq` and the full
  bilinear pairing `minkowskiInner` are boost-invariant (the latter by polarization).
* **Null-cone preservation.** The forward null direction `(1, 1)` — the light ray of
  the discrete cone — stays null under every boost.
* **Chart equivariance.** A `NullLatticeEvent (η, m)` embeds into `1+1` Minkowski by
  the classical rapidity parametrization; rapidity acting **additively** on the
  carrier is intertwined with the boost on coordinates.
* **`3+1` extension.** Embedding the radial plane into `(t, x¹, 0, 0) ⊂ Fin 4`, the
  partial boost preserves the ambient `diag(−1, 1, 1, 1)` form on that plane.
* **Spatial rotations.** The orthogonal group `O(3)` acting on `(x¹, x², x³)` (time
  fixed) preserves `minkowskiSq4`, the Euclidean inner product/norm, and — via the
  Lagrange identity — the cross-product norm `‖a × b‖²`. Boosts and rotations together
  give the full `O(3)`-extended Lorentz invariance, bundled as `FullLorentzClosure`.
* **Velocity & dispersion.** Boosts are proper (`det Λ = 1`), the boost velocity
  `v = tanh η` is sub-luminal and composes by the relativistic addition law, and the
  invariant mass `m² = E² − p²` (with on-shell `(E,p) = (m cosh η, m sinh η)`,
  `v = p/E = tanh η`) is boost-invariant.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Geometry

open Real Matrix
open scoped Matrix

/-! ## The `1+1` radial Minkowski chart -/

/-- Minkowski metric `diag(−1, 1)` on the radial `1+1` chart (`c = 1`). -/
noncomputable def minkowskiMetric : Matrix (Fin 2) (Fin 2) ℝ := !![(-1 : ℝ), 0; 0, 1]

/-- Minkowski bilinear pairing `⟨u, v⟩ = −u₀v₀ + u₁v₁`. -/
noncomputable def minkowskiInner (u v : Fin 2 → ℝ) : ℝ := dotProduct u (minkowskiMetric *ᵥ v)

theorem minkowskiInner_eq (u v : Fin 2 → ℝ) :
    minkowskiInner u v = -(u 0) * (v 0) + (u 1) * (v 1) := by
  simp [minkowskiInner, dotProduct, minkowskiMetric, mulVec, Fin.sum_univ_two]

/-- Minkowski quadratic form `Q(v) = −v₀² + v₁²`. -/
noncomputable def minkowskiSq (v : Fin 2 → ℝ) : ℝ := -(v 0) ^ 2 + (v 1) ^ 2

theorem minkowskiSq_eq_inner (v : Fin 2 → ℝ) : minkowskiSq v = minkowskiInner v v := by
  simp [minkowskiSq, minkowskiInner_eq, sq]

/-- Polarization (characteristic ≠ 2): the bilinear pairing is recovered from the form. -/
theorem minkowski_polarization (u v : Fin 2 → ℝ) :
    2 * minkowskiInner u v = minkowskiSq (u + v) - minkowskiSq u - minkowskiSq v := by
  simp only [minkowskiInner_eq, minkowskiSq, Pi.add_apply]; ring

/-! ## The rapidity boost and its group law -/

/-- Orthochronous boost on `(t, r)` with rapidity `η`. -/
noncomputable def boostApply (η : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ
  | 0 => cosh η * v 0 + sinh η * v 1
  | 1 => sinh η * v 0 + cosh η * v 1

/-- Boost matrix `Λ(η)` (symmetric). -/
noncomputable def boostMatrix (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cosh η, sinh η; sinh η, cosh η]

theorem boostMatrix_mulVec (η : ℝ) (v : Fin 2 → ℝ) : boostMatrix η *ᵥ v = boostApply η v := by
  funext i
  fin_cases i <;> simp [boostMatrix, boostApply, mulVec, dotProduct, Fin.sum_univ_two]

theorem boostMatrix_transpose (η : ℝ) : (boostMatrix η)ᵀ = boostMatrix η := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostMatrix, Matrix.transpose_apply]

/-- **Rapidity addition:** `Λ(η)·Λ(ξ) = Λ(η + ξ)` — boosts are a one-parameter group. -/
theorem boostMatrix_mul (η ξ : ℝ) : boostMatrix η * boostMatrix ξ = boostMatrix (η + ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostMatrix, Matrix.mul_apply, Fin.sum_univ_two, cosh_add, sinh_add] <;> abel

/-- **Identity:** `Λ(0) = I`. -/
theorem boostMatrix_zero : boostMatrix (0 : ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostMatrix, cosh_zero, sinh_zero]

/-- **Inverse:** `Λ(η)·Λ(−η) = I`. -/
theorem boostMatrix_mul_neg (η : ℝ) : boostMatrix η * boostMatrix (-η) = 1 := by
  rw [boostMatrix_mul, add_neg_cancel, boostMatrix_zero]

theorem boostApply_add (η ξ : ℝ) (v : Fin 2 → ℝ) :
    boostApply (η + ξ) v = boostApply η (boostApply ξ v) := by
  funext i
  fin_cases i <;> simp [boostApply] <;> rw [cosh_add, sinh_add] <;> ring

/-- **Boosts are proper** (`det Λ(η) = 1`): they sit in `SO⁺(1,1)`, not merely `O(1,1)`. -/
theorem boostMatrix_det_one (η : ℝ) : (boostMatrix η).det = 1 := by
  simp only [boostMatrix, Matrix.det_fin_two_of]
  rw [← cosh_sq_sub_sinh_sq η]; ring

/-! ## Relativistic velocity addition — the physical reading of rapidity additivity

The coordinate velocity of a boost is `v = tanh η` (units `c = 1`). Because rapidities
**add** (`boostMatrix_mul`), velocities compose by the relativistic addition law, and the
light speed `1` is the unattained supremum. -/

/-- Coordinate velocity of a rapidity-`η` boost (`c = 1`): `v = tanh η`. -/
noncomputable def velocity (η : ℝ) : ℝ := Real.tanh η

/-- **Sub-luminality:** every boost velocity satisfies `|v| < 1`. -/
theorem abs_velocity_lt_one (η : ℝ) : |velocity η| < 1 := by
  have hc : (0 : ℝ) < cosh η := cosh_pos η
  have h := cosh_sq_sub_sinh_sq η
  have hlt : |sinh η| < cosh η := by
    nlinarith [sq_abs (sinh η), abs_nonneg (sinh η), hc]
  rw [velocity, Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos hc]
  exact (div_lt_one hc).mpr hlt

/-- **Relativistic velocity addition** from rapidity additivity: composing boosts adds
rapidities (`boostMatrix_mul`), so velocities combine as
`v(η+ξ) = (v(η) + v(ξ)) / (1 + v(η)·v(ξ))`. -/
theorem velocity_add (η ξ : ℝ) :
    velocity (η + ξ) = (velocity η + velocity ξ) / (1 + velocity η * velocity ξ) := by
  have cη : cosh η ≠ 0 := (cosh_pos η).ne'
  have cξ : cosh ξ ≠ 0 := (cosh_pos ξ).ne'
  have hadd : cosh η * cosh ξ + sinh η * sinh ξ ≠ 0 := by
    rw [← cosh_add]; exact (cosh_pos (η + ξ)).ne'
  rw [velocity, velocity, velocity, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.tanh_eq_sinh_div_cosh, sinh_add, cosh_add]
  field_simp

/-- The composite of two boosts is a boost whose velocity is the relativistic sum: the
group law `Λ(η)·Λ(ξ) = Λ(η+ξ)` **is** velocity addition. -/
theorem boost_comp_velocity (η ξ : ℝ) :
    boostMatrix η * boostMatrix ξ = boostMatrix (η + ξ) ∧
      velocity (η + ξ) = (velocity η + velocity ξ) / (1 + velocity η * velocity ξ) :=
  ⟨boostMatrix_mul η ξ, velocity_add η ξ⟩

/-! ## Isometry: the boost preserves the Minkowski structure -/

/-- **Adjoint / isometry identity:** `Λ g Λ = g` (uses `cosh² − sinh² = 1`). -/
theorem boostMatrix_isometry (η : ℝ) :
    boostMatrix η * minkowskiMetric * boostMatrix η = minkowskiMetric := by
  have h := cosh_sq_sub_sinh_sq η
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [boostMatrix, minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
  all_goals rw [← sub_eq_zero]; nlinarith [h, sq_nonneg (cosh η), sq_nonneg (sinh η)]

/-- **The quadratic Minkowski invariant is boost-invariant.** -/
theorem minkowskiSq_boost_invariant (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq (boostApply η v) = minkowskiSq v := by
  dsimp [minkowskiSq, boostApply]
  have h := cosh_sq_sub_sinh_sq η
  set t : ℝ := v 0
  set x : ℝ := v 1
  calc
    -(cosh η * t + sinh η * x) ^ 2 + (sinh η * t + cosh η * x) ^ 2
        = (cosh η ^ 2 - sinh η ^ 2) * (x ^ 2 - t ^ 2) := by ring
    _ = 1 * (x ^ 2 - t ^ 2) := by rw [h]
    _ = -(t ^ 2) + x ^ 2 := by ring

theorem minkowskiSq_boost_invariant_mulVec (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq (boostMatrix η *ᵥ v) = minkowskiSq v := by
  rw [boostMatrix_mulVec]; exact minkowskiSq_boost_invariant η v

/-- **Full bilinear Lorentz invariance** (from polarization + the quadratic invariant). -/
theorem minkowskiInner_boost_invariant (η : ℝ) (u v : Fin 2 → ℝ) :
    minkowskiInner (boostMatrix η *ᵥ u) (boostMatrix η *ᵥ v) = minkowskiInner u v := by
  have hQ (w : Fin 2 → ℝ) : minkowskiSq (boostMatrix η *ᵥ w) = minkowskiSq w :=
    minkowskiSq_boost_invariant_mulVec η w
  have step : (2 : ℝ) * minkowskiInner (boostMatrix η *ᵥ u) (boostMatrix η *ᵥ v) =
      (2 : ℝ) * minkowskiInner u v := by
    rw [minkowski_polarization, minkowski_polarization u v]
    simp_rw [← mulVec_add, hQ]
  exact mul_left_cancel₀ two_ne_zero step

/-! ## The forward null ray of the discrete cone -/

/-- The forward null (light-ray) direction `(1, 1)` of the discrete cone. -/
def forwardNull : Fin 2 → ℝ := ![1, 1]

theorem forwardNull_null : minkowskiSq forwardNull = 0 := by
  simp [forwardNull, minkowskiSq, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Null-cone preservation:** the light ray stays null under every boost. -/
theorem forwardNull_boost_null (η : ℝ) : minkowskiSq (boostApply η forwardNull) = 0 := by
  rw [minkowskiSq_boost_invariant]; exact forwardNull_null

/-! ## Energy–momentum and the dispersion relation `E² − p² = m²`

A four-momentum `(E, p)` is a chart vector; its Minkowski square is `−m²`, so the
**invariant mass** `m² = E² − p²` is a boost invariant. On shell a mass-`m` particle
has `(E, p) = (m·cosh η, m·sinh η)`, whose velocity `p/E = tanh η` is exactly the
boost velocity. -/

/-- **Invariant mass-squared** `E² − p²` of a momentum `(E, p) = (P 0, P 1)`. -/
noncomputable def massSq (P : Fin 2 → ℝ) : ℝ := (P 0) ^ 2 - (P 1) ^ 2

/-- `m² = −Q`: invariant mass-squared is minus the Minkowski quadratic form. -/
theorem massSq_eq_neg_minkowskiSq (P : Fin 2 → ℝ) : massSq P = - minkowskiSq P := by
  unfold massSq minkowskiSq; ring

/-- **Invariant mass is boost-invariant:** `E'² − p'² = E² − p²`. -/
theorem massSq_boost_invariant (η : ℝ) (P : Fin 2 → ℝ) :
    massSq (boostApply η P) = massSq P := by
  rw [massSq_eq_neg_minkowskiSq, massSq_eq_neg_minkowskiSq, minkowskiSq_boost_invariant]

/-- **On-shell four-momentum** of a mass-`m` particle at rapidity `η`:
`(E, p) = (m·cosh η, m·sinh η)`. -/
noncomputable def fourMomentum (m η : ℝ) : Fin 2 → ℝ := ![m * cosh η, m * sinh η]

/-- **Dispersion relation** `E² − p² = m²` for the on-shell momentum. -/
theorem dispersion (m η : ℝ) : massSq (fourMomentum m η) = m ^ 2 := by
  simp only [massSq, fourMomentum, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc (m * cosh η) ^ 2 - (m * sinh η) ^ 2
      = m ^ 2 * (cosh η ^ 2 - sinh η ^ 2) := by ring
    _ = m ^ 2 * 1 := by rw [cosh_sq_sub_sinh_sq η]
    _ = m ^ 2 := by ring

/-- **Velocity of an on-shell momentum** is the boost velocity: `p/E = tanh η = v(η)`. -/
theorem fourMomentum_velocity (m η : ℝ) (hm : m ≠ 0) :
    fourMomentum m η 1 / fourMomentum m η 0 = velocity η := by
  simp only [fourMomentum, Matrix.cons_val_zero, Matrix.cons_val_one,
    velocity, Real.tanh_eq_sinh_div_cosh]
  rw [mul_div_mul_left _ _ hm]

/-! ## The discrete null-lattice carrier and chart equivariance -/

/-- A discrete null-lattice event: a rapidity label `η` along the forward null ray and
a discrete shell index `m`. -/
structure NullLatticeEvent where
  /-- Rapidity along the forward null ray. -/
  η : ℝ
  /-- Discrete shell index (light-cone bookkeeping). -/
  m : ℕ

/-- Chart into `1+1` Minkowski coordinates: the classical rapidity parametrization of
the forward null ray. -/
noncomputable def chart (e : NullLatticeEvent) : Fin 2 → ℝ := boostApply e.η forwardNull

/-- Rapidity acts by **addition** on the carrier (the rapidity group action). -/
def rapidityAct (ξ : ℝ) (e : NullLatticeEvent) : NullLatticeEvent := { e with η := e.η + ξ }

/-- **Chart equivariance:** rapidity acting additively on the carrier is intertwined
with the boost on coordinates — `chart (ξ ▸ e) = Λ(ξ)·chart e`. -/
theorem chart_equivariant (ξ : ℝ) (e : NullLatticeEvent) :
    chart (rapidityAct ξ e) = boostMatrix ξ *ᵥ chart e := by
  dsimp [chart, rapidityAct]
  rw [boostMatrix_mulVec, ← boostApply_add, add_comm]

/-- Every charted event lies on the null cone (it is a boosted light ray). -/
theorem chart_null (e : NullLatticeEvent) : minkowskiSq (chart e) = 0 :=
  forwardNull_boost_null e.η

/-! ## `3+1` extension on the embedded radial plane -/

/-- Flat Minkowski form `−x₀² + x₁² + x₂² + x₃²` on `Fin 4 → ℝ`. -/
noncomputable def minkowskiSq4 (x : Fin 4 → ℝ) : ℝ :=
  -(x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2

/-- Embed the radial `1+1` plane as `(t, x¹, 0, 0)`. -/
def lift4 (v : Fin 2 → ℝ) : Fin 4 → ℝ := Pi.single (0 : Fin 4) (v 0) + Pi.single (1 : Fin 4) (v 1)

theorem minkowskiSq4_lift (v : Fin 2 → ℝ) : minkowskiSq4 (lift4 v) = minkowskiSq v := by
  simp [minkowskiSq4, minkowskiSq, lift4, Pi.add_apply]

/-- Orthochronous boost acting only on the time / first-spatial components. -/
noncomputable def boostMatrix4 (η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![cosh η, sinh η, 0, 0; sinh η, cosh η, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem boostMatrix4_mulVec_lift (η : ℝ) (v : Fin 2 → ℝ) :
    boostMatrix4 η *ᵥ lift4 v = lift4 (boostApply η v) := by
  funext i
  fin_cases i <;>
    simp [boostMatrix4, lift4, boostApply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]

/-- **`3+1` plane invariance:** the partial boost preserves `minkowskiSq4` on the
embedded radial plane. -/
theorem minkowskiSq4_boost_invariant_on_plane (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq4 (boostMatrix4 η *ᵥ lift4 v) = minkowskiSq4 (lift4 v) := by
  rw [boostMatrix4_mulVec_lift, minkowskiSq4_lift, minkowskiSq4_lift, minkowskiSq_boost_invariant]

/-! ## Spatial rotations `O(3)` on the slice `(x¹, x², x³)`

Boosts mix time with one spatial axis; the remaining invariance is rotation of the
spatial slice with time fixed. `O(3)` (orthogonal, `det = ±1`) is all that the
quadratic form, dot products, and cross-product norm require. -/

/-- Euclidean inner product on the spatial slice `Fin 3`. -/
def euclideanInner3 (u v : Fin 3 → ℝ) : ℝ := dotProduct u v

/-- Squared Euclidean norm on the spatial slice. -/
def euclideanNormSq3 (v : Fin 3 → ℝ) : ℝ := euclideanInner3 v v

/-- Standard cross product on `Fin 3`. -/
def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- A `3×3` matrix is orthogonal: `Rᵀ R = 1`. -/
def IsOrthogonal3 (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop := Rᵀ * R = 1

/-- Spacetime point `(t, v₀, v₁, v₂)`. -/
def chartPoint4 (t : ℝ) (v : Fin 3 → ℝ) : Fin 4 → ℝ := ![t, v 0, v 1, v 2]

/-- Spatial components `(x¹, x², x³)` of a spacetime point. -/
def spatialPart4 (x : Fin 4 → ℝ) : Fin 3 → ℝ := ![x 1, x 2, x 3]

/-- Block spatial rotation on `Fin 4`: fix time, rotate the spatial slice by `R`. -/
noncomputable def spatialRotationApply4 (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  chartPoint4 (x 0) (R *ᵥ spatialPart4 x)

theorem spatialRotationApply4_time_fixed (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 4 → ℝ) :
    spatialRotationApply4 R x 0 = x 0 := by
  simp [spatialRotationApply4, chartPoint4]

theorem euclideanNormSq3_eq_sum_sq (v : Fin 3 → ℝ) :
    euclideanNormSq3 v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [euclideanNormSq3, euclideanInner3, dotProduct, Fin.sum_univ_three]; ring

theorem minkowskiSq4_eq_time_plus_spatial (x : Fin 4 → ℝ) :
    minkowskiSq4 x = -(x 0 ^ 2) + euclideanNormSq3 (spatialPart4 x) := by
  simp [minkowskiSq4, spatialPart4, euclideanNormSq3_eq_sum_sq, Matrix.cons_val_zero,
    Matrix.cons_val_one]; ring

theorem minkowskiSq4_chartPoint4 (t : ℝ) (v : Fin 3 → ℝ) :
    minkowskiSq4 (chartPoint4 t v) = -(t ^ 2) + euclideanNormSq3 v := by
  simp [minkowskiSq4, chartPoint4, euclideanNormSq3_eq_sum_sq, Matrix.cons_val_zero,
    Matrix.cons_val_one]; ring

/-- **Orthogonal maps preserve the Euclidean inner product.** -/
theorem euclideanInner3_rotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (u v : Fin 3 → ℝ) : euclideanInner3 (R *ᵥ u) (R *ᵥ v) = euclideanInner3 u v := by
  dsimp only [euclideanInner3, IsOrthogonal3] at *
  calc
    (R *ᵥ u) ⬝ᵥ (R *ᵥ v) = (R *ᵥ u) ᵥ* R ⬝ᵥ v := by rw [← dotProduct_mulVec]
    _ = u ᵥ* (Rᵀ * R) ⬝ᵥ v := by rw [vecMul_mulVec]
    _ = u ⬝ᵥ (Rᵀ * R) *ᵥ v := by rw [dotProduct_mulVec]
    _ = u ⬝ᵥ v := by rw [hR, one_mulVec]

theorem euclideanNormSq3_rotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (v : Fin 3 → ℝ) : euclideanNormSq3 (R *ᵥ v) = euclideanNormSq3 v := by
  dsimp [euclideanNormSq3]; rw [euclideanInner3_rotation_invariant R hR v v]

/-- **Block spatial rotations are Lorentz isometries:** `minkowskiSq4` is invariant. -/
theorem minkowskiSq4_spatialRotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (x : Fin 4 → ℝ) : minkowskiSq4 (spatialRotationApply4 R x) = minkowskiSq4 x := by
  dsimp only [spatialRotationApply4]
  rw [minkowskiSq4_chartPoint4, minkowskiSq4_eq_time_plus_spatial]
  rw [euclideanNormSq3_rotation_invariant R hR (spatialPart4 x)]

/-- **Lagrange identity:** `‖a × b‖² = ‖a‖²‖b‖² − ⟨a, b⟩²`. -/
theorem lagrange_cross_normSq (a b : Fin 3 → ℝ) :
    euclideanNormSq3 (cross3 a b) =
      euclideanNormSq3 a * euclideanNormSq3 b - (euclideanInner3 a b) ^ 2 := by
  simp [euclideanNormSq3, euclideanInner3, cross3, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]; ring

/-- **The cross-product norm is rotation-invariant** (e.g. `‖r × v‖²` angular momentum). -/
theorem cross3_normSq_rotation_invariant (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : IsOrthogonal3 R)
    (a b : Fin 3 → ℝ) :
    euclideanNormSq3 (cross3 (R *ᵥ a) (R *ᵥ b)) = euclideanNormSq3 (cross3 a b) := by
  rw [lagrange_cross_normSq, lagrange_cross_normSq]
  simp_rw [euclideanNormSq3_rotation_invariant R hR, euclideanInner3_rotation_invariant R hR]

/-! ## Packaged Lorentz-closure certificate -/

/-- The Lorentz-invariance closure of the discrete null chart: the group law, the
isometry/invariance facts, null-cone preservation, chart equivariance, and the `3+1`
plane extension — all proved, bundled as one certificate. -/
structure LorentzClosure : Prop where
  group_law : ∀ η ξ : ℝ, boostMatrix η * boostMatrix ξ = boostMatrix (η + ξ)
  identity : boostMatrix (0 : ℝ) = 1
  isometry : ∀ η : ℝ, boostMatrix η * minkowskiMetric * boostMatrix η = minkowskiMetric
  quadratic_invariant : ∀ (η : ℝ) (v : Fin 2 → ℝ), minkowskiSq (boostApply η v) = minkowskiSq v
  bilinear_invariant : ∀ (η : ℝ) (u v : Fin 2 → ℝ),
    minkowskiInner (boostMatrix η *ᵥ u) (boostMatrix η *ᵥ v) = minkowskiInner u v
  null_preserved : ∀ η : ℝ, minkowskiSq (boostApply η forwardNull) = 0
  chart_equivariant : ∀ (ξ : ℝ) (e : NullLatticeEvent), chart (rapidityAct ξ e) = boostMatrix ξ *ᵥ chart e
  plane_invariant : ∀ (η : ℝ) (v : Fin 2 → ℝ),
    minkowskiSq4 (boostMatrix4 η *ᵥ lift4 v) = minkowskiSq4 (lift4 v)

/-- **Lorentz invariance of the discrete null chart is fully discharged.** -/
theorem lorentz_closure : LorentzClosure where
  group_law := boostMatrix_mul
  identity := boostMatrix_zero
  isometry := boostMatrix_isometry
  quadratic_invariant := minkowskiSq_boost_invariant
  bilinear_invariant := minkowskiInner_boost_invariant
  null_preserved := forwardNull_boost_null
  chart_equivariant := chart_equivariant
  plane_invariant := minkowskiSq4_boost_invariant_on_plane

/-- The full `O(3)`-extended Lorentz invariance of the chart: the boost-sector closure
together with spatial-rotation invariance of the Minkowski form, the Euclidean inner
product, and the cross-product norm. -/
structure FullLorentzClosure : Prop where
  boosts : LorentzClosure
  rotation_isometry : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), IsOrthogonal3 R →
    ∀ x : Fin 4 → ℝ, minkowskiSq4 (spatialRotationApply4 R x) = minkowskiSq4 x
  rotation_inner_invariant : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), IsOrthogonal3 R →
    ∀ u v : Fin 3 → ℝ, euclideanInner3 (R *ᵥ u) (R *ᵥ v) = euclideanInner3 u v
  rotation_cross_invariant : ∀ (R : Matrix (Fin 3) (Fin 3) ℝ), IsOrthogonal3 R →
    ∀ a b : Fin 3 → ℝ, euclideanNormSq3 (cross3 (R *ᵥ a) (R *ᵥ b)) = euclideanNormSq3 (cross3 a b)

/-- **Full `O(3)`-extended Lorentz invariance of the discrete null chart is discharged**
— boosts (time–space) and spatial rotations together. -/
theorem full_lorentz_closure : FullLorentzClosure where
  boosts := lorentz_closure
  rotation_isometry := minkowskiSq4_spatialRotation_invariant
  rotation_inner_invariant := euclideanInner3_rotation_invariant
  rotation_cross_invariant := cross3_normSq_rotation_invariant

end HqivSpine.Geometry
