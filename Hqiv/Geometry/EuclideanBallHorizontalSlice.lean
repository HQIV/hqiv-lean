import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt

import Hqiv.Geometry.SpatialSliceManifold

/-!
# Horizontal slice of a Euclidean `3`-ball = embedded `2`-ball

In `SpatialSliceEuclidean3`, fix the third coordinate `z`. The intersection of the **closed ball**
`closedBall 0 R` with the affine plane `{ x | x (2 : Fin 3) = z }` is exactly the **image** of the
planar closed ball of radius `√(R² − z²)` under `joinThirdCoordinate z`.

Each horizontal slice of a solid Euclidean ball is thus a lower-dimensional ball (a **disk** in the
slice plane).

**Same `closedBall` as horizon shells:** `SpatialSliceManifold.euclideanHorizonShell r 0` is
`Metric.closedBall 0 (r 1)` on `SpatialSliceEuclidean3`. This file fixes `R` and `z` and identifies
`closedBall 0 R ∩ { x | x (2 : Fin 3) = z }` with a planar `closedBall` of radius `√(R² − z²)` — the
radius bookkeeping one expects when slicing a **3D** Euclidean ball by a coordinate hyperplane.

**Hypotheses:** `0 ≤ R` and `z² ≤ R²` (so `R² − z² ≥ 0`).

**Any coordinate:** swapping the fixed axis with the third coordinate (`Equiv.swap k 2`) induces a
linear isometry of `SpatialSliceEuclidean3`; the same slice identity holds for `{ x | x k = z }` via
`joinCoordinateSlice` / `closedBall_inter_coordPlane_k_eq_image_slice`.
-/

namespace Hqiv.Geometry

noncomputable section

open EuclideanSpace Matrix PiLp LinearIsometryEquiv

/-- Planar `L²` slice (first two coordinates). -/
abbrev SlicePlaneEuclidean2 : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- Permutation of `Fin 3` that moves axis `k` to index `2` (swap with `2` when `k ≠ 2`). -/
def coordPermToThird (k : Fin 3) : Equiv.Perm (Fin 3) :=
  if _ : k = 2 then Equiv.refl _ else Equiv.swap k 2

/-- Linear coordinate permutation (`L²` isometry) used to rotate the slice plane. -/
noncomputable def coordPlaneIsometry (k : Fin 3) : SpatialSliceEuclidean3 ≃ₗᵢ[ℝ] SpatialSliceEuclidean3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (coordPermToThird k)

/-- Embed `(y₀, y₁)` with third coordinate `z` into `SpatialSliceEuclidean3`. -/
noncomputable def joinThirdCoordinate (z : ℝ) (y : SlicePlaneEuclidean2) : SpatialSliceEuclidean3 :=
  WithLp.toLp 2 ![y 0, y 1, z]

/-- Same planar embedding, but with `z` placed on coordinate `k` (via `coordPlaneIsometry`). -/
noncomputable def joinCoordinateSlice (k : Fin 3) (z : ℝ) (y : SlicePlaneEuclidean2) :
    SpatialSliceEuclidean3 :=
  (coordPlaneIsometry k).symm (joinThirdCoordinate z y)

theorem coordPlaneIsometry_apply_third_eq (k : Fin 3) (x : SpatialSliceEuclidean3) :
    coordPlaneIsometry k x (2 : Fin 3) = x k := by
  fin_cases k
  · -- `k = 0`: swap `0` and `2` sends axis `2` to `0`
    dsimp [coordPlaneIsometry, coordPermToThird]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.swap_apply_left,
      Equiv.swap_apply_right]
  · -- `k = 1`
    dsimp [coordPlaneIsometry, coordPermToThird]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.swap_apply_left,
      Equiv.swap_apply_right]
  · -- `k = 2`: identity permutation
    rfl

/-- First two coordinates as a point in the slice plane. -/
noncomputable def planarHead (x : SpatialSliceEuclidean3) : SlicePlaneEuclidean2 :=
  WithLp.toLp 2 ![x 0, x 1]

theorem joinThirdCoordinate_planarHead (x : SpatialSliceEuclidean3) :
    joinThirdCoordinate (x (2 : Fin 3)) (planarHead x) = x := by
  refine PiLp.ext fun i => ?_
  fin_cases i <;> simp [joinThirdCoordinate, planarHead, toLp_apply]

theorem norm_sq_joinThirdCoordinate (z : ℝ) (y : SlicePlaneEuclidean2) :
    ‖joinThirdCoordinate z y‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin 3),
    EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin 2)]
  have hjoin :
      ∑ i : Fin 3, ‖(joinThirdCoordinate z y) i‖ ^ 2 = ‖y 0‖ ^ 2 + ‖y 1‖ ^ 2 + z ^ 2 := by
    rw [Fin.sum_univ_three]
    have hj0 : ‖(joinThirdCoordinate z y) 0‖ ^ 2 = ‖y 0‖ ^ 2 := by
      simp [joinThirdCoordinate, Real.norm_eq_abs, sq_abs]
    have hj1 : ‖(joinThirdCoordinate z y) 1‖ ^ 2 = ‖y 1‖ ^ 2 := by
      simp [joinThirdCoordinate, Real.norm_eq_abs, sq_abs, cons_val_zero, cons_val_one, cons_val_succ,
        empty_val']
    have hj2 : ‖(joinThirdCoordinate z y) 2‖ ^ 2 = z ^ 2 := by
      simp [joinThirdCoordinate, Real.norm_eq_abs, sq_abs, cons_val_zero, cons_val_one, cons_val_succ,
        empty_val']
    rw [hj0, hj1, hj2]
  have hy : ∑ i : Fin 2, ‖y i‖ ^ 2 = ‖y 0‖ ^ 2 + ‖y 1‖ ^ 2 := by
    rw [Fin.sum_univ_two]
  rw [hjoin, hy]

theorem norm_sq_planarHead_add_sq_third (x : SpatialSliceEuclidean3) :
    ‖planarHead x‖ ^ 2 + (x (2 : Fin 3)) ^ 2 = ‖x‖ ^ 2 :=
  calc
    ‖planarHead x‖ ^ 2 + (x (2 : Fin 3)) ^ 2
        = ‖joinThirdCoordinate (x (2 : Fin 3)) (planarHead x)‖ ^ 2 :=
      (norm_sq_joinThirdCoordinate _ _).symm
    _ = ‖x‖ ^ 2 := by rw [joinThirdCoordinate_planarHead]

theorem mem_closedBall_joinThirdCoordinate_iff {R z : ℝ} (hR : 0 ≤ R) (hz : z ^ 2 ≤ R ^ 2)
    (y : SlicePlaneEuclidean2) :
    joinThirdCoordinate z y ∈ Metric.closedBall (0 : SpatialSliceEuclidean3) R ↔
      y ∈ Metric.closedBall (0 : SlicePlaneEuclidean2) (Real.sqrt (R ^ 2 - z ^ 2)) := by
  have hsub : 0 ≤ R ^ 2 - z ^ 2 := sub_nonneg.mpr hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hjoin
    have hj2 : ‖joinThirdCoordinate z y‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 hjoin
    rw [norm_sq_joinThirdCoordinate] at hj2
    have hys : ‖y‖ ^ 2 ≤ R ^ 2 - z ^ 2 := by linarith
    exact (Real.le_sqrt (norm_nonneg y) hsub).2 hys
  · intro hy
    have hys : ‖y‖ ^ 2 ≤ R ^ 2 - z ^ 2 := (Real.le_sqrt (norm_nonneg y) hsub).1 hy
    have hj2 : ‖joinThirdCoordinate z y‖ ^ 2 ≤ R ^ 2 := by
      rw [norm_sq_joinThirdCoordinate]
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) hR).1 hj2

/-- Ball ∩ coordinate plane `{x | x 2 = z}` = embedded planar ball of radius `√(R²−z²)`. -/
theorem closedBall_inter_coordPlane_eq_image_slice (R z : ℝ) (hR : 0 ≤ R) (hz : z ^ 2 ≤ R ^ 2) :
    Metric.closedBall (0 : SpatialSliceEuclidean3) R ∩
        { x : SpatialSliceEuclidean3 | x (2 : Fin 3) = z } =
      Set.image (joinThirdCoordinate z)
        (Metric.closedBall (0 : SlicePlaneEuclidean2) (Real.sqrt (R ^ 2 - z ^ 2))) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxball, hxz⟩
    have eqx :
        joinThirdCoordinate z (planarHead x) = x :=
      (congrArg (fun t => joinThirdCoordinate t (planarHead x)) hxz.symm).trans
        (joinThirdCoordinate_planarHead x)
    refine ⟨planarHead x, ?_, eqx⟩
    exact (mem_closedBall_joinThirdCoordinate_iff hR hz _).1 (eqx.symm ▸ hxball)
  · rintro ⟨y, hyball, rfl⟩
    refine ⟨(mem_closedBall_joinThirdCoordinate_iff hR hz y).2 hyball, rfl⟩

theorem mem_closedBall_joinCoordinateSlice_iff {R z : ℝ} (hR : 0 ≤ R) (hz : z ^ 2 ≤ R ^ 2)
    (k : Fin 3) (y : SlicePlaneEuclidean2) :
    joinCoordinateSlice k z y ∈ Metric.closedBall (0 : SpatialSliceEuclidean3) R ↔
      y ∈ Metric.closedBall (0 : SlicePlaneEuclidean2) (Real.sqrt (R ^ 2 - z ^ 2)) := by
  dsimp [joinCoordinateSlice]
  have hnorm :
      ‖(coordPlaneIsometry k).symm (joinThirdCoordinate z y)‖ = ‖joinThirdCoordinate z y‖ :=
    (coordPlaneIsometry k).symm.norm_map _
  simpa [Metric.mem_closedBall, dist_zero_right, hnorm] using mem_closedBall_joinThirdCoordinate_iff hR hz y

/-- Ball ∩ coordinate plane `{x | x k = z}` = embedded planar ball (any axis `k : Fin 3`). -/
theorem closedBall_inter_coordPlane_k_eq_image_slice (k : Fin 3) (R z : ℝ) (hR : 0 ≤ R) (hz : z ^ 2 ≤ R ^ 2) :
    Metric.closedBall (0 : SpatialSliceEuclidean3) R ∩ { x | x k = z } =
      Set.image (joinCoordinateSlice k z)
        (Metric.closedBall (0 : SlicePlaneEuclidean2) (Real.sqrt (R ^ 2 - z ^ 2))) := by
  let e := coordPlaneIsometry k
  have hball : e ⁻¹' Metric.closedBall (0 : SpatialSliceEuclidean3) R =
      Metric.closedBall (0 : SpatialSliceEuclidean3) R := by
    rw [e.preimage_closedBall]
    congr 1
    exact LinearIsometryEquiv.map_zero e.symm
  have hp : e ⁻¹' { x : SpatialSliceEuclidean3 | x (2 : Fin 3) = z } =
      { x : SpatialSliceEuclidean3 | x k = z } := by
    ext x
    show (e x) (2 : Fin 3) = z ↔ x k = z
    rw [coordPlaneIsometry_apply_third_eq k x]
  have hinv : Metric.closedBall (0 : SpatialSliceEuclidean3) R ∩ { x | x k = z } =
      e ⁻¹' (Metric.closedBall (0 : SpatialSliceEuclidean3) R ∩
        { x : SpatialSliceEuclidean3 | x (2 : Fin 3) = z }) := by
    rw [Set.preimage_inter, hball, hp]
  rw [hinv, closedBall_inter_coordPlane_eq_image_slice R z hR hz]
  ext x
  simp only [Set.mem_preimage, Set.mem_image, joinCoordinateSlice]
  constructor
  · rintro ⟨y, hy, heq⟩
    refine ⟨y, hy, ?_⟩
    rw [heq]
    rw [LinearIsometryEquiv.symm_apply_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    symm
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- Euclidean planar-slice area baseline (continuum `π` model) for radius `√(R²-z²)`. -/
noncomputable def piSliceAreaBaseline (R z : ℝ) : ℝ :=
  Real.pi * (R ^ 2 - z ^ 2)

/-- Gap between an observed/model planar area and the Euclidean `π` baseline. -/
noncomputable def sliceAreaDefect (observedArea R z : ℝ) : ℝ :=
  observedArea - piSliceAreaBaseline R z

theorem piSliceAreaBaseline_eq_pi_mul_sq_sliceRadius {R z : ℝ} (hz : z ^ 2 ≤ R ^ 2) :
    piSliceAreaBaseline R z = Real.pi * (Real.sqrt (R ^ 2 - z ^ 2)) ^ 2 := by
  have hsub : 0 ≤ R ^ 2 - z ^ 2 := sub_nonneg.mpr hz
  rw [piSliceAreaBaseline, Real.sq_sqrt hsub]

theorem piSliceAreaBaseline_nonneg {R z : ℝ} (hz : z ^ 2 ≤ R ^ 2) :
    0 ≤ piSliceAreaBaseline R z := by
  rw [piSliceAreaBaseline]
  exact mul_nonneg Real.pi_nonneg (sub_nonneg.mpr hz)

theorem observedArea_eq_piBaseline_add_sliceAreaDefect (observedArea R z : ℝ) :
    observedArea = piSliceAreaBaseline R z + sliceAreaDefect observedArea R z := by
  rw [sliceAreaDefect]
  ring

theorem sliceAreaDefect_eq_zero_iff (observedArea R z : ℝ) :
    sliceAreaDefect observedArea R z = 0 ↔ observedArea = piSliceAreaBaseline R z := by
  simpa [sliceAreaDefect] using
    (sub_eq_zero : observedArea - piSliceAreaBaseline R z = 0 ↔
      observedArea = piSliceAreaBaseline R z)

/-- Shell-indexed Euclidean slice-area baseline, using radius `r (m+1)`. -/
noncomputable def piSliceAreaBaselineAt (r : ℕ → ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  piSliceAreaBaseline (r (m + 1)) z

/-- Shell-indexed gap between observed/model planar area and the Euclidean `π` baseline. -/
noncomputable def sliceAreaDefectAt (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  sliceAreaDefect (observedArea m z) (r (m + 1)) z

theorem piSliceAreaBaselineAt_eq (r : ℕ → ℝ) (m : ℕ) (z : ℝ) :
    piSliceAreaBaselineAt r m z = Real.pi * ((r (m + 1)) ^ 2 - z ^ 2) := by
  rfl

theorem sliceAreaDefectAt_eq_sub (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    sliceAreaDefectAt r observedArea m z =
      observedArea m z - piSliceAreaBaselineAt r m z := by
  rfl

theorem observedArea_eq_piBaselineAt_add_sliceAreaDefectAt
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    observedArea m z = piSliceAreaBaselineAt r m z + sliceAreaDefectAt r observedArea m z := by
  simpa [sliceAreaDefectAt, piSliceAreaBaselineAt] using
    observedArea_eq_piBaseline_add_sliceAreaDefect (observedArea m z) (r (m + 1)) z

theorem sliceAreaDefectAt_eq_zero_iff
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    sliceAreaDefectAt r observedArea m z = 0 ↔
      observedArea m z = piSliceAreaBaselineAt r m z := by
  rw [sliceAreaDefectAt, piSliceAreaBaselineAt]
  exact sliceAreaDefect_eq_zero_iff _ _ _

theorem piSliceAreaBaselineAt_nonneg
    (r : ℕ → ℝ) (m : ℕ) (z : ℝ) (hz : z ^ 2 ≤ (r (m + 1)) ^ 2) :
    0 ≤ piSliceAreaBaselineAt r m z := by
  simpa [piSliceAreaBaselineAt] using piSliceAreaBaseline_nonneg hz

theorem piSliceAreaBaselineAt_eq_pi_mul_sq_sliceRadius
    (r : ℕ → ℝ) (m : ℕ) (z : ℝ) (hz : z ^ 2 ≤ (r (m + 1)) ^ 2) :
    piSliceAreaBaselineAt r m z =
      Real.pi * (Real.sqrt ((r (m + 1)) ^ 2 - z ^ 2)) ^ 2 := by
  simpa [piSliceAreaBaselineAt] using piSliceAreaBaseline_eq_pi_mul_sq_sliceRadius hz

end

end Hqiv.Geometry
