import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hqiv.Geometry

open scoped BigOperators

noncomputable section

/-- Squared Euclidean displacement in `ℝ^n` represented as `Fin n → ℝ`. -/
def sqEuclidean (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i - y i) ^ 2

/-- Euclidean displacement magnitude in `ℝ^n` represented as `Fin n → ℝ`. -/
def euclideanDist (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (sqEuclidean x y)

/-- `ℓ¹` displacement in `ℝ^n` represented as `Fin n → ℝ`. -/
def l1Dist (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i - y i|

private lemma sq_sub_le_one_of_abs_sub_le_one {a b : ℝ} (h : |a - b| ≤ 1) :
    (a - b) ^ 2 ≤ 1 := by
  set z : ℝ := |a - b|
  have hz_nonneg : 0 ≤ z := by
    simp [z]
  have hz_le : z ≤ 1 := by
    simpa [z] using h
  have hz_sq : z ^ 2 ≤ 1 := by
    nlinarith
  simpa [z, sq_abs] using hz_sq

private lemma sq_sub_le_four_of_abs_sub_le_two {a b : ℝ} (h : |a - b| ≤ 2) :
    (a - b) ^ 2 ≤ 4 := by
  set z : ℝ := |a - b|
  have hz_nonneg : 0 ≤ z := by
    simp [z]
  have hz_le : z ≤ 2 := by
    simpa [z] using h
  have hz_sq : z ^ 2 ≤ 4 := by
    nlinarith
  simpa [z, sq_abs] using hz_sq

/--
If every coordinate difference is bounded by `1` in absolute value, then the
squared Euclidean displacement is bounded by `n`.
-/
theorem sqEuclidean_le_dim_of_axisDiff_le_one
    (x y : Fin n → ℝ)
    (hAxis : ∀ i : Fin n, |x i - y i| ≤ 1) :
    sqEuclidean x y ≤ n := by
  unfold sqEuclidean
  calc
    ∑ i : Fin n, (x i - y i) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact sq_sub_le_one_of_abs_sub_le_one (hAxis i)
    _ = n := by simp

/--
Coordinate-wise unit bounds imply Euclidean displacement bounded by `√n`.
-/
theorem euclideanDist_le_sqrt_dim_of_axisDiff_le_one
    (x y : Fin n → ℝ)
    (hAxis : ∀ i : Fin n, |x i - y i| ≤ 1) :
    euclideanDist x y ≤ Real.sqrt n := by
  unfold euclideanDist
  exact Real.sqrt_le_sqrt (sqEuclidean_le_dim_of_axisDiff_le_one x y hAxis)

/-- 2D specialization: coordinate-wise unit bounds imply distance at most `√2`. -/
theorem euclideanDist_le_sqrt_two_of_axisDiff_le_one
    (x y : Fin 2 → ℝ)
    (hAxis : ∀ i : Fin 2, |x i - y i| ≤ 1) :
    euclideanDist x y ≤ Real.sqrt 2 := by
  simpa using euclideanDist_le_sqrt_dim_of_axisDiff_le_one x y hAxis

/-- 3D specialization: coordinate-wise unit bounds imply distance at most `√3`. -/
theorem euclideanDist_le_sqrt_three_of_axisDiff_le_one
    (x y : Fin 3 → ℝ)
    (hAxis : ∀ i : Fin 3, |x i - y i| ≤ 1) :
    euclideanDist x y ≤ Real.sqrt 3 := by
  simpa using euclideanDist_le_sqrt_dim_of_axisDiff_le_one x y hAxis

/--
If every coordinate difference is bounded by `2` in absolute value, then the
squared Euclidean displacement is bounded by `4n`.
-/
theorem sqEuclidean_le_four_mul_dim_of_axisDiff_le_two
    (x y : Fin n → ℝ)
    (hAxis : ∀ i : Fin n, |x i - y i| ≤ 2) :
    sqEuclidean x y ≤ 4 * n := by
  unfold sqEuclidean
  calc
    ∑ i : Fin n, (x i - y i) ^ 2 ≤ ∑ _i : Fin n, (4 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact sq_sub_le_four_of_abs_sub_le_two (hAxis i)
    _ = 4 * n := by simp [mul_comm]

/--
Signed per-axis bounds (`|Δ_i| ≤ 2`) imply Euclidean displacement bounded by
`2 * √n`.
-/
theorem euclideanDist_le_two_mul_sqrt_dim_of_axisDiff_le_two
    (x y : Fin n → ℝ)
    (hAxis : ∀ i : Fin n, |x i - y i| ≤ 2) :
    euclideanDist x y ≤ 2 * Real.sqrt n := by
  have hsq : sqEuclidean x y ≤ (4 : ℝ) * n :=
    sqEuclidean_le_four_mul_dim_of_axisDiff_le_two x y hAxis
  calc
    euclideanDist x y = Real.sqrt (sqEuclidean x y) := by rfl
    _ ≤ Real.sqrt ((4 : ℝ) * n) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 4 * Real.sqrt n := by
      rw [Real.sqrt_mul (by positivity) (n : ℝ)]
    _ = 2 * Real.sqrt n := by norm_num

/--
Signed per-axis bounds (`|Δ_i| ≤ 2`) imply `ℓ¹` displacement bounded by `2n`.
This is a conservative worst-case ledger bound.
-/
theorem l1Dist_le_two_mul_dim_of_axisDiff_le_two
    (x y : Fin n → ℝ)
    (hAxis : ∀ i : Fin n, |x i - y i| ≤ 2) :
    l1Dist x y ≤ 2 * n := by
  unfold l1Dist
  calc
    ∑ i : Fin n, |x i - y i| ≤ ∑ _i : Fin n, (2 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hAxis i
    _ = 2 * n := by simp [mul_comm]

end

