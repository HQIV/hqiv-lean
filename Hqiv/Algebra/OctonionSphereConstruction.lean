import Hqiv.Algebra.OctonionBasics

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic.Ring

/-!
# Octonion sphere shell, 8-ball volume, and surface proxy (ℝ⁸ ≃ 𝕆 coordinates)

Work in the standard identification `ℝ⁸ ≃ Fin 8 → ℝ` used by `Hqiv.Algebra.OctonionVec` (Fano-plane
matrix model in `OctonionBasics`). The **integer octonion lattice** is `Fin 8 → ℤ` embedded in
`EuclideanSpace ℝ (Fin 8)` via `PiLp`; every `m : ℕ` is a squared Euclidean norm on this lattice
by Lagrange’s four-squares theorem (padding with zeros).

**Continuous proxies** (ambient Lebesgue measure on `ℝ⁸`): the closed 8-ball volume and the classical
`(n−1)`-sphere surface area in `ℝⁿ` satisfy `A₇ = dV₈/dr` for `V₈(r) ∝ r⁸`, `A₇(r) ∝ r⁷`. We relate
`V₈` to `MeasureTheory.volume (Metric.closedBall 0 r)` via `EuclideanSpace.volume_closedBall`.

**Shell step `m ↦ m+1` (continuous layer):** integer shells realized at radii `√m` nest:
`closedBall(0,√m) ⊆ closedBall(0,√(m+1))`, so Lebesgue mass and the polynomial proxies `V₈`, `A₇`
increase with `m`. This is the formal “surface extends” step for the **ambient** model; reading it as
encoding **modal** (Fourier-mode / factorization) **history** still requires the separate arithmetic
dictionary (`Ω`, Fano splits, etc.).

**Not formalized here** (roadmap / narrative): Jacobi’s divisor formula for representation numbers
`r₈(m)`, Fourier-axis selection at `π/(2k)`, and tomographic score functions — see
`AGENTS/archive/OCTONION_SPHERE_PATCH.md`.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory MeasureTheory.Measure Metric WithLp InnerProductSpace
open Fintype Finset PiLp

-- Do not `open Real`: it exposes `Real.volume_closedBall` (1D), which clashes with name resolution for
-- `EuclideanSpace` (type vs namespace) in dot-notation.

namespace Hqiv.Algebra

/-- Euclidean 8-space (standard `l²` inner product), used for `‖·‖` and Lebesgue balls. -/
abbrev O8 := EuclideanSpace ℝ (Fin 8)

/-- Embed integer “octonion lattice” vectors into `O8` (`PiLp 2`). -/
noncomputable def intLatticeToO8 (z : Fin 8 → ℤ) : O8 :=
  toLp 2 (fun i : Fin 8 => (z i : ℝ))

theorem intLatticeToO8_apply (z : Fin 8 → ℤ) (i : Fin 8) :
    intLatticeToO8 z i = (z i : ℝ) := by
  simp [intLatticeToO8, toLp_apply]

/-- Squared Euclidean norm on `O8` (equals `∑ xᵢ²`). -/
noncomputable def o8normSq (x : O8) : ℝ :=
  ‖x‖ ^ 2

theorem o8normSq_eq_sum_sq (x : O8) : o8normSq x = ∑ i : Fin 8, x i ^ 2 := by
  simp only [o8normSq, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- Pad a four-square representation into `Fin 8 → ℕ` (last four indices zero). -/
def embedNatFour (a b c d : ℕ) : Fin 8 → ℕ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 0
  | ⟨7, _⟩ => 0

theorem sum_sq_embedNatFour (a b c d : ℕ) :
    ∑ i : Fin 8, (embedNatFour a b c d i : ℝ) ^ 2 =
      (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 + (d : ℝ) ^ 2 := by
  have h0 : embedNatFour a b c d (0 : Fin 8) = a := rfl
  have h1 : embedNatFour a b c d 1 = b := rfl
  have h2 : embedNatFour a b c d 2 = c := rfl
  have h3 : embedNatFour a b c d 3 = d := rfl
  have h4 : embedNatFour a b c d 4 = 0 := rfl
  have h5 : embedNatFour a b c d 5 = 0 := rfl
  have h6 : embedNatFour a b c d 6 = 0 := rfl
  have h7 : embedNatFour a b c d 7 = 0 := rfl
  rw [Fin.sum_univ_eight, h0, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- Every natural is a squared Euclidean norm of some **integer** lattice point in `ℝ⁸`. -/
theorem exists_int_lattice_o8_norm_sq (m : ℕ) :
    ∃ z : Fin 8 → ℤ, o8normSq (intLatticeToO8 z) = (m : ℝ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  refine ⟨fun i => (embedNatFour a b c d i : ℤ), ?_⟩
  have hsq : ∑ i : Fin 8, (embedNatFour a b c d i : ℝ) ^ 2 = (m : ℝ) := by
    rw [sum_sq_embedNatFour]
    simp_rw [← Nat.cast_pow, ← Nat.cast_add, h]
  rw [o8normSq_eq_sum_sq]
  have hpt : ∀ i : Fin 8,
      intLatticeToO8 (fun i => (embedNatFour a b c d i : ℤ)) i = (embedNatFour a b c d i : ℝ) := by
    intro i
    simp [intLatticeToO8_apply, Int.cast_natCast]
  simp_rw [hpt]
  exact hsq

/-! ## Volume of the closed 8-ball and the `π⁴/24`, `π⁴/3` closed forms -/

/-- Lebesgue mass of the **closed** radius-`r` ball in `ℝ⁸`, as a real scalar `π⁴/24 * r⁸`. -/
theorem volume_closedBall_o8_eq (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : O8) r)).toReal = Real.pi ^ 4 / 24 * r ^ 8 := by
  have hk : Module.finrank ℝ O8 = 2 * 4 := by
    rw [finrank_euclideanSpace_fin (n := 8)]
  have hvol := volume_closedBall_of_dim_even (E := O8) hk (0 : O8) r
  rw [hvol]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hr, ENNReal.toReal_ofReal (pow_nonneg hr _),
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi ^ (4 : ℕ) / Nat.factorial 4 by positivity)]
  simp only [Nat.factorial]
  ring

/-- Classical 8-ball volume proxy `V₈(r) = π⁴/24 · r⁸`. -/
noncomputable def continuousBallVolume8 (r : ℝ) : ℝ :=
  Real.pi ^ 4 / 24 * r ^ 8

/-- Classical 7-sphere surface-area proxy in `ℝ⁸`: `A₇(r) = π⁴/3 · r⁷` (derivative of `V₈`). -/
noncomputable def continuousSphereArea7 (r : ℝ) : ℝ :=
  Real.pi ^ 4 / 3 * r ^ 7

theorem deriv_continuousBallVolume8 (r : ℝ) :
    deriv continuousBallVolume8 r = continuousSphereArea7 r := by
  unfold continuousBallVolume8 continuousSphereArea7
  rw [deriv_const_mul (Real.pi ^ 4 / 24) (DifferentiableAt.pow differentiableAt_id 8)]
  simp_rw [deriv_pow_field (𝕜 := ℝ) (n := 8)]
  ring

/-! ## Nested radii `√m` for shell `m → m+1` (nested balls, monotone `V₈` and `A₇`) -/

theorem real_sqrt_cast_le_sqrt_cast_succ (m : ℕ) :
    Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
  rw [← Nat.cast_succ]
  exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_succ m))

theorem real_sqrt_cast_lt_sqrt_cast_succ (m : ℕ) :
    Real.sqrt (m : ℝ) < Real.sqrt ((m : ℝ) + 1) := by
  rw [← Nat.cast_succ]
  refine Real.sqrt_lt_sqrt (Nat.cast_nonneg m) ?_
  exact_mod_cast Nat.lt_succ_self m

theorem closedBall_o8_sqrt_subset_sqrt_succ (m : ℕ) :
    Metric.closedBall (0 : O8) (Real.sqrt (m : ℝ)) ⊆
      Metric.closedBall (0 : O8) (Real.sqrt ((m : ℝ) + 1)) :=
  Metric.closedBall_subset_closedBall (real_sqrt_cast_le_sqrt_cast_succ m)

theorem volume_closedBall_o8_sqrt_le_sqrt_succ (m : ℕ) :
    volume (Metric.closedBall (0 : O8) (Real.sqrt (m : ℝ))) ≤
      volume (Metric.closedBall (0 : O8) (Real.sqrt ((m : ℝ) + 1))) :=
  measure_mono (closedBall_o8_sqrt_subset_sqrt_succ m)

theorem continuousBallVolume8_sqrt_le_sqrt_succ (m : ℕ) :
    continuousBallVolume8 (Real.sqrt (m : ℝ)) ≤ continuousBallVolume8 (Real.sqrt ((m : ℝ) + 1)) := by
  unfold continuousBallVolume8
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (real_sqrt_cast_le_sqrt_cast_succ m) 8

theorem continuousSphereArea7_sqrt_lt_sqrt_succ (m : ℕ) :
    continuousSphereArea7 (Real.sqrt (m : ℝ)) < continuousSphereArea7 (Real.sqrt ((m : ℝ) + 1)) := by
  unfold continuousSphereArea7
  have h7 : (Real.sqrt (m : ℝ)) ^ 7 < (Real.sqrt ((m : ℝ) + 1)) ^ 7 :=
    pow_lt_pow_left₀ (real_sqrt_cast_lt_sqrt_cast_succ m) (Real.sqrt_nonneg _) (by norm_num : (7 : ℕ) ≠ 0)
  have hpos : 0 < Real.pi ^ 4 / 3 := by positivity
  exact mul_lt_mul_of_pos_left h7 hpos

/-! ## Example shell `m = 143` (address vector from four-squares padding) -/

theorem example_143_lattice_norm :
    o8normSq (intLatticeToO8 (fun i : Fin 8 =>
      (embedNatFour 9 7 3 2 i : ℤ))) = (143 : ℝ) := by
  have hsum : ∑ i : Fin 8, (embedNatFour 9 7 3 2 i : ℝ) ^ 2 = (143 : ℝ) := by
    rw [sum_sq_embedNatFour]
    norm_num
  rw [o8normSq_eq_sum_sq]
  have hpt : ∀ i : Fin 8,
      intLatticeToO8 (fun i => (embedNatFour 9 7 3 2 i : ℤ)) i = (embedNatFour 9 7 3 2 i : ℝ) := by
    intro i
    simp [intLatticeToO8_apply, Int.cast_natCast]
  simp_rw [hpt]
  exact hsum

end Hqiv.Algebra

end
