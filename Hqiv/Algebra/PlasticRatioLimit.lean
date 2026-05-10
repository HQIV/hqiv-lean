import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

import Hqiv.Algebra.PlasticAsymptotics
import Hqiv.Algebra.PlasticBinet
import Hqiv.Algebra.PlasticDominantRoot

/-!
# Plastic ratio limit scaffold

This module sets up the real-valued ratio track and the canonical candidate
closed form in terms of `plasticRoot`.
-/

namespace Hqiv.Algebra

open Filter
open scoped Topology

/-- Real cast of the canonical numerator track. -/
def plasticPReal (n : ℕ) : ℝ := (plasticP n : ℝ)

/-- Real cast of the canonical denominator track. -/
def plasticQReal (n : ℕ) : ℝ := (plasticQ n : ℝ)

lemma plasticPReal_rec (n : ℕ) :
    plasticPReal (n + 3) = plasticPReal (n + 1) + plasticPReal n := by
  unfold plasticPReal
  norm_num [plasticP_rec]

lemma plasticQReal_rec (n : ℕ) :
    plasticQReal (n + 3) = plasticQReal (n + 1) + plasticQReal n := by
  unfold plasticQReal
  norm_num [plasticQ_rec]

lemma plasticQReal_pos (n : ℕ) : 0 < plasticQReal n := by
  unfold plasticQReal
  exact_mod_cast plasticQ_pos n

/-- Real ratio track for limit statements. -/
noncomputable def plasticRatioReal (n : ℕ) : ℝ := plasticPReal n / plasticQReal n

theorem plasticRatioReal_wellDefined (n : ℕ) : plasticQReal n ≠ 0 :=
  ne_of_gt (plasticQReal_pos n)

/-- Positivity of the real ratio track. -/
theorem plasticRatioReal_pos (n : ℕ) : 0 < plasticRatioReal n := by
  unfold plasticRatioReal
  have hp : 0 < plasticPReal n := by
    unfold plasticPReal
    exact_mod_cast plasticP_pos n
  exact div_pos hp (plasticQReal_pos n)

/-- Uniform upper bound for the canonical ratio track. -/
theorem plasticRatioReal_le_one (n : ℕ) : plasticRatioReal n ≤ 1 := by
  unfold plasticRatioReal
  have hqpos : 0 < plasticQReal n := plasticQReal_pos n
  have hle : plasticPReal n ≤ plasticQReal n := by
    unfold plasticPReal plasticQReal
    exact_mod_cast plasticP_le_plasticQ n
  exact (div_le_one hqpos).2 hle

/-- Two-sided bound used for convergence control. -/
theorem plasticRatioReal_bounds (n : ℕ) : 0 < plasticRatioReal n ∧ plasticRatioReal n ≤ 1 :=
  ⟨plasticRatioReal_pos n, plasticRatioReal_le_one n⟩

/-- One-step ratio update written as a weighted-average form. -/
theorem plasticRatioReal_rec_weighted (n : ℕ) :
    plasticRatioReal (n + 3) =
      (plasticQReal (n + 1) * plasticRatioReal (n + 1) + plasticQReal n * plasticRatioReal n) /
        (plasticQReal (n + 1) + plasticQReal n) := by
  have hq1 : plasticQReal (n + 1) ≠ 0 := plasticRatioReal_wellDefined (n + 1)
  have hq0 : plasticQReal n ≠ 0 := plasticRatioReal_wellDefined n
  have hqsum : plasticQReal (n + 1) + plasticQReal n ≠ 0 := by
    have hq1pos : 0 < plasticQReal (n + 1) := plasticQReal_pos (n + 1)
    have hq0pos : 0 < plasticQReal n := plasticQReal_pos n
    linarith
  unfold plasticRatioReal
  rw [plasticPReal_rec, plasticQReal_rec]
  -- clear denominators and normalize.
  field_simp [hq1, hq0, hqsum]

/-- A positive weighted average lies between its two inputs. -/
lemma weighted_average_between {a b w1 w0 : ℝ}
    (hw1 : 0 < w1) (hw0 : 0 < w0) :
    min a b ≤ (w1 * a + w0 * b) / (w1 + w0) ∧
      (w1 * a + w0 * b) / (w1 + w0) ≤ max a b := by
  have hsum : 0 < w1 + w0 := by linarith
  constructor
  · by_cases hab : a ≤ b
    · rw [min_eq_left hab]
      have h : w1 * a + w0 * a ≤ w1 * a + w0 * b := by
        nlinarith
      have : a * (w1 + w0) ≤ w1 * a + w0 * b := by
        simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
      exact (le_div_iff₀ hsum).2 (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this)
    · have hba : b ≤ a := le_of_not_ge hab
      rw [min_eq_right hba]
      have h : w1 * b + w0 * b ≤ w1 * a + w0 * b := by
        nlinarith
      have : b * (w1 + w0) ≤ w1 * a + w0 * b := by
        simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
      exact (le_div_iff₀ hsum).2 (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this)
  · by_cases hab : a ≤ b
    · rw [max_eq_right hab]
      have h : w1 * a + w0 * b ≤ w1 * b + w0 * b := by
        nlinarith
      have : w1 * a + w0 * b ≤ b * (w1 + w0) := by
        simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
      exact (div_le_iff₀ hsum).2 (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this)
    · have hba : b ≤ a := le_of_not_ge hab
      rw [max_eq_left hba]
      have h : w1 * a + w0 * b ≤ w1 * a + w0 * a := by
        nlinarith
      have : w1 * a + w0 * b ≤ a * (w1 + w0) := by
        simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
      exact (div_le_iff₀ hsum).2 (by simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this)

/-- The ratio update is trapped between the previous two ratio values. -/
theorem plasticRatioReal_between_prev (n : ℕ) :
    min (plasticRatioReal (n + 1)) (plasticRatioReal n) ≤ plasticRatioReal (n + 3) ∧
      plasticRatioReal (n + 3) ≤ max (plasticRatioReal (n + 1)) (plasticRatioReal n) := by
  rw [plasticRatioReal_rec_weighted]
  exact weighted_average_between (plasticQReal_pos (n + 1)) (plasticQReal_pos n)

/-- Every ratio value lies in `(0,1]`. -/
theorem plasticRatioReal_mem_Ioc (n : ℕ) :
    plasticRatioReal n ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨plasticRatioReal_pos n, plasticRatioReal_le_one n⟩

/-- Denominator weight used in convex-combination form. -/
noncomputable def plasticWeight (n : ℕ) : ℝ :=
  plasticQReal (n + 1) / (plasticQReal (n + 1) + plasticQReal n)

lemma plasticWeight_pos (n : ℕ) : 0 < plasticWeight n := by
  unfold plasticWeight
  have h1 : 0 < plasticQReal (n + 1) := plasticQReal_pos (n + 1)
  have hsum : 0 < plasticQReal (n + 1) + plasticQReal n := by
    exact add_pos h1 (plasticQReal_pos n)
  exact div_pos h1 hsum

lemma plasticWeight_lt_one (n : ℕ) : plasticWeight n < 1 := by
  unfold plasticWeight
  have hq0 : 0 < plasticQReal n := plasticQReal_pos n
  have hq1 : 0 < plasticQReal (n + 1) := plasticQReal_pos (n + 1)
  have hsum : 0 < plasticQReal (n + 1) + plasticQReal n := add_pos hq1 hq0
  have hlt : plasticQReal (n + 1) < plasticQReal (n + 1) + plasticQReal n := by linarith
  exact (div_lt_one hsum).2 hlt

/-- Convex-combination update for the ratio dynamics. -/
theorem plasticRatioReal_rec_convex (n : ℕ) :
    plasticRatioReal (n + 3) =
      plasticWeight n * plasticRatioReal (n + 1) + (1 - plasticWeight n) * plasticRatioReal n := by
  rw [plasticRatioReal_rec_weighted, plasticWeight]
  have hqsum : plasticQReal (n + 1) + plasticQReal n ≠ 0 := by
    have hsum : 0 < plasticQReal (n + 1) + plasticQReal n := add_pos (plasticQReal_pos (n + 1)) (plasticQReal_pos n)
    exact ne_of_gt hsum
  field_simp [hqsum]
  ring

/-- Distance from the new term to `r_{n}` is scaled by `plasticWeight n`. -/
theorem plasticRatioReal_sub_prev_abs (n : ℕ) :
    |plasticRatioReal (n + 3) - plasticRatioReal n|
      = plasticWeight n * |plasticRatioReal (n + 1) - plasticRatioReal n| := by
  rw [plasticRatioReal_rec_convex]
  have hw : 0 ≤ plasticWeight n := le_of_lt (plasticWeight_pos n)
  calc
    |plasticWeight n * plasticRatioReal (n + 1) + (1 - plasticWeight n) * plasticRatioReal n
        - plasticRatioReal n|
        = |plasticWeight n * (plasticRatioReal (n + 1) - plasticRatioReal n)| := by ring_nf
    _ = |plasticWeight n| * |plasticRatioReal (n + 1) - plasticRatioReal n| := by
          rw [abs_mul]
    _ = plasticWeight n * |plasticRatioReal (n + 1) - plasticRatioReal n| := by
          rw [abs_of_nonneg hw]

/-- One-step contraction bound toward `r_n`. -/
theorem plasticRatioReal_sub_prev_abs_le (n : ℕ) :
    |plasticRatioReal (n + 3) - plasticRatioReal n|
      ≤ |plasticRatioReal (n + 1) - plasticRatioReal n| := by
  rw [plasticRatioReal_sub_prev_abs]
  have hw1 : plasticWeight n ≤ 1 := le_of_lt (plasticWeight_lt_one n)
  have habs : 0 ≤ |plasticRatioReal (n + 1) - plasticRatioReal n| := abs_nonneg _
  have hmul :
      plasticWeight n * |plasticRatioReal (n + 1) - plasticRatioReal n|
        ≤ 1 * |plasticRatioReal (n + 1) - plasticRatioReal n| :=
    mul_le_mul_of_nonneg_right hw1 habs
  simpa using hmul

/-- Distance from the new term to `r_{n+1}` is scaled by `(1 - plasticWeight n)`. -/
theorem plasticRatioReal_sub_next_abs (n : ℕ) :
    |plasticRatioReal (n + 3) - plasticRatioReal (n + 1)|
      = (1 - plasticWeight n) * |plasticRatioReal (n + 1) - plasticRatioReal n| := by
  rw [plasticRatioReal_rec_convex]
  have h1w : 0 ≤ 1 - plasticWeight n := by
    have hw1 : plasticWeight n ≤ 1 := le_of_lt (plasticWeight_lt_one n)
    linarith
  calc
    |plasticWeight n * plasticRatioReal (n + 1) + (1 - plasticWeight n) * plasticRatioReal n
        - plasticRatioReal (n + 1)|
        = |(1 - plasticWeight n) * (plasticRatioReal n - plasticRatioReal (n + 1))| := by ring_nf
    _ = |1 - plasticWeight n| * |plasticRatioReal n - plasticRatioReal (n + 1)| := by
          rw [abs_mul]
    _ = (1 - plasticWeight n) * |plasticRatioReal n - plasticRatioReal (n + 1)| := by
          rw [abs_of_nonneg h1w]
    _ = (1 - plasticWeight n) * |plasticRatioReal (n + 1) - plasticRatioReal n| := by
          rw [abs_sub_comm]

/-- Canonical plastic-root closed-form candidate for the `ζ(3)` track. -/
noncomputable def plasticZeta3Candidate : ℝ :=
  (5 / 2 : ℝ) * ((plasticRoot ^ 2 + 2 * plasticRoot + 3) / (plasticRoot ^ 3 + plasticRoot ^ 2 + 1))

theorem plasticRoot_denominator_candidate_ne_zero :
    plasticRoot ^ 3 + plasticRoot ^ 2 + 1 ≠ 0 := by
  have hρ1 : (1 : ℝ) < plasticRoot := plasticRoot_mem_Ioo.1
  have hρpos : 0 < plasticRoot := lt_trans zero_lt_one hρ1
  have hcub : 0 < plasticRoot ^ 3 := by exact pow_pos hρpos 3
  have hsq : 0 < plasticRoot ^ 2 := by exact pow_pos hρpos 2
  have hsum : 0 < plasticRoot ^ 3 + plasticRoot ^ 2 + 1 := by linarith
  exact ne_of_gt hsum

/-- Conditional Binet instantiation for the canonical plastic ratio track.

This packages the exact bridge from sequence-level Binet forms to the ratio
limit theorem. The remaining work is to discharge the hypotheses by deriving
`hP`, `hQ`, and `hratio` from the plastic companion-matrix spectral data.
-/
theorem plasticRatioReal_tendsto_of_binet
    (Ap Aq Bp Cp Bq Cq ρ σ τ : ℝ)
    (hσ : |σ| < 1) (hτ : |τ| < 1) (hAq : Aq ≠ 0)
    (hP : ∀ n : ℕ, plasticPReal n = Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n)
    (hQ : ∀ n : ℕ, plasticQReal n = Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n)
    (hratio :
      ∀ n : ℕ,
        (Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) /
        (Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n) = Ap / Aq) :
    Tendsto plasticRatioReal atTop (𝓝 (Ap / Aq)) := by
  have hEq :
      plasticRatioReal =
        (fun n : ℕ =>
          (Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) /
          (Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n)) := by
    funext n
    unfold plasticRatioReal
    rw [hP n, hQ n]
  rw [hEq]
  exact tendsto_ratio_of_binet_template Ap Aq Bp Cp Bq Cq ρ σ τ hσ hτ hAq hratio

/-- Canonical placeholder theorem name for the eventual plastic closed-form
ratio limit used in the `ζ(3)` certificate chain.
-/
theorem plasticRatioReal_tendsto_closed_form_candidate
    (L : ℝ)
    (hL :
      ∃ Ap Aq Bp Cp Bq Cq ρ σ τ : ℝ,
        |σ| < 1 ∧ |τ| < 1 ∧ Aq ≠ 0 ∧
        (∀ n : ℕ, plasticPReal n = Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) ∧
        (∀ n : ℕ, plasticQReal n = Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n) ∧
        (∀ n : ℕ,
          (Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) /
          (Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n) = Ap / Aq) ∧
        L = Ap / Aq) :
    Tendsto plasticRatioReal atTop (𝓝 L) := by
  rcases hL with ⟨Ap, Aq, Bp, Cp, Bq, Cq, ρ, σ, τ, hσ, hτ, hAq, hP, hQ, hratio, rfl⟩
  exact plasticRatioReal_tendsto_of_binet Ap Aq Bp Cp Bq Cq ρ σ τ hσ hτ hAq hP hQ hratio

end Hqiv.Algebra

