import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.PNat.Equiv
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

import Hqiv.Algebra.IntegerLatticeShellCount8
import Hqiv.Algebra.ThetaZ8ModularFormScaffold

/-!
# Eisenstein `E₄`, divisor sums `σ₃`, and comparison with `r8`

Mathlib’s normalised level-one Eisenstein series `ModularForm.E 4` satisfies
(`EisensteinSeries.q_expansion_bernoulli` for weight `4`)

`E₄(τ) = 1 + 240 ∑_{n≥1} σ₃(n) q^n` with `q = exp(2π i τ)`.

The **`qExpansion` PowerSeries coefficients** agree with **`1` at `0`** and **`240 · σ₃(n)`** for
`n > 0` — see `eisensteinE4_qExpansion_coeff_eq_sigma3`.

**Contrast with `r8`:** the constant terms agree (`coeff 0 = 1 = r8 0`), but already at `q¹`
one has `240 · σ₃(1) = 240 ≠ 16 = r8 1` — see `eisensteinE4_qExpansion_coeff_eq_r8_at_zero`,
`eisensteinE4_qExpansion_coeff_sub_r8`, `eisensteinE4_r8_gap_one`.

**Related:** `ThetaZ8ModularFormScaffold`, `ThetaZ8LSeriesScaffold`.
-/

namespace Hqiv.Algebra

open Asymptotics Complex Filter UpperHalfPlane Matrix.SpecialLinearGroup ModularForm ModularFormClass
  CongruenceSubgroup
open EisensteinSeries ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma CongruenceSubgroup

noncomputable section

variable (hk : 3 ≤ (4 : ℕ))

/-- Weight-`4` level-one Eisenstein series (`thetaZ8LevelOneE4Witness.f`). -/
noncomputable abbrev eisensteinE4 : ModularForm Γ(1) 4 :=
  E hk

private lemma even_four : Even (4 : ℕ) := by decide

theorem e4_bernoulli_factor_eq_twoFourty :
    -(2 * (4 : ℂ) / (bernoulli 4 : ℂ)) = (240 : ℂ) := by
  have hB : (bernoulli 4 : ℚ) = (-1 : ℚ) / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1), bernoulli'_four]
  rw [show (bernoulli 4 : ℂ) = ((-1 : ℚ) / 30 : ℚ) by exact_mod_cast hB]
  norm_num

lemma qParam_one_eq_cexp (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = cexp (2 * Real.pi * Complex.I * (τ : ℂ)) := by
  simp [Function.Periodic.qParam, div_one]

theorem eisensteinE4_eq_one_sub_bernoulli_sigma_tsum (τ : ℍ) :
    (eisensteinE4 hk τ : ℂ) =
      1 - (2 * (4 : ℂ) / (bernoulli 4 : ℂ)) *
        ∑' n : ℕ+, (σ 3 n : ℂ) * cexp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℤ) :=
  EisensteinSeries.q_expansion_bernoulli (k := 4) hk even_four τ

theorem eisensteinE4_eq_one_add_twoFourty_sigma_tsum (τ : ℍ) :
    (eisensteinE4 hk τ : ℂ) =
      1 + (240 : ℂ) * ∑' n : ℕ+, (σ 3 n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ (n : ℕ) := by
  have hmain := EisensteinSeries.q_expansion_bernoulli (k := 4) hk even_four τ
  have hcexp :
      ∀ n : ℕ+,
        cexp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (n : ℤ) =
          Function.Periodic.qParam 1 (τ : ℂ) ^ (n : ℕ) := by
    intro n
    rw [← qParam_one_eq_cexp τ]
    simp only [zpow_natCast]
  simp_rw [hcexp, show (4 - 1 : ℕ) = 3 by norm_num] at hmain
  rw [hmain]
  rw [sub_eq_add_neg, ← neg_mul]
  simp [e4_bernoulli_factor_eq_twoFourty]

noncomputable def eisensteinE4_qCoeff (_hk : 3 ≤ (4 : ℕ)) (m : ℕ) : ℂ :=
  if m = 0 then 1 else (240 : ℂ) * (σ 3 m : ℂ)

private lemma sigma_le_pow_succ (k n : ℕ) (hn : 0 < n) : σ k n ≤ n ^ (k + 1) := by
  rw [sigma_apply]
  have hdiv :
      ∀ d ∈ n.divisors, d ≤ n := fun d hd =>
        Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)
  have hterm : ∀ d ∈ n.divisors, d ^ k ≤ n ^ k := fun d hd =>
    Nat.pow_le_pow_left (hdiv d hd) k
  calc
    ∑ d ∈ divisors n, d ^ k ≤ ∑ _ ∈ divisors n, n ^ k := Finset.sum_le_sum hterm
    _ = n ^ k * n.divisors.card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
    _ ≤ n ^ k * n := by
      gcongr
      exact Nat.card_divisors_le_self n
    _ = n ^ (k + 1) := by rw [pow_succ, mul_comm]

private lemma sigma_succ_isBigO_pow_four :
    (fun n : ℕ => (σ 3 (n + 1) : ℝ)) =O[atTop] (fun n : ℕ => (n ^ 4 : ℝ)) := by
  have hf16 :
      (fun n : ℕ => (σ 3 (n + 1) : ℝ)) =O[atTop] (fun n : ℕ => (16 : ℝ) * (n : ℝ) ^ 4) := by
    refine Eventually.isBigO ?_
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hσ : σ 3 (n + 1) ≤ (n + 1) ^ 4 := by
      have h := sigma_le_pow_succ 3 (n + 1) n.succ_pos
      rwa [show (n + 1) ^ (3 + 1) = (n + 1) ^ 4 by simp [pow_succ]] at h
    have hσ' : (σ 3 (n + 1) : ℝ) ≤ ((n + 1) ^ 4 : ℝ) := by exact_mod_cast hσ
    have hmono : ((n + 1 : ℝ) ^ 4) ≤ (2 * n) ^ 4 := by
      have hnp : (n + 1 : ℝ) ≤ 2 * n := by
        have hn1 : 1 ≤ n := hn
        have : (n + 1 : ℕ) ≤ 2 * n := by
          rw [two_mul, ← Nat.add_comm 1 n]
          exact Nat.add_le_add_right hn1 n
        exact_mod_cast this
      gcongr
    rw [mul_pow] at hmono
    have h4 : (σ 3 (n + 1) : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by
      refine hσ'.trans ?_
      simpa [mul_pow, show (2 ^ 4 : ℝ) = (16 : ℝ) by norm_num] using hmono
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact h4
  have h16 :
      (fun n : ℕ => (16 : ℝ) * (n : ℝ) ^ 4) =O[atTop] (fun n : ℕ => (n : ℝ) ^ 4) := by
    simpa using (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 4) atTop).const_mul_left (16 : ℝ)
  simpa [mul_comm] using hf16.trans h16

private lemma summable_sigma_mul_qpow (τ : ℍ) :
    Summable fun n : ℕ+ => (σ 3 n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ (n : ℕ) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa [Function.Periodic.qParam, Complex.norm_exp, neg_div] using
      UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  rw [← Equiv.pnatEquivNat.symm.summable_iff]
  have hnorm :=
    summable_norm_mul_geometric_of_norm_lt_one (k := 4) hq
      (u := fun n => σ 3 (n + 1))
      (by simpa [← Nat.cast_pow] using sigma_succ_isBigO_pow_four)
  have hbase : Summable fun n : ℕ => (σ 3 (n + 1) : ℂ) * q ^ n :=
    Summable.of_norm hnorm
  simpa [pow_succ, mul_assoc] using hbase.mul_right q

set_option maxHeartbeats 800000 in
private lemma summable_eisensteinE4_q_series (τ : ℍ) :
    Summable fun m : ℕ =>
      eisensteinE4_qCoeff hk m * Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
  have hs := summable_sigma_mul_qpow τ
  have hpnat :
      Summable fun n : ℕ+ =>
        (240 : ℂ) * (σ 3 n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ (n : ℕ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hs.mul_left (240 : ℂ)
  have h1 :
      Summable fun m : ℕ =>
        (if m = 0 then (0 : ℂ) else (240 : ℂ) * (σ 3 m : ℂ)) *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    have hb : Summable fun m : ℕ =>
        (240 : ℂ) * (σ 3 (m + 1) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1) := by
      simpa [mul_assoc] using Equiv.pnatEquivNat.symm.summable_iff.mpr hpnat
    simpa [mul_assoc] using Summable.comp_nat_add (k := 1) (f := fun m : ℕ =>
      (if m = 0 then (0 : ℂ) else (240 : ℂ) * (σ 3 m : ℂ)) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) hb
  have h0 : Summable fun m : ℕ => (if m = 0 then (1 : ℂ) else (0 : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    have : Summable fun m : ℕ => if m = 0 then (1 : ℂ) else 0 :=
      (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).summable
    refine this.congr fun m => ?_
    by_cases hm : m = 0 <;> simp [hm]
  convert h0.add h1 using 1
  ext m
  rcases m with _ | m
  · simp [eisensteinE4_qCoeff]
  · simp [eisensteinE4_qCoeff, mul_assoc]

set_option maxHeartbeats 800000 in
private lemma tsum_eisensteinE4_q_eq (τ : ℍ) :
    (∑' m : ℕ, eisensteinE4_qCoeff hk m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) =
      1 + (240 : ℂ) * ∑' n : ℕ+, (σ 3 n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ (n : ℕ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hs_tail :
      Summable fun m : ℕ => eisensteinE4_qCoeff hk (m + 1) * q ^ (m + 1) :=
    (summable_eisensteinE4_q_series hk τ).comp_injective Nat.succ_injective
  rw [tsum_eq_zero_add' hs_tail]
  simp [eisensteinE4_qCoeff, pow_zero, mul_one]
  have hterm :
      (fun b : ℕ => (240 : ℂ) * (σ 3 (b + 1) : ℂ) * q ^ (b + 1)) =
        fun b : ℕ => (240 : ℂ) * ((σ 3 (b + 1) : ℂ) * q ^ (b + 1)) := by
    funext b
    rw [← mul_assoc]
  rw [hterm, tsum_mul_left (a := (240 : ℂ)) (f := fun b : ℕ => (σ 3 (b + 1) : ℂ) * q ^ (b + 1))]
  rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (σ 3 n : ℂ) * q ^ n)]

private lemma hasSum_eisensteinE4_q (τ : ℍ) :
    HasSum (fun m : ℕ =>
        eisensteinE4_qCoeff hk m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (eisensteinE4 hk τ) := by
  have h := Summable.hasSum (summable_eisensteinE4_q_series hk τ)
  convert h using 2
  rw [tsum_eisensteinE4_q_eq hk τ, eisensteinE4_eq_one_add_twoFourty_sigma_tsum hk τ]

/-- Mathlib `qExpansion` coefficients for `E₄`: constant `1`, then `240 · σ₃(n)`. -/
theorem eisensteinE4_qExpansion_coeff_eq_sigma3 (n : ℕ) :
    (ModularFormClass.qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff n = eisensteinE4_qCoeff hk n := by
  have hf :
      ∀ τ : ℍ,
        HasSum (fun m : ℕ =>
            eisensteinE4_qCoeff hk m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (eisensteinE4 hk τ) := by
    intro τ
    simpa [smul_eq_mul] using hasSum_eisensteinE4_q hk τ
  exact (qExpansion_coeff_unique (c := eisensteinE4_qCoeff hk) (hh := zero_lt_one)
    (hΓ := by simp) (f := eisensteinE4 hk) (hf := hf) n).symm

/-- For `n > 0`, the `qExpansion` coefficient is exactly `240 · σ₃(n)` (constant term `n = 0` is `1`). -/
theorem eisensteinE4_qExpansion_coeff_eq_sigma3' (n : ℕ) (hn : 0 < n) :
    (ModularFormClass.qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff n = (240 : ℂ) * (σ 3 n : ℂ) := by
  rw [eisensteinE4_qExpansion_coeff_eq_sigma3]
  simp [eisensteinE4_qCoeff, Nat.ne_of_gt hn]

@[simp]
theorem sigma_three_one : σ 3 (1 : ℕ) = 1 :=
  sigma_one 3

/-- `E₄` and the theta/`r8` series share the same constant coefficient (`1`). -/
theorem eisensteinE4_qExpansion_coeff_eq_r8_at_zero :
    (ModularFormClass.qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff 0 = (r8 0 : ℂ) := by
  rw [eisensteinE4_qExpansion_coeff_eq_sigma3]
  simp [eisensteinE4_qCoeff, r8_zero]

/-- Pointwise gap between `E₄` `qExpansion` coefficients and shell counts `r₈` (`n > 0`). -/
theorem eisensteinE4_qExpansion_coeff_sub_r8 (n : ℕ) (hn : 0 < n) :
    (ModularFormClass.qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff n - (r8 n : ℂ) =
      (240 : ℂ) * (σ 3 n : ℂ) - (r8 n : ℂ) := by
  rw [eisensteinE4_qExpansion_coeff_eq_sigma3' hk n hn]

/-- At `n = 1`, the gap is `224 = 240 · σ₃(1) − r₈(1)` (not close to `0`). -/
theorem eisensteinE4_r8_gap_one :
    (ModularFormClass.qExpansion 1 (eisensteinE4 hk : ℍ → ℂ)).coeff 1 - (r8 1 : ℂ) = (224 : ℂ) := by
  rw [eisensteinE4_qExpansion_coeff_sub_r8 hk 1 (Nat.succ_pos 0)]
  rw [sigma_three_one, r8_one]
  norm_num

theorem eisensteinE4_sigma3_line_at_one : (240 : ℂ) * (σ 3 1 : ℂ) = 240 := by
  simp

theorem r8_one_ne_eisensteinE4_sigma3_line : (240 : ℂ) * (σ 3 1 : ℂ) ≠ (r8 1 : ℂ) := by
  rw [eisensteinE4_sigma3_line_at_one, r8_one]
  norm_num

end

end Hqiv.Algebra
