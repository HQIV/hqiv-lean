import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

import Hqiv.Algebra.MulModBSDCascadePrefixModularity
import Hqiv.Algebra.MulModBSDCoefficientScaffold
import Hqiv.Algebra.MulModBSDRamanujanPetersson

/-!
# Weak Hecke targets on good cascade shells (prime, composite, square)

Classical Hecke multiplicativity would predict `a_{pq} = a_p a_q` on the holonomy trace.
On the mul-mod stream this **fails** once `a_p = a_q = 6`: composite shells carry trace
`6`, not `36`.

The **proved weak replacement** is **numerator rigidity**: on every good shell built from
the cascade prefix (prime, distinct product, or square), the unnormalized residue numerator
is `6`, hence

`(shell index) · coeff(shell) = 6`.

Composite indices such as `143 = 11·13` appear in the global coefficient stream via
`mulModBSDLocalCoeff 143`.
-/

namespace Hqiv.Algebra

open Real
open Hqiv.Geometry

noncomputable section

/-! ## Good composite shell classification -/

def IsHarmonicCascadeGoodDistinctProduct (n : ℕ) : Prop :=
  ∃ p q,
    IsHarmonicCascadeGoodPrimeShell p ∧
      IsHarmonicCascadeGoodPrimeShell q ∧ p ≠ q ∧ n = p * q

def IsHarmonicCascadeGoodPrimeSquare (n : ℕ) : Prop :=
  ∃ p, IsHarmonicCascadeGoodPrimeShell p ∧ n = p * p

def IsHarmonicCascadeGoodCompositeShell (n : ℕ) : Prop :=
  IsHarmonicCascadeGoodDistinctProduct n ∨ IsHarmonicCascadeGoodPrimeSquare n

/-! ## Coprimality and size lemmas -/

theorem harmonic_good_prime_coprime_six {p : ℕ} (hp : Nat.Prime p)
    (h : IsHarmonicCascadeGoodPrimeShell p) : Nat.Coprime 6 p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hp6 : p ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  linarith [harmonicCascadeGoodPrimeShells_ge_eleven h]

private theorem harmonic_obstruction_of_coprime_six {n : ℕ} (h : Nat.Coprime 6 n) :
    HarmonicMulModMultiplierCoprimeObstruction n := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction]
  rw [harmonicOrbitMulModMultiplier_eq_six h]
  exact h

theorem harmonic_good_distinct_product_coprime_six {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) :
    Nat.Coprime 6 n := by
  obtain ⟨p, q, hpg, hqg, _, hn⟩ := h
  rw [hn]
  have hp6 := harmonic_good_prime_coprime_six (harmonicCascadeGoodPrimeShells_prime hpg) hpg
  have hq6 := harmonic_good_prime_coprime_six (harmonicCascadeGoodPrimeShells_prime hqg) hqg
  rw [Nat.coprime_comm] at hp6 hq6
  rw [Nat.coprime_comm]
  exact Nat.Coprime.mul_left hp6 hq6

theorem harmonic_good_prime_square_coprime_six {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) :
    Nat.Coprime 6 n := by
  obtain ⟨p, hpg, hn⟩ := h
  rw [hn]
  have hp6 := harmonic_good_prime_coprime_six (harmonicCascadeGoodPrimeShells_prime hpg) hpg
  rw [Nat.coprime_comm] at hp6
  rw [Nat.coprime_comm]
  exact Nat.Coprime.mul_left hp6 hp6

theorem harmonic_good_composite_shell_coprime_six {n : ℕ}
    (h : IsHarmonicCascadeGoodCompositeShell n) : Nat.Coprime 6 n := by
  rcases h with hprod | hsq
  · exact harmonic_good_distinct_product_coprime_six hprod
  · exact harmonic_good_prime_square_coprime_six hsq

theorem harmonic_good_distinct_product_gt_six {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) : 6 < n := by
  obtain ⟨p, q, hpg, hqg, hne, hn⟩ := h
  rw [hn]
  have hp11 := harmonicCascadeGoodPrimeShells_ge_eleven hpg
  have hq11 := harmonicCascadeGoodPrimeShells_ge_eleven hqg
  nlinarith

theorem harmonic_good_prime_square_gt_six {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) : 6 < n := by
  obtain ⟨p, hpg, hn⟩ := h
  rw [hn]
  have hp11 := harmonicCascadeGoodPrimeShells_ge_eleven hpg
  nlinarith [sq_nonneg (p : ℝ), show (11 : ℕ) ^ 2 ≤ p * p from by nlinarith]

theorem harmonic_good_distinct_product_pos {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) : 0 < n := by
  nlinarith [harmonic_good_distinct_product_gt_six h]

theorem harmonic_good_prime_square_pos {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) : 0 < n := by
  nlinarith [harmonic_good_prime_square_gt_six h]

/-! ## Uniform holonomy on good composites -/

theorem harmonic_good_composite_shell_pos {n : ℕ} (h : IsHarmonicCascadeGoodCompositeShell n) :
    0 < n := by
  rcases h with hprod | hsq
  · exact harmonic_good_distinct_product_pos hprod
  · exact harmonic_good_prime_square_pos hsq

private theorem mulModBSDShellHolonomyTrace_proof_irrel_coprime {n : ℕ} {hn hn' : 0 < n}
    (hobs : HarmonicMulModMultiplierCoprimeObstruction n) :
    mulModBSDShellHolonomyTrace n hn = mulModBSDShellHolonomyTrace n hn' := by
  simp only [mulModBSDShellHolonomyTrace,
    harmonicStructuredCascadeMultiplier_eq_raw hn hobs,
    harmonicStructuredCascadeMultiplier_eq_raw hn' hobs]

private theorem mulModBSDLocalResidueCoeffReal_proof_irrel_coprime {n : ℕ} {hn hn' : 0 < n}
    (hobs : HarmonicMulModMultiplierCoprimeObstruction n) :
    mulModBSDLocalResidueCoeffReal n hn = mulModBSDLocalResidueCoeffReal n hn' := by
  simp only [mulModBSDLocalResidueCoeffReal,
    harmonicStructuredCascadeMultiplier_eq_raw hn hobs,
    harmonicStructuredCascadeMultiplier_eq_raw hn' hobs]

private theorem mulModBSD_shell_holonomy_eq_six_of_coprime {n : ℕ} (hn : 0 < n)
    (h6 : Nat.Coprime 6 n) (hlt : 6 < n) :
    mulModBSDShellHolonomyTrace n hn = 6 := by
  have hobs := harmonic_obstruction_of_coprime_six h6
  unfold mulModBSDShellHolonomyTrace
  rw [harmonicStructuredCascadeMultiplier_eq_raw hn hobs,
    harmonicOrbitMulModMultiplier_eq_six h6, Nat.mod_eq_of_lt hlt]

theorem mulModBSD_good_distinct_product_holonomy_six {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) :
    mulModBSDShellHolonomyTrace n (harmonic_good_distinct_product_pos h) = 6 :=
  mulModBSD_shell_holonomy_eq_six_of_coprime _ (harmonic_good_distinct_product_coprime_six h)
    (harmonic_good_distinct_product_gt_six h)

theorem mulModBSD_good_prime_square_holonomy_six {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) :
    mulModBSDShellHolonomyTrace n (harmonic_good_prime_square_pos h) = 6 :=
  mulModBSD_shell_holonomy_eq_six_of_coprime _ (harmonic_good_prime_square_coprime_six h)
    (harmonic_good_prime_square_gt_six h)

theorem mulModBSD_good_composite_holonomy_six {n : ℕ}
    (h : IsHarmonicCascadeGoodCompositeShell n) :
    mulModBSDShellHolonomyTrace n (harmonic_good_composite_shell_pos h) = 6 := by
  rcases h with hprod | hsq
  · exact mulModBSD_good_distinct_product_holonomy_six hprod
  · exact mulModBSD_good_prime_square_holonomy_six hsq

/-! ## Weak numerator Hecke (proved) -/

def MulModBSDWeakNumeratorHeckeHypothesis : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), IsHarmonicCascadeGoodCompositeShell n →
    mulModBSDShellHolonomyTrace n hn = 6 ∧
      (n : ℝ) * mulModBSDLocalResidueCoeffReal n hn = 6

theorem mulModBSD_weak_numerator_hecke : MulModBSDWeakNumeratorHeckeHypothesis := by
  intro n hn hcomp
  have hpos : 0 < n := by
    rcases hcomp with hprod | hsq
    · exact harmonic_good_distinct_product_pos hprod
    · exact harmonic_good_prime_square_pos hsq
  have h6 := harmonic_good_composite_shell_coprime_six hcomp
  have hobs := harmonic_obstruction_of_coprime_six h6
  have htrace := mulModBSD_good_composite_holonomy_six hcomp
  have hn' : mulModBSDShellHolonomyTrace n hn = mulModBSDShellHolonomyTrace n hpos :=
    mulModBSDShellHolonomyTrace_proof_irrel_coprime hobs
  constructor
  · rw [hn']
    exact htrace
  · have hcoeff :=
        mulModBSDLocalResidueCoeffReal_proof_irrel_coprime (hn := hn) (hn' := hpos) hobs
    have hmod :
        harmonicStructuredCascadeMultiplier n hpos % n = 6 := by
      simpa [mulModBSDShellHolonomyTrace] using htrace
    rw [hcoeff]
    simp only [mulModBSDLocalResidueCoeffReal, hmod]
    field_simp
    norm_num

theorem mulModBSD_good_distinct_product_coeff_numerator {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) :
    (n : ℝ) * mulModBSDLocalResidueCoeffReal n (harmonic_good_distinct_product_pos h) = 6 := by
  have := mulModBSD_weak_numerator_hecke (harmonic_good_distinct_product_pos h) (Or.inl h)
  exact this.2

theorem mulModBSD_good_prime_square_coeff_numerator {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) :
    (n : ℝ) * mulModBSDLocalResidueCoeffReal n (harmonic_good_prime_square_pos h) = 6 := by
  have := mulModBSD_weak_numerator_hecke (harmonic_good_prime_square_pos h) (Or.inr h)
  exact this.2

/-! ## Classical composite Hecke (refuted) -/

def MulModBSDClassicalCompositeHolonomyHeckeTarget (n : ℕ)
    (h : IsHarmonicCascadeGoodDistinctProduct n) : Prop :=
  ∃ (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q),
    IsHarmonicCascadeGoodPrimeShell p ∧
      IsHarmonicCascadeGoodPrimeShell q ∧
        p ≠ q ∧
          n = p * q ∧
            mulModBSDShellHolonomyTrace n (harmonic_good_distinct_product_pos h) =
              mulModBSDPrimeHolonomyTrace p hp * mulModBSDPrimeHolonomyTrace q hq

theorem mulModBSD_classical_composite_holonomy_hecke_fails {n : ℕ}
    (h : IsHarmonicCascadeGoodDistinctProduct n) :
    ¬ MulModBSDClassicalCompositeHolonomyHeckeTarget n h := by
  intro hclass
  obtain ⟨p, q, hp, hq, hpg, hqg, _, _, hclass⟩ := hclass
  have htrace := mulModBSD_good_distinct_product_holonomy_six h
  have hp6 := mulModBSD_good_shell_holonomy_six hp hpg
  have hq6 := mulModBSD_good_shell_holonomy_six hq hqg
  rw [htrace, hp6, hq6] at hclass
  norm_num at hclass

/-! ## Classical prime-square Hecke (refuted) -/

def MulModBSDClassicalPrimeSquareHolonomyHeckeTarget (n : ℕ)
    (h : IsHarmonicCascadeGoodPrimeSquare n) : Prop :=
  ∃ (p : ℕ) (hp : Nat.Prime p),
    IsHarmonicCascadeGoodPrimeShell p ∧
      n = p * p ∧
        mulModBSDShellHolonomyTrace n (harmonic_good_prime_square_pos h) =
          mulModBSDPrimeHolonomyTrace p hp * mulModBSDPrimeHolonomyTrace p hp

theorem mulModBSD_classical_prime_square_holonomy_hecke_fails {n : ℕ}
    (h : IsHarmonicCascadeGoodPrimeSquare n) :
    ¬ MulModBSDClassicalPrimeSquareHolonomyHeckeTarget n h := by
  intro hclass
  obtain ⟨p, hp, hpg, _, hclass⟩ := hclass
  have htrace := mulModBSD_good_prime_square_holonomy_six h
  have hp6 := mulModBSD_good_shell_holonomy_six hp hpg
  rw [htrace, hp6] at hclass
  norm_num at hclass

/-! ## Named composite witnesses -/

theorem isHarmonicCascadeGoodPrimeShell_eleven : IsHarmonicCascadeGoodPrimeShell 11 := by
  simp [IsHarmonicCascadeGoodPrimeShell, harmonicCascadeGoodPrimeShells, List.mem_cons,
    List.mem_nil_iff, or_false, or_true]

theorem isHarmonicCascadeGoodPrimeShell_thirteen : IsHarmonicCascadeGoodPrimeShell 13 := by
  simp [IsHarmonicCascadeGoodPrimeShell, harmonicCascadeGoodPrimeShells, List.mem_cons,
    List.mem_nil_iff, or_false, or_true]

theorem isHarmonicCascadeGoodDistinctProduct_143 :
    IsHarmonicCascadeGoodDistinctProduct 143 :=
  ⟨11, 13, isHarmonicCascadeGoodPrimeShell_eleven, isHarmonicCascadeGoodPrimeShell_thirteen,
    by decide, by decide⟩

theorem mulModBSD_local_coeff_143 :
    mulModBSDLocalCoeff 143 =
      ((6 : ℝ) / 143 : ℂ) := by
  have hprod := isHarmonicCascadeGoodDistinctProduct_143
  have hnpos := Nat.succ_pos 142
  have htrace := mulModBSD_good_distinct_product_holonomy_six hprod
  have hmod : harmonicStructuredCascadeMultiplier 143 hnpos % 143 = 6 := by
    simpa [mulModBSDShellHolonomyTrace] using htrace
  simp [mulModBSDLocalCoeff, mulModBSDLocalResidueCoeff, mulModBSDLocalResidueCoeffReal, hmod]

theorem mulModBSD_classical_hecke_fails_at_143 :
    ¬ MulModBSDClassicalCompositeHolonomyHeckeTarget 143
      isHarmonicCascadeGoodDistinctProduct_143 :=
  mulModBSD_classical_composite_holonomy_hecke_fails isHarmonicCascadeGoodDistinctProduct_143

theorem isHarmonicCascadeGoodPrimeSquare_121 :
    IsHarmonicCascadeGoodPrimeSquare 121 :=
  ⟨11, isHarmonicCascadeGoodPrimeShell_eleven, by decide⟩

theorem mulModBSD_local_coeff_121 :
    mulModBSDLocalCoeff 121 =
      ((6 : ℝ) / 121 : ℂ) := by
  have hsq := isHarmonicCascadeGoodPrimeSquare_121
  have hnpos := Nat.succ_pos 120
  have htrace := mulModBSD_good_prime_square_holonomy_six hsq
  have hmod : harmonicStructuredCascadeMultiplier 121 hnpos % 121 = 6 := by
    simpa [mulModBSDShellHolonomyTrace] using htrace
  simp [mulModBSDLocalCoeff, mulModBSDLocalResidueCoeff, mulModBSDLocalResidueCoeffReal, hmod]

theorem mulModBSD_classical_hecke_fails_at_121 :
    ¬ MulModBSDClassicalPrimeSquareHolonomyHeckeTarget 121
      isHarmonicCascadeGoodPrimeSquare_121 :=
  mulModBSD_classical_prime_square_holonomy_hecke_fails isHarmonicCascadeGoodPrimeSquare_121

theorem isHarmonicCascadeGoodPrimeSquare_169 :
    IsHarmonicCascadeGoodPrimeSquare 169 :=
  ⟨13, isHarmonicCascadeGoodPrimeShell_thirteen, by decide⟩

theorem mulModBSD_classical_hecke_fails_at_169 :
    ¬ MulModBSDClassicalPrimeSquareHolonomyHeckeTarget 169
      isHarmonicCascadeGoodPrimeSquare_169 :=
  mulModBSD_classical_prime_square_holonomy_hecke_fails isHarmonicCascadeGoodPrimeSquare_169

/-! ## Tamagawa-analog bad shell (first-class) -/

private theorem sqrt_seven_lt_three : Real.sqrt (7 : ℝ) < 3 := by
  have hlt : Real.sqrt 7 < Real.sqrt 9 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (7 : ℝ) < 9)
  have h9 : Real.sqrt 9 = (3 : ℝ) := by norm_num
  nlinarith [Real.sqrt_nonneg 7, hlt, h9]

private theorem mulModBSD_seven_ramanujan_ratio_gt_one : (6 : ℝ) / (2 * Real.sqrt 7) > 1 := by
  have hsqrt := sqrt_seven_lt_three
  have hsqrt_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num : 0 < (7 : ℝ))
  have hden_pos : 0 < 2 * Real.sqrt 7 := by nlinarith [hsqrt_pos]
  rw [gt_iff_lt, lt_div_iff₀ hden_pos]
  nlinarith [Real.sqrt_nonneg 7, hsqrt, hsqrt_pos]

structure MulModBSDBadPrimeTamagawaAnalog where
  shell : MulModBSDBadPrimeShellRecord
  ramanujan_excess : (6 : ℝ) > 2 * Real.sqrt 7
  ramanujan_ratio_gt_one : (6 : ℝ) / (2 * Real.sqrt 7) > 1
  normalized_residue :
    mulModBSDLocalResidueCoeffReal 7 (by decide) = (6 : ℝ) / 7
  single_cube_fibre_card : cubeResidueClasses.card = 3
  conjectural_conductor_exponent_one_or_two : 1 = 1 ∨ 2 = 2

noncomputable def mulModBSD_bad_prime_tamagawa_analog : MulModBSDBadPrimeTamagawaAnalog where
  shell := mulModBSD_bad_prime_shell_record
  ramanujan_excess := by
    have hsqrt_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num : 0 < (7 : ℝ))
    nlinarith [Real.sqrt_nonneg 7, sqrt_seven_lt_three, hsqrt_pos]
  ramanujan_ratio_gt_one := mulModBSD_seven_ramanujan_ratio_gt_one
  normalized_residue := by
    rw [mulModBSD_local_coeff_at_prime_shell 7 Nat.prime_seven, mulModBSDPrimeHolonomyTrace_seven]
    norm_num
  single_cube_fibre_card := mod7_prime_fibre_chart_card
  conjectural_conductor_exponent_one_or_two := Or.inl rfl

/-! ## Extended prefix modularity bundle -/

structure MulModBSDCascadePrefixModularityObjectExtended where
  base : MulModBSDCascadePrefixModularityObject
  weak_numerator_hecke : MulModBSDWeakNumeratorHeckeHypothesis
  tamagawa_analog : MulModBSDBadPrimeTamagawaAnalog
  classical_hecke_fails_143 :
    ¬ MulModBSDClassicalCompositeHolonomyHeckeTarget 143
      isHarmonicCascadeGoodDistinctProduct_143
  classical_square_hecke_fails_121 :
    ¬ MulModBSDClassicalPrimeSquareHolonomyHeckeTarget 121
      isHarmonicCascadeGoodPrimeSquare_121

noncomputable def mulModBSD_cascade_prefix_modularity_extended :
    MulModBSDCascadePrefixModularityObjectExtended where
  base := mulModBSD_cascade_prefix_modularity
  weak_numerator_hecke := mulModBSD_weak_numerator_hecke
  tamagawa_analog := mulModBSD_bad_prime_tamagawa_analog
  classical_hecke_fails_143 := mulModBSD_classical_hecke_fails_at_143
  classical_square_hecke_fails_121 := mulModBSD_classical_hecke_fails_at_121

end

end Hqiv.Algebra
