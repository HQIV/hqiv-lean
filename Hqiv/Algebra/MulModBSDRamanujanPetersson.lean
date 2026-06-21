import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

import Hqiv.Algebra.MulModBSDEulerFactor
import Hqiv.Geometry.HarmonicMulModCubeTriangulation

/-!
# Ramanujan–Petersson audit for mul-mod prime holonomy traces

The global hypothesis `MulModBSDHeckeEigenformHypothesis` (Ramanujan–Petersson at every
prime) is **refuted** at the Fano base shell `p = 7`: holonomy trace `a_7 = 6` exceeds
`2√7`.

On the **cascade prefix** primes `{11, 13, …, 41}` the trace is uniformly `6` and the
bound holds.  Small primes `2`, `3`, `5` also satisfy RP individually.

See `mulModBSD_global_ramanujan_petersson_fails` and
`mulModBSD_ramanujan_petersson_cascade_prefix`.
-/

namespace Hqiv.Algebra

open Complex Real
open Hqiv.Geometry

noncomputable section

/-- Ramanujan–Petersson bound at a single prime shell. -/
def MulModBSDRamanujanPeterssonAt (p : ℕ) (hp : Nat.Prime p) : Prop :=
  ‖mulModBSDPrimeAp p hp‖ ≤ 2 * Real.sqrt (p : ℝ)

private theorem norm_natCast_complex (n : ℕ) : ‖(n : ℂ)‖ = (n : ℝ) := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by simp]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

private theorem harmonic_obstruction_of_coprime_six {n : ℕ} (h : Nat.Coprime 6 n) :
    HarmonicMulModMultiplierCoprimeObstruction n := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction]
  rw [harmonicOrbitMulModMultiplier_eq_six h]
  exact h

private theorem mulModBSDPrimeHolonomyTrace_eq_six_of_coprime_six_lt {p : ℕ} (hp : Nat.Prime p)
    (h6 : Nat.Coprime 6 p) (hlt : 6 < p) :
    mulModBSDPrimeHolonomyTrace p hp = 6 := by
  have hn : 0 < p := Nat.Prime.pos hp
  have hobs := harmonic_obstruction_of_coprime_six h6
  unfold mulModBSDPrimeHolonomyTrace
  rw [harmonicStructuredCascadeMultiplier_eq_raw hn hobs,
      harmonicOrbitMulModMultiplier_eq_six h6, Nat.mod_eq_of_lt hlt]

private theorem Nat.Prime.coprime_six_of_ge {p : ℕ} (hp : Nat.Prime p) (h : 11 ≤ p) :
    Nat.Coprime 6 p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hp6 : p ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  linarith

/-! ## Holonomy traces -/

theorem mulModBSDPrimeHolonomyTrace_two :
    mulModBSDPrimeHolonomyTrace 2 Nat.prime_two = 1 := by
  have h6 : ¬ Nat.Coprime 6 2 := by decide
  have h5 : Nat.Coprime 5 2 := by decide
  have hobs : HarmonicMulModMultiplierCoprimeObstruction 2 := by
    dsimp [HarmonicMulModMultiplierCoprimeObstruction]
    rw [harmonicOrbitMulModMultiplier_eq_five h6 h5]
    exact h5
  unfold mulModBSDPrimeHolonomyTrace harmonicStructuredCascadeMultiplier
  simp [hobs, harmonicOrbitMulModMultiplier_eq_five h6 h5]

theorem mulModBSDPrimeHolonomyTrace_three :
    mulModBSDPrimeHolonomyTrace 3 Nat.prime_three = 2 := by
  have h6 : ¬ Nat.Coprime 6 3 := by decide
  have h5 : Nat.Coprime 5 3 := by decide
  have hobs : HarmonicMulModMultiplierCoprimeObstruction 3 := by
    dsimp [HarmonicMulModMultiplierCoprimeObstruction]
    rw [harmonicOrbitMulModMultiplier_eq_five h6 h5]
    exact h5
  unfold mulModBSDPrimeHolonomyTrace harmonicStructuredCascadeMultiplier
  simp [hobs, harmonicOrbitMulModMultiplier_eq_five h6 h5]

theorem mulModBSDPrimeHolonomyTrace_five :
    mulModBSDPrimeHolonomyTrace 5 Nat.prime_five = 1 := by
  have h6 : Nat.Coprime 6 5 := by decide
  have hn : 0 < 5 := by decide
  have hobs := harmonic_obstruction_of_coprime_six h6
  unfold mulModBSDPrimeHolonomyTrace
  rw [harmonicStructuredCascadeMultiplier_eq_raw hn hobs,
      harmonicOrbitMulModMultiplier_eq_six h6]

theorem mulModBSDPrimeHolonomyTrace_seven :
    mulModBSDPrimeHolonomyTrace 7 Nat.prime_seven = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_of_coprime_six_lt Nat.prime_seven (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime {p : ℕ} (hp : Nat.Prime p)
    (hp11 : 11 ≤ p) :
    mulModBSDPrimeHolonomyTrace p hp = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_of_coprime_six_lt hp
    (Nat.Prime.coprime_six_of_ge hp hp11) (Nat.lt_of_lt_of_le (by decide : 6 < 11) hp11)

theorem mulModBSDPrimeHolonomyTrace_eleven :
    mulModBSDPrimeHolonomyTrace 11 Nat.prime_eleven = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime Nat.prime_eleven (by decide)

theorem mulModBSDPrimeHolonomyTrace_thirteen :
    mulModBSDPrimeHolonomyTrace 13 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_seventeen :
    mulModBSDPrimeHolonomyTrace 17 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_nineteen :
    mulModBSDPrimeHolonomyTrace 19 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_twentyThree :
    mulModBSDPrimeHolonomyTrace 23 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_twentyNine :
    mulModBSDPrimeHolonomyTrace 29 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_thirtyOne :
    mulModBSDPrimeHolonomyTrace 31 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_thirtySeven :
    mulModBSDPrimeHolonomyTrace 37 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

theorem mulModBSDPrimeHolonomyTrace_fortyOne :
    mulModBSDPrimeHolonomyTrace 41 (by decide) = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime (by decide) (by decide)

/-! ## Generic bound when trace = 6 and p ≥ 11 -/

private theorem two_sqrt_eleven_gt_six : (6 : ℝ) ≤ 2 * Real.sqrt 11 := by
  have h11 : (0 : ℝ) ≤ 11 := by norm_num
  have hsq : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt h11
  nlinarith [Real.sqrt_nonneg 11, hsq, Real.sqrt_le_sqrt (by norm_num : (9 : ℝ) ≤ 11)]

theorem mulModBSD_ramanujan_petersson_of_holonomy_six {p : ℕ} (hp : Nat.Prime p)
    (htrace : mulModBSDPrimeHolonomyTrace p hp = 6) (hp11 : 11 ≤ p) :
    MulModBSDRamanujanPeterssonAt p hp := by
  dsimp [MulModBSDRamanujanPeterssonAt]
  rw [mulModBSDPrimeAp_real, htrace, norm_natCast_complex]
  have hsq : Real.sqrt (p : ℝ) ≥ Real.sqrt 11 :=
    Real.sqrt_le_sqrt (by exact_mod_cast hp11)
  have hbound : (6 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by
    nlinarith [two_sqrt_eleven_gt_six, mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)]
  exact_mod_cast hbound

/-! ## Small primes and the p = 7 counterexample -/

private theorem one_lt_sqrt_nat {n : ℕ} (hn : 1 < n) : (1 : ℝ) < Real.sqrt (n : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  exact_mod_cast hn

private theorem sqrt_seven_lt_three : Real.sqrt (7 : ℝ) < 3 := by
  have hlt : Real.sqrt 7 < Real.sqrt 9 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (7 : ℝ) < 9)
  have h9 : Real.sqrt 9 = (3 : ℝ) := by norm_num
  nlinarith [Real.sqrt_nonneg 7, hlt, h9]

private theorem one_le_two_sqrt {n : ℕ} (h : (1 : ℝ) < Real.sqrt (n : ℝ)) :
    (1 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hsqrt := le_of_lt h
  have h2 : (2 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2)
  exact le_of_lt (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2)

theorem mulModBSD_ramanujan_petersson_at_two :
    MulModBSDRamanujanPeterssonAt 2 Nat.prime_two := by
  dsimp [MulModBSDRamanujanPeterssonAt]
  rw [mulModBSDPrimeAp_real, mulModBSDPrimeHolonomyTrace_two, norm_natCast_complex]
  exact_mod_cast one_le_two_sqrt (one_lt_sqrt_nat (by decide : 1 < 2))

theorem mulModBSD_ramanujan_petersson_at_three :
    MulModBSDRamanujanPeterssonAt 3 Nat.prime_three := by
  dsimp [MulModBSDRamanujanPeterssonAt]
  rw [mulModBSDPrimeAp_real, mulModBSDPrimeHolonomyTrace_three, norm_natCast_complex]
  exact_mod_cast
    mul_le_mul_of_nonneg_left (le_of_lt (one_lt_sqrt_nat (by decide : 1 < 3))) (by norm_num : (0 : ℝ) ≤ 2)

theorem mulModBSD_ramanujan_petersson_at_five :
    MulModBSDRamanujanPeterssonAt 5 Nat.prime_five := by
  dsimp [MulModBSDRamanujanPeterssonAt]
  rw [mulModBSDPrimeAp_real, mulModBSDPrimeHolonomyTrace_five, norm_natCast_complex]
  exact_mod_cast one_le_two_sqrt (one_lt_sqrt_nat (by decide : 1 < 5))

theorem mulModBSD_ramanujan_petersson_fails_at_seven :
    ¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven := by
  intro h
  dsimp [MulModBSDRamanujanPeterssonAt] at h
  rw [mulModBSDPrimeAp_real, mulModBSDPrimeHolonomyTrace_seven, norm_natCast_complex] at h
  have hgt : (6 : ℝ) > 2 * Real.sqrt 7 := by
    nlinarith [Real.sqrt_nonneg 7, sqrt_seven_lt_three]
  exact not_le.mpr hgt h

theorem mulModBSD_global_ramanujan_petersson_fails :
    ¬ MulModBSDHeckeEigenformHypothesis := by
  intro h
  exact mulModBSD_ramanujan_petersson_fails_at_seven (h.ramanujan_petersson 7 Nat.prime_seven)

/-! ## Cascade prefix (11 … 41) -/

/--
**Scoped RP hypothesis:** Ramanujan–Petersson at cascade prefix chart primes except the
Fano base `7` (where RP fails).
-/
structure MulModBSDRamanujanPeterssonCascadePrefixHypothesis : Prop where
  at_eleven : MulModBSDRamanujanPeterssonAt 11 Nat.prime_eleven
  at_thirteen : MulModBSDRamanujanPeterssonAt 13 (by decide)
  at_seventeen : MulModBSDRamanujanPeterssonAt 17 (by decide)
  at_nineteen : MulModBSDRamanujanPeterssonAt 19 (by decide)
  at_twentyThree : MulModBSDRamanujanPeterssonAt 23 (by decide)
  at_twentyNine : MulModBSDRamanujanPeterssonAt 29 (by decide)
  at_thirtyOne : MulModBSDRamanujanPeterssonAt 31 (by decide)
  at_thirtySeven : MulModBSDRamanujanPeterssonAt 37 (by decide)
  at_fortyOne : MulModBSDRamanujanPeterssonAt 41 (by decide)

theorem mulModBSD_ramanujan_petersson_cascade_prefix :
    MulModBSDRamanujanPeterssonCascadePrefixHypothesis where
  at_eleven := mulModBSD_ramanujan_petersson_of_holonomy_six Nat.prime_eleven
    mulModBSDPrimeHolonomyTrace_eleven (by decide)
  at_thirteen := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_thirteen (by decide)
  at_seventeen := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_seventeen (by decide)
  at_nineteen := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_nineteen (by decide)
  at_twentyThree := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_twentyThree (by decide)
  at_twentyNine := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_twentyNine (by decide)
  at_thirtyOne := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_thirtyOne (by decide)
  at_thirtySeven := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_thirtySeven (by decide)
  at_fortyOne := mulModBSD_ramanujan_petersson_of_holonomy_six (by decide)
    mulModBSDPrimeHolonomyTrace_fortyOne (by decide)

end

end Hqiv.Algebra
