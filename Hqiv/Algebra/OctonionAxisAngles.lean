import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Axis angles `π/(2k)` from total prime-factor count `Ω`

This module **packages** the bookkeeping used in the octonion-sphere patch narrative:

* **`Ω n`** (`ArithmeticFunction.cardFactors`) counts prime factors **with multiplicity**.
* For shells `m > 1`, define the **intrinsic polar angle** `π / (2 * Ω m)` on the unwrapped circle model.
  Then **primes** (`Ω = 1`) sit at **`π/2`**, semiprimes with `Ω = 2` at **`π/4`**, etc.

* The **six quark poles** are the six nonzero non-EM Fano indices `1 … 6` inside `Fin 7` (vertex `0` is the EM /
  lepton axis in `Hqiv.Physics.FanoResonance`).

* **`k`-th roots of unity** use the standard equally spaced angles `2π j / k` (`j < k`); this is a different
  normalization from `π/(2k)`.

**What is *not* proved here:** that an external harmonic-analysis pipeline **must** recover these angles
without **defining** the map from arithmetic to angles. This file proves **internal consistency** of the
`Ω`–angle assignment and the **six-pole** embedding `Fin 6 ↪ Fin 7`.

See `AGENTS/archive/OCTONION_SPHERE_PATCH.md` §2.
-/

noncomputable section

open scoped ArithmeticFunction.Omega
open ArithmeticFunction

namespace Hqiv.Algebra

/-- Polar angle `π / (2k)` for integer `k ≥ 1` (narrative “`π/(2k)` axis”). -/
noncomputable def axisAngle (k : ℕ) (_hk : 0 < k) : ℝ :=
  Real.pi / (2 * k)

theorem axisAngle_pos (k : ℕ) (hk : 0 < k) : 0 < axisAngle k hk := by
  unfold axisAngle
  exact div_pos Real.pi_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Nat.cast_pos.mpr hk))

theorem axisAngle_one : axisAngle 1 (by decide : 0 < 1) = Real.pi / 2 := by
  unfold axisAngle
  simp

theorem axisAngle_two : axisAngle 2 (by decide : 0 < 2) = Real.pi / 4 := by
  unfold axisAngle
  field_simp
  ring

/-- Doubling the per-step axis angle yields `π/k` (two patch steps span a `k`-fold circle fraction). -/
theorem two_mul_axisAngle_eq_pi_div_k (k : ℕ) (hk : 0 < k) :
    2 * axisAngle k hk = Real.pi / k := by
  unfold axisAngle
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  field_simp [hk0]

/-- For `m > 1`, `Ω m > 0` (so `axisAngle (Ω m)` is well-formed). -/
theorem Omega_pos_of_one_lt {m : ℕ} (hm : 1 < m) : 0 < Ω m := by
  rwa [cardFactors_pos_iff_one_lt]

/-- Intrinsic angle from **total** prime-factor count (with multiplicity). -/
noncomputable def intrinsicShellAxisAngle (m : ℕ) (hm : 1 < m) : ℝ :=
  axisAngle (Ω m) (Omega_pos_of_one_lt hm)

theorem intrinsicShellAxisAngle_eq (m : ℕ) (hm : 1 < m) :
    intrinsicShellAxisAngle m hm = Real.pi / (2 * Ω m) := by
  simp [intrinsicShellAxisAngle, axisAngle]

/-- Primes (`Ω = 1`) lie at angle `π/2` (“base” opening — **one** prime factor). -/
theorem intrinsicShellAxisAngle_of_prime {p : ℕ} (hp : p.Prime) (hp1 : 1 < p) :
    intrinsicShellAxisAngle p hp1 = Real.pi / 2 := by
  rw [intrinsicShellAxisAngle_eq]
  simp [cardFactors_apply_prime hp]

/-- If `Ω m = 2`, the intrinsic angle is `π/4`. -/
theorem intrinsicShellAxisAngle_of_Omega_two {m : ℕ} (hm : 1 < m) (hΩ : Ω m = 2) :
    intrinsicShellAxisAngle m hm = Real.pi / 4 := by
  rw [intrinsicShellAxisAngle_eq, hΩ]
  norm_num

/-- If `Ω m = k`, the intrinsic angle is exactly the `π/(2k)` axis. -/
theorem intrinsicShellAxisAngle_eq_axisAngle_of_Omega {m : ℕ} (hm : 1 < m) {k : ℕ}
    (hk : 0 < k) (hΩ : Ω m = k) :
    intrinsicShellAxisAngle m hm = axisAngle k hk := by
  subst hΩ
  simp [intrinsicShellAxisAngle, axisAngle]

/-! ## Six quark poles inside `Fin 7` (EM vertex excluded) -/

/-- Fano vertex index: `0` = EM/lepton, `1…6` = quark lines (same convention as `FanoResonance`). -/
abbrev FanoVertex := Fin 7

/-- The six quark directions as `1 … 6` in `Fin 7`. -/
def quarkPole (i : Fin 6) : FanoVertex :=
  ⟨Nat.succ i.val, by
    have hi : i.val < 6 := i.is_lt
    exact Nat.succ_lt_succ hi⟩

theorem quarkPole_ne_em (i : Fin 6) : (quarkPole i).val ≠ 0 := by
  simp [quarkPole]

theorem quarkPole_injective : Function.Injective quarkPole := by
  intro i j h
  ext
  simpa [quarkPole, Fin.ext_iff] using congr_arg Fin.val h

/-- Angles of the standard `k`-th roots of unity on the circle: `2π j / k` for `j = 0 … k-1`. -/
noncomputable def kthRootUnityAngle (k : ℕ) (_hk : 0 < k) (j : Fin k) : ℝ :=
  (2 * Real.pi * j.val) / k

theorem kthRootUnityAngle_mem_Icc_two_pi (k : ℕ) (hk : 0 < k) (j : Fin k) :
    kthRootUnityAngle k hk j ∈ Set.Icc 0 (2 * Real.pi) := by
  unfold kthRootUnityAngle
  have hj : j.val < k := j.is_lt
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  constructor
  · positivity
  · have hj' : (j.val : ℝ) ≤ k := by exact_mod_cast Nat.le_of_lt hj
    rw [div_le_iff₀ hk']
    nlinarith [Real.pi_pos]

/-! ## Powers of two realize every `Ω = k` (hence every `π/(2k)` axis is populated) -/

theorem one_lt_two_pow_of_ne_zero {k : ℕ} (hk : k ≠ 0) : 1 < 2 ^ k :=
  one_lt_pow' (by decide : 1 < 2) hk

/-- For every `k ≥ 1`, some shell has `Ω = k` (e.g. `2^k`). -/
theorem exists_one_lt_with_Omega_eq {k : ℕ} (hk : 1 ≤ k) :
    ∃ m : ℕ, 1 < m ∧ Ω m = k := by
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk
    norm_num at hk
  refine ⟨2 ^ k, ?_, ?_⟩
  · exact one_lt_two_pow_of_ne_zero hk0
  · rw [cardFactors_apply_prime_pow Nat.prime_two]

theorem Omega_two_pow (k : ℕ) : Ω (2 ^ k) = k :=
  cardFactors_apply_prime_pow Nat.prime_two

/-- For every `K`, some `m > 1` has `Ω m ≥ K` (take `m = 2^K` when `K ≠ 0`, else `m = 2`). -/
theorem forall_le_exists_Omega_ge (K : ℕ) : ∃ m : ℕ, 1 < m ∧ K ≤ Ω m := by
  by_cases hK : K = 0
  · subst hK
    refine ⟨2, by decide, ?_⟩
    simp [cardFactors_apply_prime Nat.prime_two]
  · refine ⟨2 ^ K, ?_, ?_⟩
    · exact one_lt_two_pow_of_ne_zero hK
    · rw [Omega_two_pow]

/-- **Milestone:** for every `k ≥ 1`, some shell has `Ω m = k` and the intrinsic polar angle is exactly
`π/(2k)` — so every narrative `π/(2k)` axis appears on a concrete shell (witness `m = 2^k` from
`exists_one_lt_with_Omega_eq`). -/
theorem exists_one_lt_intrinsicShellAxisAngle_eq_pi_div_two_k (k : ℕ) (hk : 1 ≤ k) :
    ∃ (m : ℕ) (hm : 1 < m), intrinsicShellAxisAngle m hm = Real.pi / (2 * k) ∧ Ω m = k := by
  rcases exists_one_lt_with_Omega_eq hk with ⟨m, hm, hΩ⟩
  refine ⟨m, hm, ?_, hΩ⟩
  rw [intrinsicShellAxisAngle_eq, hΩ]

end Hqiv.Algebra

end
