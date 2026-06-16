import Hqiv.Story.S3ExplicitFormulaIdentity
import Hqiv.Story.S3HigherTwiddleFactorizationProbe
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Semiprime mediation on explicit-formula weights

Higher-twiddle cross-talk is typed to survive only on **semiprime** spectral indices
(`SemiprimeSupportedWeight` in `S3HigherTwiddleFactorizationProbe`).  The explicit
formula's prime-side weights are carried by **von Mangoldt** `Λ`, which is nonzero
exactly on prime powers.

This module proves the **mediation theorem**: the two carriers decouple on primes and
on square-free semiprimes; the only overlap is **prime squares** `p²`.  Quantitative
finite-frame bounds show the Λ-side contribution is carried by at most `√N` indices
and vanishes in the frame average at rate `(log N) / √N`.

RH discharge remains on the main `interiorStripH` capstone; probe channels do not
locate zeros.
-/

namespace Hqiv.Story

open ArithmeticFunction Nat Real

noncomputable section

/-! ## Prime squares inside finite frames -/

/-- `n` is a prime square `p²`. -/
def isPrimeSquare (n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ n = p * p

instance (n : ℕ) : Decidable (isPrimeSquare n) := by
  classical
  unfold isPrimeSquare
  infer_instance

theorem isPrimeSquare_iff {n : ℕ} :
    isPrimeSquare n ↔ ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2 := by
  simp [isPrimeSquare, pow_two, mul_comm]

theorem isPrimeSquare_implies_isSemiprime {n : ℕ} (h : isPrimeSquare n) :
    isSemiprime n := by
  rcases h with ⟨p, hp, heq⟩
  exact ⟨p, p, hp, hp, heq.symm⟩

theorem isPrimeSquare_prime_eq {n : ℕ} (h : isPrimeSquare n) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (heq : p * q = n) : p = q := by
  rcases h with ⟨r, hr, hnn⟩
  have heqr : p * q = r * r := heq.trans hnn
  have hrdiv : r ∣ p * q := by rw [heqr]; exact dvd_mul_left r r
  rcases (Nat.Prime.dvd_mul hr).1 hrdiv with hrp | hrq
  · have hpr : r = p := ((Nat.dvd_prime hp).1 hrp).resolve_left (Nat.Prime.ne_one hr)
    rw [hpr] at heqr
    exact Nat.mul_left_cancel (Nat.Prime.pos hp) heqr.symm
  · have hqr : r = q := ((Nat.dvd_prime hq).1 hrq).resolve_left (Nat.Prime.ne_one hr)
    rw [hqr] at heqr
    exact Nat.mul_right_cancel (Nat.Prime.pos hq) heqr

theorem isSemiprime_not_prime_square_iff {n : ℕ} :
    isSemiprime n ∧ ¬isPrimeSquare n ↔
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p * q = n := by
  constructor
  · rintro ⟨hsemi, hps⟩
    rcases hsemi with ⟨p, q, hp, hq, heq⟩
    refine ⟨p, q, hp, hq, ?_, heq⟩
    intro heq'
    apply hps
    exact ⟨p, hp, by rw [← heq, heq', mul_comm]⟩
  · rintro ⟨p, q, hp, hq, hne, heq⟩
    exact ⟨⟨p, q, hp, hq, heq⟩, fun hps => hne (isPrimeSquare_prime_eq hps hp hq heq)⟩

/-- Prime-square indices visible in the level-`N` frame. -/
def primeSquareIndicesInFrame (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => isPrimeSquare n)

theorem mem_primeSquareIndicesInFrame {n N : ℕ} :
    n ∈ primeSquareIndicesInFrame N ↔ isPrimeSquare n ∧ 1 ≤ n ∧ n ≤ N := by
  simp [primeSquareIndicesInFrame, Finset.mem_filter, Finset.mem_Icc, and_assoc, and_comm,
    and_left_comm]

theorem mem_primeSquareIndicesInFrame_primes {n N : ℕ}
    (hn : n ∈ primeSquareIndicesInFrame N) :
    ∃ p ≤ Nat.sqrt N, Nat.Prime p ∧ n = p * p := by
  rcases (mem_primeSquareIndicesInFrame.mp hn).1 with ⟨p, hp, heq⟩
  have hp2 : p * p ≤ N := heq.symm.trans_le (mem_primeSquareIndicesInFrame.mp hn).2.2
  exact ⟨p, Nat.le_sqrt.mpr hp2, hp, heq⟩

/-- Prime roots whose squares lie in the frame. -/
def primeSquareRootsInFrame (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.sqrt N)).filter Nat.Prime

theorem Finset.card_Icc_one_le (k : ℕ) : (Finset.Icc 1 k).card ≤ k + 1 := by
  have hsub : Finset.Icc 1 k ⊆ Finset.range (k + 1) := by
    intro x hx
    simp [Finset.mem_Icc, Finset.mem_range] at hx ⊢
    omega
  exact le_trans (Finset.card_le_card hsub) (by simp)

theorem primeSquareRootsInFrame_card_le_sqrt (N : ℕ) :
    (primeSquareRootsInFrame N).card ≤ Nat.sqrt N + 1 := by
  exact le_trans (Finset.card_filter_le _ _) (Finset.card_Icc_one_le (Nat.sqrt N))

noncomputable def primeSquareInFrameImage (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.sqrt N)).image (fun p => p * p)

theorem primeSquareIndicesInFrame_subset_Icc (N : ℕ) :
    primeSquareIndicesInFrame N ⊆ Finset.Icc 1 N := by
  intro n hn
  exact Finset.mem_Icc.mpr (mem_primeSquareIndicesInFrame.mp hn).2

theorem primeSquareIndicesInFrame_subset_image (N : ℕ) :
    primeSquareIndicesInFrame N ⊆ primeSquareInFrameImage N := by
  intro n hn
  obtain ⟨p, hple, hp, heq⟩ := mem_primeSquareIndicesInFrame_primes hn
  simp only [primeSquareInFrameImage, Finset.mem_image, Finset.mem_Icc]
  exact ⟨p, ⟨Nat.one_le_of_lt (Nat.Prime.one_lt hp), hple⟩, heq.symm⟩

theorem primeSquareInFrameImage_card_le_sqrt (N : ℕ) :
    (primeSquareInFrameImage N).card ≤ Nat.sqrt N + 1 := by
  exact le_trans Finset.card_image_le (Finset.card_Icc_one_le (Nat.sqrt N))

theorem primeSquareIndicesInFrame_card_le (N : ℕ) :
    (primeSquareIndicesInFrame N).card ≤ N := by
  refine le_trans (Finset.card_le_card (primeSquareIndicesInFrame_subset_Icc N)) ?_
  simp [Nat.card_Icc]

theorem primeSquareIndicesInFrame_card_le_sqrt (N : ℕ) :
    (primeSquareIndicesInFrame N).card ≤ Nat.sqrt N + 1 := by
  exact le_trans (Finset.card_le_card (primeSquareIndicesInFrame_subset_image N))
    (primeSquareInFrameImage_card_le_sqrt N)

/-! ## Real semiprime support (explicit-formula side) -/

/-- Real cross-talk carrier supported only on semiprime indices. -/
def SemiprimeSupportedRealWeight (w : ℕ → ℝ) : Prop :=
  ∀ n, ¬isSemiprime n → w n = 0

theorem semiprime_supported_real_weight_zero_on_prime {w : ℕ → ℝ}
    (h : SemiprimeSupportedRealWeight w) {p : ℕ} (hp : Nat.Prime p) :
    w p = 0 :=
  h p (not_isSemiprime_of_prime hp)

theorem semiprime_supported_real_iff_complex {w : ℕ → ℝ} :
    SemiprimeSupportedRealWeight w ↔
      SemiprimeSupportedWeight (fun n => (w n : ℂ)) := by
  constructor
  · intro h n hnot
    show (w n : ℂ) = 0
    exact mod_cast h n hnot
  · intro h n hnot
    exact Complex.ofReal_injective (h n hnot)

/-! ## von Mangoldt on semiprimes -/

theorem not_isPrimePow_of_two_distinct_primes {a b : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hne : a ≠ b) :
    ¬IsPrimePow (a * b) := by
  intro hpow
  obtain ⟨r, k, hr, hk, heq⟩ := (isPrimePow_nat_iff (a * b)).mp hpow
  have havd : a ∣ r ^ k := by rw [heq]; exact Nat.dvd_mul_right a b
  obtain ⟨t, _ht, hpt⟩ := (Nat.dvd_prime_pow hr).1 havd
  have hr_eq : r = a := by
    by_cases ht0 : t = 0
    · subst ht0
      simp at hpt
      exact absurd (hpt ▸ ha) Nat.not_prime_one
    · by_cases ht1 : t = 1
      · rw [ht1, pow_one] at hpt
        exact hpt.symm
      · have hge2 : 2 ≤ t := by omega
        exact absurd (hpt ▸ ha) (Nat.Prime.not_prime_pow (x := r) hge2)
  rw [hr_eq] at heq
  have hb_eq : a ^ (k - 1) = b := by
    have hkpos : 0 < k := hk
    have hle : 1 ≤ k := Nat.succ_le_iff.mpr hkpos
    have hsucc : a ^ k = a * a ^ (k - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, tsub_add_cancel_of_le hle]
    have hmul : a ^ k = a * b := by rw [heq]
    exact Nat.mul_left_cancel (Nat.Prime.pos ha) (hsucc.symm.trans hmul)
  by_cases hk1 : k = 1
  · rw [hk1, Nat.sub_self, pow_zero] at hb_eq
    have hp1 : Nat.Prime 1 := hb_eq.symm ▸ hb
    exact absurd hp1 Nat.not_prime_one
  · by_cases hkm1one : k - 1 = 1
    · rw [hkm1one, pow_one] at hb_eq
      exact hne hb_eq
    · have hge2 : 2 ≤ k - 1 := by omega
      have hbpow : Nat.Prime (a ^ (k - 1)) := hb_eq ▸ hb
      exact absurd hbpow (Nat.Prime.not_prime_pow (x := a) hge2)

theorem vonMangoldt_squarefree_semiprime_eq_zero {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    vonMangoldt (p * q) = 0 :=
  vonMangoldt_eq_zero_iff.mpr (not_isPrimePow_of_two_distinct_primes hp hq hne)

theorem vonMangoldt_eq_zero_of_squarefree_semiprime {n : ℕ}
    (h : isSemiprime n) (hps : ¬isPrimeSquare n) :
    vonMangoldt n = 0 := by
  rcases (isSemiprime_not_prime_square_iff.mp ⟨h, hps⟩) with
    ⟨p, q, hp, hq, hne, heq⟩
  rw [← heq]
  exact vonMangoldt_squarefree_semiprime_eq_zero hp hq hne

theorem isSemiprime_prime_square {p : ℕ} (hp : Nat.Prime p) :
    isSemiprime (p * p) :=
  ⟨p, p, hp, hp, rfl⟩

theorem vonMangoldt_prime_square {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldt (p * p) = Real.log p := by
  rw [show p * p = p ^ 2 by ring]
  rw [vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0), vonMangoldt_apply_prime hp]

/-! ## Explicit-formula weight pairing -/

/--
Finite truncation of the explicit-formula prime-side pairing against a spectral
carrier `w`:

`∑_{n ≤ N} Λ(n) · w(n)`.
-/
noncomputable def explicitFormulaWeightPair (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, vonMangoldt n * w n

/--
**Prime-square-only sum.**  Under semiprime support, the Λ-side pairing collapses to
prime squares inside the frame; every other index contributes zero.
-/
theorem explicitFormulaWeightPair_eq_prime_square_sum
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) (N : ℕ) :
    explicitFormulaWeightPair N w =
      ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * w n := by
  unfold explicitFormulaWeightPair
  exact (Finset.sum_subset (primeSquareIndicesInFrame_subset_Icc N) (by
    intro n hn hnot
    have hps : ¬isPrimeSquare n :=
      fun hps => hnot (mem_primeSquareIndicesInFrame.mpr ⟨hps, Finset.mem_Icc.mp hn⟩)
    by_cases hw : w n = 0
    · rw [hw, mul_zero]
    · have hsemi : isSemiprime n := by
        by_contra hnotsemi
        exact hw (h n hnotsemi)
      rw [vonMangoldt_eq_zero_of_squarefree_semiprime hsemi hps, zero_mul])).symm

theorem explicitFormulaWeightPair_eq_zero_of_no_prime_squares
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) (N : ℕ)
    (hempty : primeSquareIndicesInFrame N = ∅) :
    explicitFormulaWeightPair N w = 0 := by
  rw [explicitFormulaWeightPair_eq_prime_square_sum h, hempty, Finset.sum_empty]

/-- Frame average of the Λ-side pairing: `(∑ Λ(n) w(n)) / N`. -/
noncomputable def frameAverageExplicitPair (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  explicitFormulaWeightPair N w / N

theorem frameAverageExplicitPair_eq_zero_of_no_prime_squares
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) (N : ℕ)
    (hempty : primeSquareIndicesInFrame N = ∅) :
    frameAverageExplicitPair N w = 0 := by
  unfold frameAverageExplicitPair
  rw [explicitFormulaWeightPair_eq_zero_of_no_prime_squares h N hempty, zero_div]

theorem vonMangoldt_prime_square_le_log {p N : ℕ} (hp : Nat.Prime p) (hN1 : 1 ≤ N)
    (hN : p * p ≤ N) :
    Real.log p ≤ Real.log N := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp)
  exact Real.log_le_log hp0 (Nat.cast_le.mpr (le_trans (Nat.le_mul_self p) hN))

theorem primeSquareIndicesInFrame_vonMangoldt_sum_le
    (N : ℕ) (hN1 : 1 ≤ N) :
    ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n ≤
      (primeSquareIndicesInFrame N).card * Real.log N := by
  calc
    ∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n ≤
        ∑ _ ∈ primeSquareIndicesInFrame N, Real.log N :=
      Finset.sum_le_sum fun n hn => by
        obtain ⟨p, _, hp, heq⟩ := mem_primeSquareIndicesInFrame_primes hn
        have hp2 : p * p ≤ N := heq.symm.trans_le (mem_primeSquareIndicesInFrame.mp hn).2.2
        rw [show vonMangoldt n = Real.log p from by rw [heq, vonMangoldt_prime_square hp]]
        exact vonMangoldt_prime_square_le_log hp hN1 hp2
    _ = (primeSquareIndicesInFrame N).card * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]

/--
**Quantitative smallness.**  If `|w n| ≤ C` on the frame, the Λ-side pairing is
bounded by `C` times at most `√N` prime-square weights, each at most `log N`.
-/
theorem explicitFormulaWeightPair_abs_le
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) {N : ℕ} (hN1 : 1 ≤ N) (C : ℝ)
    (hC : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ C) (hC0 : 0 ≤ C) :
    |explicitFormulaWeightPair N w| ≤
      C * (primeSquareIndicesInFrame N).card * Real.log N := by
  rw [explicitFormulaWeightPair_eq_prime_square_sum h]
  have hterm :
      ∀ n ∈ primeSquareIndicesInFrame N,
        |vonMangoldt n * w n| ≤ C * Real.log N := by
    intro n hn
    obtain ⟨p, _, hp, heq⟩ := mem_primeSquareIndicesInFrame_primes hn
    have hmem := mem_primeSquareIndicesInFrame.mp hn
    have hp2 : p * p ≤ N := heq.symm.trans_le hmem.2.2
    have hnIcc : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hmem.2.1, hmem.2.2⟩
    rw [heq, vonMangoldt_prime_square hp]
    have hw := hC (p * p) (by simpa [heq] using hnIcc)
    have hlog := vonMangoldt_prime_square_le_log hp hN1 hp2
    have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Nat.Prime.one_le hp)
    calc
      |Real.log p * w (p * p)| = Real.log p * |w (p * p)| := by
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg hp1)]
      _ ≤ Real.log p * C := mul_le_mul_of_nonneg_left hw
          (Real.log_nonneg hp1)
      _ ≤ Real.log N * C := mul_le_mul_of_nonneg_right hlog hC0
      _ = C * Real.log N := mul_comm _ _
  have hsum :=
    Finset.sum_le_sum hterm
  have hsum' :
      ∑ n ∈ primeSquareIndicesInFrame N, |vonMangoldt n * w n| ≤
        (primeSquareIndicesInFrame N).card * (C * Real.log N) := by
    calc
      _ ≤ ∑ n ∈ primeSquareIndicesInFrame N, C * Real.log N := hsum
      _ = (primeSquareIndicesInFrame N).card * (C * Real.log N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc
    |∑ n ∈ primeSquareIndicesInFrame N, vonMangoldt n * w n| ≤
        ∑ n ∈ primeSquareIndicesInFrame N, |vonMangoldt n * w n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (primeSquareIndicesInFrame N).card * (C * Real.log N) := hsum'
    _ = C * (primeSquareIndicesInFrame N).card * Real.log N := by ring

/--
**Averaged vanishing rate.**  For `N ≥ 2` and a bounded semiprime carrier,
`|(∑ Λ w)/N| ≤ C · (log N)/N · |{p² ≤ N}|`, and the carrier count is at most `√N`.
-/
theorem frameAverageExplicitPair_abs_le
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) {N : ℕ} (hN : 2 ≤ N)
    (C : ℝ) (hC : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ C) (hC0 : 0 ≤ C) :
    |frameAverageExplicitPair N w| ≤
      C * (Nat.sqrt N + 1 : ℝ) * Real.log N / N := by
  unfold frameAverageExplicitPair
  have h1 : 1 ≤ N := Nat.one_le_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hbound := explicitFormulaWeightPair_abs_le h h1 C hC hC0
  have hcard : (primeSquareIndicesInFrame N).card ≤ Nat.sqrt N + 1 :=
    primeSquareIndicesInFrame_card_le_sqrt N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (Nat.one_le_cast.mpr h1)
  calc
    |frameAverageExplicitPair N w|
        ≤ C * (primeSquareIndicesInFrame N).card * Real.log N / N := by
          unfold frameAverageExplicitPair
          rw [abs_div, abs_of_pos hNpos]
          exact div_le_div_of_nonneg_right hbound (le_of_lt hNpos)
    _ ≤ C * (Nat.sqrt N + 1 : ℝ) * Real.log N / N := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hNpos)
          have hcardR : ((primeSquareIndicesInFrame N).card : ℝ) ≤ (Nat.sqrt N + 1 : ℝ) := by
            simpa [Nat.cast_add] using Nat.cast_le.mpr hcard
          convert mul_le_mul_of_nonneg_left hcardR (mul_nonneg hC0 hlog) using 1 <;> ring

/--
**Prime decoupling.**  A semiprime-supported carrier vanishes on primes, so the
Λ-weight at every prime index is zero.
-/
theorem semiprime_mediation_kills_prime_explicit_weight
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldt p * w p = 0 := by
  rw [semiprime_supported_real_weight_zero_on_prime h hp, mul_zero]

/--
**Square-free decoupling.**  von Mangoldt vanishes on square-free semiprimes
`pq` with `p ≠ q`.
-/
theorem semiprime_mediation_kills_squarefree_explicit_weight
    {w : ℕ → ℝ} {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    vonMangoldt (p * q) * w (p * q) = 0 := by
  rw [vonMangoldt_squarefree_semiprime_eq_zero hp hq hne, zero_mul]

/--
**Joint carrier classification.**  If both Λ and a semiprime-supported carrier
are nonzero at `n`, then `n = p²` for some prime `p`.
-/
theorem semiprime_mediation_joint_carrier_prime_square
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) {n : ℕ}
    (hΛ : vonMangoldt n ≠ 0) (hw : w n ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n = p * p := by
  have hsemi : isSemiprime n := by
    by_contra hnot
    exact hw (h n hnot)
  rcases hsemi with ⟨p, q, hp, hq, heq⟩
  have hpow : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
  rw [← heq] at hpow
  by_cases hne : p = q
  · exact ⟨p, hp, by rw [← heq, hne, mul_comm]⟩
  · exact ((not_isPrimePow_of_two_distinct_primes hp hq hne) hpow).elim

/--
**Semiprime mediation (explicit-formula weights).**  Packaging: prime indices and
square-free semiprime indices carry no Λ-side cross-talk; only prime squares can
pair a semiprime carrier with a nonzero von Mangoldt weight.
-/
theorem semiprime_mediation_explicit_formula
    {w : ℕ → ℝ} (h : SemiprimeSupportedRealWeight w) :
    (∀ p, Nat.Prime p → vonMangoldt p * w p = 0) ∧
      (∀ p q, Nat.Prime p → Nat.Prime q → p ≠ q →
        vonMangoldt (p * q) * w (p * q) = 0) ∧
      (∀ n, vonMangoldt n ≠ 0 → w n ≠ 0 → ∃ p, Nat.Prime p ∧ n = p * p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact semiprime_mediation_kills_prime_explicit_weight h hp
  · intro p q hp hq hne
    exact semiprime_mediation_kills_squarefree_explicit_weight hp hq hne
  · intro n hΛ hw
    exact semiprime_mediation_joint_carrier_prime_square h hΛ hw

/--
At prime squares the explicit-formula weight is exactly `log p` times the carrier.
-/
theorem semiprime_mediation_prime_square_weight {p : ℕ} (hp : Nat.Prime p) (w : ℕ → ℝ) :
    vonMangoldt (p * p) * w (p * p) = Real.log p * w (p * p) := by
  rw [vonMangoldt_prime_square hp]

/-- Complex semiprime mediation lifts to the spectral cross-talk bundle. -/
theorem semiprime_mediation_of_cross_talk
    (ct : HigherTwiddleCrossTalk) (h : ct.semiprimeMediated) {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldt p * (ct.weight p).re = 0 :=
  semiprime_mediation_kills_prime_explicit_weight
    (w := fun n => (ct.weight n).re)
    (by
      intro n hnot
      show (ct.weight n).re = 0
      rw [h n hnot, Complex.zero_re])
    hp

end

end Hqiv.Story
