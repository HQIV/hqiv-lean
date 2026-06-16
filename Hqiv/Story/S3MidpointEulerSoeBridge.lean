import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3EulerSpectralCancellation
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Midpoint SoE ↔ Euler spectral cancellation bridge

This module wires the **additive** midpoint overlay (`GoldbachG2Parity`) to the
**multiplicative** Euler prime spectrum (`S3SpectralResonanceChanneling`,
`S3EulerSpectralCancellation`, `S3ZeroHolonomyGoldbachChain`).

## Proved today

1. **Self-cancel (additive) ⟺ prime mirror** (`ReflectedSpectrumSelfCancel`).
2. **Composite mirror ⟺ nontrivial spectral product split** — composite midpoints
   cannot present as a single atomic spectral line; `N = a·b` with `1 < a,b`
   and `N^{−s} = a^{−s}·b^{−s}`.
3. **Dual survivor ⟺ Goldbach midpoint pair + both Euler legs nonzero** on the
   strip (`Re s > 0`): additive overlay survivors are exactly the prime pairs
   whose `(1 − p^{−s})` factors persist (no single-prime cancellation).
4. **Every additive survivor is activated at every ζ-zero** — collective
   cancellation uses both prime legs (`midpoint_survivor_zero_activates`).
5. **Finite SoE modulus spectrum** parallels **finite spectral truncation**
   cannot produce global cancellation.

## Open ( = Goldbach midpoint)

`MidpointEulerSoeDischarge N` ≡ `CompositeMidpointHasSurvivor N`: finitely many
SoE mod lines cannot kill every off-diagonal slot when the Euler side forbids
mirror self-cancel for composite `N`.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## Euler legs for midpoint pairs -/

/-- Prime Euler factor `(1 − p^{−s})`. -/
noncomputable def primeEulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  (1 : ℂ) - (p : ℂ) ^ (-s)

theorem prime_euler_factor_ne_zero_strip {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : Nat.Prime p) :
    primeEulerFactor p s ≠ 0 :=
  euler_factor_base_ne_zero_right_half hs ⟨p, hp⟩

theorem prime_euler_factor_eq {p : ℕ} (s : ℂ) :
    primeEulerFactor p s = (1 : ℂ) - (p : ℂ) ^ (-s) :=
  rfl

/-! ## 1. Composite mirror: additive no-self-cancel ↔ spectral branch -/

private theorem midpoint_nontrivial_factor_ge_two {m a b : ℕ} (hm : 2 ≤ m)
    (ha : a < m) (hb : b < m) (hab : a * b = m) : 2 ≤ a ∧ 2 ≤ b := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have ha2 : a < 2 := by omega
    interval_cases a
    · rw [Nat.zero_mul] at hab; omega
    · rw [Nat.one_mul] at hab; omega
  · by_contra hlt
    push_neg at hlt
    have hb2 : b < 2 := by omega
    interval_cases b
    · rw [Nat.mul_zero] at hab; omega
    · rw [Nat.mul_one] at hab; omega

/--
**Spectral branch at composite midpoints.**  A composite `N` cannot be atomic:
its spectral line splits through a nontrivial product, parallel to `4 = 2 × 2`.
-/
theorem composite_midpoint_nontrivial_spectral_split (N : ℕ) (s : ℂ) (hN : 2 ≤ N)
    (hc : ¬ Nat.Prime N) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = N ∧
      so4SpectralLine N s = so4SpectralLine a s * so4SpectralLine b s := by
  obtain ⟨a, b, ha, hb, hab⟩ := composite_has_nontrivial_factor hN hc
  exact ⟨a, b, (midpoint_nontrivial_factor_ge_two hN ha hb hab).1,
    (midpoint_nontrivial_factor_ge_two hN ha hb hab).2, hab,
    by rw [← hab, so4SpectralLine_mul]⟩

theorem composite_no_self_cancel_has_spectral_branch (N : ℕ) (s : ℂ) (hN : 2 ≤ N)
    (hc : ¬ ReflectedSpectrumSelfCancel N) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = N ∧
      so4SpectralLine N s = so4SpectralLine a s * so4SpectralLine b s := by
  have hnp : ¬ Nat.Prime N := fun h => hc ((reflected_spectrum_self_cancel_iff_prime N).mpr h)
  exact composite_midpoint_nontrivial_spectral_split N s hN hnp

/-! ## 2. Dual survivor ↔ pair + persistent Euler legs -/

theorem goldbachMidpointPair_to_dual_survivor {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    dualMidpointSurvivor N p := by
  obtain ⟨hp, hq, hle, hge, _⟩ := h
  have hq' : q = 2 * N - p := by omega
  unfold dualMidpointSurvivor sieveFromTwo sieveFromTwoN
  rw [show 2 * N - p = q from hq'.symm]
  exact ⟨hp, hq, hle, hge⟩

theorem dualMidpointSurvivor_euler_factors_ne_zero {N p : ℕ} (s : ℂ) (hs : 0 < s.re)
    (h : dualMidpointSurvivor N p) :
    primeEulerFactor p s ≠ 0 ∧
      primeEulerFactor (2 * N - p) s ≠ 0 := by
  rcases h with ⟨hp, hq, _, _⟩
  exact ⟨prime_euler_factor_ne_zero_strip hs hp,
    prime_euler_factor_ne_zero_strip hs hq⟩

/--
**Bridge cap (local).**  Additive overlay survivor at `p` is exactly a midpoint
Goldbach pair whose two Euler legs are nonzero on the strip — no single-prime
spectral cancellation on either arm.
-/
theorem dualMidpointSurvivor_iff_euler_pair_channel {N p : ℕ} (s : ℂ) (hs : 0 < s.re) :
    dualMidpointSurvivor N p ↔
      GoldbachMidpointPair N p (2 * N - p) ∧
        (primeEulerFactor p s ≠ 0 ∧ primeEulerFactor (2 * N - p) s ≠ 0) := by
  constructor
  · intro h
    refine ⟨dual_midpoint_survivor_gives_pair h, dualMidpointSurvivor_euler_factors_ne_zero s hs h⟩
  · intro ⟨hPair, _⟩
    exact goldbachMidpointPair_to_dual_survivor hPair

theorem midpointOverlaySurvivor_iff_euler_pair_channel {N p : ℕ} (s : ℂ) (hs : 0 < s.re)
    (hp : p ≤ N) :
    midpointOverlaySurvivor N p ↔
      GoldbachMidpointPair N p (2 * N - p) ∧
        (primeEulerFactor p s ≠ 0 ∧ primeEulerFactor (2 * N - p) s ≠ 0) := by
  rw [← (dualMidpointSurvivor_iff_overlay_of_left_bound (N := N) (p := p) hp),
    dualMidpointSurvivor_iff_euler_pair_channel (N := N) (p := p) s hs]

/-! ## 3. Collective cancellation activates every survivor pair -/

/--
At any nontrivial zero, an additive dual survivor's two prime legs are both
active in the collective Euler cancellation (`zero_activates_pair`).
-/
theorem midpoint_survivor_zero_activates {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ)
    {N p : ℕ} (h : dualMidpointSurvivor N p) :
    ((1 : ℂ) - (p : ℂ) ^ (-ρ)) ≠ 0 ∧
      ((1 : ℂ) - (Nat.cast (2 * N - p)) ^ (-ρ)) ≠ 0 := by
  rcases h with ⟨hp, hq, _, _⟩
  exact zero_activates_pair hzz hp hq

theorem midpoint_survivor_contains_holonomy {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ)
    {N p : ℕ} (h : dualMidpointSurvivor N p) :
    (((1 : ℂ) - (p : ℂ) ^ (-ρ)) ≠ 0 ∧ ((1 : ℂ) - (Nat.cast (2 * N - p)) ^ (-ρ)) ≠ 0) ∧
      so4SpectralLine (p * (2 * N - p)) ρ =
        so4SpectralLine p ρ * so4SpectralLine (2 * N - p) ρ ∧
      SO4OrthogonalTangentMidpointSlope N p (2 * N - p) = (1 / 2 : ℝ) ∧
      HopfFiberMidpointHolonomySupport N p (2 * N - p) := by
  have hN : 0 < N := by
    rcases h with ⟨hp, _, hle, _⟩
    have : 2 ≤ p := Nat.Prime.two_le hp
    omega
  exact zero_contains_pair_holonomy hzz hN (dual_midpoint_survivor_gives_pair h)

/-! ## 4. Finite SoE spectrum ↔ finite spectral truncation -/

/--
**Parallel finiteness.**  SoE up to `2N` uses only `soeModulusSpectrum (2N)`;
no finite Euler truncation `(1 − p^{−s})` can vanish on the strip — global
cancellation needs all primes (`finite_spectral_truncation_ne_zero`).
-/
theorem finite_soe_and_finite_euler_parallel {N : ℕ} (hN : 2 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    (soeModulusSpectrum (2 * N)).Nonempty ∧
      ∀ (F : Finset Nat.Primes), ∏ p ∈ F, primeEulerFactor (p : ℕ) s ≠ 0 := by
  constructor
  · refine ⟨2, ?_⟩
    simp only [soeModulusSpectrum, Finset.mem_filter, Finset.mem_Icc, Nat.Prime]
    refine ⟨?_, Nat.prime_two⟩
    have h4 : 4 ≤ 2 * N := by omega
    have hsq : 2 ≤ Nat.sqrt (2 * N) := by
      calc
        2 = Nat.sqrt 4 := by norm_num
        _ ≤ Nat.sqrt (2 * N) := Nat.sqrt_le_sqrt h4
    exact ⟨by decide, hsq⟩
  · intro F
    simpa [primeEulerFactor] using finite_spectral_truncation_ne_zero hs F

/-! ## 5. Open discharge target -/

/--
**Euler–SoE discharge (open).**  Composite midpoints cannot self-cancel additively
or spectrally at the mirror; finitely many SoE lines cannot kill every
off-diagonal slot — equivalently `CompositeMidpointHasSurvivor`.
-/
def MidpointEulerSoeDischarge (N : ℕ) : Prop :=
  FiniteSoeSpectrumForcesOffDiagonalSurvivor N

theorem midpoint_euler_soe_discharge_iff_composite (N : ℕ) :
    MidpointEulerSoeDischarge N ↔ CompositeMidpointHasSurvivor N := by
  unfold MidpointEulerSoeDischarge FiniteSoeSpectrumForcesOffDiagonalSurvivor
  rfl

/--
**Profile packaging.**  What is proved unconditionally for composite midpoint `N`
before discharging existence of an off-diagonal survivor.
-/
structure CompositeMidpointEulerSoeProfile (N : ℕ) (s : ℂ) (hs : 0 < s.re) where
  no_additive_self_cancel : ¬ ReflectedSpectrumSelfCancel N
  nontrivial_spectral_split :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = N ∧
      so4SpectralLine N s = so4SpectralLine a s * so4SpectralLine b s
  finite_soe_moduli : (soeModulusSpectrum (2 * N)).Nonempty
  finite_euler_truncation_never_vanishes :
    ∀ (F : Finset Nat.Primes), ∏ p ∈ F, primeEulerFactor (p : ℕ) s ≠ 0

theorem composite_midpoint_euler_soe_profile (N : ℕ) (s : ℂ) (hN : 2 ≤ N) (hs : 0 < s.re)
    (hc : ¬ Nat.Prime N) : CompositeMidpointEulerSoeProfile N s hs where
  no_additive_self_cancel := composite_no_reflected_self_cancel hc
  nontrivial_spectral_split := composite_midpoint_nontrivial_spectral_split N s hN hc
  finite_soe_moduli := (finite_soe_and_finite_euler_parallel hN hs).1
  finite_euler_truncation_never_vanishes := (finite_soe_and_finite_euler_parallel hN hs).2

theorem composite_midpoint_has_survivor_fifteen_euler :
    MidpointEulerSoeDischarge 15 := by
  unfold MidpointEulerSoeDischarge FiniteSoeSpectrumForcesOffDiagonalSurvivor
  exact composite_midpoint_has_survivor_fifteen

theorem composite_midpoint_has_survivor_eight_euler :
    MidpointEulerSoeDischarge 8 := by
  unfold MidpointEulerSoeDischarge FiniteSoeSpectrumForcesOffDiagonalSurvivor
  exact composite_midpoint_has_survivor_eight

end

end Hqiv.Story
