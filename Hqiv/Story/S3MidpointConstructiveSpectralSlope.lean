import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3MidpointEulerSoeBridge
import Hqiv.Story.S3SpectralResonanceChanneling

/-!
# Constructive spectral slope forcing at the Goldbach midpoint

This module separates **what is proved constructively today** from the single
open discharge that must be a *spectral* argument (not a tautological rename).

## Constructive spine (proved)

1. **Finite angle stack** = `finiteSoeAngleStack N` (prime moduli `r ≤ sqrt(2N)`).
2. **Gap certificate** = `gapSurvivesFiniteAngleStack N g`: every modulus clears
   both forward/reflected residue rays at slot `p = N - g`.
3. **Sieve–primality (constructive, finite)** =
   `gap_survives_stack_iff_symmetric_prime`: the certificate ⟺ both arms `N ± g` prime.
4. **Composite reflected crossing (constructive witness)** =
   `composite_reflected_partner_crosses_stack`: if the left arm is prime and the
   reflected arm is composite, `minFac` gives an explicit stack modulus hitting it.
5. **Spectral channels do not vanish locally** =
   `gapSpectralChannel_ne_zero_of_symmetric`: at `Re s > 0`, a certified gap has
   nonzero joint line ` (N-g)^{-s} · (N+g)^{-s}`; finite Euler truncations also
   never vanish (`finite_spectral_truncation_ne_zero`).

## Open (must be spectral / finiteness forcing — not repackaging)

`FiniteStackCannotExtinctAllGaps N` / `ConstructiveSpectralForcesSlopeHit N`: for
composite `N`, the finite angle stack (`r ≤ sqrt(2N)`) cannot simultaneously cross
every positive gap on the slope orbit.  Equivalently Goldbach at the midpoint, but
the *obligated proof method* is constructive finite interference:

- proved per-gap decode (`constructive_gap_spectral_witness`);
- proved prime-slot failure ⇒ explicit reflect crossing (`prime_slot_failure_gives_reflect_cross`);
- proved composite reflected arm ⇒ `minFac` crossing (`composite_reflected_partner_crosses_stack`);
- open: global extinction impossible while composite mirror splits spectrally.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## 1. Joint spectral line at gap `g` -/

/-- **Joint spectral channel** at symmetric gap `g`: `(N-g)^{-s} · (N+g)^{-s}`. -/
noncomputable def gapSpectralChannel (N g : ℕ) (s : ℂ) : ℂ :=
  so4SpectralLine (N - g) s * so4SpectralLine (N + g) s

/-- **Euler synthesis** at gap: `(1-(N-g)^{-s})(1-(N+g)^{-s})`. -/
noncomputable def gapEulerSynthesis (N g : ℕ) (s : ℂ) : ℂ :=
  primeEulerFactor (N - g) s * primeEulerFactor (N + g) s

theorem gapSpectralChannel_ne_zero {N g : ℕ} (hp : 2 ≤ N - g) (hq : 2 ≤ N + g) (s : ℂ) :
    gapSpectralChannel N g s ≠ 0 := by
  unfold gapSpectralChannel so4SpectralLine
  apply mul_ne_zero
  · rw [Complex.cpow_ne_zero_iff]
    left
    exact Nat.cast_ne_zero.mpr (by omega)
  · rw [Complex.cpow_ne_zero_iff]
    left
    exact Nat.cast_ne_zero.mpr (by omega)

theorem gapSpectralChannel_ne_zero_of_symmetric {N g : ℕ} (h : symmetricPrimeReflectionAtGap N g)
    (s : ℂ) :
    gapSpectralChannel N g s ≠ 0 :=
  gapSpectralChannel_ne_zero (N := N) (g := g) h.1 h.2.2.two_le s

theorem gapEulerSynthesis_ne_zero_of_symmetric {N g : ℕ} {s : ℂ} (hs : 0 < s.re)
    (h : symmetricPrimeReflectionAtGap N g) :
    gapEulerSynthesis N g s ≠ 0 := by
  unfold gapEulerSynthesis
  rcases h with ⟨hp2, hpl, hpr⟩
  exact mul_ne_zero
    (prime_euler_factor_ne_zero_strip hs hpl)
    (prime_euler_factor_ne_zero_strip hs hpr)

theorem gapSpectral_eq_euler_on_prime_arms {N g : ℕ} {s : ℂ}
    (_h : symmetricPrimeReflectionAtGap N g) :
    gapSpectralChannel N g s =
      so4SpectralLine (N - g) s * so4SpectralLine (N + g) s ∧
      gapEulerSynthesis N g s =
        primeEulerFactor (N - g) s * primeEulerFactor (N + g) s := by
  constructor <;> rfl

/-! ## 2. Constructive profile (unconditional inputs) -/

/--
**Constructive spectral profile** at composite midpoint `N` and strip point `s`.
Packages every ingredient that is already proved without Goldbach.
-/
structure ConstructiveSpectralSlopeProfile (N : ℕ) (s : ℂ) (hs : 0 < s.re) where
  composite_mirror_splits :
    CompositeMidpointEulerSoeProfile N s hs
  stack_survivor_decodes :
    ∀ g, 2 ≤ N - g → N - g ≤ N →
      (gapSurvivesFiniteAngleStack N g ↔ symmetricPrimeReflectionAtGap N g)
  finite_truncation_never_vanishes :
    ∀ (F : Finset Nat.Primes), ∏ p ∈ F, primeEulerFactor (p : ℕ) s ≠ 0
  composite_reflected_crossing :
    ∀ p ∈ midpointScanSlots N, Nat.Prime p → ¬ Nat.Prime (2 * N - p) → 4 ≤ 2 * N - p →
      ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p

theorem constructive_spectral_slope_profile (N : ℕ) (s : ℂ) (hN : 2 ≤ N) (hs : 0 < s.re)
    (hc : ¬ Nat.Prime N) : ConstructiveSpectralSlopeProfile N s hs where
  composite_mirror_splits := composite_midpoint_euler_soe_profile N s hN hs hc
  stack_survivor_decodes g hp hle :=
    gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp hle
  finite_truncation_never_vanishes := fun F =>
    (finite_soe_and_finite_euler_parallel hN hs).2 F
  composite_reflected_crossing := fun p hp hpr hc hq =>
    composite_reflected_partner_crosses_stack hp hpr hc hq

/-! ## 3. Certified gap ⇒ slope hit (constructive decode) -/

theorem stack_survivor_gives_slope_hit {N g : ℕ} (hg : g ∈ midpointGapOrbit N)
    (_hgpos : 0 < g) (hStack : gapSurvivesFiniteAngleStack N g) :
    MidpointSlopeOrbitPrimeHit N := by
  obtain ⟨p, hpSlot, hgap⟩ := (mem_midpointGapOrbit_iff (N := N)).mp hg
  have hpLe : p ≤ N := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.2
  have hp2 : 2 ≤ N - g := by
    have hp2' : 2 ≤ p := (mem_midpointScanSlots_iff (N := N) (p := p)).mp hpSlot |>.1
    rw [show N - g = p from by unfold midpointLeftGap at hgap; rw [← hgap, Nat.sub_sub_self hpLe]]
    exact hp2'
  exact ⟨g, hg, (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 (Nat.sub_le N g)).mp hStack⟩

theorem stack_survivor_gives_spectral_channel {N g : ℕ} {s : ℂ} (hs : 0 < s.re)
    (hStack : gapSurvivesFiniteAngleStack N g) (hp : 2 ≤ N - g) (hle : N - g ≤ N) :
    symmetricPrimeReflectionAtGap N g ∧
      gapSpectralChannel N g s ≠ 0 ∧
        gapEulerSynthesis N g s ≠ 0 := by
  have hReflect := (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp hle).mp hStack
  exact ⟨hReflect, gapSpectralChannel_ne_zero_of_symmetric hReflect s,
    gapEulerSynthesis_ne_zero_of_symmetric hs hReflect⟩

/-! ## 4. Constructive obstruction chain (proved) vs finite extinction (open) -/

/--
**Per-gap decode (proved).**  Stack certificate ⟺ symmetric prime reflection ⟺
nonzero joint spectral / Euler channel on the strip.
-/
theorem constructive_gap_spectral_witness {N g : ℕ} {s : ℂ} (hs : 0 < s.re)
    (hp : 2 ≤ N - g) (hle : N - g ≤ N) :
    gapSurvivesFiniteAngleStack N g ↔
      symmetricPrimeReflectionAtGap N g ∧
        gapSpectralChannel N g s ≠ 0 ∧
          gapEulerSynthesis N g s ≠ 0 := by
  constructor
  · intro hStack
    have hReflect := (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp hle).mp hStack
    exact ⟨hReflect, gapSpectralChannel_ne_zero_of_symmetric hReflect s,
      gapEulerSynthesis_ne_zero_of_symmetric hs hReflect⟩
  · intro ⟨hReflect, _, _⟩
    exact (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp hle).mpr hReflect

/--
**Prime slot failure ⇒ explicit reflect crossing (proved).**  This is the
constructive SoE blocker behind spectral generalization: finitely many moduli
act as explicit angle witnesses, not as a restatement of Goldbach.
-/
theorem prime_slot_failure_gives_reflect_cross {N p : ℕ} (hpLe : p ≤ N) (hpr : Nat.Prime p)
    (hFail : ¬ gapSurvivesFiniteAngleStack N (midpointLeftGap N p)) :
    ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p :=
  prime_slot_stack_failure_forces_reflect_cross hpLe hpr hFail

/--
**Open target in extinction form.**  Prove `FiniteStackCannotExtinctAllGaps N` by
showing the finite angle stack cannot simultaneously cross every positive gap while
the composite mirror branch splits spectrally (`ConstructiveSpectralSlopeProfile`).
-/
theorem constructive_spectral_open_target (N : ℕ) :
    FiniteStackCannotExtinctAllGaps N ↔ ConstructiveSpectralForcesSlopeHit N :=
  finite_stack_extinction_iff_constructive N

theorem constructive_spectral_open_target_slope (N : ℕ) :
    FiniteStackCannotExtinctAllGaps N ↔ CompositeSlopeOrbitForcesPrimeReflection N := by
  rw [finite_stack_extinction_iff_constructive, constructive_spectral_forces_iff_slope_hit]

/-! ## 5. Examples (constructive certificates) -/

theorem constructive_stack_survivor_fifteen_eight :
    gapSurvivesFiniteAngleStack 15 8 := by
  have h := symmetric_prime_reflection_fifteen_eight
  have hp2 : 2 ≤ 15 - 8 := by decide
  have hle : 15 - 8 ≤ 15 := by decide
  exact (gap_survives_stack_iff_symmetric_prime (N := 15) (g := 8) hp2 hle).mpr h

theorem constructive_stack_survivor_eight_three :
    gapSurvivesFiniteAngleStack 8 3 := by
  have h := symmetric_prime_reflection_eight_three
  have hp2 : 2 ≤ 8 - 3 := by decide
  have hle : 8 - 3 ≤ 8 := by decide
  exact (gap_survives_stack_iff_symmetric_prime (N := 8) (g := 3) hp2 hle).mpr h

theorem constructive_spectral_forces_fifteen :
    ConstructiveSpectralForcesSlopeHit 15 := by
  intro _
  refine ⟨8, midpoint_gap_orbit_fifteen_eight, by decide, constructive_stack_survivor_fifteen_eight⟩

theorem constructive_spectral_forces_eight :
    ConstructiveSpectralForcesSlopeHit 8 := by
  intro _
  refine ⟨3, midpoint_gap_orbit_eight_three, by decide, constructive_stack_survivor_eight_three⟩

end

end Hqiv.Story
