import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3MidpointEulerSoeBridge
import Hqiv.Story.S3MidpointConstructiveSpectralSlope

/-!
# Constructive spectral build of the forward SoE

The SoE is **built spectrally first**, then decoded to additive sieve legs.

## Layer 1 — spectral slot (proved)

At scan slot `p` on `p + q = 2N`, gap `g = N - p`:

- **Joint line** `soeSlotSpectralChannel N p s = (N-g)^{-s} · (N+g)^{-s} = p^{-s} · q^{-s}`
- **Euler synthesis** `soeSlotEulerSynthesis N p s = (1-p^{-s})(1-q^{-s})`

## Layer 2 — additive SoE (proved, equivalent on survivors)

- Forward leg `sieveFromTwo p` ⟺ left arm prime
- Reflected leg `sieveFromTwoN N p` ⟺ partner prime
- Finite stack `finiteSoeAngleStack N` ⟺ finitely many residue rays

## Layer 3 — decode (proved locally)

`soe_slot_reflection_iff_spectral` / `constructive_gap_spectral_witness`:
stack or slot reflection ⟺ symmetric primes ⟺ spectral/Euler nonzero on strip.

## What reflection means (not symmetric)

| Claim | Status |
|-------|--------|
| Mirror slot reflection ⟺ `N` prime | Proved |
| Off-diagonal reflection ⟹ `N` composite | **False** (`N = 5`, `3 + 7`) |
| Composite ⟹ off-diagonal reflection | Open (= Goldbach midpoint) |
| No reflection ⟹ `N` prime | Open (contrapositive) |

The composite-only theorem is **`composite_reflection_survivor_is_off_diagonal`**:
if `N` is composite and a scan reflection exists, it cannot be at the mirror.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## 1. Spectral SoE at scan slot `p` -/

/-- **Spectral SoE channel** at scan slot `p`: `(N-(N-p))^{-s} · (N+(N-p))^{-s}`. -/
noncomputable def soeSlotSpectralChannel (N p : ℕ) (s : ℂ) : ℂ :=
  gapSpectralChannel N (midpointLeftGap N p) s

/-- **Spectral SoE Euler synthesis** at slot `p`. -/
noncomputable def soeSlotEulerSynthesis (N p : ℕ) (s : ℂ) : ℂ :=
  gapEulerSynthesis N (midpointLeftGap N p) s

theorem soeSlotSpectralChannel_eq_arms {N p : ℕ} (s : ℂ) (hp : p ≤ N) :
    soeSlotSpectralChannel N p s = so4SpectralLine p s * so4SpectralLine (2 * N - p) s := by
  unfold soeSlotSpectralChannel gapSpectralChannel so4SpectralLine midpointLeftGap
  rw [Nat.sub_sub_self hp, show N + (N - p) = 2 * N - p from by omega]

theorem soeSlotEulerSynthesis_eq_arms {N p : ℕ} (s : ℂ) (hp : p ≤ N) :
    soeSlotEulerSynthesis N p s =
      primeEulerFactor p s * primeEulerFactor (2 * N - p) s := by
  unfold soeSlotEulerSynthesis gapEulerSynthesis primeEulerFactor midpointLeftGap
  rw [Nat.sub_sub_self hp, show N + (N - p) = 2 * N - p from by omega]

theorem soe_slot_reflection_iff_spectral {N p : ℕ} {s : ℂ} (hs : 0 < s.re) (hp : p ≤ N)
    (hp2 : 2 ≤ p) :
    symmetricPrimeReflectionAt N p ↔
      gapSurvivesFiniteAngleStack N (midpointLeftGap N p) ∧
        soeSlotSpectralChannel N p s ≠ 0 ∧
          soeSlotEulerSynthesis N p s ≠ 0 := by
  have hparm : 2 ≤ N - midpointLeftGap N p := by
    dsimp [midpointLeftGap]
    omega
  have hle : N - midpointLeftGap N p ≤ N := Nat.sub_le N _
  constructor
  · intro hReflect
    have hg := (symmetricPrimeReflectionAt_iff_gap (N := N) (p := p) hp).mp hReflect
    have hStack := (gap_survives_stack_iff_symmetric_prime (N := N)
      (g := midpointLeftGap N p) hparm hle).mpr hg
    exact ⟨hStack, gapSpectralChannel_ne_zero_of_symmetric hg s,
      gapEulerSynthesis_ne_zero_of_symmetric hs hg⟩
  · intro ⟨hStack, _, _⟩
    have hg := (gap_survives_stack_iff_symmetric_prime (N := N)
      (g := midpointLeftGap N p) hparm hle).mp hStack
    exact (symmetricPrimeReflectionAt_iff_gap (N := N) (p := p) hp).mpr hg

theorem soe_slot_reflection_iff_additive {N p : ℕ} (hp : p ∈ midpointScanSlots N) :
    symmetricPrimeReflectionAt N p ↔ dualMidpointSurvivor N p :=
  scan_slot_reflection_iff_survivor (N := N) (p := p) hp

/-! ## 2. Constructive spectral SoE profile (unconditional inputs) -/

/--
Packages the **spectral build + additive decode** available without Goldbach.
-/
structure ConstructiveSpectralSoeBuild (N : ℕ) (s : ℂ) (hs : 0 < s.re) where
  composite_profile : ConstructiveSpectralSlopeProfile N s hs
  slot_spectral_arms :
    ∀ p, p ≤ N →
      soeSlotSpectralChannel N p s = so4SpectralLine p s * so4SpectralLine (2 * N - p) s
  slot_euler_arms :
    ∀ p, p ≤ N →
      soeSlotEulerSynthesis N p s =
        primeEulerFactor p s * primeEulerFactor (2 * N - p) s
  mirror_tests_prime :
    symmetricPrimeReflectionAt N N ↔ Nat.Prime N
  reflection_not_composite_detector :
    ¬ (∀ N, offDiagonalPrimeReflection N → ¬ Nat.Prime N)

theorem constructive_spectral_soe_build (N : ℕ) (s : ℂ) (hN : 2 ≤ N) (hs : 0 < s.re)
    (hc : ¬ Nat.Prime N) : ConstructiveSpectralSoeBuild N s hs where
  composite_profile := constructive_spectral_slope_profile N s hN hs hc
  slot_spectral_arms := fun p hp => soeSlotSpectralChannel_eq_arms (N := N) (p := p) s hp
  slot_euler_arms := fun p hp => soeSlotEulerSynthesis_eq_arms (N := N) (p := p) s hp
  mirror_tests_prime := mirror_slot_reflection_iff_prime N
  reflection_not_composite_detector := off_diagonal_reflection_not_composite_test

/-! ## 3. Composite-only reflection lemma (proved) -/

theorem composite_scan_reflection_off_mirror {N p : ℕ} (hc : ¬ Nat.Prime N)
    (hp : p ∈ midpointScanSlots N) (h : symmetricPrimeReflectionAt N p) :
    p < N :=
  composite_reflection_survivor_is_off_diagonal hc h hp

theorem composite_off_diagonal_target_iff_goldbach (N : ℕ) :
    SOEForwardForcesOffDiagonalReflection N ↔ CompositeMidpointHasSurvivor N :=
  soe_forward_forces_off_diagonal_iff_composite N

end

end Hqiv.Story
