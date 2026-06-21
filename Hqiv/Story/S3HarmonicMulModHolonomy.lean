import Hqiv.Story.S3ScaleOrbitMulModHolonomy
import Hqiv.Story.S3HarmonicDeltaEvenOrbit
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Harmonic `6/5` orbit multiplier → mul-mod holonomy on Goldbach shells

The real harmonic orbit multiplier is `harmonicEvenOrbitMultiplier = 6/5`
(`S3HarmonicDeltaEvenOrbit`).  On the **integer holonomy** side this becomes a
coprime mul-mod step

`x ↦ (x · m) mod n`,  `m = harmonicOrbitMulModMultiplier n`,

which permutes every residue on the Goldbach shell `n = 2N = p + q`.

## Proved on certified shells

For the six small-composite witness shells
`8, 12, 16, 18, 20, 30` (midpoints `N = 4, 6, 8, 9, 10, 15`):

* `harmonic_multiplier_coprime_certified` — `m` is coprime to `n`;
* `harmonic_mul_mod_sweep_certified` — full `MulModScaleOrbitSweep` certificate;
* `midpoint_harmonic_mul_mod_bundle_*` — packages pair + sweep + zero holonomy.

## Open globally

Choosing `m` from `{6, 5, 11, 7}` is not coprime for every `n` (e.g. `n = 105`).
Global discharge still needs either a larger multiplier search or the full
`LockedScaleOrbit` geometric lock.
-/

namespace Hqiv.Story

open Hqiv.Geometry Complex

noncomputable section

/-! ## Harmonic link -/

theorem harmonic_orbit_multiplier_is_six_fifths :
    harmonicEvenOrbitMultiplier = 6 / 5 :=
  harmonicEvenOrbitMultiplier_eq_six_fifths

theorem harmonic_orbit_integer_step_eq_six {n : ℕ} (h : Nat.Coprime 6 n) :
    harmonicOrbitMulModMultiplier n = 6 :=
  harmonicOrbitMulModMultiplier_eq_six h

/-! ## Midpoint shell packaging -/

/--
Bundle: certified midpoint pair, Goldbach shell `2N`, harmonic mul-mod sweep.
-/
structure MidpointHarmonicMulModBundle (N p q : ℕ) where
  pair : GoldbachMidpointPair N p q
  shell : ℕ
  shell_eq : shell = 2 * N
  shell_certified : shell ∈ certifiedGoldbachShells
  multiplier : ℕ
  multiplier_eq : multiplier = harmonicOrbitMulModMultiplier shell
  coprime : Nat.Coprime multiplier shell
  sweep : MulModScaleOrbitSweep shell multiplier

def midpointShell (N : ℕ) : ℕ :=
  2 * N

theorem goldbach_shell_eq_sum {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    midpointShell N = p + q := by
  dsimp [midpointShell]
  exact (h.2.2.2.2).symm

noncomputable def midpointHarmonicMulModBundle (N p q : ℕ)
    (h : GoldbachMidpointPair N p q)
    (hShell : midpointShell N ∈ certifiedGoldbachShells) :
    MidpointHarmonicMulModBundle N p q where
  pair := h
  shell := midpointShell N
  shell_eq := rfl
  shell_certified := hShell
  multiplier := harmonicOrbitMulModMultiplier (midpointShell N)
  multiplier_eq := rfl
  coprime := harmonic_multiplier_coprime_certified (midpointShell N) hShell
  sweep := harmonic_mul_mod_sweep_certified (midpointShell N) hShell

/-! ## Certified midpoint instances -/

theorem midpoint_shell_four_mem : (8 : ℕ) ∈ certifiedGoldbachShells := by decide
theorem midpoint_shell_six_mem : (12 : ℕ) ∈ certifiedGoldbachShells := by decide
theorem midpoint_shell_eight_mem : (16 : ℕ) ∈ certifiedGoldbachShells := by decide
theorem midpoint_shell_nine_mem : (18 : ℕ) ∈ certifiedGoldbachShells := by decide
theorem midpoint_shell_ten_mem : (20 : ℕ) ∈ certifiedGoldbachShells := by decide
theorem midpoint_shell_fifteen_mem : (30 : ℕ) ∈ certifiedGoldbachShells := by decide

noncomputable def harmonicMulModBundle_four :
    MidpointHarmonicMulModBundle 4 3 5 :=
  midpointHarmonicMulModBundle 4 3 5 goldbach_midpoint_pair_four_three_five
    midpoint_shell_four_mem

noncomputable def harmonicMulModBundle_six :
    MidpointHarmonicMulModBundle 6 5 7 :=
  midpointHarmonicMulModBundle 6 5 7 goldbach_midpoint_pair_six_five_seven
    midpoint_shell_six_mem

noncomputable def harmonicMulModBundle_eight :
    MidpointHarmonicMulModBundle 8 5 11 :=
  midpointHarmonicMulModBundle 8 5 11 goldbach_midpoint_pair_eight_five_eleven
    midpoint_shell_eight_mem

noncomputable def harmonicMulModBundle_nine :
    MidpointHarmonicMulModBundle 9 7 11 :=
  midpointHarmonicMulModBundle 9 7 11 goldbach_midpoint_pair_nine_seven_eleven
    midpoint_shell_nine_mem

noncomputable def harmonicMulModBundle_ten :
    MidpointHarmonicMulModBundle 10 3 17 :=
  midpointHarmonicMulModBundle 10 3 17 goldbach_midpoint_pair_ten_three_seventeen
    midpoint_shell_ten_mem

noncomputable def harmonicMulModBundle_fifteen :
    MidpointHarmonicMulModBundle 15 7 23 :=
  midpointHarmonicMulModBundle 15 7 23 goldbach_midpoint_pair_fifteen_seven_twentythree
    midpoint_shell_fifteen_mem

theorem harmonic_mul_mod_bundles_small_composites :
    Nonempty (MidpointHarmonicMulModBundle 4 3 5) ∧
      Nonempty (MidpointHarmonicMulModBundle 6 5 7) ∧
      Nonempty (MidpointHarmonicMulModBundle 8 5 11) ∧
      Nonempty (MidpointHarmonicMulModBundle 9 7 11) ∧
      Nonempty (MidpointHarmonicMulModBundle 10 3 17) ∧
      Nonempty (MidpointHarmonicMulModBundle 15 7 23) :=
  ⟨⟨harmonicMulModBundle_four⟩, ⟨harmonicMulModBundle_six⟩, ⟨harmonicMulModBundle_eight⟩,
    ⟨harmonicMulModBundle_nine⟩, ⟨harmonicMulModBundle_ten⟩, ⟨harmonicMulModBundle_fifteen⟩⟩

/-! ## Zero holonomy + harmonic mul-mod on certified midpoints -/

theorem midpointHarmonicMulModBundle_hits {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) {k : ℕ} (hk₀ : 0 < k) (hk : k < B.shell) :
    ∃ x : ℕ, x < B.shell ∧ scaleOrbitMulMod B.shell B.multiplier x = k :=
  B.sweep.hits k hk₀ hk

theorem zero_holonomy_harmonic_mul_mod_four {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 4 3 5 ∧
      (∀ k : ℕ, 0 < k → k < 8 →
        ∃ x : ℕ, x < 8 ∧ scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) x = k) := by
  have B := harmonicMulModBundle_four
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_six {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 6 5 7 ∧
      (∀ k : ℕ, 0 < k → k < 12 →
        ∃ x : ℕ, x < 12 ∧ scaleOrbitMulMod 12 (harmonicOrbitMulModMultiplier 12) x = k) := by
  have B := harmonicMulModBundle_six
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_eight {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 8 5 11 ∧
      (∀ k : ℕ, 0 < k → k < 16 →
        ∃ x : ℕ, x < 16 ∧ scaleOrbitMulMod 16 (harmonicOrbitMulModMultiplier 16) x = k) := by
  have B := harmonicMulModBundle_eight
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_nine {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 9 7 11 ∧
      (∀ k : ℕ, 0 < k → k < 18 →
        ∃ x : ℕ, x < 18 ∧ scaleOrbitMulMod 18 (harmonicOrbitMulModMultiplier 18) x = k) := by
  have B := harmonicMulModBundle_nine
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_ten {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 10 3 17 ∧
      (∀ k : ℕ, 0 < k → k < 20 →
        ∃ x : ℕ, x < 20 ∧ scaleOrbitMulMod 20 (harmonicOrbitMulModMultiplier 20) x = k) := by
  have B := harmonicMulModBundle_ten
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_fifteen {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 15 7 23 ∧
      (∀ k : ℕ, 0 < k → k < 30 →
        ∃ x : ℕ, x < 30 ∧ scaleOrbitMulMod 30 (harmonicOrbitMulModMultiplier 30) x = k) := by
  have B := harmonicMulModBundle_fifteen
  refine ⟨?_, fun k hk₀ hk => ?_⟩
  · exact (zero_contains_pair_holonomy hzz (by decide) B.pair).2.2.2
  · simpa [B.shell_eq, B.multiplier_eq] using
      midpointHarmonicMulModBundle_hits B hk₀ (by simpa [B.shell_eq] using hk)

theorem zero_holonomy_harmonic_mul_mod_small_composites {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 4 3 5 ∧
      HopfFiberMidpointHolonomySupport 6 5 7 ∧
      HopfFiberMidpointHolonomySupport 8 5 11 ∧
      HopfFiberMidpointHolonomySupport 9 7 11 ∧
      HopfFiberMidpointHolonomySupport 10 3 17 ∧
      HopfFiberMidpointHolonomySupport 15 7 23 ∧
      (∀ n ∈ certifiedGoldbachShells, HarmonicMulModMultiplierCoprimeObstruction n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (zero_holonomy_harmonic_mul_mod_four hzz).1
  · exact (zero_holonomy_harmonic_mul_mod_six hzz).1
  · exact (zero_holonomy_harmonic_mul_mod_eight hzz).1
  · exact (zero_holonomy_harmonic_mul_mod_nine hzz).1
  · exact (zero_holonomy_harmonic_mul_mod_ten hzz).1
  · exact (zero_holonomy_harmonic_mul_mod_fifteen hzz).1
  · exact harmonic_mul_mod_multiplier_coprime_certified_shells

/--
Prime split on a swept shell: if position `p` and complement `n − p` are both prime,
this is a `GoldbachPair` — the mul-mod route to a locked-scale prime hit.
-/
theorem goldbach_pair_of_harmonic_mul_mod_prime_split {n p : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime (n - p)) (hpn : p ≤ n) :
    GoldbachPair n p (n - p) :=
  goldbach_pair_of_mul_mod_prime_split hp hq hpn

theorem harmonic_mul_mod_prime_split_four :
    GoldbachPair 8 3 5 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_four_three_five

theorem harmonic_mul_mod_prime_split_six :
    GoldbachPair 12 5 7 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_six_five_seven

theorem harmonic_mul_mod_prime_split_eight :
    GoldbachPair 16 5 11 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_eight_five_eleven

theorem harmonic_mul_mod_prime_split_nine :
    GoldbachPair 18 7 11 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_nine_seven_eleven

theorem harmonic_mul_mod_prime_split_ten :
    GoldbachPair 20 3 17 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_ten_three_seventeen

theorem harmonic_mul_mod_prime_split_fifteen :
    GoldbachPair 30 7 23 :=
  goldbach_pair_of_midpoint_pair goldbach_midpoint_pair_fifteen_seven_twentythree

theorem harmonic_mul_mod_prime_splits_certified_midpoints :
    GoldbachPair 8 3 5 ∧ GoldbachPair 12 5 7 ∧ GoldbachPair 16 5 11 ∧
      GoldbachPair 18 7 11 ∧ GoldbachPair 20 3 17 ∧ GoldbachPair 30 7 23 :=
  ⟨harmonic_mul_mod_prime_split_four, harmonic_mul_mod_prime_split_six,
    harmonic_mul_mod_prime_split_eight, harmonic_mul_mod_prime_split_nine,
    harmonic_mul_mod_prime_split_ten, harmonic_mul_mod_prime_split_fifteen⟩

/-!
**Next discharge step.**  From `MidpointHarmonicMulModBundle` + a prime hit at swept
position `p`, invoke `goldbach_pair_of_locked_scale_orbit_prime_hit` once a full
`LockedScaleOrbit` is built with `scale_parameter k = (scaleOrbitMulMod n m k : ℝ)`.
-/

end

end Hqiv.Story
