import Hqiv.Geometry.ScaleOrbitMulMod
import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Mul-mod scale orbit → Δ holonomy / Goldbach spine

The map **`x ↦ (x · m) mod n`** (`scaleOrbitMulMod`) is the arithmetic holonomy
transport: when `Nat.Coprime m n`, it permutes every residue class and therefore
sweeps all positive tangency positions `1 ≤ k < n`.

This module connects that sweep to the existing geometric holonomy payloads in
`GoldbachG2Parity`:

* `LockedScaleOrbit.integer_positions` — complementary radii `k + (n − k) = n`;
* `LockedScaleOrbitBilateralPoleHit` — pole-locked left/right radii;
* `LockedScaleOrbitPrimeHit` — prime + prime ⇒ `GoldbachPair`.

## Status

| Layer | Content |
|-------|---------|
| **Proved** | Coprime mul-mod is bijective; hits every `0 < k < n`; complementary sum |
| **Proved** | Mul-mod sweep ⇒ bilateral complementary geometry |
| **Open** | Full `LockedScaleOrbit` from live `G₂` pole-lock + coprime `m` |
| **Open** | `DeltaHolonomyScaleOrbitCapturesIntegers`, prime hit selection |

The mul-mod tool discharges the **integer-capture arithmetic** once a coprime
multiplier is supplied by the Δ/G₂ holonomy lock; it does not replace the
`SO8AdmissibleHolonomy` certificate or global Goldbach discharge.
-/

namespace Hqiv.Story

open Hqiv.Geometry

/-! ## Mul-mod sweep ⇒ bilateral pole geometry -/

/--
From a mul-mod sweep, every position has the complementary-radius identity used
by `LockedScaleOrbitBilateralPoleHit`.
-/
theorem mul_mod_bilateral_complement_of_sweep (S : MulModScaleOrbitSweep n m)
    {k : ℕ} (hk₀ : 0 < k) (hk : k < n) :
    k + (n - k) = n ∧ (n - k) + k = n :=
  scaleOrbitMulMod_bilateral_complement hk₀ hk

/--
If a locked scale orbit uses the identity parameterization `scale_parameter k = k`,
the complementary-radius half of `integer_positions` is exactly the mul-mod
bilateral identity (independent of `m`).
-/
theorem locked_scale_orbit_complementary_radius (n : ℕ)
    {L : LockedG2TangentLanding n} (orbit : LockedScaleOrbit L)
    {k : ℕ} (hk₀ : 0 < k) (hk : k < n) :
    k + (n - k) = n :=
  (orbit.integer_positions k hk₀ hk).2

/-! ## Mul-mod hits ⇒ existence of a scale preimage at each position -/

theorem mul_mod_scale_orbit_hits_position (S : MulModScaleOrbitSweep n m)
    {k : ℕ} (hk₀ : 0 < k) (hk : k < n) :
    ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k :=
  mulModScaleOrbitSweep_hits S hk₀ hk

/-! ## Prime hit on a swept position ⇒ Goldbach pair -/

/--
Template: once a mul-mod sweep lands on a prime position with prime complement,
the existing `goldbach_pair_of_locked_scale_orbit_prime_hit` route applies.
This lemma records only the **arithmetic** prime split `p + (n − p) = n`.
-/
theorem goldbach_pair_of_mul_mod_prime_split {n p : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime (n - p)) (hpn : p ≤ n) :
    GoldbachPair n p (n - p) :=
  ⟨hp, hq, Nat.add_sub_of_le hpn⟩

/-! ## Holonomy chain hook -/

/--
**Arithmetic holonomy capture (proved).**  Coprime mul-mod sweeps every positive
position below `n`.  This is the modular backbone for
`DeltaHolonomyScaleOrbitCapturesIntegers` — the geometric Prop still needs a
`LockedG2TangentLanding` and pole-lock data, but the integer sweep is no longer
heuristic once `m` is coprime to `n`.
-/
theorem mul_mod_holonomy_sweeps_all_positions (n m : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    ∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k :=
  fun k hk₀ hk => scaleOrbitMulMod_hits_position (k := k) hn hcop hk₀ hk

/--
Relating mul-mod transport to zero–pair holonomy: if a midpoint pair exists at
`N`, the unconditional Hopf holonomy support still holds at every zero; mul-mod
supplies the **scale-axis permutation** that a full `LockedScaleOrbit` proof
can cite for residue coverage.
-/
theorem zero_holonomy_plus_mul_mod_sweep
    {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) {n m : ℕ} (hn : 0 < n)
    (hcop : Nat.Coprime m n) {N p q : ℕ} (hN : 0 < N) (hPair : GoldbachMidpointPair N p q) :
    HopfFiberMidpointHolonomySupport N p q ∧
      (∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k) := by
  refine ⟨?_, mul_mod_holonomy_sweeps_all_positions n m hn hcop⟩
  exact (zero_contains_pair_holonomy hzz hN hPair).2.2.2

/-!
**Proof strategy note.**  To discharge `DeltaHolonomyScaleOrbitCapturesIntegers` from
mul-mod, exhibit `m` coprime to `n` from the Δ holonomy index (typically the
locked harmonic multiplier / shell step) and build `LockedScaleOrbit` with
`scale_parameter k = (scaleOrbitMulMod n m k : ℝ)` once the `G₂` pole-lock
certificate is in hand.
-/

end Hqiv.Story
