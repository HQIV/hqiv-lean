import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3HarmonicMulModHolonomy
import Hqiv.Story.S3TwinMulModTwiddleBridge
import Hqiv.Story.S3ZeroHolonomyGoldbachChain

/-!
# Δ plaquette holonomy ↔ harmonic mul-mod at square anchor `N = 4`

Minimal local bridge between Path C and the recent twin/mul-mod certificates:

* **Lie side:** seed commutator `[J₀₁, J₁₃] = J₀₃ = Δ₄` (`so4_seed_commutator_is_delta_generator`).
* **Harmonic side:** real orbit multiplier `6/5` (`harmonicEvenOrbitMultiplier`).
* **Integer holonomy side:** on certified twin shells `8` and `12`, the `6/5` shadow uses
  the denominator branch `m = 5` (`gcd(6,n) ≠ 1`).
* **Twin side:** gap-one arms are constructively hit on those shells.
* **Zero side (unconditional):** every nontrivial zero activates anchor holonomy and the
  full mul-mod sweep on shell `8`.

This is **local twin-ladder packaging** — no global discharge, no
`LockedScaleOrbit`, no claim that the commutator forces twin density.
-/

namespace Hqiv.Story

open Hqiv.Geometry Hqiv.Algebra Complex

noncomputable section

/-! ## Plaquette commutator = Δ seed generator -/

theorem so4_seed_commutator_eq_so4_delta_generator :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      so4DeltaGenerator := by
  rw [so4_seed_commutator_is_delta_generator, so4_delta_generator_eq_plane03]

/-! ## Harmonic `6/5` ↔ integer step on shell `8` -/

/--
On shell `n = 8`, the numerator branch `6` is blocked (`gcd(6,8) = 2`), so the
integer holonomy uses the **denominator** branch `5` — still the `6/5` shadow.
-/
theorem not_coprime_six_eight : ¬ Nat.Coprime 6 8 := by decide

theorem coprime_five_eight : Nat.Coprime 5 8 := by decide

theorem harmonic_orbit_mul_mod_multiplier_eight_eq_five :
    harmonicOrbitMulModMultiplier 8 = 5 :=
  harmonicOrbitMulModMultiplier_eq_five not_coprime_six_eight coprime_five_eight

theorem harmonic_six_fifths_real_and_integer_at_anchor :
    harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 :=
  ⟨harmonic_orbit_multiplier_is_six_fifths, harmonic_orbit_mul_mod_multiplier_eight_eq_five⟩

/-! ## Next twin shell `N = 6`, shell `12` -/

theorem not_coprime_six_twelve : ¬ Nat.Coprime 6 12 := by decide

theorem coprime_five_twelve : Nat.Coprime 5 12 := by decide

theorem harmonic_orbit_mul_mod_multiplier_twelve_eq_five :
    harmonicOrbitMulModMultiplier 12 = 5 :=
  harmonicOrbitMulModMultiplier_eq_five not_coprime_six_twelve coprime_five_twelve

theorem harmonic_six_fifths_real_and_integer_at_six :
    harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 12 = 5 :=
  ⟨harmonic_orbit_multiplier_is_six_fifths, harmonic_orbit_mul_mod_multiplier_twelve_eq_five⟩

/-! ## 8D phase-lift Δ plane (SO(8) shadow of Path C) -/

theorem delta_holonomy_so8_phase_lift_plane :
    Hqiv.phaseLiftDelta 1 7 = -1 ∧ Hqiv.phaseLiftDelta 7 1 = 1 :=
  so8_phase_lift_delta_plane

/-! ## Twin shell pack (generic local certificate) -/

/--
A certified twin midpoint together with its harmonic mul-mod bundle and the
integer multiplier selected by the `6/5` cascade on shell `2N`.
-/
structure DeltaHolonomyTwinShellPack (N p q : ℕ) where
  mul_mod_bundle : MidpointHarmonicMulModBundle N p q
  twin_support : goldbachMidpointSupportsTwinPrime N
  integer_multiplier :
    mul_mod_bundle.multiplier = harmonicOrbitMulModMultiplier (2 * N)

noncomputable def deltaHolonomyTwinShellPack_four : DeltaHolonomyTwinShellPack 4 3 5 where
  mul_mod_bundle := harmonicMulModBundle_four
  twin_support := goldbach_midpoint_supports_twin_four
  integer_multiplier := by
    rw [harmonicMulModBundle_four.multiplier_eq,
      harmonicMulModBundle_four.shell_eq,
      harmonic_orbit_mul_mod_multiplier_eight_eq_five]

noncomputable def deltaHolonomyTwinShellPack_six : DeltaHolonomyTwinShellPack 6 5 7 where
  mul_mod_bundle := harmonicMulModBundle_six
  twin_support := goldbach_midpoint_supports_twin_six
  integer_multiplier := by
    rw [harmonicMulModBundle_six.multiplier_eq,
      harmonicMulModBundle_six.shell_eq,
      harmonic_orbit_mul_mod_multiplier_twelve_eq_five]

theorem delta_holonomy_twin_shell_pack_four_twin_arm_hits :
    ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
      scaleOrbitMulMod 8 5 xL = 3 ∧
      scaleOrbitMulMod 8 5 xR = 5 :=
  twin_harmonic_mul_mod_arm_hits_four

theorem delta_holonomy_twin_shell_pack_six_twin_arm_hits :
    ∃ (xL xR : ℕ), xL < 12 ∧ xR < 12 ∧
      scaleOrbitMulMod 12 5 xL = 5 ∧
      scaleOrbitMulMod 12 5 xR = 7 :=
  twin_harmonic_mul_mod_arm_hits_six

theorem delta_holonomy_twin_ladder_axis_offsets :
    goldbachLeftArmAngle 4 3 (by decide) (by decide) = Real.pi - Real.pi / 4 ∧
      goldbachLeftArmAngle 4 5 (by decide) (by decide) = Real.pi + Real.pi / 4 ∧
      goldbachLeftArmAngle 6 5 (by decide) (by decide) = Real.pi - Real.pi / 6 ∧
      goldbachLeftArmAngle 6 7 (by decide) (by decide) = Real.pi + Real.pi / 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact twin_left_arm_angle_eq goldbach_midpoint_supports_twin_four
  · exact twin_right_arm_angle_eq goldbach_midpoint_supports_twin_four
  · exact twin_left_arm_angle_eq goldbach_midpoint_supports_twin_six
  · exact twin_right_arm_angle_eq goldbach_midpoint_supports_twin_six

/-! ## Square-anchor package -/

/--
Local certificate at the twiddle pole midpoint `N = 4`: Path C Δ holonomy,
harmonic `6/5` normalization, and the certified mul-mod bundle on shell `8`.
-/
structure DeltaHolonomyMulModAnchorPack where
  holonomy : SO4PhaseDeltaHolonomyPack
  plaquette_commutator_eq_delta :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      so4DeltaGenerator
  mul_mod_bundle : MidpointHarmonicMulModBundle 4 3 5
  integer_multiplier_five : mul_mod_bundle.multiplier = 5
  twin_support : goldbachMidpointSupportsTwinPrime 4

noncomputable def deltaHolonomyMulModAnchorPack_default : DeltaHolonomyMulModAnchorPack where
  holonomy := so4_phase_delta_holonomy_pack_default
  plaquette_commutator_eq_delta := so4_seed_commutator_eq_so4_delta_generator
  mul_mod_bundle := harmonicMulModBundle_four
  integer_multiplier_five := by
    rw [harmonicMulModBundle_four.multiplier_eq,
      harmonicMulModBundle_four.shell_eq,
      harmonic_orbit_mul_mod_multiplier_eight_eq_five]
  twin_support := goldbach_midpoint_supports_twin_four

theorem delta_holonomy_mul_mod_anchor_pack_exists :
    Nonempty DeltaHolonomyMulModAnchorPack :=
  ⟨deltaHolonomyMulModAnchorPack_default⟩

theorem delta_holonomy_mul_mod_anchor_twin_arm_hits :
    ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xL = 3 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xR = 5 :=
  twin_harmonic_mul_mod_arm_hits_four

/--
Master square-anchor certificate: Δ plaquette holonomy, `6/5` shadow,
integer mul-mod on shell `8`, twiddle-pole depth, and twin arm hits.
-/
theorem delta_holonomy_mul_mod_anchor_certificate :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 ∧
      (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧
        scaleOrbitMulMod 8 5 xR = 5 := by
  refine ⟨delta_holonomy_mul_mod_anchor_pack_exists, ?_, ?_, ?_, ?_⟩
  · exact harmonic_orbit_multiplier_is_six_fifths
  · exact harmonic_orbit_mul_mod_multiplier_eight_eq_five
  · exact twin_anchor_shell_eq_twiddle_pole_depth.1
  · rcases delta_holonomy_mul_mod_anchor_twin_arm_hits with
      ⟨xL, xR, hxL, hxR, hxLslot, hxRslot⟩
    refine ⟨xL, xR, hxL, hxR, ?_, ?_⟩
    · simpa [harmonic_orbit_mul_mod_multiplier_eight_eq_five] using hxLslot
    · simpa [harmonic_orbit_mul_mod_multiplier_eight_eq_five] using hxRslot

/-! ## Unconditional zero activation at the anchor -/

theorem delta_anchor_zero_holonomy {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    HopfFiberMidpointHolonomySupport 4 3 5 ∧
      (∀ k : ℕ, 0 < k → k < 8 →
        ∃ x : ℕ, x < 8 ∧ scaleOrbitMulMod 8 5 x = k) :=
  by
  rcases zero_holonomy_harmonic_mul_mod_four hzz with ⟨hHol, hSweep⟩
  refine ⟨hHol, fun k hk₀ hk => ?_⟩
  simpa [harmonic_orbit_mul_mod_multiplier_eight_eq_five] using hSweep k hk₀ hk

theorem delta_anchor_zero_holonomy_from_pack {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ)
    (_P : DeltaHolonomyMulModAnchorPack) :
    HopfFiberMidpointHolonomySupport 4 3 5 :=
  (delta_anchor_zero_holonomy hzz).1

/--
At any nontrivial zero: square-anchor Δ pack exists, zero activates holonomy,
full shell sweep works, and twin arms are constructively hit.
-/
theorem delta_anchor_at_zero_certificate {ρ : ℂ} (hzz : IsNontrivialZetaZero ρ) :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      HopfFiberMidpointHolonomySupport 4 3 5 ∧
      (∀ k : ℕ, 0 < k → k < 8 →
        ∃ x : ℕ, x < 8 ∧ scaleOrbitMulMod 8 5 x = k) ∧
      ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧
        scaleOrbitMulMod 8 5 xR = 5 := by
  rcases delta_anchor_zero_holonomy hzz with ⟨hHol, hSweep⟩
  rcases delta_holonomy_mul_mod_anchor_twin_arm_hits with
    ⟨xL, xR, hxL, hxR, hxLslot, hxRslot⟩
  refine ⟨delta_holonomy_mul_mod_anchor_pack_exists, hHol, hSweep, ?_⟩
  refine ⟨xL, xR, hxL, hxR, ?_, ?_⟩
  · simpa [harmonic_orbit_mul_mod_multiplier_eight_eq_five] using hxLslot
  · simpa [harmonic_orbit_mul_mod_multiplier_eight_eq_five] using hxRslot

/--
First two twin midpoints on the ladder: `N = 4` (square/twiddle pole) and `N = 6`
(off-square), each with denominator-branch mul-mod `m = 5` and constructive twin arms.
-/
theorem delta_holonomy_twin_ladder_certificate :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      Nonempty (DeltaHolonomyTwinShellPack 6 5 7) ∧
      harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 ∧
      harmonicOrbitMulModMultiplier 12 = 5 ∧
      (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      (∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
        scaleOrbitMulMod 8 5 xL = 3 ∧ scaleOrbitMulMod 8 5 xR = 5) ∧
      (∃ (xL xR : ℕ), xL < 12 ∧ xR < 12 ∧
        scaleOrbitMulMod 12 5 xL = 5 ∧ scaleOrbitMulMod 12 5 xR = 7) ∧
      (goldbachLeftArmAngle 4 3 (by decide) (by decide) = Real.pi - Real.pi / 4 ∧
        goldbachLeftArmAngle 4 5 (by decide) (by decide) = Real.pi + Real.pi / 4 ∧
        goldbachLeftArmAngle 6 5 (by decide) (by decide) = Real.pi - Real.pi / 6 ∧
        goldbachLeftArmAngle 6 7 (by decide) (by decide) = Real.pi + Real.pi / 6) := by
  refine ⟨delta_holonomy_mul_mod_anchor_pack_exists, ⟨deltaHolonomyTwinShellPack_six⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact harmonic_orbit_multiplier_is_six_fifths
  · exact harmonic_orbit_mul_mod_multiplier_eight_eq_five
  · exact harmonic_orbit_mul_mod_multiplier_twelve_eq_five
  · exact twin_anchor_shell_eq_twiddle_pole_depth.1
  · exact delta_holonomy_twin_shell_pack_four_twin_arm_hits
  · exact delta_holonomy_twin_shell_pack_six_twin_arm_hits
  · exact delta_holonomy_twin_ladder_axis_offsets

end

end Hqiv.Story
