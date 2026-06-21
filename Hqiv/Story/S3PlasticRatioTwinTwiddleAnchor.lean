import Hqiv.Algebra.PlasticAsymptotics
import Hqiv.Story.S3TwinMulModTwiddleBridge
import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.S3GoldbachAnnulusCircle

/-!
# Plastic ratio ↔ first twin ↔ twiddle pole (square anchor only)

The global `plasticRatio n = plasticP n / plasticQ n` track is a ζ(3)-limit scaffold
in `Hqiv.Algebra`.  At the **first twin** `(3,5)` with midpoint `N = 4` and twiddle
pole shell `8`, the canonical `plasticP` / `plasticQ` seeds line up with:

* left twin `3 = plasticP N`, right twin `5 = plasticP (N + 2)`;
* smaller twin `5 = plasticQ N`, shell `8 = plasticQ (N + 2)`;
* twin ratio `3/5 = plasticRatio N`;
* right-arm sweep fraction `5/8 = plasticRatio (N + 2)`;
* twiddle shell depth (`plasticQ (N + 2) = twiddleAddressShellDepth (2,2,2)`);
* Hopf sweep angles `2π · plasticP k / plasticQ (N + 2)` on slots `k = 3, 5`.

This is **anchor-specific** — the second twin `(5,7)` already breaks the naive
right-arm / shell pattern (`plasticP 8 ≠ 7`, `plasticQ 8 ≠ 12`).  There is no proved
link here to `plasticNumber ρ` or spiral phase `2π/ρ`.
-/

namespace Hqiv.Story

open Hqiv.Algebra Hqiv.Geometry Real

noncomputable section

/-! ## Canonical plastic values at the first-twin anchor indices -/

theorem plasticP_four : plasticP 4 = 3 := by
  norm_num [plasticP, plasticSeq]

theorem plasticP_six : plasticP 6 = 5 := by
  norm_num [plasticP, plasticSeq]

theorem plasticP_eight : plasticP 8 = 9 := by
  norm_num [plasticP, plasticSeq]

theorem plasticQ_four : plasticQ 4 = 5 := by
  norm_num [plasticQ, plasticSeq]

theorem plasticQ_six : plasticQ 6 = 8 := by
  norm_num [plasticQ, plasticSeq]

theorem plasticQ_eight : plasticQ 8 = 14 := by
  norm_num [plasticQ, plasticSeq]

theorem plastic_ratio_four : plasticRatio 4 = (3 : ℚ) / 5 := by
  norm_num [plasticRatio, plasticP, plasticQ, plasticSeq]

theorem plastic_ratio_six : plasticRatio 6 = (5 : ℚ) / 8 := by
  norm_num [plasticRatio, plasticP, plasticQ, plasticSeq]

theorem plastic_ratio_four_eq_first_twin_ratio :
    plasticRatio 4 = (plasticP 4 : ℚ) / plasticQ 4 := by
  simp [plastic_ratio_four, plasticP_four, plasticQ_four]

theorem plastic_ratio_six_eq_larger_twin_over_shell :
    plasticRatio 6 = (plasticP 6 : ℚ) / plasticQ 6 := by
  simp [plastic_ratio_six, plasticP_six, plasticQ_six]

/-! ## Twiddle pole shell = `plasticQ (N + 2)` at `N = 4` -/

theorem plasticQ_six_eq_twiddle_pole_shell :
    plasticQ 6 = twiddleAddressShellDepth twiddleAddress222 := by
  simp [plasticQ_six, twiddleAddressShellDepth, twiddleAddress222]

theorem plasticQ_six_eq_first_twin_midpoint_shell :
    plasticQ 6 = 2 * 4 := by
  rw [plasticQ_six]
  norm_num

/-! ## First twin arm slots = plastic indices at `N` and `N + 2` -/

theorem first_twin_left_arm_eq_plasticP_at_midpoint :
    goldbachMidpointSupportsTwinPrime 4 → (4 : ℕ) - 1 = 3 := by
  intro _
  rfl

theorem first_twin_right_arm_eq_plasticP_at_midpoint_plus_two :
    goldbachMidpointSupportsTwinPrime 4 → (4 : ℕ) + 1 = 5 := by
  intro _
  rfl

theorem first_twin_left_arm_eq_plasticP_four :
    goldbachMidpointSupportsTwinPrime 4 → plasticP 4 = (4 : ℕ) - 1 := by
  intro _
  rw [plasticP_four]
  norm_num

theorem first_twin_right_arm_eq_plasticP_six :
    goldbachMidpointSupportsTwinPrime 4 → plasticP 6 = (4 : ℕ) + 1 := by
  intro _
  rw [plasticP_six]
  norm_num

/-! ## Sweep angles = `2π · plasticP / plasticQ (N + 2)` at the anchor -/

theorem first_twin_left_arm_angle_eq_plastic_sweep :
    goldbachLeftArmAngle 4 3 (by decide) (by decide) =
      2 * Real.pi * ((plasticP 4 : ℝ) / (plasticQ 6 : ℝ)) := by
  rw [goldbach_left_arm_angle_eq 4 3 (by decide) (by decide), plasticP_four, plasticQ_six]
  norm_num [mul_div_assoc]

theorem first_twin_right_arm_angle_eq_plastic_sweep :
    goldbachLeftArmAngle 4 5 (by decide) (by decide) =
      2 * Real.pi * ((plasticP 6 : ℝ) / (plasticQ 6 : ℝ)) := by
  rw [goldbach_left_arm_angle_eq 4 5 (by decide) (by decide), plasticP_six, plasticQ_six]
  norm_num [mul_div_assoc]

/-! ## Anchor packaging -/

/-- Certificate proposition for the square-anchor plastic–twin–twiddle alignment. -/
abbrev PlasticRatioTwinTwiddleAnchorCert : Prop :=
  TwinPrimePair 3 ∧
    plasticP 4 = 3 ∧ plasticP 6 = 5 ∧ plasticQ 4 = 5 ∧ plasticQ 6 = 8 ∧
    plasticRatio 4 = (3 : ℚ) / 5 ∧ plasticRatio 6 = (5 : ℚ) / 8 ∧
    plasticQ 6 = twiddleAddressShellDepth twiddleAddress222 ∧
    plasticQ 6 = 2 * 4 ∧
    (4 : ℕ) - 1 = 3 ∧ (4 : ℕ) + 1 = 5 ∧
    goldbachLeftArmAngle 4 3 (by decide) (by decide) =
      2 * Real.pi * 3 / 8 ∧
    goldbachLeftArmAngle 4 5 (by decide) (by decide) =
      2 * Real.pi * 5 / 8

/--
Square-anchor certificate: plastic ratio indices, twiddle shell `8`, and twin `(3,5)`
sweep angles coincide at the first twin midpoint `N = 4`.
-/
theorem plastic_ratio_twin_twiddle_anchor_certificate :
    PlasticRatioTwinTwiddleAnchorCert := by
  refine ⟨goldbach_midpoint_supports_twin_four.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact plasticP_four
  · exact plasticP_six
  · exact plasticQ_four
  · exact plasticQ_six
  · exact plastic_ratio_four
  · exact plastic_ratio_six
  · exact plasticQ_six_eq_twiddle_pole_shell
  · exact plasticQ_six_eq_first_twin_midpoint_shell
  · rfl
  · rfl
  · rw [goldbach_left_arm_angle_eq 4 3 (by decide) (by decide)]
    norm_num
  · rw [goldbach_left_arm_angle_eq 4 5 (by decide) (by decide)]
    norm_num

/-! ## Honest non-global facts (second twin breaks the pattern) -/

theorem plasticP_eight_ne_second_twin_right_arm : plasticP 8 ≠ 7 := by
  rw [plasticP_eight]
  norm_num

theorem plasticQ_eight_ne_second_twin_shell : plasticQ 8 ≠ 12 := by
  rw [plasticQ_eight]
  norm_num

theorem second_twin_left_arm_eq_plasticP_six :
    goldbachMidpointSupportsTwinPrime 6 → (6 : ℕ) - 1 = 5 := by
  intro _
  rfl

theorem second_twin_left_arm_eq_plasticP_six_rat :
    goldbachMidpointSupportsTwinPrime 6 → plasticP 6 = (6 : ℕ) - 1 := by
  intro _
  rw [plasticP_six]
  norm_num

theorem second_twin_right_arm_ne_plasticP_eight :
    goldbachMidpointSupportsTwinPrime 6 → (6 : ℕ) + 1 ≠ 9 := by
  intro _
  decide

theorem second_twin_right_arm_ne_plasticP_eight_rat :
    goldbachMidpointSupportsTwinPrime 6 → plasticP 8 ≠ (6 : ℕ) + 1 := by
  intro _
  rw [plasticP_eight]
  norm_num

end

end Hqiv.Story
