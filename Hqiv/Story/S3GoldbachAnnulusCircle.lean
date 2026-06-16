import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Geometry.SoeModStackCombinatorics
import Hqiv.Story.S3CountableCircleFill
import Hqiv.Story.PlasticTwistedEulerCharacter

/-!
# Goldbach midpoint as an S³ annulus: twiddle axis `N`, circumference `m = 2N`

The operative constraint is **equidistance from the twiddle axis** `N`, not a hex-column
cancellation rule.  A midpoint pair `p + q = 2N` places the partners at

* left arm  `N − g = p`
* right arm `N + g = q`

for gap `g = N − p`.  This is exactly the mirror annulus `(m−1)+(m+1) = 2m` with
`m = N` in `annulusMirrorRadius` — outer scale `2N` is the Hopf circle shell depth.

## Circle build (S³ countable fill)

Shell depth `m = 2N` gives `m` arc slots at angles `2πk/m`.  The axis sits at slot
`N` (angle `π`).  Partners at slots `p` and `q` are **equidistant** from the axis
and **complementary** on the circle (`p + q = m`).

Example `N = 10`, `m = 20`: gap `g = 3`, arms `7` and `13` fill one annulus slot;
`7 + 13 = 20` and `|10−7| = |13−10|`.

## Mod-stack on the finite circle

Before the circle is countably filled, only moduli `r ≤ √(2N)` matter
(`finiteSoeAngleStack N`).  Mod-stack survival is the meet of forward/reflected
residue lines — the discrete sieve that mustClear before a slot carries prime
phase on the Hopf circle (`S3ExplicitFormulaPrimePhaseCoincidence` layer).

## Open ( = Goldbach midpoint )

`GoldbachAnnulusCircleFill N`: composite axis `N` forces some gap slot to survive
the finite mod-stack **and** host a prime pair on the annulus.  Equivalent to
`ModStackGoldbachMidpoint N` / `CompositeMidpointHasSurvivor N`.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real

/-! ## Annulus scale: `m = 2N`, axis `N` -/

/-- Hopf shell depth / annulus circumference for midpoint index `N`. -/
def goldbachAnnulusCircumference (N : ℕ) : ℕ :=
  2 * N

/-- Twiddle axis index on the `2N`-slot circle. -/
def goldbachTwiddleAxis (N : ℕ) : ℕ :=
  N

theorem goldbach_annulus_circumference_eq_two_mul (N : ℕ) :
    goldbachAnnulusCircumference N = 2 * N := rfl

theorem goldbach_annulus_radius_eq_mirror (N : ℕ) :
    (goldbachAnnulusCircumference N : ℝ) = annulusMirrorRadius N := by
  norm_num [goldbachAnnulusCircumference, annulusMirrorRadius_eq_two_mul]

theorem goldbach_twiddle_axis_lt_circumference {N : ℕ} (hN : 0 < N) :
    goldbachTwiddleAxis N < goldbachAnnulusCircumference N := by
  dsimp [goldbachTwiddleAxis, goldbachAnnulusCircumference]
  omega

/-! ## Equidistant arms from axis `N` -/

theorem goldbach_gap_arms_left {N p : ℕ} (hp : p ≤ N) :
    gapLeftArm N (midpointLeftGap N p) = p := by
  unfold gapLeftArm midpointLeftGap
  omega

theorem goldbach_gap_arms_right {N p : ℕ} (hp : p ≤ N) :
    gapRightArm N (midpointLeftGap N p) = 2 * N - p := by
  unfold gapRightArm midpointLeftGap
  omega

theorem goldbach_partner_equidistant {N p : ℕ} (hp : p ≤ N) :
    N - midpointLeftGap N p = p ∧
      (2 * N - p) - N = midpointLeftGap N p := by
  unfold midpointLeftGap
  constructor <;> omega

theorem goldbach_midpoint_pair_arms {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    gapLeftArm N (midpointLeftGap N p) = p ∧
      gapRightArm N (midpointLeftGap N p) = q := by
  have hpLe : p ≤ N := h.right.right.left
  have hsum := h.right.right.right.right
  constructor
  · exact goldbach_gap_arms_left hpLe
  · rw [goldbach_gap_arms_right hpLe]
    omega

theorem goldbach_gap_equidistant_from_axis {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    N - p = q - N := by
  have hsum := h.right.right.right.right
  omega

/-! ## Hopf circle slots at shell depth `m = 2N` -/

theorem goldbach_shell_depth_pos {N : ℕ} (hN : 0 < N) :
    0 < goldbachAnnulusCircumference N := by
  dsimp [goldbachAnnulusCircumference]
  omega

/-- Left-arm slot angle on the `2N`-slot Hopf circle. -/
noncomputable def goldbachLeftArmAngle (N p : ℕ) (hN : 0 < N) (hp : p < 2 * N) : ℝ :=
  shellSweepAngle (goldbach_shell_depth_pos hN) ⟨p, hp⟩

theorem goldbach_left_arm_angle_eq (N p : ℕ) (hN : 0 < N) (hp : p < 2 * N) :
    goldbachLeftArmAngle N p hN hp = 2 * Real.pi * (p : ℝ) / (2 * N) := by
  unfold goldbachLeftArmAngle goldbachAnnulusCircumference shellSweepAngle
  field_simp
  norm_cast
  ring

theorem goldbach_axis_angle_eq_pi {N : ℕ} (hN : 0 < N) :
    shellSweepAngle (goldbach_shell_depth_pos hN)
        ⟨goldbachTwiddleAxis N, goldbach_twiddle_axis_lt_circumference hN⟩ =
      Real.pi := by
  dsimp [goldbachTwiddleAxis, goldbachAnnulusCircumference, shellSweepAngle]
  field_simp
  norm_cast

theorem goldbach_partner_slots_complement {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    (p + q : ℝ) / (2 * N) = 1 := by
  have hsum := h.right.right.right.right
  have hpos : 0 < 2 * N := by
    have : 2 ≤ p := Nat.Prime.two_le h.left
    omega
  have hsumR : (p + q : ℝ) = 2 * N := by exact_mod_cast hsum
  rw [hsumR, div_self]
  exact_mod_cast hpos.ne'

/-! ## Worked annulus slot: `7 + 13 = 20`, axis `N = 10`, gap `g = 3` -/

theorem nat_prime_thirteen : Nat.Prime 13 := by decide

theorem goldbach_midpoint_pair_ten_seven_thirteen :
    GoldbachMidpointPair 10 7 13 := by
  refine ⟨nat_prime_seven, nat_prime_thirteen, by omega, by omega, by omega⟩

theorem goldbach_annulus_slot_ten_gap_three :
    gapLeftArm 10 3 = 7 ∧ gapRightArm 10 3 = 13 := by
  unfold gapLeftArm gapRightArm
  decide

theorem goldbach_ten_equidistant_seven_thirteen :
    (10 : ℕ) - 7 = 13 - 10 := by decide

theorem goldbach_ten_shell_slots :
    goldbachLeftArmAngle 10 7 (by decide) (by decide) = 2 * Real.pi * 7 / 20 ∧
      goldbachLeftArmAngle 10 13 (by decide) (by decide) = 2 * Real.pi * 13 / 20 := by
  constructor <;> norm_num [goldbach_left_arm_angle_eq]

/-! ## Mod-stack ↔ annulus prime slot -/

theorem mod_stack_survivor_is_annulus_prime_slot {N p : ℕ} (hp : p ∈ midpointScanSlots N)
    (hStack : modStackSlotSurvives N p) :
    Nat.Prime p ∧ Nat.Prime (2 * N - p) ∧
      gapLeftArm N (midpointLeftGap N p) = p ∧
        gapRightArm N (midpointLeftGap N p) = 2 * N - p := by
  have hSurv := (modStackSlotSurvives_iff_dualSurvivor (N := N) (p := p) hp).mp hStack
  have hpLe : p ≤ N := hSurv.2.2.1
  exact ⟨hSurv.1, hSurv.2.1, goldbach_gap_arms_left hpLe, goldbach_gap_arms_right hpLe⟩

/--
**Annulus circle fill target.**  Composite twiddle axis `N` forces a gap slot that
survives the finite mod-stack and hosts a prime pair on the `2N` annulus — the
circle-ready form of the Goldbach midpoint problem.
-/
def GoldbachAnnulusCircleFill (N : ℕ) : Prop :=
  ModStackGoldbachMidpoint N

theorem goldbach_annulus_circle_fill_iff_mod_stack (N : ℕ) :
    GoldbachAnnulusCircleFill N ↔ ModStackGoldbachMidpoint N := Iff.rfl

theorem goldbach_annulus_circle_fill_iff_composite (N : ℕ) :
    GoldbachAnnulusCircleFill N ↔ CompositeMidpointHasSurvivor N := by
  rw [goldbach_annulus_circle_fill_iff_mod_stack, mod_stack_goldbach_iff_composite_survivor]

theorem goldbach_annulus_circle_fill_fifteen : GoldbachAnnulusCircleFill 15 :=
  mod_stack_goldbach_fifteen

/-!
**Status.**  Equidistant annulus geometry and Hopf slot angles are unconditional.
Mod-stack survival ↔ prime pair on the arms is proved via `SoeModStackCombinatorics`.
Global `GoldbachAnnulusCircleFill` for every composite `N` is the Goldbach midpoint
problem on the countably filled circle.  See `S3GoldbachAnnulusPhasePinning` for
Hopf prime phases and two-prime angle pinning.
-/

end Hqiv.Story