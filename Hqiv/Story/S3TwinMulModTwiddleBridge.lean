import Hqiv.Story.S3HarmonicMulModHolonomy
import Hqiv.Story.S3GoldbachAnnulusCircle
import Hqiv.Story.S3GoldbachGapOneActivationBudget
import Hqiv.Story.S3DeepTwiddlePoleLadder

/-!
# Twin gap-one arms as constructive mul-mod hits on the annulus shell

On shell `n = 2N`, a twin midpoint hosts arms at slots `N − 1` and `N + 1`.
Those slots are **complementary** (`(N−1) + (N+1) = 2N`) and, given any
`MulModScaleOrbitSweep n m`, admit **constructive** preimages `x` with
`x · m ≡ arm (mod n)`.

This is the minimal bridge toward the twiddle ladder: we do **not** claim a
global multiplier law, full `LockedScaleOrbit`, or twin density — only
explicit arm hits and axis-offset angles on certified shells.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real

noncomputable section

/-! ## Twin arms on the `2N` shell -/

theorem goldbach_midpoint_pair_of_twin_support {N : ℕ}
    (h : goldbachMidpointSupportsTwinPrime N) :
    GoldbachMidpointPair N (N - 1) (N + 1) := by
  rcases (goldbachMidpointSupportsTwinPrime_iff N).mp h with ⟨_, hp⟩
  have hN : 1 ≤ N := by omega
  simpa [Nat.sub_add_cancel hN, show N - 1 + 2 = N + 1 by omega] using
    goldbach_gap_one_midpoint_pair (p := N - 1) hp

theorem twin_shell_arm_complement {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    (N - 1) + (N + 1) = 2 * N := by
  have := h.1
  omega

theorem twin_arm_left_pos {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    0 < N - 1 := by
  have := h.1
  omega

theorem twin_arm_left_lt_shell {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    N - 1 < 2 * N := by
  have := h.1
  omega

theorem twin_arm_right_lt_shell {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    N + 1 < 2 * N := by
  have := h.1
  omega

theorem twin_midpoint_pos {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    0 < N := by
  have := h.1
  omega

/-! ## Constructive mul-mod hits (any coprime sweep) -/

/--
Given a mul-mod sweep on shell `n = 2N`, twin arms are **constructively** hit.
No global multiplier choice is required beyond the sweep certificate.
-/
theorem twin_arm_mul_mod_hits {n m N : ℕ} (S : MulModScaleOrbitSweep n m)
    (h : goldbachMidpointSupportsTwinPrime N) (hshell : n = 2 * N) :
    ∃ x₁, x₁ < n ∧ scaleOrbitMulMod n m x₁ = N - 1 ∧
      ∃ x₂, x₂ < n ∧ scaleOrbitMulMod n m x₂ = N + 1 := by
  have hL₀ := twin_arm_left_pos h
  have hL : N - 1 < n := by rw [hshell]; exact twin_arm_left_lt_shell h
  have hR : N + 1 < n := by rw [hshell]; exact twin_arm_right_lt_shell h
  obtain ⟨x₁, hx₁lt, hx₁⟩ := S.hits (N - 1) hL₀ hL
  obtain ⟨x₂, hx₂lt, hx₂⟩ := S.hits (N + 1) (by have := h.1; omega) hR
  exact ⟨x₁, hx₁lt, hx₁, x₂, hx₂lt, hx₂⟩

theorem twin_harmonic_mul_mod_arm_hits {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q)
    (h : goldbachMidpointSupportsTwinPrime N) :
    ∃ (xL xR : ℕ), xL < B.shell ∧ xR < B.shell ∧
      scaleOrbitMulMod B.shell B.multiplier xL = N - 1 ∧
      scaleOrbitMulMod B.shell B.multiplier xR = N + 1 := by
  rcases twin_arm_mul_mod_hits B.sweep h (by simp [B.shell_eq]) with
    ⟨xL, hxLlt, hxL, xR, hxRlt, hxR⟩
  exact ⟨xL, xR, hxLlt, hxRlt, hxL, hxR⟩

/-! ## Axis-offset angles (±π/N), not a stronger phase coupling -/

theorem twin_left_arm_angle_eq {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    goldbachLeftArmAngle N (N - 1) (twin_midpoint_pos h)
        (by simpa using twin_arm_left_lt_shell h) =
      Real.pi - Real.pi / N := by
  rw [goldbach_left_arm_angle_eq_pi_mul_slot_over_N
      (twin_midpoint_pos h) (by simpa using twin_arm_left_lt_shell h)]
  rcases (goldbachMidpointSupportsTwinPrime_iff N).mp h with ⟨_, _⟩
  have hN1 : 1 ≤ N := by omega
  have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  field_simp
  rw [Nat.cast_sub hN1]
  ring

theorem twin_right_arm_angle_eq {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    goldbachLeftArmAngle N (N + 1) (twin_midpoint_pos h)
        (by simpa using twin_arm_right_lt_shell h) =
      Real.pi + Real.pi / N := by
  rw [goldbach_left_arm_angle_eq_pi_mul_slot_over_N
      (twin_midpoint_pos h) (by simpa using twin_arm_right_lt_shell h)]
  have hpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (twin_midpoint_pos h)
  field_simp
  norm_cast

theorem twin_arm_sweep_angles_sum_two_pi {N : ℕ} (h : goldbachMidpointSupportsTwinPrime N) :
    goldbachLeftArmAngle N (N - 1) (twin_midpoint_pos h)
        (by simpa using twin_arm_left_lt_shell h) +
        goldbachLeftArmAngle N (N + 1) (twin_midpoint_pos h)
          (by simpa using twin_arm_right_lt_shell h) =
      2 * Real.pi := by
  rw [twin_left_arm_angle_eq h, twin_right_arm_angle_eq h]
  ring

/-! ## Square anchor: twiddle pole shell matches `2N` only at `N = 4` -/

theorem twin_anchor_shell_eq_twiddle_pole_depth :
    (2 * 4 : ℕ) = twiddleAddressShellDepth twiddleAddress222 ∧
      symmetricTwiddleAddress 2 = twiddleAddress222 := by
  refine ⟨?_, symmetric_twiddle_address_222⟩
  simp [twiddleAddressShellDepth, twiddleAddress222]

/-! ## Certified twin shells (first two gap-one examples) -/

theorem goldbach_midpoint_supports_twin_four :
    goldbachMidpointSupportsTwinPrime 4 :=
  ⟨by omega, ⟨nat_prime_three, nat_prime_five⟩⟩

theorem goldbach_midpoint_supports_twin_six :
    goldbachMidpointSupportsTwinPrime 6 :=
  ⟨by omega, ⟨nat_prime_five, nat_prime_seven⟩⟩

theorem twin_harmonic_mul_mod_arm_hits_four :
    ∃ (xL xR : ℕ), xL < 8 ∧ xR < 8 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xL = 3 ∧
      scaleOrbitMulMod 8 (harmonicOrbitMulModMultiplier 8) xR = 5 := by
  exact twin_harmonic_mul_mod_arm_hits harmonicMulModBundle_four
    goldbach_midpoint_supports_twin_four

theorem twin_harmonic_mul_mod_arm_hits_six :
    ∃ (xL xR : ℕ), xL < 12 ∧ xR < 12 ∧
      scaleOrbitMulMod 12 (harmonicOrbitMulModMultiplier 12) xL = 5 ∧
      scaleOrbitMulMod 12 (harmonicOrbitMulModMultiplier 12) xR = 7 := by
  exact twin_harmonic_mul_mod_arm_hits harmonicMulModBundle_six
    goldbach_midpoint_supports_twin_six

end

end Hqiv.Story
