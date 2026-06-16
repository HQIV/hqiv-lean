import Hqiv.Story.S3CountableCircleFill
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith

/-!
# Farey / mediant interpolation of Hopf circle rays

The harmonic-shell ladder already places **countably many** rays at angles
`2πk/n` (`shellSweepAngle`).  This module makes the **between-two-rays** picture
explicit:

1. **Farey mediant** — if rational slopes `k₁/n₁ < k₂/n₂`, then
   `(k₁+k₂)/(n₁+n₂)` lies strictly between them and is an exact shell slot.
2. **Consecutive midpoint** — adjacent slots `k` and `k+1` on shell `n` have
   the exact angular midpoint at slot `2k+1` on shell `2n`.
3. **Sum shell** — the Farey mediant is realized on harmonic depth `n₁+n₂`
   (`fareySumShell` / `fareyMediantShellSlot`).  Coarser embedding into finer
   shells remains `sweep_refines_coarser_angle` when `n ∣ m` (separate lemma).
4. **Density** — arbitrary angles are approached by shell slots
   (`exists_shell_slot_near_angle` from `S3CountableCircleFill`).

This is the formal backbone for “between every two rays there is another”
(countable interpolation), without requiring every ray to carry a Pythagorean
triple.  Zeros on mod families remain a separate balance / identification bridge.

## Honesty

* Proved: mediant inequalities, shell-slot realization, consecutive midpoints,
  density packaging.
* Not claimed: Pythagorean triple coverage; automatic ζ-zeros on every mediant ray.
-/

namespace Hqiv.Story

noncomputable section

open Real

/-! ## Farey mediant on rational slopes -/

/--
Farey mediant slope: `(k₁+k₂)/(n₁+n₂)` lies strictly between `k₁/n₁` and `k₂/n₂`
whenever `k₁/n₁ < k₂/n₂` (cross-multiplied as `k₁·m < k₂·n₁`).
-/
theorem nat_farey_mediant_between {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) (h : k₁ * m < k₂ * n₁) :
    k₁ * (n₁ + m) < n₁ * (k₁ + k₂) ∧
      (k₁ + k₂) * m < k₂ * (n₁ + m) := by
  constructor
  · zify at h hk₁ hk₂ ⊢
    linarith
  · zify at h ⊢
    linarith

theorem rat_slope_lt_iff_mul_lt {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m) :
    (k₁ : ℚ) / n₁ < (k₂ : ℚ) / m ↔ k₁ * m < k₂ * n₁ := by
  constructor
  · intro hlt
    rw [div_lt_div_iff₀ (show 0 < (n₁ : ℚ) by positivity)
      (show 0 < (m : ℚ) by positivity)] at hlt
    norm_cast at hlt ⊢
  · intro hlt
    rw [div_lt_div_iff₀ (show 0 < (n₁ : ℚ) by positivity)
      (show 0 < (m : ℚ) by positivity)]
    norm_cast at hlt ⊢

theorem rat_farey_mediant_between {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m)
    (h : (k₁ : ℚ) / n₁ < (k₂ : ℚ) / m) :
    (k₁ : ℚ) / n₁ < (k₁ + k₂ : ℚ) / (n₁ + m) ∧
      (k₁ + k₂ : ℚ) / (n₁ + m) < (k₂ : ℚ) / m := by
  have hnat : k₁ * m < k₂ * n₁ := (rat_slope_lt_iff_mul_lt hn₁ hm).mp h
  have hnat' := nat_farey_mediant_between hn₁ hm hk₁ hk₂ hnat
  constructor
  · rw [div_lt_div_iff₀ (show 0 < (n₁ : ℚ) by positivity)
      (show 0 < (n₁ + m : ℚ) by positivity)]
    norm_cast
    simpa [Nat.mul_comm] using hnat'.1
  · rw [div_lt_div_iff₀ (show 0 < (n₁ + m : ℚ) by positivity)
      (show 0 < (m : ℚ) by positivity)]
    norm_cast
    exact hnat'.2

theorem nat_farey_mediant_index_lt {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    k₁ + k₂ < n₁ + m := by
  have : k₁ ≤ n₁ - 1 := Nat.le_pred_of_lt hk₁
  have : k₂ ≤ m - 1 := Nat.le_pred_of_lt hk₂
  omega

/-! ## Mediant as an exact harmonic-shell slot -/

/-- Shell depth for a Farey mediant slot. -/
def fareySumShell (n₁ m : ℕ) : ℕ :=
  n₁ + m

theorem farey_sum_shell_pos {n₁ m : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m) :
    0 < fareySumShell n₁ m := by
  dsimp [fareySumShell]
  omega

/-- Slot index for the Farey mediant ray at shell depth `n₁ + n₂`. -/
def fareyMediantSlotIndex (n₁ m k₁ k₂ : ℕ) : ℕ :=
  k₁ + k₂

theorem mem_farey_mediant_slot {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    fareyMediantSlotIndex n₁ m k₁ k₂ < fareySumShell n₁ m :=
  nat_farey_mediant_index_lt hn₁ hm hk₁ hk₂

noncomputable def fareyMediantShellSlot {n₁ m : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (k₁ k₂ : ℕ) (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    Fin (fareySumShell n₁ m) :=
  ⟨fareyMediantSlotIndex n₁ m k₁ k₂, mem_farey_mediant_slot hn₁ hm hk₁ hk₂⟩

theorem farey_mediant_shell_angle {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    shellSweepAngle (farey_sum_shell_pos hn₁ hm)
      (fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂) =
      2 * Real.pi * (k₁ + k₂ : ℝ) / fareySumShell n₁ m := by
  dsimp [fareyMediantShellSlot, fareyMediantSlotIndex, fareySumShell, shellSweepAngle]
  norm_cast

theorem shell_slot_angle_eq_pi_ratio {n : ℕ} (hn : 0 < n) (k : Fin n) :
    shellSweepAngle hn k = 2 * Real.pi * (k.val : ℝ) / n := by
  rfl

theorem farey_mediant_angle_between {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m)
    (hlt : (k₁ : ℚ) / n₁ < (k₂ : ℚ) / m) :
    shellSweepAngle hn₁ ⟨k₁, hk₁⟩ <
      shellSweepAngle (farey_sum_shell_pos hn₁ hm)
        (fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂) ∧
      shellSweepAngle (farey_sum_shell_pos hn₁ hm)
        (fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂) <
        shellSweepAngle hm ⟨k₂, hk₂⟩ := by
  have hnat' :=
    nat_farey_mediant_between hn₁ hm hk₁ hk₂ ((rat_slope_lt_iff_mul_lt hn₁ hm).mp hlt)
  dsimp [shellSweepAngle, fareyMediantShellSlot, fareyMediantSlotIndex, fareySumShell]
  have hn₁0 : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₁.ne'
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsum0 : (n₁ + m : ℝ) ≠ 0 := by positivity
  constructor
  · field_simp [hn₁0, hsum0]
    norm_cast
    nlinarith [Real.pi_pos, hnat'.1, Nat.mul_comm n₁ (k₁ + k₂)]
  · field_simp [hm0, hsum0]
    norm_cast
    nlinarith [Real.pi_pos, hnat'.2, Nat.mul_comm m (k₁ + k₂)]

/-! ## Midpoint between consecutive slots on one shell -/

def doubleShell (n : ℕ) : ℕ :=
  2 * n

theorem double_shell_pos {n : ℕ} (hn : 0 < n) : 0 < doubleShell n := by
  dsimp [doubleShell]
  omega

/-- Exact midpoint index on shell `2n` between slots `k` and `k+1` on shell `n`. -/
def shellConsecutiveMidpointIndex (n k : ℕ) : ℕ :=
  2 * k + 1

theorem shell_consecutive_midpoint_index_lt {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n) :
    shellConsecutiveMidpointIndex n k < doubleShell n := by
  dsimp [shellConsecutiveMidpointIndex, doubleShell]
  omega

noncomputable def shellConsecutiveMidpointSlot {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hk : k + 1 < n) : Fin (doubleShell n) :=
  ⟨shellConsecutiveMidpointIndex n k, shell_consecutive_midpoint_index_lt hn hk⟩

theorem shell_consecutive_midpoint_angle {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n) :
    shellSweepAngle (double_shell_pos hn) (shellConsecutiveMidpointSlot hn k hk) =
      Real.pi * (2 * k + 1 : ℝ) / n := by
  dsimp only [shellConsecutiveMidpointSlot, shellConsecutiveMidpointIndex, doubleShell, shellSweepAngle]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h2n : (2 * n : ℝ) ≠ 0 := by positivity
  field_simp [hn', h2n]
  ring_nf
  norm_cast
  ring

theorem shell_consecutive_midpoint_between {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n) :
    shellSweepAngle hn ⟨k, by omega⟩ <
      shellSweepAngle (double_shell_pos hn) (shellConsecutiveMidpointSlot hn k hk) ∧
      shellSweepAngle (double_shell_pos hn) (shellConsecutiveMidpointSlot hn k hk) <
        shellSweepAngle hn ⟨k + 1, hk⟩ := by
  rw [shell_consecutive_midpoint_angle hn k hk]
  dsimp [shellSweepAngle]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · field_simp [hn0]
    norm_cast
    nlinarith [Real.pi_pos]
  · field_simp [hn0]
    norm_cast
    nlinarith [Real.pi_pos]

/-! ## Countable interpolation bundle -/

/--
Between two ordered rational shell rays there is a third **exact** shell ray
(the Farey mediant on shell `n₁+n₂`).
-/
theorem exists_shell_ray_between_ratios {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m)
    (hlt : (k₁ : ℚ) / n₁ < (k₂ : ℚ) / m) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ k : Fin n,
      shellSweepAngle hn₁ ⟨k₁, hk₁⟩ < shellSweepAngle hn k ∧
        shellSweepAngle hn k < shellSweepAngle hm ⟨k₂, hk₂⟩ := by
  refine ⟨fareySumShell n₁ m, farey_sum_shell_pos hn₁ hm,
    fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂, ?_⟩
  exact farey_mediant_angle_between hn₁ hm hk₁ hk₂ hlt

/--
Bundle: Farey mediants, consecutive midpoints, and approach density for arbitrary angles.
-/
structure CountableRayInterpolationBundle where
  /-- Farey mediant slot lies strictly between two ordered rational rays. -/
  farey_between :
    ∀ {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m) (hk₁ : k₁ < n₁) (hk₂ : k₂ < m)
      (hlt : (k₁ : ℚ) / n₁ < (k₂ : ℚ) / m),
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ k : Fin n,
        shellSweepAngle hn₁ ⟨k₁, hk₁⟩ < shellSweepAngle hn k ∧
          shellSweepAngle hn k < shellSweepAngle hm ⟨k₂, hk₂⟩
  /-- Adjacent slots on shell `n` have an exact midpoint on shell `2n`. -/
  consecutive_midpoint :
    ∀ {n k : ℕ} (hn : 0 < n) (hk : k + 1 < n),
      shellSweepAngle hn ⟨k, by omega⟩ <
        shellSweepAngle (double_shell_pos hn) (shellConsecutiveMidpointSlot hn k hk) ∧
        shellSweepAngle (double_shell_pos hn) (shellConsecutiveMidpointSlot hn k hk) <
          shellSweepAngle hn ⟨k + 1, hk⟩
  /-- Arbitrary angles in `[0,2π)` are approached by shell slots. -/
  approaches_any_angle :
    ∀ {θ : ℝ} (hθ : 0 ≤ θ ∧ θ < 2 * Real.pi) {ε : ℝ} (hε : 0 < ε),
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ k : Fin n, |shellSweepAngle hn k - θ| < ε

noncomputable def countableRayInterpolationBundle : CountableRayInterpolationBundle where
  farey_between := fun hn₁ hm hk₁ hk₂ hlt =>
    exists_shell_ray_between_ratios hn₁ hm hk₁ hk₂ hlt
  consecutive_midpoint := fun hn hk =>
    @shell_consecutive_midpoint_between _ hn _ hk
  approaches_any_angle := by intro θ hθ ε hε; exact exists_shell_slot_near_angle hθ hε

/-!
## Status

* **Unconditional:** between two ordered rational shell rays there is a third exact
  ray (Farey mediant slot); consecutive slots have a midpoint slot; arbitrary
  angles are approached.
* **Interpretation:** countable interpolation of the Hopf circle — the same fill
  picture as harmonic-shell counting, now with explicit mediant/midpoint lemmas.
* **Not claimed:** zeros on every interpolated ray; Pythagorean triple labeling.
-/

end

end Hqiv.Story
