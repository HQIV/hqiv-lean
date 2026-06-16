import Hqiv.Story.S3HopfJKEulerPrimeCircleCounting
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Basic

/-!
# Countably filling the Hopf circle toward infinity

The compact critical-line carrier is a unit circle in the `j`/`k` plane.  Height
`t ∈ ℝ` is only its universal cover.  This module formalizes the **countable fill**:

* shell `n` contributes `n` new arc slots at angles `2πk/n`;
* cumulative slot count through depth `N` is `N(N−1)/2` — divergent;
* arc width `2π/n` tends to `0` — resolution refines;
* every angle in `[0, 2π)` is approached by shell slots;
* each rational angle `2πa/n` is exact at slot `(n, a)`;
* prime phases `linePhase p` attach to every slot — a countable `(p, n, k)` grid;
* harmonic depth `H_n` diverges while angular resolution sharpens.

**Honesty.**  ζ-zero identification at a slot remains conditional on the rolling
bridge.  Countable fill and prime-phase lattice are unconditional.
-/

namespace Hqiv.Story

noncomputable section

open Filter Topology Complex Real
open scoped BigOperators

/-! ## Cumulative arc slots through shell depth -/

/-- Slots contributed by shells `0, …, N−1` (`Fin i` has `i` elements). -/
noncomputable def cumulativeArcSlotCount (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, k

theorem cumulative_arc_slot_count_eq (N : ℕ) :
    cumulativeArcSlotCount N = N * (N - 1) / 2 := by
  dsimp [cumulativeArcSlotCount]
  exact Finset.sum_range_id N

theorem cumulative_arc_slot_count_mono :
    Monotone cumulativeArcSlotCount := by
  intro m n hmn
  simp only [cumulativeArcSlotCount]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    fun _ _ _ => Nat.zero_le _

theorem cumulative_arc_slot_count_succ (N : ℕ) :
    cumulativeArcSlotCount (N + 1) = cumulativeArcSlotCount N + N := by
  dsimp [cumulativeArcSlotCount]
  rw [Finset.sum_range_succ, add_comm]

theorem two_le_cumulative_at_depth_two (b : ℕ) :
    b ≤ cumulativeArcSlotCount (b + 2) := by
  rw [cumulative_arc_slot_count_eq]
  rcases b with _ | b <;> simp [Nat.mul_add, Nat.add_mul] <;> omega

theorem cumulative_arc_slot_count_tends_to_atTop :
    Tendsto cumulativeArcSlotCount atTop atTop :=
  tendsto_atTop_atTop_of_monotone cumulative_arc_slot_count_mono fun b =>
    ⟨b + 2, two_le_cumulative_at_depth_two b⟩

/-! ## Arc width vanishes: the circle is filled ever more finely -/

theorem shell_arc_width_succ_tends_to_zero :
    Tendsto (fun n : ℕ => shellArcWidth (n + 1)) atTop (nhds (0 : ℝ)) := by
  have hone' :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds (0 : ℝ)) :=
    ((tendsto_inv_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds (0 : ℝ))).comp
      (tendsto_add_atTop_nat 1))
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds (0 : ℝ)) := by
    convert hone' using 1
    funext n
    simp
  simpa [shellArcWidth, div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ => (2 * Real.pi : ℝ)) atTop _).mul hone

/-! ## Exact rational angles and density on `[0, 2π)` -/

theorem shell_slot_rational_angle {n a : ℕ} (hn : 0 < n) (ha : a < n) :
    shellSweepAngle hn ⟨a, ha⟩ = 2 * Real.pi * a / n := by
  simp [shellSweepAngle]

/--
Every rational angle `2πa/n` with `a < n` is an **exact** shell slot.
-/
theorem rational_circle_angle_is_slot (n a : ℕ) (hn : 0 < n) (ha : a < n) :
    ∃ k : Fin n, shellSweepAngle hn k = 2 * Real.pi * a / n :=
  ⟨⟨a, ha⟩, shell_slot_rational_angle hn ha⟩

/--
**Density:** for any angle in `[0, 2π)` and any tolerance `ε`, some shell slot lies
within `ε`.  The circle is countably filled to arbitrary resolution.
-/
theorem exists_shell_slot_near_angle {θ : ℝ} (hθ : 0 ≤ θ ∧ θ < 2 * Real.pi) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ k : Fin n,
      |shellSweepAngle hn k - θ| < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * Real.pi / ε)
  let n := M + 1
  have hn : 0 < n := by omega
  have hM' : (2 * Real.pi : ℝ) < (M : ℝ) * ε := by
    rw [← div_lt_iff₀ hε]
    exact_mod_cast hM
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hεM : (M : ℝ) * ε < ε * (n : ℝ) := by
    have hnR' : (n : ℝ) = (M : ℝ) + 1 := by simp [n]
    rw [hnR']
    nlinarith [hε]
  have hwidth : 2 * Real.pi / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hnR]
    exact lt_trans hM' hεM
  set x := θ * (n : ℝ) / (2 * Real.pi)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    apply div_nonneg (mul_nonneg hθ.1 (Nat.cast_nonneg n))
    nlinarith [Real.pi_pos]
  set kNat := Nat.floor x
  have hx : x < (n : ℝ) := by
    dsimp [x]
    rw [div_lt_iff₀ (by nlinarith [Real.pi_pos])]
    nlinarith [hθ.2, hnR, Real.pi_pos]
  have hkNat : kNat < n := (Nat.floor_lt hxnonneg).mpr (by exact_mod_cast hx)
  refine ⟨n, hn, ⟨kNat, hkNat⟩, ?_⟩
  have hfloor := Nat.floor_le hxnonneg
  have hfloor' := Nat.lt_floor_add_one x
  have hslot_le : shellSweepAngle hn ⟨kNat, hkNat⟩ ≤ θ := by
    have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hle := mul_le_mul_of_nonneg_left hfloor (le_of_lt hπ)
    dsimp only [x, shellSweepAngle, kNat] at hle ⊢
    field_simp at hle
    exact (div_le_iff₀ hnR).mpr hle
  have hupper : θ < 2 * Real.pi * (kNat + 1) / (n : ℝ) := by
    have hπ : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hlt := mul_lt_mul_of_pos_left hfloor' hπ
    dsimp only [x, kNat] at hlt
    field_simp at hlt
    exact (lt_div_iff₀ hnR).mpr hlt
  have hgap : θ - shellSweepAngle hn ⟨kNat, hkNat⟩ < 2 * Real.pi / (n : ℝ) := by
    dsimp [shellSweepAngle]
    have hdiff : 2 * Real.pi * (kNat + 1) / (n : ℝ) - 2 * Real.pi * kNat / (n : ℝ) =
        2 * Real.pi / (n : ℝ) := by
      field_simp [hnR.ne']
      ring
    linarith [hupper, hdiff]
  rw [abs_lt]
  constructor
  · linarith [hslot_le]
  · linarith [hgap, hwidth]

/-! ## Prime phases on the fill grid -/

/-- Encode a prime label together with a harmonic-shell slot into `ℕ`. -/
noncomputable def encodePrimeShellSlot (p : ℕ) (slot : HarmonicShellSlot) : ℕ :=
  Nat.pair p (encodeHarmonicShellSlot slot)

theorem encode_prime_shell_slot_injective :
    Function.Injective (fun x : ℕ × HarmonicShellSlot => encodePrimeShellSlot x.1 x.2) := by
  rintro ⟨p, s⟩ ⟨q, t⟩ h
  dsimp [encodePrimeShellSlot] at h
  rw [Nat.pair_eq_pair] at h
  exact Prod.ext h.1 (encodeHarmonicShellSlot_injective h.2)

/-- Prime phase at harmonic-shell slot. -/
noncomputable def primePhaseAtEncodedSlot : ℕ → HarmonicShellSlot → ℂ
| _, ⟨0, k⟩ => Fin.elim0 k
| p, ⟨n + 1, k⟩ => primePhaseAtShellSlot (Nat.succ_pos n) p k

theorem prime_phase_at_encoded_slot_on_circle (p : ℕ) (slot : HarmonicShellSlot) :
    ‖primePhaseAtEncodedSlot p slot‖ = 1 := by
  rcases slot with ⟨n, k⟩
  rcases n with _ | n
  · exact Fin.elim0 k
  · dsimp [primePhaseAtEncodedSlot]
    exact prime_phase_shell_slot_on_unit_circle (Nat.succ_pos n) p k

/-! ## Depth + resolution pair -/

/--
At shell depth `n`, cumulative harmonic weight `H_n` grows while arc width
`2π/n` shrinks — depth and resolution are paired, not a bare height scan.
-/
structure CircleFillDepthResolution where
  depth : ℕ → ℝ
  depth_eq_harmonic : ∀ n, depth n = harmonicPartialSum n
  arc_width : ℕ → ℝ
  arc_width_eq : ∀ n (hn : 0 < n), arc_width n = shellArcWidth n
  depth_diverges : Tendsto depth atTop atTop
  width_vanishes : Tendsto (fun n => arc_width (n + 1)) atTop (nhds (0 : ℝ))

noncomputable def circleFillDepthResolution : CircleFillDepthResolution where
  depth := harmonicPartialSum
  depth_eq_harmonic := fun _ => rfl
  arc_width := shellArcWidth
  arc_width_eq := fun _ _ => rfl
  depth_diverges := harmonic_depth_diverges
  width_vanishes := shell_arc_width_succ_tends_to_zero

/-! ## Countable circle-fill bundle -/

/--
Bundle: countable arc slots fill the Hopf circle with vanishing width, divergent
harmonic depth, prime phases on each slot, and Euler-product counting axis.
-/
structure CountableCircleFillBundle where
  slot_count_diverges : Tendsto cumulativeArcSlotCount atTop atTop
  arc_width_vanishes : Tendsto (fun n => shellArcWidth (n + 1)) atTop (nhds (0 : ℝ))
  depth_resolution : CircleFillDepthResolution
  slots_countable : ∃ f : HarmonicShellSlot → ℕ, Function.Injective f
  prime_slots_countable :
    ∃ g : ℕ × HarmonicShellSlot → ℕ, Function.Injective g
  euler_axis : EulerPrimeCircleCountingAxis

noncomputable def countableCircleFillBundle : CountableCircleFillBundle where
  slot_count_diverges := cumulative_arc_slot_count_tends_to_atTop
  arc_width_vanishes := shell_arc_width_succ_tends_to_zero
  depth_resolution := circleFillDepthResolution
  slots_countable := ⟨encodeHarmonicShellSlot, encodeHarmonicShellSlot_injective⟩
  prime_slots_countable := ⟨fun x => encodePrimeShellSlot x.1 x.2,
    encode_prime_shell_slot_injective⟩
  euler_axis := eulerPrimeCircleCountingAxis

theorem countable_circle_fill_near_any_angle {θ : ℝ} (hθ : 0 ≤ θ ∧ θ < 2 * Real.pi)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (hn : 0 < n) (k : Fin n), |shellSweepAngle hn k - θ| < ε :=
  exists_shell_slot_near_angle hθ hε

theorem countable_circle_fill_rational_exact (n a : ℕ) (hn : 0 < n) (ha : a < n) :
    ∃ slot : HarmonicShellSlot,
      slot.1 = n ∧ shellSweepAngle hn ⟨a, ha⟩ = 2 * Real.pi * a / n := by
  refine ⟨⟨n, ⟨a, ha⟩⟩, rfl, shell_slot_rational_angle hn ha⟩

/-!
## Status

* **Unconditional:** cumulative slot count `N(N−1)/2 → ∞`; arc width `2π/n → 0`;
  harmonic depth `H_n → ∞`; slots dense in `[0, 2π)`; rational angles exact;
  `(prime, slot)` encodable; prime phases on unit circle at every slot.
* **Conditional:** ζ-zero at a slot angle ↔ balance / prime twiddle under rolling
  bridge (`S3HopfJKEulerPrimeCircleCounting`).
-/

end

end Hqiv.Story
