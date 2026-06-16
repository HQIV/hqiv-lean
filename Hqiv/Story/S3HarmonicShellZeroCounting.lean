import Hqiv.Story.S3CriticalLineCarrierBundle
import Hqiv.Story.S3LogExpTrigReadoutBridge
import Hqiv.Story.DimensionalGrowthAnalyticScaffold
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3PrimeAxisCancellation
import Hqiv.Story.S3HopfShellHolonomy
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3HopfJKUnitCircleZeroReadout
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Harmonic-shell zero counting: arc partitions on the circle, not heights `t`

On the critical-line carrier the Hopf fiber is a circle.  The strip height
`t = Im(s)` is a **non-compact cover** coordinate (`sameStripHeight` / `2π`
periodicity): it rolls the circle but does **not** furnish a discrete counter.

This module promotes the **harmonic shell ladder** `H_n` as the counting axis:

* shell depth `n ∈ ℕ` carries cumulative harmonic weight `H_n`;
* at each shell `n > 0` the circle is swept into **`n` arcs** of width
  `2π/n`, indexed by `k : Fin n` at polar angle `2πk/n`;
* finer shells refine the sweep (`n ∣ m` embeds coarser slots into finer ones);
* the slot index type `HarmonicShellSlot = Σ n, Fin n` injects into `ℕ` — a
  countable union of finite angular partitions, not a scan of `ℝ`.

**Contrast with linear counting.**  Monotone `1, 2, 3, …` orders shells by size
only.  The sweep adds **spatial resolution on `S¹`**: shell `n` sees the circle
as `n` arcs.  Passing to shell `n+1` is not merely “one more tick” — it is a
**refined arc partition** of the same compact carrier.  That is the geometric content
of “infinity” in this projection: divergent `H_n` supplies depth; angular
`2πk/n` supplies partition; together they replace continuous `t`.

**Honesty.**  ζ-zero balance on the line is still conditional on
`RollingZetaIdentificationAtCriticalLine` (same order as the residual bridge).
The **counting axis** `(n, k)` is unconditional.
-/

namespace Hqiv.Story

noncomputable section

open Complex Real Filter
open scoped BigOperators

/-! ## Height `t` is a cover, not a counter -/

/-- Strip height is a **cover** coordinate: only the compact fiber point matters. -/
abbrev StripHeightCover := ℝ

theorem strip_height_not_injective_on_circle :
    ∃ t₁ t₂ : StripHeightCover, t₁ ≠ t₂ ∧ sameStripHeight t₁ t₂ := by
  refine ⟨0, 2 * Real.pi, by nlinarith [Real.pi_pos], ?_⟩
  exact ⟨1, by ring⟩

theorem strip_rolling_map_respects_height_cover {t₁ t₂ : ℝ}
    (h : sameStripHeight t₁ t₂) :
    stripRollingMap t₁ = stripRollingMap t₂ := by
  have hσ : stripAnalyticLift (1 / 2) t₁ = stripAnalyticLift (1 / 2) t₂ :=
    strip_analytic_lift_respects_height (1 / 2) h
  rw [← strip_analytic_lift_eq_rolling t₁, ← strip_analytic_lift_eq_rolling t₂]
  exact hσ

/-! ## Harmonic shell index and arc partitions -/

/--
A **harmonic-shell slot**: shell depth `n` and angular index `k < n`.

This is the discrete index for circle sweeping — not a real height `t`.
-/
def HarmonicShellSlot : Type :=
  Σ n : ℕ, Fin n

/-- Injective encoding into `ℕ` (countable union of finite slot sets). -/
noncomputable def encodeHarmonicShellSlot : HarmonicShellSlot → ℕ
| ⟨n, k⟩ => n * (n + 1) + k.val

private theorem encode_mono_shell {n m : ℕ} (k : Fin n) (j : Fin m) (h : n < m) :
    encodeHarmonicShellSlot ⟨n, k⟩ < encodeHarmonicShellSlot ⟨m, j⟩ := by
  dsimp [encodeHarmonicShellSlot]
  have hk : k.val < n := k.isLt
  have hbase : n * (n + 1) + k.val < (n + 1) * (n + 2) := by nlinarith
  calc
    n * (n + 1) + k.val < (n + 1) * (n + 2) := hbase
    _ ≤ m * (m + 1) + j.val := by nlinarith [Nat.le_of_lt h, j.isLt]

theorem encodeHarmonicShellSlot_injective :
    Function.Injective encodeHarmonicShellSlot := by
  rintro ⟨n, k⟩ ⟨m, j⟩ h
  simp only [encodeHarmonicShellSlot] at h
  have hn_eq_m : n = m := by
    rcases lt_trichotomy n m with hlt | heq | hgt
    · exfalso
      exact (encode_mono_shell k j hlt).ne h
    · exact heq
    · exfalso
      exact (encode_mono_shell j k hgt).ne h.symm
  subst hn_eq_m
  have hkj : k = j := Fin.ext (by linarith [k.isLt, j.isLt, h])
  exact congrArg (Sigma.mk n) hkj

/-- Cumulative harmonic weight at shell `n`. -/
noncomputable def harmonicShellWeight (n : ℕ) : ℝ :=
  harmonicPartialSum n

/-- Angular width of one arc at shell `n > 0`. -/
noncomputable def shellArcWidth (n : ℕ) : ℝ :=
  2 * Real.pi / n

/-- Polar angle `2πk/n` for slot `k` at shell `n > 0`. -/
noncomputable def shellSweepAngle {n : ℕ} (_hn : 0 < n) (k : Fin n) : ℝ :=
  2 * Real.pi * (k.val : ℝ) / n

theorem shell_arc_width_pos {n : ℕ} (hn : 0 < n) :
    0 < shellArcWidth n := by
  dsimp [shellArcWidth]
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (Nat.cast_pos.mpr hn)

theorem shell_sweep_angle_in_period {n : ℕ} (hn : 0 < n) (k : Fin n) :
    0 ≤ shellSweepAngle hn k ∧ shellSweepAngle hn k < 2 * Real.pi := by
  dsimp [shellSweepAngle]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk : (k.val : ℝ) < n := Nat.cast_lt.mpr k.isLt
  constructor
  · dsimp [shellSweepAngle]
    positivity
  · have hk' : (k.val : ℝ) < n := Nat.cast_lt.mpr k.isLt
    have hbound : (2 * Real.pi * (k.val : ℝ)) / (n : ℝ) < 2 * Real.pi := by
      rw [div_lt_iff₀ hn']
      nlinarith [Real.pi_pos, hk']
    exact hbound

/-- Slot phase on `S¹` — the primitive `n`th root chart at index `k`. -/
noncomputable def shellSlotPhase {n : ℕ} (hn : 0 < n) (k : Fin n) : ℂ :=
  primitiveRoot n hn k

theorem shell_slot_phase_on_circle {n : ℕ} (hn : 0 < n) (k : Fin n) :
    ‖shellSlotPhase hn k‖ = 1 :=
  norm_primitiveRoot n hn k

theorem shell_slot_phase_eq_exp_angle {n : ℕ} (hn : 0 < n) (k : Fin n) :
    shellSlotPhase hn k = exp (I * shellSweepAngle hn k) := by
  dsimp only [shellSlotPhase, primitiveRoot, shellSweepAngle]
  congr 1
  rw [mul_comm]
  norm_cast

/-- Consecutive slots are one arc apart. -/
theorem shell_sweep_angle_succ {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n) :
    shellSweepAngle hn ⟨k + 1, hk⟩ - shellSweepAngle hn ⟨k, by omega⟩ =
      shellArcWidth n := by
  dsimp [shellSweepAngle, shellArcWidth]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']
  push_cast
  ring

/-! ## Rolling circle: slot angle ↔ `stripRollingMap` -/

/-- Read the critical-line circle at harmonic slot angle. -/
noncomputable def stripRollingAtSlot {n : ℕ} (hn : 0 < n) (k : Fin n) : QuaternionCoords :=
  stripRollingMap (shellSweepAngle hn k)

theorem strip_rolling_at_slot_eq_lift (n : ℕ) (hn : 0 < n) (k : Fin n) :
    stripRollingAtSlot hn k = stripAnalyticLift (1 / 2) (shellSweepAngle hn k) := by
  dsimp [stripRollingAtSlot]
  rw [strip_analytic_lift_eq_rolling]

theorem hopf_coords_at_slot {n : ℕ} (hn : 0 < n) (k : Fin n) :
    hopfFiberCoords (shellSweepAngle hn k) 0 = Real.cos (shellSweepAngle hn k) ∧
      hopfFiberCoords (shellSweepAngle hn k) 1 = Real.sin (shellSweepAngle hn k) := by
  dsimp [hopfFiberCoords]
  exact ⟨rfl, rfl⟩

/-! ## Sweep refines: coarser arcs embed into finer -/

/--
Embed a coarser slot into a finer shell when `n ∣ m` — a coarser slice
subdivides into equal finer slices.
-/
noncomputable def embedCoarserShellSlot {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdiv : n ∣ m) (k : Fin n) : Fin m :=
  ⟨(k.val * (m / n)), by
    have hmn := Nat.div_mul_cancel hdiv
    have hle : n ≤ m := Nat.le_of_dvd hm hdiv
    have hquot : 0 < m / n := by
      rcases Nat.eq_or_lt_of_le hle with rfl | hnm
      · simpa [Nat.div_self hn] using zero_lt_one
      · exact Nat.div_pos (Nat.le_of_lt hnm) hn
    have h₁ : k.val * (m / n) < n * (m / n) :=
      Nat.mul_lt_mul_of_pos_right k.isLt hquot
    have h₂ : n * (m / n) = m := by rw [Nat.mul_comm, hmn]
    exact Nat.lt_of_lt_of_eq h₁ h₂⟩

private theorem nat_slot_embed_mul_eq {n m k : ℕ} (hdiv : n ∣ m) :
    k * (m / n) * n = k * m := by
  calc
    k * (m / n) * n = k * ((m / n) * n) := Nat.mul_assoc k (m / n) n
    _ = k * m := by rw [Nat.div_mul_cancel hdiv]

theorem sweep_refines_coarser_angle {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hdiv : n ∣ m) (k : Fin n) :
    shellSweepAngle hm (embedCoarserShellSlot hn hm hdiv k) =
      shellSweepAngle hn k := by
  dsimp [shellSweepAngle, embedCoarserShellSlot]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp [hm']
  norm_cast
  rw [nat_slot_embed_mul_eq hdiv, Nat.mul_comm]

theorem sweep_arc_width_refines {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdiv : n ∣ m) :
    shellArcWidth m ≤ shellArcWidth n := by
  dsimp [shellArcWidth]
  have h2π : 0 ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
  exact div_le_div_of_nonneg_left h2π (Nat.cast_pos.mpr hn)
    (Nat.cast_le.mpr (Nat.le_of_dvd hm hdiv))

/-! ## Head/tail reflection: antipodal slot identification -/

/--
Head/tail reflection on the rolled circle is **antipodal**: angle `θ ↦ θ + π`
on the `j`/`k` Hopf chart.
-/
theorem head_tail_reflect_rolling_antipodal (θ : ℝ) :
    headTailReflect (stripRollingMap θ) = stripRollingMap (θ + Real.pi) := by
  funext i
  fin_cases i
  · simp [headTailReflect, stripRollingMap]
  · simp [headTailReflect, stripRollingMap]
  · simp [headTailReflect, stripRollingMap, Real.cos_add_pi]
  · simp [headTailReflect, stripRollingMap, Real.sin_add_pi]

theorem slot_head_tail_pairs_antipodal {n : ℕ} (hn : 0 < n) (k : Fin n) :
    headTailReflect (stripRollingAtSlot hn k) =
      stripRollingMap (shellSweepAngle hn k + Real.pi) := by
  dsimp [stripRollingAtSlot]
  exact head_tail_reflect_rolling_antipodal (shellSweepAngle hn k)

/-! ## Countability: countable union of finite arc partitions -/

theorem shell_slot_finset_card (n : ℕ) :
    Fintype.card (Fin n) = n :=
  Fintype.card_fin n

theorem harmonic_shell_slots_finite_at_depth (n : ℕ) :
    Fintype.card (Fin n) = n :=
  shell_slot_finset_card n

/-! ## Harmonic depth vs linear ticks -/

/--
**Linear counting** sees shell `n` as one more unit in `H_n = ∑_{i<n} 1/(i+1)`.

**Sweep counting** sees shell `n` as an `n`-way partition of `S¹` with arc width
`2π/n`.  Depth and angular resolution are paired — that is what the projection
buys over scanning `t ∈ ℝ`.
-/
structure HarmonicSweepCountingAxis where
  depth : ℕ → ℝ
  depth_eq_harmonic : ∀ n, depth n = harmonicPartialSum n
  arc_width : ℕ → ℝ
  arc_width_eq : ∀ n (hn : 0 < n), arc_width n = shellArcWidth n
  slot_angle : ∀ {n : ℕ}, 0 < n → Fin n → ℝ
  slot_angle_eq : ∀ {n : ℕ} (hn : 0 < n) (k : Fin n),
    slot_angle hn k = shellSweepAngle hn k

noncomputable def harmonicSweepCountingAxis : HarmonicSweepCountingAxis where
  depth := harmonicPartialSum
  depth_eq_harmonic := fun _ => rfl
  arc_width := shellArcWidth
  arc_width_eq := fun _ _ => rfl
  slot_angle := shellSweepAngle
  slot_angle_eq := fun _ _ => rfl

theorem harmonic_depth_diverges :
    Tendsto harmonicPartialSum atTop atTop := by
  unfold harmonicPartialSum
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem harmonic_shell_weight_eq_axis (n : ℕ) :
    harmonicShellWeight n = harmonicSweepCountingAxis.depth n :=
  rfl

/-! ## Harmonic shell phase readout at depth `n` -/

theorem harmonic_shell_phase_at_depth (n : ℕ) :
    harmonicShellPhaseReadout.u n = exp (I * harmonicPartialSum n) :=
  rfl

theorem harmonic_shell_phase_on_circle (n : ℕ) :
    ‖harmonicShellPhaseReadout.u n‖ = 1 :=
  harmonicShellPhaseReadout.onCircle n

/-! ## Balance events at slots; cover balance under bridge -/

/--
A **harmonic-shell balance event**: the rolled projection cancels at slot angle
`2πk/n` on the critical-line circle.
-/
def HarmonicShellBalanceEvent {n : ℕ} (hn : 0 < n) (k : Fin n) : Prop :=
  criticalProj (stripRollingAtSlot hn k) = 0

theorem harmonic_shell_balance_iff_cos_sin
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    HarmonicShellBalanceEvent hn k ↔
      Real.cos (shellSweepAngle hn k) + Real.sin (shellSweepAngle hn k) = 0 := by
  dsimp [HarmonicShellBalanceEvent, stripRollingAtSlot]
  exact strip_rolling_cancellation_iff (shellSweepAngle hn k)

theorem harmonic_shell_balance_iff_hopf_jk_amplitude
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    HarmonicShellBalanceEvent hn k ↔
      hopfJKCriticalAmplitude (shellSweepAngle hn k) = 0 := by
  simp [HarmonicShellBalanceEvent, stripRollingAtSlot, hopf_jk_amplitude_eq_critical_proj]

theorem harmonic_shell_balance_iff_jk_product_phase
    {n : ℕ} (hn : 0 < n) (k : Fin n) :
    HarmonicShellBalanceEvent hn k ↔
      hopfJKTwiddleReadout (shellSweepAngle hn k) = 0 := by
  rw [harmonic_shell_balance_iff_hopf_jk_amplitude,
    hopf_jk_twiddle_vanishes_iff_amplitude]

/--
**Cover balance** (conditional on rolling identification): ζ vanishes at
`s = 1/2 + it` iff the rolled projection cancels at height `t`.

The counting axis remains `(n, k)` — `t` is only the cover preimage.
-/
theorem zeta_zero_iff_cover_balance
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      criticalProj (stripRollingMap t) = 0 := by
  have hLine : (criticalLinePointAtHeight t).re = (1 / 2 : ℝ) := by
    simp [criticalLinePointAtHeight]
  exact zeta_zero_iff_rolling_cancellation_of_match
    (rolling_matches_critical_height_rolledSample hLine) (hId t)

theorem zeta_zero_iff_cover_balance_slot_form
    (hId : RollingZetaIdentificationAtCriticalLine) (t : ℝ) :
    riemannZeta (criticalLinePointAtHeight t) = 0 ↔
      Real.cos t + Real.sin t = 0 :=
  (zeta_zero_iff_cover_balance hId t).trans (strip_rolling_cancellation_iff t)

/--
Bundle: countable slot index + sweep axis + harmonic phase + cover-vs-slot
distinction.
-/
structure HarmonicShellZeroCountingBundle where
  countable_slots : ∃ f : HarmonicShellSlot → ℕ, Function.Injective f
  sweep : HarmonicSweepCountingAxis
  depth_diverges : Tendsto harmonicPartialSum atTop atTop
  height_is_cover : ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧ sameStripHeight t₁ t₂
  sweep_refines :
    ∀ {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdiv : n ∣ m) (k : Fin n),
      shellSweepAngle hm (embedCoarserShellSlot hn hm hdiv k) = shellSweepAngle hn k

noncomputable def harmonicShellZeroCountingBundle : HarmonicShellZeroCountingBundle where
  countable_slots := ⟨encodeHarmonicShellSlot, encodeHarmonicShellSlot_injective⟩
  sweep := harmonicSweepCountingAxis
  depth_diverges := harmonic_depth_diverges
  height_is_cover := strip_height_not_injective_on_circle
  sweep_refines := @sweep_refines_coarser_angle

/-!
## Status

* **Unconditional:** `t` is a non-injective cover; `(n, k)` arc slots at
  `2πk/n`; sweep refines under `n ∣ m`; antipodal head/tail; encodable slots;
  divergent `H_n` depth; harmonic shell phase on `S¹`; countable slot encoding.
* **Conditional:** `zeta_zero_iff_cover_balance` — balance on the cover under
  `RollingZetaIdentificationAtCriticalLine`; zero **counting** uses shell slots,
  not scanning `t ∈ ℝ`.
-/

end

end Hqiv.Story
