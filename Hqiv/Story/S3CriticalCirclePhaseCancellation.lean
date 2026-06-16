import Hqiv.Story.S3HopfJKUnitCircleZeroReadout
import Hqiv.Story.S3HarmonicShellZeroCounting
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3HopfJKEulerPrimeCircleCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Critical-circle additive phase cancellation (Euler parallel)

Discrete rolling on the Hopf `j`–`k` circle supplies **additive cancellation** of
the 45° critical amplitude — the model-side analogue of prime-phase cancellation
in the Euler product on `s = ½ + it`.

## Model side (proved here)

* shell `n` contributes arc width `2π/n` between consecutive slot angles;
* **head/tail antipodal** symmetry adds `π` to the circle angle and flips the
  critical amplitude (`antipodal_critical_amplitude_pair_sum`);
* the amplitude is `cos(t − π/4)` and vanishes on `t = 3π/4 + kπ`;
* harmonic weight `H_n` scales the detector without changing the zero locus when
  `H_n > 0` (`harmonic_weighted_critical_amplitude_eq_zero_iff`).

## Classical side (imported)

Prime powers on the line split as modulus × unit phase (`critical_line_prime_power_polar`);
multiplication in `ℕ` is phase multiplication on `S¹` (`euler_phase_multiplicative_at_slot`).

## Bridge

`EulerPhaseCancellationParallel` packages the parallel; ζ-zero identification remains
conditional on `RollingZetaIdentificationAtCriticalLine`.  For cumulative truncation
weights and the `Δ_N` remainder slot, see `S3CumulativeHarmonicPhase`.

**Honesty.** The antipodal **pair** sum of critical amplitudes vanishes for every
angle (not only at zeros) — that is the finite symmetry cancellation. Zeros are
where the amplitude itself vanishes before pairing.

**Cumulative weight scaling** (`S3CumulativeHarmonicPhase`).  The Euler parallel
here is structural: both sides factor as `A(θ)` times an arithmetic weight, and
antipodal pairs cancel.  The von Mangoldt truncation `∑_{n≤N} Λ(n)` grows like `N`
(PNT), while the harmonic-arc weight `2π ∑_{n≤N} H_n/n` grows like `(log N)²`; the
remainder `Δ_N` absorbs that gap.  The geometric model supplies `A(θ)` and the
cancellation mechanism; the classical side carries the dominant weight — not a
term-by-term numerical approximation.
-/

namespace Hqiv.Story

noncomputable section

open Real Complex ArithmeticFunction

/-! ## Rolling step geometry (harmonic shells) -/

/-- Arc width between consecutive slots on shell `n` — one rolling step in angle. -/
noncomputable abbrev rollingStepArcWidth (n : ℕ) : ℝ :=
  shellArcWidth n

theorem rolling_step_arc_width_eq (n : ℕ) :
    rollingStepArcWidth n = 2 * Real.pi / n := by
  rfl

/-- Slot polar angle `2πk/n` on shell `n`. -/
noncomputable abbrev rollingStepPhase {n : ℕ} (hn : 0 < n) (k : Fin n) : ℝ :=
  shellSweepAngle hn k

theorem rolling_step_phase_eq (n : ℕ) (hn : 0 < n) (k : Fin n) :
    rollingStepPhase hn k = 2 * Real.pi * (k.val : ℝ) / n := by
  rfl

theorem consecutive_rolling_step_phase_increment {n : ℕ} (hn : 0 < n) (k : ℕ)
    (hk : k + 1 < n) :
    rollingStepPhase hn ⟨k + 1, hk⟩ - rollingStepPhase hn ⟨k, by omega⟩ =
      rollingStepArcWidth n :=
  shell_sweep_angle_succ hn k hk

/-! ## Critical amplitude on the rolled circle -/

/-- 45° critical amplitude at circle angle `θ` (`stripRollingMap θ`). -/
noncomputable abbrev criticalAmplitudeAt (θ : ℝ) : ℝ :=
  hopfJKCriticalAmplitude θ

theorem critical_amplitude_at_eq_cos_sub_pi_four (θ : ℝ) :
    criticalAmplitudeAt θ = Real.cos (θ - Real.pi / 4) :=
  hopf_jk_amplitude_eq_cos_sub_pi_four θ

theorem critical_amplitude_at_eq_critical_proj (θ : ℝ) :
    criticalAmplitudeAt θ = criticalProj (stripRollingMap θ) := by
  simpa using hopf_jk_amplitude_eq_critical_proj θ

theorem critical_amplitude_at_eq_zero_iff_balance (θ : ℝ) :
    criticalAmplitudeAt θ = 0 ↔ ∃ n : ℤ, θ = (3 * Real.pi / 4) + (n : ℝ) * Real.pi := by
  simpa [criticalAmplitudeAt] using hopf_jk_amplitude_eq_zero_iff θ

/-! ## Finite symmetry on circle angles -/

/--
Minimal proved symmetry on the rolled circle: identity and head/tail antipodal
shift `θ ↦ θ + π` (`head_tail_reflect_rolling_antipodal`).
-/
inductive CriticalCircleSymmetry where
  | id
  | headTailAntipodal
  deriving DecidableEq

/-- Action on the circle angle parameter. -/
def criticalCircleSymmetryAngle (σ : CriticalCircleSymmetry) (θ : ℝ) : ℝ :=
  match σ with
  | CriticalCircleSymmetry.id => θ
  | CriticalCircleSymmetry.headTailAntipodal => θ + Real.pi

/-- `j`–`k` swap symmetry: angle `π/2 − θ` carries the same critical amplitude. -/
noncomputable def swapJKCircleAngle (θ : ℝ) : ℝ :=
  Real.pi / 2 - θ

def criticalCircleSymmetryOrbit : List CriticalCircleSymmetry :=
  [CriticalCircleSymmetry.id, CriticalCircleSymmetry.headTailAntipodal]

def criticalCircleSymmetryAngles (θ : ℝ) : List ℝ :=
  criticalCircleSymmetryOrbit.map (criticalCircleSymmetryAngle · θ)

/-- Critical amplitudes at each symmetry image of `θ`. -/
def criticalCircleSymmetryAmplitudes (θ : ℝ) : List ℝ :=
  criticalCircleSymmetryOrbit.map
    (fun σ => criticalAmplitudeAt (criticalCircleSymmetryAngle σ θ))

theorem swap_jk_circle_angle_preserves_amplitude (θ : ℝ) :
    criticalAmplitudeAt (swapJKCircleAngle θ) = criticalAmplitudeAt θ := by
  rw [critical_amplitude_at_eq_cos_sub_pi_four, critical_amplitude_at_eq_cos_sub_pi_four]
  rw [swapJKCircleAngle]
  have hcos : Real.cos (Real.pi / 2 - θ - Real.pi / 4) = Real.cos (θ - Real.pi / 4) := by
    rw [show Real.pi / 2 - θ - Real.pi / 4 = -(θ - Real.pi / 4) by ring]
    exact Real.cos_neg (θ - Real.pi / 4)
  rw [hcos]

/-! ## Antipodal pair cancellation (additive phase cancellation) -/

theorem antipodal_critical_amplitude_pair_sum (θ : ℝ) :
    criticalAmplitudeAt θ + criticalAmplitudeAt (θ + Real.pi) = 0 := by
  rw [critical_amplitude_at_eq_cos_sub_pi_four, critical_amplitude_at_eq_cos_sub_pi_four]
  rw [show θ + Real.pi - Real.pi / 4 = θ - Real.pi / 4 + Real.pi by ring]
  rw [Real.cos_add_pi]
  ring

theorem antipodal_critical_amplitude_pair_sum_via_head_tail (θ : ℝ) :
    criticalProj (stripRollingMap θ) +
      criticalProj (headTailReflect (stripRollingMap θ)) = 0 :=
  headTail_orbit_pair_cancels (stripRollingMap θ)

theorem symmetry_orbit_amplitude_sum_eq_zero (θ : ℝ) :
    (criticalCircleSymmetryAmplitudes θ).foldl (· + ·) 0 = 0 := by
  have hsum :
      (criticalCircleSymmetryAmplitudes θ).foldl (· + ·) 0 =
        criticalAmplitudeAt θ + criticalAmplitudeAt (θ + Real.pi) := by
    simp only [criticalCircleSymmetryAmplitudes, criticalCircleSymmetryOrbit, List.map_cons,
      List.map_nil, criticalCircleSymmetryAngle, List.foldl_cons, List.foldl_nil]
    ring
  rw [hsum, antipodal_critical_amplitude_pair_sum θ]

/-! ## Harmonic-weighted detector -/

theorem harmonicPartialSum_lt_succ (n : ℕ) :
    harmonicPartialSum n < harmonicPartialSum (n + 1) := by
  dsimp [harmonicPartialSum]
  rw [Finset.sum_range_succ]
  have hn : (0 : ℝ) < (n + 1) := by positivity
  linarith [div_pos one_pos hn]

theorem harmonicPartialSum_ge_one {n : ℕ} (hn : 0 < n) :
    harmonicPartialSum 1 ≤ harmonicPartialSum n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · simp [hz, harmonicPartialSum]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hz
      linarith [ih hn', harmonicPartialSum_lt_succ n]

theorem harmonicPartialSum_pos {n : ℕ} (hn : 0 < n) : 0 < harmonicPartialSum n := by
  have h1 : 0 < harmonicPartialSum 1 := by
    dsimp [harmonicPartialSum]
    norm_num
  exact lt_of_lt_of_le h1 (harmonicPartialSum_ge_one hn)

/-- Harmonic depth `H_n` scales the critical amplitude detector at angle `θ`. -/
noncomputable def harmonicWeightedCriticalAmplitude (n : ℕ) (θ : ℝ) : ℝ :=
  harmonicPartialSum n * criticalAmplitudeAt θ

theorem harmonic_weighted_critical_amplitude_eq_zero_iff {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    harmonicWeightedCriticalAmplitude n θ = 0 ↔
      ∃ k : ℤ, θ = (3 * Real.pi / 4) + (k : ℝ) * Real.pi := by
  dsimp [harmonicWeightedCriticalAmplitude]
  constructor
  · intro h
    replace h := (mul_eq_zero.mp h).resolve_left (harmonicPartialSum_pos hn).ne'
    exact (critical_amplitude_at_eq_zero_iff_balance θ).mp h
  · intro h
    rw [(critical_amplitude_at_eq_zero_iff_balance θ).mpr h, mul_zero]

theorem harmonic_weighted_critical_amplitude_slot_eq_zero_iff {n : ℕ} (hn : 0 < n)
    (k : Fin n) :
    harmonicWeightedCriticalAmplitude n (rollingStepPhase hn k) = 0 ↔
      ∃ j : ℤ,
        rollingStepPhase hn k = (3 * Real.pi / 4) + (j : ℝ) * Real.pi :=
  harmonic_weighted_critical_amplitude_eq_zero_iff hn (rollingStepPhase hn k)

/-! ## Euler product parallel (packaging) -/

/--
Parallel between Euler prime-phase cancellation on `S¹` and finite symmetry
cancellation of the rolled critical amplitude.

The **classical** slot is multiplicative prime phases on the circle; the **model**
slot is antipodal additive cancellation of `cos(θ − π/4)` with harmonic weight
`H_n`.  ζ-zero coincidence is conditional on `RollingZetaIdentificationAtCriticalLine`.
-/
structure EulerPhaseCancellationParallel where
  /-- `p^{-ms}` on the line is modulus × unit phase (`critical_line_prime_power_polar`). -/
  prime_power_polar :
    ∀ (n : ℕ) (hn : 0 < n) (t : ℝ),
      so4SpectralLine n (criticalLinePointAtHeight t) =
        (criticalLineModulus n : ℂ) * linePhase n t
  /-- Prime phases multiply along `ℕ` at each shell slot. -/
  euler_phase_multiplicative :
    ∀ {n : ℕ} (hn : 0 < n) (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (k : Fin n),
      primePhaseAtShellSlot hn (p * q) k =
        primePhaseAtShellSlot hn p k * primePhaseAtShellSlot hn q k
  /-- Antipodal symmetry images of the amplitude always cancel in pairs. -/
  antipodal_amplitude_cancellation :
    ∀ θ : ℝ, criticalAmplitudeAt θ + criticalAmplitudeAt (θ + Real.pi) = 0
  /-- Full antipodal orbit sum vanishes. -/
  symmetry_orbit_amplitude_sum :
    ∀ θ : ℝ, (criticalCircleSymmetryAmplitudes θ).foldl (· + ·) 0 = 0
  /-- Balance locus on the circle. -/
  balance_locus :
    ∀ θ : ℝ,
      criticalAmplitudeAt θ = 0 ↔
        ∃ k : ℤ, θ = (3 * Real.pi / 4) + (k : ℝ) * Real.pi
  /-- Harmonic-weighted detector (positive depth). -/
  harmonic_weighted_balance :
    ∀ {n : ℕ} (hn : 0 < n) (θ : ℝ),
      harmonicWeightedCriticalAmplitude n θ = 0 ↔
        ∃ k : ℤ, θ = (3 * Real.pi / 4) + (k : ℝ) * Real.pi
  /-- ζ-zeros on the line ↔ amplitude balance under identification. -/
  zeta_zero_iff_amplitude_balance :
    RollingZetaIdentificationAtCriticalLine →
      ∀ t : ℝ,
        riemannZeta (criticalLinePointAtHeight t) = 0 ↔ criticalAmplitudeAt t = 0

noncomputable def eulerPhaseCancellationParallel : EulerPhaseCancellationParallel where
  prime_power_polar := fun n hn t => critical_line_prime_power_polar hn t
  euler_phase_multiplicative := euler_phase_multiplicative_at_slot
  antipodal_amplitude_cancellation := antipodal_critical_amplitude_pair_sum
  symmetry_orbit_amplitude_sum := symmetry_orbit_amplitude_sum_eq_zero
  balance_locus := critical_amplitude_at_eq_zero_iff_balance
  harmonic_weighted_balance := harmonic_weighted_critical_amplitude_eq_zero_iff
  zeta_zero_iff_amplitude_balance := fun hId t =>
    (zeta_zero_iff_hopf_jk_amplitude hId t).trans
      (by simp [criticalAmplitudeAt])

/-!
## Status

* **Proved:** rolling step width/phase; `criticalAmplitudeAt = cos(θ−π/4)`;
  antipodal pair/orbit sum cancellation; harmonic-weighted balance locus;
  packaging parallel with Euler polar factors and conditional ζ bridge.
* **Not claimed:** full dihedral four-fold phase sum = `√2 · amplitude` (antipodal
  pair already cancels unconditionally; `swapJK` preserves amplitude).
-/

end

end Hqiv.Story
