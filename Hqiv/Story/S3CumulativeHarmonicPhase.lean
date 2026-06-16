import Hqiv.Story.S3CriticalCirclePhaseCancellation
import Hqiv.Story.S3ExplicitFormulaIdentity
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Cumulative harmonic-shell phase sum and von Mangoldt truncation

Stacks shell contributions up to depth `N`:

\[
  \sum_{n=1}^{N} \frac{2\pi}{n}\, H_n \cdot A(\theta),
\]

where `A(θ) = cos(θ − π/4)` is the critical amplitude and each shell uses the
**slot-0 representative** sweep angle (angle `0`, so all shells read the same
`baseθ`).

## Proved

* exact factorization `cumulativeHarmonicPhaseSum N θ = A(θ) · totalArcHarmonicWeight N`;
* antipodal cancellation of the cumulative sum;
* vanishing ⟺ `A(θ) = 0` when `N > 0`;
* structural parallel with `partialVonMangoldtSumUpTo N · A(θ)` (distinct weights);
* exact split `W_N = Λ_N + Δ_N` and cumulative model = classical truncation +
  `A(θ) · Δ_N`.

## Honesty / scaling

The two weights grow at very different rates:

* `partialVonMangoldtWeight N = ∑_{n≤N} Λ(n)` is Θ(`N`) by the Prime Number Theorem;
* `totalArcHarmonicWeight N = 2π ∑_{n≤N} H_n/n` is Θ(`(log N)²`) (harmonic–log
  integral asymptotics).

So `Δ_N = weightDifference N` is asymptotically dominated by the linear von
Mangoldt term.  The parallel is a **structural** analogy — shared `A(θ)` factorization
and antipodal cancellation — not a term-by-term numerical match.  The geometric model
supplies the amplitude mechanism; the classical side carries the much larger weight;
`Δ_N` absorbs the growth gap.

`WeightDifferenceAsymptoticSlot` records leading term + bounded remainder when analytic
input is wired in (not instantiated here).
-/

namespace Hqiv.Story

noncomputable section

open Real ArithmeticFunction

/-! ## Shell representative angle (slot 0) -/

/-- Slot-0 sweep angle on shell `n > 0` — always `0`. -/
noncomputable def shellRepresentativeSweepAngle {n : ℕ} (hn : 0 < n) : ℝ :=
  shellSweepAngle hn ⟨0, Nat.pos_of_ne_zero (Nat.ne_of_gt hn)⟩

theorem shell_representative_sweep_angle_zero {n : ℕ} (hn : 0 < n) :
    shellRepresentativeSweepAngle hn = 0 := by
  dsimp [shellRepresentativeSweepAngle, shellSweepAngle]
  simp

/-! ## Per-shell and cumulative contributions -/

/-- One shell's arc × harmonic-weighted amplitude at the representative slot. -/
noncomputable def cumulativeShellPhaseContribution (n : ℕ) (baseθ : ℝ) : ℝ :=
  if h : 0 < n then
    rollingStepArcWidth n * harmonicWeightedCriticalAmplitude n
      (baseθ + shellRepresentativeSweepAngle h)
  else 0

theorem cumulative_shell_phase_contribution_pos {n : ℕ} (hn : 0 < n) (baseθ : ℝ) :
    cumulativeShellPhaseContribution n baseθ =
      rollingStepArcWidth n * harmonicPartialSum n * criticalAmplitudeAt baseθ := by
  dsimp [cumulativeShellPhaseContribution, harmonicWeightedCriticalAmplitude]
  rw [dif_pos hn, shell_representative_sweep_angle_zero hn, add_zero]
  ring

/-- `∑_{n=1}^{N} (2π/n) · H_n` — total arc–harmonic weight (normalizer). -/
noncomputable def totalArcHarmonicWeight (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, rollingStepArcWidth n * harmonicPartialSum n

theorem total_arc_harmonic_weight_eq_arc_times_harmonic (N : ℕ) :
    totalArcHarmonicWeight N =
      ∑ n ∈ Finset.Icc 1 N, (2 * Real.pi / n) * harmonicPartialSum n := by
  dsimp [totalArcHarmonicWeight]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [rolling_step_arc_width_eq]

/-- Cumulative weighted phase sum up to shell depth `N`. -/
noncomputable def cumulativeHarmonicPhaseSum (N : ℕ) (baseθ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, cumulativeShellPhaseContribution n baseθ

theorem cumulative_harmonic_phase_sum_eq (N : ℕ) (baseθ : ℝ) :
    cumulativeHarmonicPhaseSum N baseθ =
      criticalAmplitudeAt baseθ * totalArcHarmonicWeight N := by
  dsimp [cumulativeHarmonicPhaseSum, totalArcHarmonicWeight]
  have hterm :
      ∀ n ∈ Finset.Icc 1 N,
        cumulativeShellPhaseContribution n baseθ =
          rollingStepArcWidth n * harmonicPartialSum n * criticalAmplitudeAt baseθ := fun n hn => by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    exact cumulative_shell_phase_contribution_pos hnpos baseθ
  calc
    ∑ n ∈ Finset.Icc 1 N, cumulativeShellPhaseContribution n baseθ =
        ∑ n ∈ Finset.Icc 1 N, rollingStepArcWidth n * harmonicPartialSum n * criticalAmplitudeAt baseθ :=
      Finset.sum_congr rfl hterm
    _ = (∑ n ∈ Finset.Icc 1 N, rollingStepArcWidth n * harmonicPartialSum n) * criticalAmplitudeAt baseθ := by
      rw [← Finset.sum_mul]
    _ = criticalAmplitudeAt baseθ * totalArcHarmonicWeight N := by
      dsimp [totalArcHarmonicWeight]
      ring

theorem total_arc_harmonic_weight_pos {N : ℕ} (hN : 0 < N) :
    0 < totalArcHarmonicWeight N := by
  dsimp [totalArcHarmonicWeight]
  have hterm : 0 < rollingStepArcWidth 1 * harmonicPartialSum 1 := by
    rw [rolling_step_arc_width_eq]
    exact mul_pos (by positivity) (harmonicPartialSum_pos Nat.one_pos)
  have hnonneg :
      ∀ n ∈ Finset.Icc 1 N, 0 ≤ rollingStepArcWidth n * harmonicPartialSum n := fun n hn => by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    rw [rolling_step_arc_width_eq]
    exact mul_nonneg (by positivity) (le_of_lt (harmonicPartialSum_pos hnpos))
  have hle :
      rollingStepArcWidth 1 * harmonicPartialSum 1 ≤ totalArcHarmonicWeight N := by
    dsimp [totalArcHarmonicWeight]
    refine Finset.single_le_sum hnonneg ?_
    have hone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN.ne'
    exact Finset.mem_Icc.mpr ⟨le_rfl, hone⟩
  exact lt_of_lt_of_le hterm hle

/-! ## Antipodal cancellation (cumulative) -/

theorem cumulative_harmonic_phase_antipodal_cancels (N : ℕ) (baseθ : ℝ) :
    cumulativeHarmonicPhaseSum N baseθ +
      cumulativeHarmonicPhaseSum N (baseθ + Real.pi) = 0 := by
  rw [cumulative_harmonic_phase_sum_eq, cumulative_harmonic_phase_sum_eq]
  rw [show criticalAmplitudeAt baseθ * totalArcHarmonicWeight N +
        criticalAmplitudeAt (baseθ + Real.pi) * totalArcHarmonicWeight N =
      (criticalAmplitudeAt baseθ + criticalAmplitudeAt (baseθ + Real.pi)) * totalArcHarmonicWeight N
      from by ring]
  rw [antipodal_critical_amplitude_pair_sum baseθ, zero_mul]

theorem cumulative_harmonic_phase_sum_eq_zero_iff {N : ℕ} (hN : 0 < N) (baseθ : ℝ) :
    cumulativeHarmonicPhaseSum N baseθ = 0 ↔ criticalAmplitudeAt baseθ = 0 := by
  rw [cumulative_harmonic_phase_sum_eq]
  constructor
  · intro h
    replace h := (mul_eq_zero.mp h).resolve_right (total_arc_harmonic_weight_pos hN).ne'
    exact h
  · intro h
    simp [h]

/-! ## Von Mangoldt truncation (classical finite side) -/

/-- Finite von Mangoldt truncation `∑_{n=1}^{N} Λ(n)` (prime-power log weights). -/
noncomputable def partialVonMangoldtSumUpTo (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, vonMangoldt n

theorem partial_von_mangoldt_sum_up_to_eq_prime_explicit (N : ℕ) :
    partialVonMangoldtSumUpTo N = primeExplicitTerm N (fun _ => 1) := by
  dsimp [partialVonMangoldtSumUpTo, primeExplicitTerm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-- Classical truncation paired with the same amplitude factor as the model sum. -/
noncomputable def classicalTruncatedAmplitudeSum (N : ℕ) (baseθ : ℝ) : ℝ :=
  partialVonMangoldtSumUpTo N * criticalAmplitudeAt baseθ

theorem classical_truncated_amplitude_sum_eq (N : ℕ) (baseθ : ℝ) :
    classicalTruncatedAmplitudeSum N baseθ =
      criticalAmplitudeAt baseθ * partialVonMangoldtSumUpTo N := by
  dsimp [classicalTruncatedAmplitudeSum]
  ring

theorem classical_truncated_amplitude_antipodal_cancels (N : ℕ) (baseθ : ℝ) :
    classicalTruncatedAmplitudeSum N baseθ +
      classicalTruncatedAmplitudeSum N (baseθ + Real.pi) = 0 := by
  dsimp [classicalTruncatedAmplitudeSum]
  rw [show partialVonMangoldtSumUpTo N * criticalAmplitudeAt baseθ +
        partialVonMangoldtSumUpTo N * criticalAmplitudeAt (baseθ + Real.pi) =
      partialVonMangoldtSumUpTo N *
        (criticalAmplitudeAt baseθ + criticalAmplitudeAt (baseθ + Real.pi)) from by ring]
  rw [antipodal_critical_amplitude_pair_sum baseθ, mul_zero]

/-! ## Weight difference (explicit remainder slot)

Classical truncation grows like `N`; harmonic-arc weight grows like `(log N)²`.
The exact split `W_N = Λ_N + Δ_N` is algebraically sharp; asymptotically `Δ_N ≈ Λ_N`
to leading order.  See module doc for the intended structural (not numerical) parallel.
-/

/-- Classical truncation weight `∑_{n=1}^{N} Λ(n)` (alias). -/
noncomputable abbrev partialVonMangoldtWeight (N : ℕ) : ℝ :=
  partialVonMangoldtSumUpTo N

/-- Harmonic-arc weight minus von Mangoldt truncation — the honest remainder. -/
noncomputable def weightDifference (N : ℕ) : ℝ :=
  totalArcHarmonicWeight N - partialVonMangoldtWeight N

theorem weight_difference_eq (N : ℕ) :
    weightDifference N =
      totalArcHarmonicWeight N - partialVonMangoldtSumUpTo N := by
  rfl

theorem total_arc_harmonic_weight_eq_von_mangoldt_plus_difference (N : ℕ) :
    totalArcHarmonicWeight N =
      partialVonMangoldtWeight N + weightDifference N := by
  dsimp [partialVonMangoldtWeight, weightDifference]
  ring

theorem cumulative_vs_von_mangoldt_exact (N : ℕ) (baseθ : ℝ) :
    cumulativeHarmonicPhaseSum N baseθ =
      criticalAmplitudeAt baseθ * partialVonMangoldtWeight N +
        criticalAmplitudeAt baseθ * weightDifference N := by
  rw [cumulative_harmonic_phase_sum_eq]
  rw [total_arc_harmonic_weight_eq_von_mangoldt_plus_difference]
  ring

theorem cumulative_classical_amplitude_difference (N : ℕ) (baseθ : ℝ) :
    cumulativeHarmonicPhaseSum N baseθ - classicalTruncatedAmplitudeSum N baseθ =
      criticalAmplitudeAt baseθ * weightDifference N := by
  rw [cumulative_harmonic_phase_sum_eq, classical_truncated_amplitude_sum_eq]
  rw [show criticalAmplitudeAt baseθ * totalArcHarmonicWeight N -
        criticalAmplitudeAt baseθ * partialVonMangoldtSumUpTo N =
      criticalAmplitudeAt baseθ *
        (totalArcHarmonicWeight N - partialVonMangoldtSumUpTo N) from by ring]
  rfl

theorem classical_truncated_amplitude_sum_eq_model_minus_remainder (N : ℕ) (baseθ : ℝ) :
    classicalTruncatedAmplitudeSum N baseθ =
      cumulativeHarmonicPhaseSum N baseθ -
        criticalAmplitudeAt baseθ * weightDifference N := by
  linarith [cumulative_classical_amplitude_difference N baseθ]

/-!
Asymptotic shape of `weightDifference N` (leading term + controlled remainder).

Left uninstantiated until Euler–Maclaurin or explicit-formula input is wired in.
When populated, expect a leading term tracking `Λ_N − π(log N)²` (order of the
growth gap) plus a bounded Euler–Maclaurin tail.
-/
structure WeightDifferenceAsymptoticSlot (N : ℕ) where
  /-- Leading asymptotic term at truncation `N`. -/
  leadingTerm : ℝ
  /-- Euler–Maclaurin / explicit-formula remainder. -/
  eulerMaclaurinRemainder : ℝ
  /-- Exact split at truncation `N`. -/
  decomposition :
    weightDifference N = leadingTerm + eulerMaclaurinRemainder
  /-- Explicit error budget on the remainder. -/
  remainderBound : ℝ
  remainder_le : |eulerMaclaurinRemainder| ≤ remainderBound

/-! ## Concrete asymptotic sketch (Option A)

Classical leading terms (not proved here, standard analytic number theory):

* `partialVonMangoldtWeight N = ∑_{n≤N} Λ(n) ~ N` (PNT);
* `totalArcHarmonicWeight N = 2π ∑_{n≤N} H_n/n ~ π (log N)² + c log N + O(1)`.

So `weightDifference N = W_N − Λ_N` is dominated at large `N` by the linear gap
`−Λ_N + π(log N)²`.  We name the **positive** leading comparison term
`Λ_N − π(log N)²`; the remainder below is the exact algebraic tail.
-/

/-- Safe logarithm for asymptotic formulas (`log (N+1)`). -/
noncomputable def asymptoticLog (N : ℕ) : ℝ :=
  Real.log (N + 1)

/-- Harmonic-arc scale `π (log N)²` matching `totalArcHarmonicWeight N` growth. -/
noncomputable def totalArcHarmonicWeightLeadingApprox (N : ℕ) : ℝ :=
  Real.pi * asymptoticLog N ^ 2

/-- Named leading comparison: `Λ_N − π(log N)²` (classical minus harmonic scale). -/
noncomputable def weightDifferenceLeadingTerm (N : ℕ) : ℝ :=
  partialVonMangoldtWeight N - totalArcHarmonicWeightLeadingApprox N

/-- Exact Euler–Maclaurin tail after subtracting the named leading term. -/
noncomputable def weightDifferenceEulerMaclaurinRemainder (N : ℕ) : ℝ :=
  weightDifference N - weightDifferenceLeadingTerm N

theorem weight_difference_leading_decomposition (N : ℕ) :
    weightDifference N =
      weightDifferenceLeadingTerm N + weightDifferenceEulerMaclaurinRemainder N := by
  dsimp [weightDifferenceEulerMaclaurinRemainder, weightDifferenceLeadingTerm]
  ring

/--
Named remainder bound hypothesis for the Euler–Maclaurin tail (analytic input).
-/
structure WeightDifferenceRemainderBound (N : ℕ) where
  remainderBound : ℝ
  remainderBound_nonneg : 0 ≤ remainderBound
  remainder_le :
    |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound

/-- Build a `WeightDifferenceAsymptoticSlot` from the named leading term + bound. -/
noncomputable def weightDifferenceAsymptoticSketch (N : ℕ) (h : WeightDifferenceRemainderBound N) :
    WeightDifferenceAsymptoticSlot N where
  leadingTerm := weightDifferenceLeadingTerm N
  eulerMaclaurinRemainder := weightDifferenceEulerMaclaurinRemainder N
  decomposition := weight_difference_leading_decomposition N
  remainderBound := h.remainderBound
  remainder_le := h.remainder_le

theorem weight_difference_eq_leading_plus_remainder (N : ℕ) :
    weightDifference N =
      weightDifferenceLeadingTerm N + weightDifferenceEulerMaclaurinRemainder N :=
  weight_difference_leading_decomposition N

/-! ## Parallel packaging (honest remainder slot) -/

/--
Structural parallel between cumulative harmonic rolling and finite von Mangoldt
truncation.

Both sides factor as `criticalAmplitudeAt θ` times an **additive arithmetic
weight**.  Equality of the weights (`totalArcHarmonicWeight` vs
`partialVonMangoldtSumUpTo`) is **not** asserted — that is the continuum / explicit
formula remainder.
-/
structure CumulativePhaseVonMangoldtParallel (N : ℕ) where
  /-- Model cumulative sum factors through the critical amplitude. -/
  model_factorization :
    ∀ baseθ : ℝ,
      cumulativeHarmonicPhaseSum N baseθ =
        criticalAmplitudeAt baseθ * totalArcHarmonicWeight N
  /-- Antipodal cancellation of the cumulative model sum. -/
  model_antipodal :
    ∀ baseθ : ℝ,
      cumulativeHarmonicPhaseSum N baseθ +
        cumulativeHarmonicPhaseSum N (baseθ + Real.pi) = 0
  /-- Classical truncation uses the same amplitude factorization pattern. -/
  classical_factorization :
    ∀ baseθ : ℝ,
      classicalTruncatedAmplitudeSum N baseθ =
        criticalAmplitudeAt baseθ * partialVonMangoldtSumUpTo N
  /-- Classical side also antipodal-cancels in pairs. -/
  classical_antipodal :
    ∀ baseθ : ℝ,
      classicalTruncatedAmplitudeSum N baseθ +
        classicalTruncatedAmplitudeSum N (baseθ + Real.pi) = 0
  /-- Balance locus when `N > 0`. -/
  model_vanishes_iff_balance :
    0 < N →
      ∀ baseθ : ℝ,
        cumulativeHarmonicPhaseSum N baseθ = 0 ↔ criticalAmplitudeAt baseθ = 0

noncomputable def cumulativePhaseVonMangoldtParallel (N : ℕ) : CumulativePhaseVonMangoldtParallel N where
  model_factorization := cumulative_harmonic_phase_sum_eq N
  model_antipodal := cumulative_harmonic_phase_antipodal_cancels N
  classical_factorization := classical_truncated_amplitude_sum_eq N
  classical_antipodal := classical_truncated_amplitude_antipodal_cancels N
  model_vanishes_iff_balance := fun hN baseθ =>
    cumulative_harmonic_phase_sum_eq_zero_iff hN baseθ

/--
Refined parallel: same factorization pattern plus the named weight remainder
`weightDifference N` and the exact cumulative split against classical truncation.
-/
structure CumulativePhaseVonMangoldtParallelWithRemainder (N : ℕ) where
  /-- Model cumulative sum factors through the harmonic-arc weight. -/
  harmonic_model :
    ∀ baseθ : ℝ,
      cumulativeHarmonicPhaseSum N baseθ =
        criticalAmplitudeAt baseθ * totalArcHarmonicWeight N
  /-- Classical truncation uses the von Mangoldt weight. -/
  classical_truncation :
    ∀ baseθ : ℝ,
      classicalTruncatedAmplitudeSum N baseθ =
        criticalAmplitudeAt baseθ * partialVonMangoldtWeight N
  /-- Exact weight split `W_N = Λ_N + Δ_N`. -/
  weight_split :
    totalArcHarmonicWeight N =
      partialVonMangoldtWeight N + weightDifference N
  /-- Cumulative model = classical truncation + amplitude-weighted remainder. -/
  cumulative_exact :
    ∀ baseθ : ℝ,
      cumulativeHarmonicPhaseSum N baseθ =
        criticalAmplitudeAt baseθ * partialVonMangoldtWeight N +
          criticalAmplitudeAt baseθ * weightDifference N
  /-- Antipodal cancellation of the cumulative model sum. -/
  model_antipodal :
    ∀ baseθ : ℝ,
      cumulativeHarmonicPhaseSum N baseθ +
        cumulativeHarmonicPhaseSum N (baseθ + Real.pi) = 0
  /-- Classical side also antipodal-cancels in pairs. -/
  classical_antipodal :
    ∀ baseθ : ℝ,
      classicalTruncatedAmplitudeSum N baseθ +
        classicalTruncatedAmplitudeSum N (baseθ + Real.pi) = 0
  /-- Balance locus when `N > 0`. -/
  model_vanishes_iff_balance :
    0 < N →
      ∀ baseθ : ℝ,
        cumulativeHarmonicPhaseSum N baseθ = 0 ↔ criticalAmplitudeAt baseθ = 0
  /-- The remainder weight at this truncation. -/
  remainder := weightDifference N
  remainder_eq :
    remainder = totalArcHarmonicWeight N - partialVonMangoldtWeight N
  /-- Optional asymptotic control on `weightDifference N` (`none` until analytic input). -/
  asymptoticSlot : Option (WeightDifferenceAsymptoticSlot N)

noncomputable def cumulativePhaseVonMangoldtParallelWithRemainder (N : ℕ) :
    CumulativePhaseVonMangoldtParallelWithRemainder N where
  harmonic_model := cumulative_harmonic_phase_sum_eq N
  classical_truncation := classical_truncated_amplitude_sum_eq N
  weight_split := total_arc_harmonic_weight_eq_von_mangoldt_plus_difference N
  cumulative_exact := cumulative_vs_von_mangoldt_exact N
  model_antipodal := cumulative_harmonic_phase_antipodal_cancels N
  classical_antipodal := classical_truncated_amplitude_antipodal_cancels N
  model_vanishes_iff_balance := fun hN baseθ =>
    cumulative_harmonic_phase_sum_eq_zero_iff hN baseθ
  remainder_eq := rfl
  asymptoticSlot := none

/-- Attach asymptotic data to an existing remainder parallel. -/
noncomputable def cumulativePhaseVonMangoldtParallelWithRemainder.withAsymptotic
    (N : ℕ) (par : CumulativePhaseVonMangoldtParallelWithRemainder N)
    (slot : WeightDifferenceAsymptoticSlot N) :
    CumulativePhaseVonMangoldtParallelWithRemainder N :=
  { par with asymptoticSlot := some slot }

/-!
## Status

* **Exact:** cumulative model = `A(θ) · ∑ (2π/n) H_n`; antipodal pair cancels.
* **Exact split:** `W_N = Λ_N + Δ_N` and model = `A(θ)·Λ_N + A(θ)·Δ_N`.
* **Parallel:** `∑ Λ(n) · A(θ)` shares the amplitude factor; weights differ honestly.
* **Scaling:** `Λ_N` is Θ(`N`); `W_N` is Θ(`(log N)²`); `Δ_N` tracks the linear gap.
* **Not claimed:** term-by-term numerical match, or asymptotics without
  `WeightDifferenceAsymptoticSlot`.
-/

end

end Hqiv.Story
