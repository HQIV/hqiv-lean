import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3SurvivorsForcePhase

/-!
# Explicit-formula localization → rolling zero candidates → RH

This module attempts the proof program:

1. **Survivor / Euler channel** (`PrimeAxisEulerSO4Slot`): prime-axis samples with
   nonzero rolled projection — the geometric counterpart of the explicit-formula
   *prime* term.  SO(4) head/tail pairs cancel as sums; individual poles stay ±.

2. **Zero channel** (`MatchedRollingZeroAt`): rolled strip samples on the critical
   line where `ζ(s)=0` ↔ balanced / zero-producing orbit.  Nontrivial zeta zeros
   live here, not on prime-axis survivors.

3. **Explicit-formula localization** (`ExplicitFormulaLocalization`): discrete Weil
   positivity forces every nontrivial zero onto `Re = 1/2`.

4. **Rolling identification** (`RollingZetaIdentificationAtCriticalLine`): the
   analytic bridge identifying `ζ` with the rolled S³ residual on the critical
   line — RH-hard, same order as constructing a centered residual model.

**Proved here (no `sorry`):**

* prime-axis matched candidates are **impossible** at nontrivial zeta zeros;
* on-line zeros admit canonical rolling matches once identification is supplied;
* explicit-formula localization + rolling identification ⇒ matched rolling
  candidates ⇒ Mathlib `RiemannHypothesis`;
* parallel packaging with survivor slot realization and the harmonic–prime–ζ path.

The remaining RH-hard inputs are exactly `ExplicitFormulaLocalization`,
`RollingZetaIdentificationAtCriticalLine`, and `S3PrimeSurvivorPhaseRealizesEulerSO4Slot`.
-/

namespace Hqiv.Story

noncomputable section

/-! ## Canonical rolled sample at strip height -/

/-- Non-prime scale tag for the rolled fiber (composite, not a prime-axis scale). -/
def rolledSampleScale : ℕ := 4

theorem rolledSampleScale_not_prime : ¬ Nat.Prime rolledSampleScale := by
  decide

/-- Canonical `ScaledS3Sample` on the rolled j–k circle at height `t`. -/
noncomputable def rolledSampleAtHeight (t : ℝ) : ScaledS3Sample where
  scale := rolledSampleScale
  coords := stripRollingMap t
  onS3 := strip_rolling_map_on_s3 t

theorem rolledSampleAtHeight_coords (t : ℝ) :
    (rolledSampleAtHeight t).coords = stripRollingMap t :=
  rfl

theorem rolling_matches_critical_height_rolledSample
    {s : ℂ} (hLine : s.re = (1 / 2 : ℝ)) :
    RollingMatchesCriticalHeight s (rolledSampleAtHeight s.im) :=
  ⟨hLine, rfl⟩

theorem complex_eq_criticalLinePointAtHeight_iff_im (s : ℂ) :
    s = criticalLinePointAtHeight s.im ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    rw [h]
    simp [criticalLinePointAtHeight]
  · intro hre
    apply Complex.ext
    · simpa [criticalLinePointAtHeight] using hre
    · simp [criticalLinePointAtHeight]

/-! ## Zero-channel matched candidate -/

/--
A matched rolling zero candidate at `s`: the sample sits on the rolled fiber at
`Im(s)` and the zeta / S³ residual equations are identified at `s`.
-/
def MatchedRollingZeroAt (s : ℂ) (P : ScaledS3Sample) : Prop :=
  RollingMatchesCriticalHeight s P ∧ ZetaEqualsS3ResidualAt s P

/--
Every nontrivial zeta zero has a matched rolling zero candidate.
This is the honest zero-channel localization target.
-/
def EveryNontrivialZeroHasMatchedRollingCandidate : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s →
    ∃ P : ScaledS3Sample, MatchedRollingZeroAt s P

/--
Pointwise rolling identification on the critical line at height `t`.
-/
def RollingZetaIdentificationAtCriticalLine : Prop :=
  ∀ t : ℝ,
    ZetaEqualsS3ResidualAt (criticalLinePointAtHeight t) (rolledSampleAtHeight t)

theorem matched_rolling_of_on_line_and_identification
    (hId : RollingZetaIdentificationAtCriticalLine)
    {s : ℂ} (hLine : s.re = (1 / 2 : ℝ)) :
    MatchedRollingZeroAt s (rolledSampleAtHeight s.im) := by
  refine ⟨rolling_matches_critical_height_rolledSample hLine, ?_⟩
  dsimp [ZetaEqualsS3ResidualAt]
  rw [(complex_eq_criticalLinePointAtHeight_iff_im s).mpr hLine]
  exact hId s.im

theorem matched_rolling_of_explicit_localization
    (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine)
    {s : ℂ} (hzz : IsNontrivialZetaZero s) :
    MatchedRollingZeroAt s (rolledSampleAtHeight s.im) :=
  matched_rolling_of_on_line_and_identification hId
    (hLoc hWeil s hzz)

theorem everyNontrivialZeroHasMatchedRollingCandidate_of_explicit_and_identification
    (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine) :
    EveryNontrivialZeroHasMatchedRollingCandidate := by
  intro s hzz
  refine ⟨rolledSampleAtHeight s.im, ?_⟩
  exact matched_rolling_of_explicit_localization hWeil hLoc hId hzz

theorem RiemannHypothesis_of_matchedRollingCandidates
    (hEvery : EveryNontrivialZeroHasMatchedRollingCandidate) :
    RiemannHypothesis := by
  intro s hz hNontrivial hNotOne
  rcases hEvery s ⟨hz, hNontrivial, hNotOne⟩ with ⟨_, hRoll⟩
  exact hRoll.1.1

/-! ## Prime-axis matched candidates cannot occur at nontrivial zeros -/

/--
**Channel honesty.** A nontrivial zeta zero cannot carry a prime-axis Euler/SO(4)
matched candidate: prime-axis samples have nonzero `criticalProj`, but a matched
slot identifies `ζ(s)` with that projection at the same point.
-/
theorem not_matchedEulerSO4CancellationAt_nontrivial_zero
    {χ : PlasticTwiddleCharacter} {s : ℂ} {P : ScaledS3Sample}
    (hzz : IsNontrivialZetaZero s)
    (hMatch : MatchedEulerSO4CancellationAt χ s P) : False := by
  rcases hMatch with ⟨hSlot, hsEq⟩
  rcases hSlot with ⟨hPrime, _, hZeta, _⟩
  dsimp [ZetaEqualsEulerSO4ResidualAt] at hZeta
  rw [← hsEq] at hZeta
  have hcp0 : criticalProj P.coords = 0 := by
    have hz0 : (criticalProj P.coords : ℂ) = 0 := by
      simpa [hzz.1] using hZeta.symm
    exact Complex.ofReal_eq_zero.mp hz0
  exact (prime_axis_at_scale_survives P hPrime) hcp0

theorem not_everyNontrivialZeroHasMatchedEulerSO4Candidate_of_nontrivial_zero
    (χ : PlasticTwiddleCharacter) {s : ℂ}
    (hzz : IsNontrivialZetaZero s) :
    ¬ EveryNontrivialZeroHasMatchedEulerSO4Candidate χ := by
  intro hEvery
  rcases hEvery s hzz with ⟨P, hMatch⟩
  exact not_matchedEulerSO4CancellationAt_nontrivial_zero hzz hMatch

/-! ## Full proof-target packaging -/

/--
The corrected explicit-formula proof target: discrete Weil positivity, localization,
rolling identification, and survivor-slot realization for the prime/Euler channel.
-/
structure EulerExplicitFormulaProofTarget (χ : PlasticTwiddleCharacter) where
  weil_positive : DiscreteWeilFormPositive
  explicit_localization : ExplicitFormulaLocalization
  rolling_identification : RollingZetaIdentificationAtCriticalLine
  slot_realize : S3PrimeSurvivorPhaseRealizesEulerSO4Slot χ

/-- RH from the explicit-formula bridge alone (path 1). -/
theorem RiemannHypothesis_of_euler_explicit_formula_target_weil
    {χ : PlasticTwiddleCharacter} (T : EulerExplicitFormulaProofTarget χ) :
    RiemannHypothesis :=
  RiemannHypothesis_of_fullExplicitFormulaBridge
    ⟨T.weil_positive, T.explicit_localization⟩

/-- RH from rolling zero localization (path 2). -/
theorem RiemannHypothesis_of_euler_explicit_formula_target_rolling
    {χ : PlasticTwiddleCharacter} (T : EulerExplicitFormulaProofTarget χ) :
    RiemannHypothesis :=
  RiemannHypothesis_of_matchedRollingCandidates
    (everyNontrivialZeroHasMatchedRollingCandidate_of_explicit_and_identification
      T.weil_positive T.explicit_localization T.rolling_identification)

/-- RH from the harmonic–prime–ζ path bundled in the same target (path 3). -/
theorem RiemannHypothesis_of_euler_explicit_formula_target_harmonic
    {χ : PlasticTwiddleCharacter} (T : EulerExplicitFormulaProofTarget χ) :
    RiemannHypothesis :=
  RiemannHypothesis_of_harmonic_prime_zeta_path
    ⟨T.weil_positive, T.explicit_localization⟩

/--
S³ discrete geometry + survivor slots + explicit-formula rolling localization.
Survivor slots feed `PhaseForcesCriticalLine`; rolling localization closes on zeros.
-/
theorem s3_discrete_geometry_RH_of_explicit_rolling_localization
    (χ : PlasticTwiddleCharacter)
    (L : S3DiscreteNullLatticeLaw)
    (T : EulerExplicitFormulaProofTarget χ) :
    RiemannHypothesis := by
  have _hPhase : PhaseForcesCriticalLine χ :=
    PhaseForcesCriticalLine_of_s3_law_and_slot_realization χ L T.slot_realize
  have _hSurvivors : S3PrimeSurvivorClassification :=
    s3_prime_survivor_classification_of_law L
  exact RiemannHypothesis_of_euler_explicit_formula_target_rolling T

/--
Named analytic obligation for the zero channel:
explicit-formula localization transports to matched rolling candidates once the
critical-line rolling identification is supplied.
-/
def EulerExplicitFormulaRollingLocalization : Prop :=
  ∀ (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine),
    EveryNontrivialZeroHasMatchedRollingCandidate

theorem eulerExplicitFormulaRollingLocalization :
    EulerExplicitFormulaRollingLocalization :=
  fun hWeil hLoc hId =>
    everyNontrivialZeroHasMatchedRollingCandidate_of_explicit_and_identification
      hWeil hLoc hId

end

end Hqiv.Story
