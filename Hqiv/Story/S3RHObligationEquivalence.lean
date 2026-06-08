import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Story.S3SurvivorsForcePhase

/-!
# Guardrails for the remaining S³/RH obligations

This module is a guardrail against hiding RH inside a renamed analytic
assumption.

The old all-height `PhaseForcesCriticalLine_Legacy` route made vertical rigidity
look like the remaining step.  The corrected route is pointwise: every actual
nontrivial zero must be matched to an Euler/SO(4) cancellation candidate.  That
candidate-localization step implies RH; its converse is not supplied here because
RH alone does not construct the extra S³/Euler witness data.
-/

namespace Hqiv.Story

noncomputable section

/-- Mathlib RH immediately gives the Story vertical-rigidity obligation. -/
theorem StoryCriticalLineVerticalRigidity_of_RiemannHypothesis
    (hRH : RiemannHypothesis) :
    StoryCriticalLineVerticalRigidity := by
  intro s hs _hLineAtSameHeight
  exact hRH s hs.1 hs.2.1 hs.2.2

/--
Candidate localization is sufficient for Mathlib RH.
-/
theorem RiemannHypothesis_of_candidate_localization
    (χ : PlasticTwiddleCharacter)
    (hEvery : EveryNontrivialZeroHasMatchedEulerSO4Candidate χ) :
    RiemannHypothesis :=
  RiemannHypothesis_of_euler_cancellation_localization χ hEvery

/-- The corrected S³ slot layer bundled for readability. -/
structure S3CandidateLocalizationLayer (χ : PlasticTwiddleCharacter) where
  realize : S3PrimeSurvivorPhaseRealizesEulerSO4Slot χ
  localize :
    PhaseForcesCriticalLine χ → EveryNontrivialZeroHasMatchedEulerSO4Candidate χ

/--
Under the discrete law plus corrected slot realization and candidate
localization, Mathlib RH follows.
-/
theorem RiemannHypothesis_of_s3_candidate_localization_layer
    (χ : PlasticTwiddleCharacter)
    (L : S3DiscreteNullLatticeLaw)
    (A : S3CandidateLocalizationLayer χ) :
    RiemannHypothesis := by
  have hPhase : PhaseForcesCriticalLine χ :=
    PhaseForcesCriticalLine_of_s3_law_and_slot_realization χ L A.realize
  exact RiemannHypothesis_of_candidate_localization χ (A.localize hPhase)

/--
Current full-proof target after the verified S³ geometric layers: prove the
candidate-localization map from corrected slot realization to matched candidates
for every nontrivial zero.

For the live zero-channel route see `S3EulerExplicitFormulaLocalization`.
-/
theorem s3_remaining_candidate_localization_implies_RH
    (χ : PlasticTwiddleCharacter)
    (L : S3DiscreteNullLatticeLaw)
    (hRealize : S3PrimeSurvivorPhaseRealizesEulerSO4Slot χ)
    (hLocalize :
      PhaseForcesCriticalLine χ → EveryNontrivialZeroHasMatchedEulerSO4Candidate χ) :
    RiemannHypothesis := by
  exact RiemannHypothesis_of_s3_candidate_localization_layer χ L
    ⟨hRealize, hLocalize⟩

end
end Hqiv.Story
