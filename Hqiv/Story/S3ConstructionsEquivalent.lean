import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3ComplexResidualModel

/-!
# The two constructions are equivalent — master iff chain

We already proved that the geometric/analytic packagings are **not weaker** than RH:
they are **the same statement** in different coordinates.

This module collects the master equivalences so the proof target is unambiguous:

* `Nonempty S3ComplexResidualModel ↔ RiemannHypothesis`
* `WeilFormPositive ↔ RiemannHypothesis`
* `AllNontrivialZerosOnLine ↔ RiemannHypothesis`
* therefore **`Nonempty S3ComplexResidualModel ↔ WeilFormPositive`**

and under a zeta/S³ identification at a point,

* `ZetaZeroAt s ↔ S3ResidualZero P` when `ZetaEqualsS3ResidualAt s P`.

So there is no logical gap *between* the constructions. Proving any packaging
constructively **is** proving RH. What remains open is supplying the inhabitant /
positivity witness from the harmonic–Δ–prime–ζ pipeline — not bridging two
inequivalent statements.
-/

namespace Hqiv.Story

noncomputable section

/-- S³ complex residual packaging ↔ Mathlib RH (proved in `S3ComplexResidualModel`). -/
theorem complexResidualModel_iff_RH :
    Nonempty S3ComplexResidualModel ↔ RiemannHypothesis :=
  nonempty_complexResidualModel_iff_RiemannHypothesis

/-- Weil positivity packaging ↔ Mathlib RH (proved in `S3WeilPositivityCriterion`). -/
theorem weilFormPositive_iff_RH :
    WeilFormPositive ↔ RiemannHypothesis :=
  weilFormPositive_iff_RiemannHypothesis

/-- Pointwise on-line packaging ↔ Mathlib RH (proved in `S3OrbitVsPointwiseGap`). -/
theorem allZerosOnLine_iff_RH :
    AllNontrivialZerosOnLine ↔ RiemannHypothesis :=
  allNontrivialZerosOnLine_iff_RiemannHypothesis

/--
**Master equivalence.** The S³ complex-residual construction and the Weil
positivity construction are equivalent — not merely each implying RH separately.
-/
theorem complexResidualModel_iff_weilFormPositive :
    Nonempty S3ComplexResidualModel ↔ WeilFormPositive := by
  rw [complexResidualModel_iff_RH, weilFormPositive_iff_RH]

/--
**Master equivalence (three ways).** All three named packagings are the same target.
-/
theorem three_packagings_mutually_equivalent :
    (Nonempty S3ComplexResidualModel ↔ WeilFormPositive) ∧
      (WeilFormPositive ↔ AllNontrivialZerosOnLine) ∧
      (AllNontrivialZerosOnLine ↔ Nonempty S3ComplexResidualModel) := by
  refine ⟨complexResidualModel_iff_weilFormPositive, ?_, ?_⟩
  · rw [weilFormPositive_iff_RH, allZerosOnLine_iff_RH]
  · rw [allZerosOnLine_iff_RH, complexResidualModel_iff_RH]

/--
Under a pointwise zeta/S³ identification, the zero equations are equivalent
(proved in `S3ZeroEquationEquivalence`).
-/
theorem zeta_zero_iff_s3_residual_zero
    {s : ℂ} {P : ScaledS3Sample} (hEq : ZetaEqualsS3ResidualAt s P) :
    ZetaZeroAt s ↔ S3ResidualZero P :=
  zeta_zero_iff_s3_residual_zero_of_eq hEq

end

end Hqiv.Story
