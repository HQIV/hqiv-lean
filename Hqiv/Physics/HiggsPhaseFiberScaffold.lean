import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.FanoOmaxwellSpectrum
import Hqiv.Physics.FanoParticleVertexSelectors
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Algebra.OctonionBasics

namespace Hqiv.Physics

open Matrix
open Hqiv.Algebra

/-!
# Higgs phase-fiber scaffold

This module adds a minimal Lean-facing scaffold toward the paper's
`e₇`-projected phase-fiber Higgs story.

What is made explicit here:

- the preferred Fano-plane axis corresponding to matrix index `7` (`e₇`),
- the canonical incident Fano line used by the current `FanoLine.ofTag` convention,
- the fact that this line also contains the electromagnetic axis (`e₁`, matrix index `1`),
- the fact that projecting the phase-lift generator `Δ` to that line preserves `Δ`,
- the resulting projected O-Maxwell phase-lift mode at `bosonClosureShell`,
- the **associator-derived `e₇` coefficient** for the standard basis triple `(e₁,e₃,e₅)` as a real
  readout (`e7ProjectedAssociatorCoeff`), and a **quadratic scalar weight** built from the same
  `Δ²` trace used in `FanoOmaxwellSpectrum` and `phaseLiftCoeff bosonClosureShell`.

This does **not** replace the outer-horizon closure for `vacuumExpectationValueScalar` or assert
definitional equality between the associator channel and the EW vev: it places the paper’s
“effective quadratic term” ingredients next to the existing scalar witness.
-/

/-- `e₇` component of the octonion associator on the **Higgs triple** `(e₁,e₃,e₅)` (matrix indices). -/
noncomputable def e7ProjectedAssociatorCoeff : ℝ :=
  octonionAssociator e1 e3 e5 (⟨7, by decide⟩ : Fin 8)

/-- Quadratic weight: `Tr(Δ²)` on the octonion carrier times `(φ/6)²` at `bosonClosureShell`. -/
noncomputable def higgsPhaseFiberQuadraticWeight : ℝ :=
  phaseLiftDeltaQuadraticTrace * (Hqiv.Algebra.phaseLiftCoeff bosonClosureShell) ^ 2

theorem higgsPhaseFiberQuadraticWeight_eq_two_mul_phaseLiftCoeff_sq :
    higgsPhaseFiberQuadraticWeight = 2 * (Hqiv.Algebra.phaseLiftCoeff bosonClosureShell) ^ 2 := by
  simp [higgsPhaseFiberQuadraticWeight, phaseLiftDeltaQuadraticTrace_eq_two]

/-- Lepton-style basis triple for comparison: `e₇` component of `[e₁,e₂,e₃]` (numeric value not forced here). -/
noncomputable def leptonStyleE7AssociatorCoeff : ℝ :=
  octonionAssociator e1 e2 e3 (⟨7, by decide⟩ : Fin 8)

/-- Preferred colour / Higgs-projecting Fano-plane axis: the vertex mapping to matrix index `7` (`e₇`).
Same as `scalarHiggsFanoVertex` in `FanoParticleVertexSelectors` (all-sector table). -/
def higgsPreferredAxis : FanoVertex := scalarHiggsFanoVertex

/-- Electromagnetic axis in the same `FanoVertex` bookkeeping: matrix index `1` (`e₁`). -/
def phaseLiftEmAxis : FanoVertex := ⟨0, by decide⟩

/-- Canonical Fano line used for the Higgs phase-fiber scaffold: standard line `2` (matrix
indices `{1,6,7}`), the **lowest-index** line through `higgsPreferredAxis`; provably
`FanoLine.ofTag higgsPreferredAxis` (`higgsPreferredLine_eq_ofTag_higgsAxis`). For shell- or
rapidity-cycled choices over the three incident lines, use `fanoLineFromVertexShell` in
`FanoLineRapidityChoice`. -/
def higgsPreferredLine : FanoLine := ofIndex 2

theorem higgsPreferredLine_eq_ofTag_higgsAxis : higgsPreferredLine = FanoLine.ofTag higgsPreferredAxis := by
  simp [higgsPreferredLine, higgsPreferredAxis, scalarHiggsFanoVertex, FanoLine.ofTag, FanoLine.ofIncidentVertex,
    ofIndex, incidentLineLabelLowest]

theorem fanoVertexMatrixIndex_phaseLiftEmAxis :
    fanoVertexMatrixIndex phaseLiftEmAxis = 1 := by
  rfl

theorem fanoVertexMatrixIndex_higgsPreferredAxis :
    fanoVertexMatrixIndex higgsPreferredAxis = 7 := by
  rfl

theorem higgsPreferredLine_contains_higgsPreferredAxis :
    higgsPreferredAxis ∈ higgsPreferredLine.pts := by
  native_decide

theorem higgsPreferredLine_contains_phaseLiftEmAxis :
    phaseLiftEmAxis ∈ higgsPreferredLine.pts := by
  native_decide

/-- Explicit diagonal selector for the canonical `e₇` incident line `{e₁,e₆,e₇}` in matrix indices. -/
noncomputable def higgsPreferredLineSelectorExplicit : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal fun i =>
    if i = (1 : Fin 8) ∨ i = (6 : Fin 8) ∨ i = (7 : Fin 8) then (1 : ℝ) else 0

theorem higgsPreferredLineSelector_eq_explicit :
    fanoLineSelector higgsPreferredLine = higgsPreferredLineSelectorExplicit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higgsPreferredLine,
      ofIndex, fanoStandardLine, fanoLineSelector, fanoVertexSelector,
      fanoVertexMatrixIndex, higgsPreferredLineSelectorExplicit]

/-- The canonical `e₇`-incident Fano-line projection keeps the `(1,7)` phase-lift entry. -/
theorem higgsPreferredLine_projectedDelta_17 :
    (fanoLineSelector higgsPreferredLine * Hqiv.Algebra.phaseLiftDeltaMatrix *
        fanoLineSelector higgsPreferredLine) 1 7 = -1 := by
  rw [higgsPreferredLineSelector_eq_explicit, higgsPreferredLineSelectorExplicit]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  norm_num [Hqiv.Algebra.phaseLiftDeltaMatrix, Hqiv.phaseLiftDelta, Matrix.of_apply]

/-- The canonical `e₇`-incident Fano-line projection keeps the `(7,1)` phase-lift entry. -/
theorem higgsPreferredLine_projectedDelta_71 :
    (fanoLineSelector higgsPreferredLine * Hqiv.Algebra.phaseLiftDeltaMatrix *
        fanoLineSelector higgsPreferredLine) 7 1 = 1 := by
  rw [higgsPreferredLineSelector_eq_explicit, higgsPreferredLineSelectorExplicit]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [Hqiv.Algebra.phaseLiftDeltaMatrix, Hqiv.phaseLiftDelta, Matrix.of_apply]

/-- O-Maxwell spectral mode attached to the Higgs-phase scaffold: canonical `e₇` line at the EW shell. -/
noncomputable def higgsPhaseFiberMode : FanoOmaxwellSpectralMode :=
  ⟨higgsPreferredLine, bosonClosureShell⟩

theorem higgsPhaseFiberMode_shell :
    higgsPhaseFiberMode.shell = bosonClosureShell := rfl

theorem higgsPhaseFiberMode_line :
    higgsPhaseFiberMode.line = higgsPreferredLine := rfl

theorem higgsPhaseFiberMode_projectedStrength_eq_phaseLiftCoeff :
    higgsPhaseFiberMode.projectedStrength = Hqiv.Algebra.phaseLiftCoeff bosonClosureShell := by
  unfold higgsPhaseFiberMode FanoOmaxwellSpectralMode.projectedStrength
  simp [spectralProjectionNormalization_eq_one]

theorem higgsPhaseFiberMode_projectedPhaseLiftMatrix_17 :
    higgsPhaseFiberMode.projectedPhaseLiftMatrix 1 7 =
      - Hqiv.Algebra.phaseLiftCoeff bosonClosureShell := by
  simp [higgsPhaseFiberMode, FanoOmaxwellSpectralMode.projectedPhaseLiftMatrix,
    spectralProjectionNormalization_eq_one, higgsPreferredLine_projectedDelta_17]

theorem higgsPhaseFiberMode_projectedPhaseLiftMatrix_71 :
    higgsPhaseFiberMode.projectedPhaseLiftMatrix 7 1 =
      Hqiv.Algebra.phaseLiftCoeff bosonClosureShell := by
  simp [higgsPhaseFiberMode, FanoOmaxwellSpectralMode.projectedPhaseLiftMatrix,
    spectralProjectionNormalization_eq_one, higgsPreferredLine_projectedDelta_71]

theorem higgsPhaseFiberQuadraticWeight_eq_two_mul_projectedStrength_sq :
    higgsPhaseFiberQuadraticWeight = 2 * higgsPhaseFiberMode.projectedStrength ^ 2 := by
  simp [higgsPhaseFiberQuadraticWeight, higgsPhaseFiberMode_projectedStrength_eq_phaseLiftCoeff,
    phaseLiftDeltaQuadraticTrace_eq_two]

/-- The same outer-horizon shell indexes the phase-lift window and the geometric vev factor. -/
theorem higgsPhaseFiber_mode_and_vev_share_bosonClosureShell :
    higgsPhaseFiberMode.shell = bosonClosureShell ∧
      vacuumExpectationValue =
        T_lockin * outerHorizonSurface bosonClosureShell * outerClosureMonogamyLift := by
  constructor
  · exact higgsPhaseFiberMode_shell
  · rfl

/-- Higgs scaffold readout keeps the same scalar closure witness used downstream. -/
theorem scalarClosureWitness_eq_higgs_mass_readout :
    scalarClosureWitness = m_H_derived := rfl

theorem scalarClosureWitness_eq_two_vacuumExpectationValueScalar :
    scalarClosureWitness = 2 * vacuumExpectationValueScalar := by
  simpa [scalarClosureWitness] using higgs_mass_from_outer_resonance

/-- Scalar vev is the same combination of `outerHorizonSurface bosonClosureShell` as the phase-lift shell. -/
theorem vacuumExpectationValueScalar_quadratic_support :
    ∃ (c₁ c₂ c₃ : ℝ), vacuumExpectationValueScalar = c₁ * outerHorizonSurface bosonClosureShell * c₂ * c₃ := by
  refine ⟨T_lockin, outerClosureMonogamyLift, (ewScalarSectorQuantumLift : ℝ), ?_⟩
  unfold vacuumExpectationValueScalar vacuumExpectationValue ewScalarSectorQuantumLift
  ring

end Hqiv.Physics
