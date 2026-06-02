import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Hqiv.Physics.FanoLine
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.OMaxwellAlgebraSeed
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Algebra.PhaseLiftDelta

namespace Hqiv.Physics

open Hqiv
open Matrix
open scoped BigOperators

/-!
# Fano-projected O-Maxwell spectral scaffold

This module packages the direct denominator source requested by the O-Maxwell/Fano roadmap:

- a `FanoOmaxwellSpectralMode` indexed by a combinatorial `FanoLine` and shell `m`,
- a line selector on the octonion carrier,
- a projected `Δ`-coupled matrix object,
- a scalar 1-jet `spectralFanoRindler1Jet` used as the public detuning source.

The present spectrum is still a **certified scaffold**: it is built from the matrix-level choices
already fixed in the HQVM calculator (`Δ`, octonion carrier, Fano restriction) and is proved to
recover the existing affine/Rindler law exactly on the natural readout chart.

In the current architecture this module is a direct spectral source. Upstream modal frequency and
interaction-horizon packaging is handled in `ModalFrequencyHorizon.lean`, where natural indices are
treated as readout/bookkeeping rather than mandatory primary inputs.
-/

/-- Embed a Fano-plane vertex into the octonion carrier indices `1..7`, reserving `0` for the scalar slot. -/
def fanoVertexMatrixIndex (v : FanoVertex) : Fin 8 :=
  ⟨v.1 + 1, Nat.succ_lt_succ v.2⟩

/-- Diagonal selector for one Fano-plane vertex in the 8x8 octonion carrier. -/
noncomputable def fanoVertexSelector (v : FanoVertex) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.diagonal fun i => if i = fanoVertexMatrixIndex v then (1 : ℝ) else 0

theorem fanoVertexSelector_trace (v : FanoVertex) : Matrix.trace (fanoVertexSelector v) = 1 := by
  simp [fanoVertexSelector, Matrix.trace_diagonal]

/-- Fano-line selector: sum of the three diagonal vertex selectors on the line. -/
noncomputable def fanoLineSelector (L : FanoLine) : Matrix (Fin 8) (Fin 8) ℝ :=
  ∑ v ∈ L.pts, fanoVertexSelector v

theorem fanoLineSelector_trace (L : FanoLine) : Matrix.trace (fanoLineSelector L) = 3 := by
  unfold fanoLineSelector
  simp [fanoVertexSelector_trace, L.size_three]

/-- Quadratic `Δ` energy used by the spectral scaffold. For the calculator's `Δ`, the value is `2`. -/
noncomputable def phaseLiftDeltaQuadraticTrace : ℝ :=
  Matrix.trace (Hqiv.Algebra.phaseLiftDeltaMatrix * Hqiv.Algebra.phaseLiftDeltaMatrixᵀ)

theorem phaseLiftDeltaQuadraticTrace_eq_two : phaseLiftDeltaQuadraticTrace = 2 := by
  unfold phaseLiftDeltaQuadraticTrace Hqiv.Algebra.phaseLiftDeltaMatrix Hqiv.phaseLiftDelta
  let Δ : Matrix (Fin 8) (Fin 8) ℝ :=
    Matrix.of (fun i j => if i = 1 ∧ j = 7 then (-1 : ℝ) else if i = 7 ∧ j = 1 then 1 else 0)
  have hmul :
      Δ * Δᵀ = Matrix.diagonal (fun i : Fin 8 => if i = 1 ∨ i = 7 then (1 : ℝ) else 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Δ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  change Matrix.trace (Δ * Δᵀ) = 2
  rw [hmul, Matrix.trace_diagonal]
  have hsum :
      (∑ i : Fin 8, if i = 1 ∨ i = 7 then (1 : ℝ) else 0) =
        (((Finset.univ.filter fun i : Fin 8 => i = 1 ∨ i = 7).card : ℕ) : ℝ) := by
    simp
  rw [hsum]
  have hcard : (Finset.univ.filter fun i : Fin 8 => i = 1 ∨ i = 7).card = 2 := by
    native_decide
  norm_num [hcard]

/-- Normalized scalar extracted from the Fano selector and the underlying `Δ` matrix. -/
noncomputable def spectralProjectionNormalization (L : FanoLine) : ℝ :=
  (Matrix.trace (fanoLineSelector L) + phaseLiftDeltaQuadraticTrace) / 5

theorem spectralProjectionNormalization_eq_one (L : FanoLine) :
    spectralProjectionNormalization L = 1 := by
  rw [spectralProjectionNormalization, fanoLineSelector_trace, phaseLiftDeltaQuadraticTrace_eq_two]
  norm_num

/-- A named O-Maxwell spectral mode on one Fano line and one shell. -/
structure FanoOmaxwellSpectralMode where
  line : FanoLine
  shell : ℕ

/-- Parent 8x8 generator drawn from the existing O-Maxwell algebraic seed ladder. -/
noncomputable def FanoOmaxwellSpectralMode.parentGenerator (mode : FanoOmaxwellSpectralMode) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  Hqiv.algebraicMaxwellParentGenerator mode.shell

/-- H-sector block of the parent O-Maxwell generator for the mode. -/
noncomputable def FanoOmaxwellSpectralMode.hBlock (mode : FanoOmaxwellSpectralMode) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Hqiv.algebraicMaxwellQuadrantBottomRight mode.parentGenerator

/-- Projected `Δ`-coupled mode matrix on the chosen Fano line. -/
noncomputable def FanoOmaxwellSpectralMode.projectedPhaseLiftMatrix
    (mode : FanoOmaxwellSpectralMode) : Matrix (Fin 8) (Fin 8) ℝ :=
  (spectralProjectionNormalization mode.line * Hqiv.Algebra.phaseLiftCoeff mode.shell) •
    (fanoLineSelector mode.line * Hqiv.Algebra.phaseLiftDeltaMatrix * fanoLineSelector mode.line)

/-- Scalar strength of the spectral mode used by the first detuning 1-jet. -/
noncomputable def FanoOmaxwellSpectralMode.projectedStrength
    (mode : FanoOmaxwellSpectralMode) : ℝ :=
  spectralProjectionNormalization mode.line * Hqiv.Algebra.phaseLiftCoeff mode.shell

/-- Direct spectral 1-jet source for the detuning denominator on a chosen Fano line. -/
noncomputable def spectralFanoRindler1Jet (L : FanoLine) (m : ℕ) : ℝ :=
  let mode : FanoOmaxwellSpectralMode := ⟨L, m⟩
  let base : FanoOmaxwellSpectralMode := ⟨L, 0⟩
  1 + ((3 * gamma_HQIV) / 2) * (mode.projectedStrength - base.projectedStrength)

theorem spectralFanoRindler1Jet_eq_rindler (L : FanoLine) (m : ℕ) :
    spectralFanoRindler1Jet L m = rindlerDetuningShared (m : ℝ) := by
  have hnorm : spectralProjectionNormalization L = 1 := spectralProjectionNormalization_eq_one L
  unfold spectralFanoRindler1Jet FanoOmaxwellSpectralMode.projectedStrength
  simp [hnorm]
  unfold Hqiv.Algebra.phaseLiftCoeff rindlerDetuningShared c_rindler_shared
  rw [phi_of_shell_closed_form, phi_of_shell_closed_form (m := 0), phiTemperatureCoeff_eq_two]
  ring

theorem spectralFanoRindler1Jet_eq_one_plus_half_gamma (L : FanoLine) (m : ℕ) :
    spectralFanoRindler1Jet L m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  rw [spectralFanoRindler1Jet_eq_rindler]
  unfold rindlerDetuningShared c_rindler_shared
  ring

theorem spectralFanoRindler1Jet_at_shell_zero_eq_one (L : FanoLine) :
    spectralFanoRindler1Jet L 0 = 1 := by
  rw [spectralFanoRindler1Jet_eq_rindler]
  simp [rindlerDetuningShared]

theorem spectralFanoRindler1Jet_line_invariant (L₁ L₂ : FanoLine) (m : ℕ) :
    spectralFanoRindler1Jet L₁ m = spectralFanoRindler1Jet L₂ m := by
  rw [spectralFanoRindler1Jet_eq_rindler, spectralFanoRindler1Jet_eq_rindler]

end Hqiv.Physics
