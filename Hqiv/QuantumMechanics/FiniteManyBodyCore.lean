import Mathlib.Data.Real.Basic
import Hqiv.QuantumMechanics.FiniteDimVonNeumann
import Hqiv.QuantumMechanics.HubbardDimerGapBridge
import Hqiv.Physics.HQIVFluidClosureScaffold

/-!
# General finite many-body core (dimension-agnostic)

This module provides a small reusable core for finite-dimensional many-body models:

* a model carrier bundling Hamiltonian + named observables;
* a generic Hermitian interaction update `H ↦ H + g V`;
* shell/coherence parameter injection via `lambdaShell` and
  `coherenceFromPlasmaAmp`.

It is intentionally abstract so specific systems (dimer, atoms, molecules) can
plug in without re-deriving the same boilerplate.
-/

namespace Hqiv.QM

open Matrix

/-- Dimension-agnostic finite many-body model:
Hamiltonian and a family of observables on the same finite Hilbert space. -/
structure FiniteManyBodyModel (n : ℕ) where
  /-- Hamiltonian as a Hermitian observable. -/
  H : Observable n
  /-- Label type for registered observables. -/
  ObsLabel : Type
  /-- Observable lookup by label. -/
  O : ObsLabel → Observable n

/-- Add a Hermitian interaction term `g * V` to an observable Hamiltonian. -/
noncomputable def addInteractionObservable {n : ℕ}
    (H V : Observable n) (g : ℝ) : Observable n where
  A := H.A + (g : ℂ) • V.A
  isHerm := by
    refine H.isHerm.add ?_
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, V.isHerm]
    simp

/-- Update a model Hamiltonian by adding `g * V`. -/
noncomputable def FiniteManyBodyModel.withInteraction {n : ℕ}
    (M : FiniteManyBodyModel n) (V : Observable n) (g : ℝ) : FiniteManyBodyModel n where
  H := addInteractionObservable M.H V g
  ObsLabel := M.ObsLabel
  O := M.O

/-- Plasma/coherence parameter packet used across finite many-body models. -/
structure ShellCoherenceParams where
  lambda0 : ℝ
  κ : ℝ
  j₀ : ℝ
  r : ℝ

/-- Coherence factor pulled from the F3 plasma amplitude branch. -/
noncomputable def ShellCoherenceParams.coherence (p : ShellCoherenceParams) : ℝ :=
  Hqiv.Physics.coherenceFromPlasmaAmp p.κ p.j₀ p.r

/-- Shell coupling inherited by finite many-body interaction strengths. -/
noncomputable def ShellCoherenceParams.shellCoupling (p : ShellCoherenceParams) (m : ℕ) : ℝ :=
  lambdaShell m p.lambda0 p.coherence

theorem ShellCoherenceParams.shellCoupling_eq_unsat
    (p : ShellCoherenceParams) (m : ℕ)
    (h_unsat : p.κ * |Hqiv.schematicPlasmaScalar p.j₀ p.r| ≤ 1) :
    p.shellCoupling m
      = p.lambda0 * (p.κ * |Hqiv.schematicPlasmaScalar p.j₀ p.r|) * ((m + 1 : ℝ) / 5) := by
  unfold ShellCoherenceParams.shellCoupling ShellCoherenceParams.coherence
  have hcoh :
      Hqiv.Physics.coherenceFromPlasmaAmp p.κ p.j₀ p.r =
        p.κ * |Hqiv.schematicPlasmaScalar p.j₀ p.r| :=
    (Hqiv.Physics.coherenceFromPlasmaAmp_eq_mul_iff p.κ p.j₀ p.r).2 h_unsat
  rw [hcoh, lambdaShell_closed_form]

theorem ShellCoherenceParams.shellCoupling_monotone
    (p : ShellCoherenceParams) (h_nonneg : 0 ≤ p.lambda0 * p.coherence) :
    Monotone (fun m => p.shellCoupling m) := by
  intro m n hmn
  unfold ShellCoherenceParams.shellCoupling
  exact lambdaShell_monotone p.lambda0 p.coherence h_nonneg hmn

end Hqiv.QM
