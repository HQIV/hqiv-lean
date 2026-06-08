import Hqiv.QuantumMechanics.Schrodinger

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Helium scaffold (two-electron spatial+spin layer)

This module provides a minimal, composable two-electron scaffold for helium-like
systems:

- two-electron spatial wavefunctions,
- exchange symmetry projections,
- a concrete shell-based helium spatial ansatz,
- a spin-singlet scaffold,
- Pauli-compatible total-state witness (symmetric spatial × antisymmetric spin).

No new axioms, no `sorry`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv

/-- Two-electron spatial wavefunction on the continuum position chart. -/
abbrev TwoElectronWavefunction := Position → Position → ℂ

/-- Two-electron spin wavefunction (toy two-level spin label). -/
abbrev TwoSpinWavefunction := Bool → Bool → ℂ

/-- Particle-exchange operator on two-electron spatial wavefunctions. -/
def swap12 (ψ : TwoElectronWavefunction) : TwoElectronWavefunction :=
  fun x₁ x₂ => ψ x₂ x₁

theorem swap12_involutive (ψ : TwoElectronWavefunction) :
    swap12 (swap12 ψ) = ψ := by
  funext x₁ x₂
  rfl

/-- Symmetric and antisymmetric projectors (spatial sector). -/
noncomputable def symmetrize (ψ : TwoElectronWavefunction) : TwoElectronWavefunction :=
  fun x₁ x₂ => ((ψ x₁ x₂ + ψ x₂ x₁) / 2)

noncomputable def antisymmetrize (ψ : TwoElectronWavefunction) : TwoElectronWavefunction :=
  fun x₁ x₂ => ((ψ x₁ x₂ - ψ x₂ x₁) / 2)

theorem symmetrize_exchange_invariant (ψ : TwoElectronWavefunction) :
    ∀ x₁ x₂, symmetrize ψ x₁ x₂ = symmetrize ψ x₂ x₁ := by
  intro x₁ x₂
  unfold symmetrize
  ring

theorem antisymmetrize_exchange_sign (ψ : TwoElectronWavefunction) :
    ∀ x₁ x₂, antisymmetrize ψ x₂ x₁ = - antisymmetrize ψ x₁ x₂ := by
  intro x₁ x₂
  unfold antisymmetrize
  ring

theorem symm_plus_antisymm_eq_original (ψ : TwoElectronWavefunction) :
    ∀ x₁ x₂, symmetrize ψ x₁ x₂ + antisymmetrize ψ x₁ x₂ = ψ x₁ x₂ := by
  intro x₁ x₂
  unfold symmetrize antisymmetrize
  ring

/-- Product spatial ansatz from shell-resolved hydrogenic orbitals (`Z = 2` for helium-like core). -/
noncomputable def heliumSpatialAnsatz (m : ℕ) (μ : ℝ) : TwoElectronWavefunction :=
  fun x₁ x₂ => hydrogenGroundStateOfShell m 2 μ x₁ * hydrogenGroundStateOfShell m 2 μ x₂

theorem heliumSpatialAnsatz_exchange_invariant (m : ℕ) (μ : ℝ) :
    ∀ x₁ x₂, heliumSpatialAnsatz m μ x₁ x₂ = heliumSpatialAnsatz m μ x₂ x₁ := by
  intro x₁ x₂
  unfold heliumSpatialAnsatz
  ring

/-- Canonical spin-singlet scaffold (`|↑↓⟩ - |↓↑⟩`) up to normalization factor. -/
noncomputable def spinSinglet : TwoSpinWavefunction :=
  fun s₁ s₂ =>
    if s₁ = false ∧ s₂ = true then (1 / Real.sqrt 2 : ℂ)
    else if s₁ = true ∧ s₂ = false then (- (1 / Real.sqrt 2 : ℂ))
    else 0

theorem spinSinglet_antisymmetric :
    ∀ s₁ s₂, spinSinglet s₂ s₁ = - spinSinglet s₁ s₂ := by
  intro s₁ s₂
  cases s₁ <;> cases s₂ <;> simp [spinSinglet]

/-- Pauli-compatible helium scaffold witness:
spatial factor is exchange-symmetric and spin factor is exchange-antisymmetric. -/
def heliumPauliCompatible (m : ℕ) (μ : ℝ) : Prop :=
  (∀ x₁ x₂, heliumSpatialAnsatz m μ x₁ x₂ = heliumSpatialAnsatz m μ x₂ x₁) ∧
    (∀ s₁ s₂, spinSinglet s₂ s₁ = - spinSinglet s₁ s₂)

theorem heliumPauliCompatible_holds (m : ℕ) (μ : ℝ) :
    heliumPauliCompatible m μ := by
  exact ⟨heliumSpatialAnsatz_exchange_invariant m μ, spinSinglet_antisymmetric⟩

end Hqiv.QuantumChemistry
