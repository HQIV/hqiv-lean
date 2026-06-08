import Hqiv.QuantumChemistry.AtomicExcitations
import Hqiv.QuantumChemistry.HeliumScaffold

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Slater scaffold (antisymmetrized atomic wavefunctions)

Minimal Slater-style layer on top of the atomic excitation scaffold:

- generic 2-orbital antisymmetrized determinant,
- specialization to any atom (`AtomicShellSpec`) by choosing active indices,
- excited-state specialization via `AtomicShellSpec.excited`.

This keeps antisymmetry explicit without requiring full determinant machinery for
all `n` yet.
-/

namespace Hqiv.QuantumChemistry

open Hqiv

/-- One-electron orbital over continuum position. -/
abbrev Orbital := Position → ℂ

/-- Two-orbital Slater determinant scaffold (normalized by `1 / sqrt 2`). -/
noncomputable def slaterDetTwo (φa φb : Orbital) : TwoElectronWavefunction :=
  fun x₁ x₂ => (φa x₁ * φb x₂ - φa x₂ * φb x₁) / Real.sqrt 2

theorem slaterDetTwo_exchange_sign (φa φb : Orbital) :
    ∀ x₁ x₂, slaterDetTwo φa φb x₂ x₁ = - slaterDetTwo φa φb x₁ x₂ := by
  intro x₁ x₂
  unfold slaterDetTwo
  ring

/-- Shell-resolved orbital channel for electron index `i` of atom `a`. -/
noncomputable def atomOrbital (a : AtomicShellSpec) (μ : ℝ) (i : Fin a.e) : Orbital :=
  hydrogenGroundStateOfShell (a.shell i) a.Z μ

/-- Active-pair antisymmetrized wavefunction for any atom state. -/
noncomputable def atomActivePairSlater (a : AtomicShellSpec) (μ : ℝ) (i j : Fin a.e) :
    TwoElectronWavefunction :=
  slaterDetTwo (atomOrbital a μ i) (atomOrbital a μ j)

theorem atomActivePairSlater_exchange_sign (a : AtomicShellSpec) (μ : ℝ) (i j : Fin a.e) :
    ∀ x₁ x₂, atomActivePairSlater a μ i j x₂ x₁ = - atomActivePairSlater a μ i j x₁ x₂ := by
  simpa [atomActivePairSlater] using slaterDetTwo_exchange_sign (atomOrbital a μ i) (atomOrbital a μ j)

/-- Excited-state active-pair antisymmetrized wavefunction. -/
noncomputable def atomActivePairSlaterExcited (a : AtomicShellSpec) (δ : ExcitationProfile a.e)
    (μ : ℝ) (i j : Fin a.e) : TwoElectronWavefunction :=
  atomActivePairSlater (a.excited δ) μ i j

theorem atomActivePairSlaterExcited_exchange_sign (a : AtomicShellSpec) (δ : ExcitationProfile a.e)
    (μ : ℝ) (i j : Fin a.e) :
    ∀ x₁ x₂,
      atomActivePairSlaterExcited a δ μ i j x₂ x₁ =
        - atomActivePairSlaterExcited a δ μ i j x₁ x₂ := by
  simpa [atomActivePairSlaterExcited] using atomActivePairSlater_exchange_sign (a.excited δ) μ i j

end Hqiv.QuantumChemistry
