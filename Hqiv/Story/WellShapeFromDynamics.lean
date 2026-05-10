import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Well shape from fixed dynamics

This module formalizes the statement:

> If the dynamical equations are fixed (phase step and curvature / `Ω_k` by axis and shell),
> then the well profile is fixed as a derived function; no calibration/search is needed to
> define the well shape itself.

Search may still be used to locate minima ("quanta"), but the profile is fully determined by
the dynamics.
-/

namespace Hqiv.Story

noncomputable section

/-- Minimal dynamics record needed for the well-profile statement. -/
structure QuantumWellDynamics (Axis : Type) where
  /-- One-shell phase increment on a chosen axis/frame. -/
  phaseStep : Axis → Nat → ℝ
  /-- Curvature self-support readout (`Ω_k`) on a chosen axis/frame. -/
  omega : Axis → Nat → ℝ

/-- Well profile from fixed dynamics:
phase-lock mismatch + curvature self-support mismatch. -/
def wellProfile {Axis : Type} (D : QuantumWellDynamics Axis) (a : Axis) (m : Nat) : ℝ :=
  |D.phaseStep a m - 2 * Real.pi| + |D.omega a m - 1|

/-- "Quanta" at `(a,m)` as local minima of the derived well profile. -/
def IsQuantum {Axis : Type} (D : QuantumWellDynamics Axis) (a : Axis) (m : Nat) : Prop :=
  wellProfile D a m ≤ wellProfile D a (m + 1) ∧
    (∀ k : Nat, k + 1 = m → wellProfile D a m ≤ wellProfile D a k)

/-- If two dynamics are pointwise equal, their well profiles are pointwise equal. -/
theorem wellProfile_eq_of_dynamics_eq {Axis : Type}
    (D₁ D₂ : QuantumWellDynamics Axis)
    (hPhase : ∀ a m, D₁.phaseStep a m = D₂.phaseStep a m)
    (hOmega : ∀ a m, D₁.omega a m = D₂.omega a m) :
    ∀ a m, wellProfile D₁ a m = wellProfile D₂ a m := by
  intro a m
  simp [wellProfile, hPhase a m, hOmega a m]

/-- Extensional form: dynamics equality implies well-profile equality as functions. -/
theorem wellProfile_funext_of_dynamics_eq {Axis : Type}
    (D₁ D₂ : QuantumWellDynamics Axis)
    (hPhase : ∀ a m, D₁.phaseStep a m = D₂.phaseStep a m)
    (hOmega : ∀ a m, D₁.omega a m = D₂.omega a m) :
    wellProfile D₁ = wellProfile D₂ := by
  funext a m
  exact wellProfile_eq_of_dynamics_eq D₁ D₂ hPhase hOmega a m

/-- The well profile is definitionally determined by the two dynamical fields. -/
theorem wellProfile_determined_by_phase_and_omega {Axis : Type}
    (D : QuantumWellDynamics Axis) :
    wellProfile D =
      (fun a m => |D.phaseStep a m - 2 * Real.pi| + |D.omega a m - 1|) := rfl

/-- Quanta are exactly local minima of the derived well profile (unfolded form). -/
theorem isQuantum_iff_local_min {Axis : Type}
    (D : QuantumWellDynamics Axis) (a : Axis) (m : Nat) :
    IsQuantum D a m ↔
      (wellProfile D a m ≤ wellProfile D a (m + 1) ∧
        ∀ k : Nat, k + 1 = m → wellProfile D a m ≤ wellProfile D a k) := Iff.rfl

end

end Hqiv.Story
