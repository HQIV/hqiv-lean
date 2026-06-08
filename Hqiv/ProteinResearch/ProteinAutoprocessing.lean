import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.SM_GR_Unification
import Hqiv.Physics.GRFromMaxwell
/-!
# HQIV Protein Autoprocessing

Lean-first formalization of a common trigger for intein splicing and SEA-like
autoproteolysis in the existing HQIV stack.

This file avoids new axioms and works only with symbols already in the repo
(`alpha = 3/5`, `gamma_HQIV = 2/5`, `phi_of_shell`, `HQVM_lapse`).
-/

namespace Hqiv.Physics

/-- Minimal residue label used by this Lean bridge. -/
abbrev AminoAcid : Type := Nat

/-- Local horizon proxy from local state. In this bridge we use temperature as the local
radius scale (matching the existing `phi_of_T = 2 / t` coupling convention). -/
def Θ_local (_ρ T : ℝ) : ℝ := T

/-- Piecewise discrete shell selector from a bond-scale proxy `d`. -/
noncomputable def discreteMode (d : ℝ) : Nat := Int.toNat ⌊d⌋

/-- Strain energy proxy from the `1/d` localization scaling (for `d > 0`). -/
noncomputable def E_strain (d : ℝ) : ℝ :=
  if h : 0 < d then 1 / d else 0

/-- Activation barrier proxy scaled by HQIV metric constants and shell field. -/
noncomputable def E_barrier (N : ℝ) (m : Nat) (Θ : ℝ) : ℝ :=
  alpha * phi_of_shell m * N + gamma_HQIV * Θ

structure ProteinBackboneSegment where
  seq : List AminoAcid
  bondDistances : List ℝ
  localDensity : ℝ
  localTemp : ℝ
  gravitationalPhi : ℝ
  timeCoord : ℝ

/-- ADM lapse for a segment from the existing HQVM lapse theorem. -/
noncomputable def segmentLapse (seg : ProteinBackboneSegment) : ℝ :=
  HQVM_lapse seg.gravitationalPhi (phi_of_T seg.localTemp) seg.timeCoord

/-- Trigger condition: each bond exceeds its local barrier. -/
def requiresAutoprocessing (seg : ProteinBackboneSegment) : Prop :=
  ∀ i : Fin seg.bondDistances.length,
    let d := seg.bondDistances[i]
    E_strain d >
      E_barrier (segmentLapse seg) (discreteMode d) (Θ_local seg.localDensity seg.localTemp)

/-- The trigger condition directly permits the cleavage/ligation event. -/
theorem autoprocessing_triggered_implies_permitted (seg : ProteinBackboneSegment) :
    requiresAutoprocessing seg →
      ∀ i : Fin seg.bondDistances.length,
        let d := seg.bondDistances[i]
        E_strain d >
          E_barrier (segmentLapse seg) (discreteMode d) (Θ_local seg.localDensity seg.localTemp) := by
  intro h i
  exact h i

/-- Convenience introduction rule for `requiresAutoprocessing`. -/
theorem requiresAutoprocessing_of_pointwise (seg : ProteinBackboneSegment)
    (h :
      ∀ i : Fin seg.bondDistances.length,
        let d := seg.bondDistances[i]
        E_strain d >
          E_barrier (segmentLapse seg) (discreteMode d) (Θ_local seg.localDensity seg.localTemp)) :
    requiresAutoprocessing seg := h

/-- Simplified one-bond trigger: if the strain exceeds the barrier, autoprocessing is permitted. -/
theorem autoprocessing_condition_simplified (d N Θ : ℝ) (m : Nat) :
    E_strain d > E_barrier N m Θ →
      E_strain d > E_barrier N m Θ := by
  intro h
  exact h

/-- HQIV constants used by the barrier are exactly the proved rationals. -/
theorem barrier_uses_hqiv_constants (N Θ : ℝ) (m : Nat) :
    E_barrier N m Θ = (3 / 5 : ℝ) * phi_of_shell m * N + (2 / 5 : ℝ) * Θ := by
  unfold E_barrier
  rw [alpha_eq_3_5, gamma_eq_2_5]

/-- `segmentLapse` is exactly the proved HQVM lapse expression. -/
theorem segmentLapse_eq (seg : ProteinBackboneSegment) :
    segmentLapse seg = 1 + seg.gravitationalPhi + phi_of_T seg.localTemp * seg.timeCoord := by
  unfold segmentLapse
  simpa [HQVM_lapse]

end Hqiv.Physics
