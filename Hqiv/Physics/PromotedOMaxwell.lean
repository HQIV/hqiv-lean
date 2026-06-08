import Hqiv.Physics.CovariantSolution
import Hqiv.Physics.ContinuumOmaxwellClosure

namespace Hqiv

open BigOperators

noncomputable section

/--
Minimal chart-level hypotheses for promoting the current Maxwell-like O-equation.

`PromotedOMaxwellAlgebraicSlotHypotheses` identifies the action-side `φ_val + 1` slot
with the algebra-first Maxwell projection slot, while
`PromotedOMaxwellGradientHypotheses` matches the placeholder `grad_phi` used by
`Action`/`CovariantSolution` to the continuum chart gradient used by
`ContinuumOmaxwellClosure`. `PromotedOMaxwellProjectionToPhiOfT` is the optional second
step that recovers the old shell-based `phi_of_T (T ν.val)` presentation.
-/
structure PromotedOMaxwellAlgebraicSlotHypotheses (φ_val : ℝ) (ν : Fin 4) : Prop where
  algebraic_slot_eq : φ_val + 1 = algebraicMaxwellProjectionSlot ν.val

structure PromotedOMaxwellGradientHypotheses (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (ν : Fin 4) : Prop where
  grad_slot_eq : grad_phi ν = Hqiv.Geometry.coordsGradientComponents φF c ν

structure PromotedOMaxwellProjectionToPhiOfT (ν : Fin 4) : Prop where
  slot_eq_phi_of_T : algebraicMaxwellProjectionSlot ν.val = phi_of_T (T ν.val)

structure PromotedOMaxwellChartHypotheses (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (ν : Fin 4) : Prop
    extends PromotedOMaxwellAlgebraicSlotHypotheses φ_val ν,
      PromotedOMaxwellGradientHypotheses φF c ν

/--
Promoted O-Maxwell residual on a chosen chart.

This uses the operator slot already present in `CovariantSolution`, specialized to the
flat identity-metric surrogate so it still matches the action-side chart operator while
keeping the algebra-first Maxwell coupling slot from `ModifiedMaxwell` in the
electromagnetic leg `a = 0`.
-/
noncomputable def promotedOMaxwellResidual (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) : ℝ :=
  covariant_div_F_O (fun b μ ρ => F_from_A A b μ ρ) 1 identityMetric4 a ν
    - 4 * Real.pi * J_src a ν
    - (if a = 0 then
        alpha * algebraicMaxwellCouplingLog ν *
          Hqiv.Geometry.coordsGradientComponents φF c ν
      else 0)

theorem promotedOMaxwellResidual_eq (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) :
    promotedOMaxwellResidual J_src A φF c a ν =
      covariant_div_F_O (fun b μ ρ => F_from_A A b μ ρ) 1 identityMetric4 a ν
        - 4 * Real.pi * J_src a ν
        - (if a = 0 then
            alpha * algebraicMaxwellCouplingLog ν *
              Hqiv.Geometry.coordsGradientComponents φF c ν
          else 0) := by
  rfl

theorem promotedOMaxwellResidual_eq_legacyShellProjected (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) (hφ : PromotedOMaxwellProjectionToPhiOfT ν) :
    promotedOMaxwellResidual J_src A φF c a ν =
      covariant_div_F_O (fun b μ ρ => F_from_A A b μ ρ) 1 identityMetric4 a ν
        - 4 * Real.pi * J_src a ν
        - (if a = 0 then
            alpha * Real.log (phi_of_T (T ν.val)) *
              Hqiv.Geometry.coordsGradientComponents φF c ν
          else 0) := by
  rw [promotedOMaxwellResidual_eq]
  simp_rw [algebraicMaxwellCouplingLog_eq_phi_of_T ν ⟨hφ.slot_eq_phi_of_T⟩]

/-- Promotion theorem to the chart-level Euler–Lagrange residual. -/
theorem promotedOMaxwellResidual_eq_EL_coordsField (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : PromotedOMaxwellAlgebraicSlotHypotheses φ_val ν) :
    promotedOMaxwellResidual J_src A φF c a ν =
      Hqiv.Physics.EL_O_general_coordsField J_src A φ_val φF c a ν := by
  unfold promotedOMaxwellResidual Hqiv.Physics.EL_O_general_coordsField
  rw [covariant_div_F_O_identityMetric]
  rw [show algebraicMaxwellCouplingLog ν = Real.log (φ_val + 1) by
    unfold algebraicMaxwellCouplingLog
    rw [← hφ.algebraic_slot_eq]]

theorem promotedOMaxwellResidual_zero_iff_EL_coordsField_zero (J_src : Fin 8 → Fin 4 → ℝ)
    (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : PromotedOMaxwellAlgebraicSlotHypotheses φ_val ν) :
    promotedOMaxwellResidual J_src A φF c a ν = 0 ↔
      Hqiv.Physics.EL_O_general_coordsField J_src A φ_val φF c a ν = 0 := by
  rw [promotedOMaxwellResidual_eq_EL_coordsField J_src A φ_val φF c a ν hφ]

/-- Promotion theorem to the explicit metric-data residual under the chart hypotheses. -/
theorem promotedOMaxwellResidual_eq_covariantResidual (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : PromotedOMaxwellAlgebraicSlotHypotheses φ_val ν)
    (hgrad : PromotedOMaxwellGradientHypotheses φF c ν) :
    promotedOMaxwellResidual J_O A φF c a ν =
      covariant_O_Maxwell_residual_withMetric (fun b μ ρ => F_from_A A b μ ρ) 1
        identityMetric4 φ_val a ν := by
  unfold promotedOMaxwellResidual covariant_O_Maxwell_residual_withMetric covariant_div_F_O
  rw [show algebraicMaxwellCouplingLog ν = Real.log (φ_val + 1) by
    unfold algebraicMaxwellCouplingLog
    rw [← hφ.algebraic_slot_eq], hgrad.grad_slot_eq]

theorem promotedOMaxwellResidual_zero_iff_covariantResidual_zero (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (φF : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : PromotedOMaxwellAlgebraicSlotHypotheses φ_val ν)
    (hgrad : PromotedOMaxwellGradientHypotheses φF c ν) :
    promotedOMaxwellResidual J_O A φF c a ν = 0 ↔
      covariant_O_Maxwell_residual_withMetric (fun b μ ρ => F_from_A A b μ ρ) 1
        identityMetric4 φ_val a ν = 0 := by
  rw [promotedOMaxwellResidual_eq_covariantResidual A φ_val φF c a ν hφ hgrad]

/--
If the kinetic slot vanishes in the electromagnetic channel, the promoted residual
reduces to the continuum chart version of the current emergent O-Maxwell RHS.
-/
theorem promotedOMaxwellResidual_EM_eq_emergent_coordsField_of_zero_kinetic
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φF : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) (ν : Fin 4)
    (hkin : ∑ μ : Fin 4, F_from_A A 0 μ ν = 0) :
    promotedOMaxwellResidual J_src A φF c 0 ν =
      Hqiv.Physics.emergentMaxwellInhomogeneous_O_coordsField J_src φF c 0 ν := by
  unfold promotedOMaxwellResidual Hqiv.Physics.emergentMaxwellInhomogeneous_O_coordsField
  rw [covariant_div_F_O_identityMetric]
  simp [hkin]

/--
H/quaternionic corollary recovered from the promoted equation in the same flat,
constant-φ regime already used by `ModifiedMaxwell`.

This keeps the H/classic-Maxwell statement as a downstream corollary rather than the
primary validation case for the promoted residual.
-/
theorem promotedOMaxwellResidual_H_eq_classic_under_flat_limit (r : ℝ) (c : Fin 4 → ℝ)
    (ν : Fin 4) (h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff) :
    promotedOMaxwellResidual J_O A_O (fun _ : Fin 4 → ℝ => r) c 0 ν =
      classicMaxwellInhomogeneous ν := by
  calc
    promotedOMaxwellResidual J_O A_O (fun _ : Fin 4 → ℝ => r) c 0 ν
        = Hqiv.Physics.emergentMaxwellInhomogeneous_O_coordsField J_O (fun _ : Fin 4 → ℝ => r) c 0 ν := by
            apply promotedOMaxwellResidual_EM_eq_emergent_coordsField_of_zero_kinetic
            simp [A_O, F_from_A]
    _ = emergentMaxwellInhomogeneous_O_general J_O 0 ν := by
          exact Hqiv.Physics.emergent_coordsField_const_eq_general J_O r c 0 ν
            (grad_φ_zero_when_phi_of_T_constant h_phi_const)
    _ = emergentMaxwellInHomogeneous_H ν := by
          rfl
    _ = classicMaxwellInhomogeneous ν := by
          exact O_reduces_to_classic_Maxwell_in_H ν g_rr_flat h_phi_const
            (grad_φ_zero_when_phi_of_T_constant h_phi_const)

end

end Hqiv
