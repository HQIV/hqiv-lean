import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.CasimirClosureAction
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.JointClosureAction` — coupled shell `m` and emission `ξ` closure

The remaining exploratory item — coupled `(v, ξ)` / `(v, m)` carrier dynamics — closes at the
**scalar slow-manifold** level: sector budget (`ClosureAction`) and inner/outer Casimir balance
(`CasimirClosureAction`) share the **same** unique minimum and the **same** gradient flow as
`lockInDrive`.

* **joint potential** `V_joint(m) = V_closure(m) + V_Casimir(m)`;
* **unique zero** at `m = referenceM` only (`jointClosurePotential_eq_zero_iff`);
* **gradient flow** matches `shellGradientDrive`, `casimirGradientDrive`, and `lockInDrive`;
* **emission chart** `ξ_lock = xiOfShell referenceM` at the joint minimum.

Full fast octonion carrier dynamics on `S⁷` remain in `scripts/hqiv_hopf_delta_action.py` /
`scripts/hqiv_joint_closure_action.py`; no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open ContinuousHorizon
open NowSliceFromLattice

/-! ## Joint budget potential -/

/-- **Joint closure potential** — sector budget plus Casimir balance. -/
noncomputable def jointClosurePotential (m : ℕ) : ℝ :=
  closureBudgetPotential m + casimirBudgetPotential m

theorem jointClosurePotential_nonneg (m : ℕ) : 0 ≤ jointClosurePotential m := by
  unfold jointClosurePotential
  exact add_nonneg (closureBudgetPotential_nonneg m) (casimirBudgetPotential_nonneg m)

theorem jointClosurePotential_eq_zero_iff (m : ℕ) :
    jointClosurePotential m = 0 ↔ m = referenceM := by
  constructor
  · intro h
    unfold jointClosurePotential at h
    have hc := closureBudgetPotential_nonneg m
    have hcas := casimirBudgetPotential_nonneg m
    have hclosure : closureBudgetPotential m = 0 := by linarith
    exact (closureBudgetPotential_eq_zero_iff m).mp hclosure
  · rintro rfl
    unfold jointClosurePotential
    have h1 := (closureBudgetPotential_eq_zero_iff referenceM).mpr rfl
    have h2 := (casimirBudgetPotential_eq_zero_iff referenceM).mpr rfl
    rw [h1, h2]; ring

theorem jointClosurePotential_referenceM :
    jointClosurePotential referenceM = 0 := by
  exact (jointClosurePotential_eq_zero_iff referenceM).mpr rfl

/-! ## Joint gradient flow aligns with lock-in -/

theorem shellGradientDrive_eq_casimirGradientDrive_outward (m : ℕ) :
    shellGradientDrive m = .outward ↔ casimirGradientDrive m = .outward := by
  rw [shellGradientDrive_eq_outward_iff, casimirGradientDrive_eq_outward_iff]

theorem shellGradientDrive_eq_casimirGradientDrive_inward (m : ℕ) :
    shellGradientDrive m = .inward ↔ casimirGradientDrive m = .inward := by
  rw [shellGradientDrive_eq_inward_iff, casimirGradientDrive_eq_inward_iff]

theorem shellGradientDrive_eq_casimirGradientDrive_neutral (m : ℕ) :
    shellGradientDrive m = .neutral ↔ casimirGradientDrive m = .neutral := by
  rw [shellGradientDrive_eq_neutral_iff, casimirGradientDrive_eq_neutral_iff]

/-! ## Capstone -/

structure JointClosureActionClosure where
  /-- Joint potential vanishes iff `m = referenceM`. -/
  potential_unique_min : ∀ m, jointClosurePotential m = 0 ↔ m = referenceM
  /-- Shell and Casimir gradient drives are parallel at every shell. -/
  gradient_agreement :
    (∀ m, shellGradientDrive m = .outward ↔ casimirGradientDrive m = .outward) ∧
    (∀ m, shellGradientDrive m = .inward ↔ casimirGradientDrive m = .inward) ∧
    (∀ m, shellGradientDrive m = .neutral ↔ casimirGradientDrive m = .neutral)
  /-- Sector and Casimir capstones remain available. -/
  closure : ReferenceMClosureAction
  casimir : ReferenceMCasimirClosureAction
  /-- Emission coordinate at lock-in. -/
  xi_lock : xiOfShell referenceM = xiLockin

noncomputable def jointClosureAction : JointClosureActionClosure where
  potential_unique_min := jointClosurePotential_eq_zero_iff
  gradient_agreement :=
    ⟨shellGradientDrive_eq_casimirGradientDrive_outward,
      ⟨shellGradientDrive_eq_casimirGradientDrive_inward,
        shellGradientDrive_eq_casimirGradientDrive_neutral⟩⟩
  closure := referenceMClosureAction
  casimir := referenceMCasimirClosureAction
  xi_lock := by unfold xiLockin; rfl

structure ReferenceMJointClosureAction where
  joint : JointClosureActionClosure

noncomputable def referenceMJointClosureAction : ReferenceMJointClosureAction where
  joint := jointClosureAction

end HqivSpine.Physics
