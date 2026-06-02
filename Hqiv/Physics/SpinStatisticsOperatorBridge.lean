import Hqiv.Physics.SpinStatistics
import Hqiv.QuantumMechanics.PatchIntervalMaxSmeared

namespace Hqiv.Physics

open Hqiv.QM

open scoped InnerProductSpace

noncomputable section

/-- Weight concentrated on the primary patch pair carried by a pair of HQIV modes. -/
def hqivModePairWeight (m₁ m₂ : HQIVMode) : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    if i = hqivModePrimaryPatch m₁ ∧ j = hqivModePrimaryPatch m₂ then 1 else 0

/-- Interval-max operator attached to the primary patch pair of two HQIV modes. -/
noncomputable def hqivModePairObservableOp (m₁ m₂ : HQIVMode) :
    LatticeHilbert 2 →ₗ[ℂ] LatticeHilbert 2 :=
  smearedOpIntervalMax patchEventChartFour (hqivModePairWeight m₁ m₂)

/-- The interval-max commutator of the mode-pair observable with `σ_y`. -/
noncomputable def hqivModePairObservableCommutatorY (m₁ m₂ : HQIVMode) :
    LatticeHilbert 2 →ₗ[ℂ] LatticeHilbert 2 :=
  opCommutator (hqivModePairObservableOp m₁ m₂) (Matrix.toEuclideanLin pauliY_comm)

/-- Nonzero weight forces the support to be the primary patch pair of the two HQIV modes. -/
theorem hqivModePairWeight_ne_zero_iff {m₁ m₂ : HQIVMode} {i j : Fin 4} :
    hqivModePairWeight m₁ m₂ i j ≠ 0 ↔
      i = hqivModePrimaryPatch m₁ ∧ j = hqivModePrimaryPatch m₂ := by
  unfold hqivModePairWeight
  by_cases h : i = hqivModePrimaryPatch m₁ ∧ j = hqivModePrimaryPatch m₂
  · simp [h]
  · simp [h]

/-- The triality-style observable always lands in the bosonic carrier and records shell/patch support. -/
theorem hqivTrialityObservable_support_data (m₁ m₂ : HQIVMode) :
    ∃ b : HQIVBosonMode,
      hqivTrialityObservable m₁ m₂ = Sum.inr b ∧
      b.shell = Nat.min (hqivModeShell m₁) (hqivModeShell m₂) ∧
      b.leftPatch = hqivModePrimaryPatch m₁ ∧
      b.rightPatch = hqivModePrimaryPatch m₂ := by
  cases m₁ <;> cases m₂ <;>
    refine ⟨_, rfl, rfl, rfl, rfl⟩

/-- If two HQIV modes are spacelike, the operator supported on their patch pair vanishes. -/
theorem hqivModePairObservableOp_eq_zero_of_spacelike {m₁ m₂ : HQIVMode}
    (hsp : hqivModeSpacelikeSep m₁ m₂) :
    hqivModePairObservableOp m₁ m₂ = 0 := by
  refine smearedOpIntervalMax_eq_zero_of_spacelike_support patchEventChartFour
    (hqivModePairWeight m₁ m₂) ?_
  intro i j hij
  have hsupp : i = hqivModePrimaryPatch m₁ ∧ j = hqivModePrimaryPatch m₂ :=
    (hqivModePairWeight_ne_zero_iff).mp hij
  rcases hsp with ⟨_, hpatch⟩
  dsimp [spacelikeRelationMinkowski]
  rw [patchEventChartFour_lt_four i.val i.is_lt, patchEventChartFour_lt_four j.val j.is_lt]
  rcases hsupp with ⟨rfl, rfl⟩
  simpa using hpatch

/-- The corresponding interval-max commutator with `σ_y` also vanishes on spacelike HQIV pairs. -/
theorem hqivModePairObservableCommutatorY_eq_zero_of_spacelike {m₁ m₂ : HQIVMode}
    (hsp : hqivModeSpacelikeSep m₁ m₂) :
    hqivModePairObservableCommutatorY m₁ m₂ = 0 := by
  refine opCommutator_smearedOpIntervalMax_pauliY_eq_zero_of_spacelike_support patchEventChartFour
    (hqivModePairWeight m₁ m₂) ?_
  intro i j hij
  have hsupp : i = hqivModePrimaryPatch m₁ ∧ j = hqivModePrimaryPatch m₂ :=
    (hqivModePairWeight_ne_zero_iff).mp hij
  rcases hsp with ⟨_, hpatch⟩
  dsimp [spacelikeRelationMinkowski]
  rw [patchEventChartFour_lt_four i.val i.is_lt, patchEventChartFour_lt_four j.val j.is_lt]
  rcases hsupp with ⟨rfl, rfl⟩
  simpa using hpatch

/-- Concrete fermionic witness: same-shell spatially separated HQIV fermion pairs induce zero operator. -/
theorem sampleFermionMode_pairObservable_zero (m : ℕ) {i j : Fin 4}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    hqivModePairObservableOp (sampleFermionMode m i) (sampleFermionMode m j) = 0 := by
  exact hqivModePairObservableOp_eq_zero_of_spacelike
    (hqivModeSpacelikeSep_same_shell_spatial hi hj hij)

/-- The associated Pauli commutator also vanishes on the same-shell spatial witness. -/
theorem sampleFermionMode_pairObservableCommutatorY_zero (m : ℕ) {i j : Fin 4}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    hqivModePairObservableCommutatorY (sampleFermionMode m i) (sampleFermionMode m j) = 0 := by
  exact hqivModePairObservableCommutatorY_eq_zero_of_spacelike
    (hqivModeSpacelikeSep_same_shell_spatial hi hj hij)

end

end Hqiv.Physics
