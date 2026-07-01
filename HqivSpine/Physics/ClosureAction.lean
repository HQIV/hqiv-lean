import HqivSpine.Physics.LockIn
import HqivSpine.Physics.LockInMechanism
import HqivSpine.Physics.Shell
import HqivSpine.Algebra.Closure
import HqivSpine.Foundation.HopfLadder
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.ClosureAction` — variational shell lock-in from the closure budget

The last *freeish* parameter on the spine — why `referenceM = 4` — is discharged as the
**unique minimum** of a closure-budget potential built only from proved spine counts:

* unlocked modes `N(m) = 8(m+1)` (`LockIn.newModes`);
* sector capacity `C = dim 𝔰𝔬(8) + carrier + base = 40` (`LockIn.sectorClosureCapacity`);
* **budget potential** `V(m) = (N(m)−C)²/(2C)`;
* **budget gradient** `∂V/∂m = 8(N(m)−C)/C = −8·modeDeficit(m)/C`.

No spring toward `referenceM`, no hand-coded shell drive: the restoring direction is the
Euler–Lagrange slope of `V`. The carrier layer (Hopf fiber–base nonlinearity at the
octonionic rung, phase lift `Δ` with coefficient `φ(m)/6`, `𝔤₂ ∪ {Δ} ⊂ 𝔰𝔬(8)`) supplies
the **fast** octonion dynamics; the shell coordinate is the **slow** closure sector.

**Honest scope:** this module proves the **scalar closure action** and its alignment with
`lockInDrive` / `modeDeficit`. Full coupled `(v, m)` dynamics on `S⁷` remain in the Python
probe (`scripts/hqiv_hopf_delta_action.py`); no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation HqivSpine.Algebra

/-! ## Closure budget potential -/

/-- Signed mode **surplus** `N(m) − C` (negative below lock-in, positive above). -/
noncomputable def budgetMismatch (m : ℕ) : ℝ :=
  (newModes m : ℝ) - (sectorClosureCapacity : ℝ)

theorem budgetMismatch_eq_neg_modeDeficit (m : ℕ) :
    budgetMismatch m = -(modeDeficit m : ℝ) := by
  unfold budgetMismatch modeDeficit newModes sectorClosureCapacity
  push_cast; ring

/-- **Closure-budget potential** `V(m) = (N(m)−C)²/(2C)`. -/
noncomputable def closureBudgetPotential (m : ℕ) : ℝ :=
  (budgetMismatch m) ^ 2 / (2 * (sectorClosureCapacity : ℝ))

theorem closureBudgetPotential_nonneg (m : ℕ) : 0 ≤ closureBudgetPotential m := by
  unfold closureBudgetPotential
  apply div_nonneg (sq_nonneg _) (by norm_num [sectorClosureCapacity_eq_forty])

/-- **Potential vanishes exactly at lock-in** — the unique sector-closure balance. -/
theorem closureBudgetPotential_eq_zero_iff (m : ℕ) :
    closureBudgetPotential m = 0 ↔ m = referenceM := by
  constructor
  · intro h
    unfold closureBudgetPotential at h
    have h0 : budgetMismatch m = 0 := by
      have hC : (0 : ℝ) < 2 * (sectorClosureCapacity : ℝ) := by
        rw [sectorClosureCapacity_eq_forty]; norm_num
      rw [div_eq_zero_iff] at h
      rcases h with hnum | hden
      · rcases sq_eq_zero_iff.mp hnum with h0
        exact h0
      · linarith
    have hN : newModes m = sectorClosureCapacity := by
      simpa [eq_comm] using sub_eq_zero.mp h0
    exact referenceM_unique_balance hN
  · intro hm
    subst hm
    unfold closureBudgetPotential budgetMismatch
    rw [newModes_referenceM, sub_self, zero_pow two_ne_zero, zero_div]

/-- **Analytic budget gradient** `∂V/∂m = 8(N−C)/C`. -/
noncomputable def closureBudgetGradient (m : ℕ) : ℝ :=
  (carrierMultiplicity : ℝ) * budgetMismatch m / (sectorClosureCapacity : ℝ)

theorem closureBudgetGradient_eq (m : ℕ) :
    closureBudgetGradient m =
      (carrierMultiplicity : ℝ) * (budgetMismatch m) / (sectorClosureCapacity : ℝ) := rfl

theorem closureBudgetGradient_eq_neg_eight_modeDeficit (m : ℕ) :
    closureBudgetGradient m =
      -(8 : ℝ) * (modeDeficit m : ℝ) / (sectorClosureCapacity : ℝ) := by
  rw [closureBudgetGradient_eq, budgetMismatch_eq_neg_modeDeficit, carrierMultiplicity_eq_eight]
  ring_nf

theorem closureBudgetGradient_eq_zero_iff (m : ℕ) :
    closureBudgetGradient m = 0 ↔ m = referenceM := by
  rw [closureBudgetGradient_eq_neg_eight_modeDeficit]
  constructor
  · intro h
    have hC : (sectorClosureCapacity : ℝ) ≠ 0 := by
      rw [sectorClosureCapacity_eq_forty]; norm_num
    have hmd : modeDeficit m = 0 := by
      have h0 : (modeDeficit m : ℝ) = 0 := by
        field_simp [hC] at h
        linarith
      exact_mod_cast h0
    exact (modeDeficit_eq_zero_iff m).mp hmd
  · intro hm
    subst hm
    simp [modeDeficit_referenceM, sectorClosureCapacity_eq_forty]

private lemma modeDeficit_cast_pos_iff (m : ℕ) : (0 : ℝ) < (modeDeficit m : ℝ) ↔ 0 < modeDeficit m := by
  simp

private lemma modeDeficit_cast_neg_iff (m : ℕ) : (modeDeficit m : ℝ) < 0 ↔ modeDeficit m < 0 := by
  simp

theorem budgetMismatch_neg_iff (m : ℕ) : budgetMismatch m < 0 ↔ m < referenceM := by
  rw [budgetMismatch_eq_neg_modeDeficit, neg_lt_zero, modeDeficit_cast_pos_iff]
  exact modeDeficit_pos_iff m

theorem budgetMismatch_pos_iff (m : ℕ) : 0 < budgetMismatch m ↔ referenceM < m := by
  rw [budgetMismatch_eq_neg_modeDeficit, neg_pos, modeDeficit_cast_neg_iff]
  exact modeDeficit_neg_iff m

theorem budgetMismatch_eq_zero_iff (m : ℕ) : budgetMismatch m = 0 ↔ m = referenceM := by
  rw [budgetMismatch_eq_neg_modeDeficit, neg_eq_zero, Int.cast_eq_zero]
  exact modeDeficit_eq_zero_iff m

/-! ## Gradient flow aligns with the discrete restoring drive -/

/-- Direction of **overdamped gradient flow** `ṁ ∝ −∂V/∂m` on the shell ladder. -/
inductive ShellGradientDrive
  | outward
  | neutral
  | inward
  deriving DecidableEq, Repr

/-- Gradient-flow drive: overdamped flow on `V` has the same sign as `modeDeficit`. -/
def shellGradientDrive (m : ℕ) : ShellGradientDrive :=
  if 0 < modeDeficit m then .outward
  else if modeDeficit m < 0 then .inward
  else .neutral

theorem shellGradientDrive_eq_lockInDrive (m : ℕ) :
    (shellGradientDrive m = .outward ↔ lockInDrive m = .outward) ∧
    (shellGradientDrive m = .inward ↔ lockInDrive m = .inward) ∧
    (shellGradientDrive m = .neutral ↔ lockInDrive m = .neutral) := by
  unfold shellGradientDrive lockInDrive
  repeat' constructor <;> split_ifs <;> simp

theorem shellGradientDrive_outward_iff_lockIn (m : ℕ) :
    shellGradientDrive m = .outward ↔ lockInDrive m = .outward :=
  (shellGradientDrive_eq_lockInDrive m).1

theorem shellGradientDrive_inward_iff_lockIn (m : ℕ) :
    shellGradientDrive m = .inward ↔ lockInDrive m = .inward :=
  (shellGradientDrive_eq_lockInDrive m).2.1

theorem shellGradientDrive_neutral_iff_lockIn (m : ℕ) :
    shellGradientDrive m = .neutral ↔ lockInDrive m = .neutral :=
  (shellGradientDrive_eq_lockInDrive m).2.2

theorem shellGradientDrive_eq_outward_iff (m : ℕ) :
    shellGradientDrive m = .outward ↔ m < referenceM := by
  rw [shellGradientDrive_outward_iff_lockIn, lockInDrive_outward_iff]

theorem shellGradientDrive_eq_inward_iff (m : ℕ) :
    shellGradientDrive m = .inward ↔ referenceM < m := by
  rw [shellGradientDrive_inward_iff_lockIn, lockInDrive_inward_iff]

theorem shellGradientDrive_eq_neutral_iff (m : ℕ) :
    shellGradientDrive m = .neutral ↔ m = referenceM := by
  rw [shellGradientDrive_neutral_iff_lockIn, lockInDrive_neutral_iff]

/-! ## Carrier layer: Hopf + phase lift (no extra shell pin) -/

/-- Octonionic Hopf index on the Adams ladder (`S⁷ ↪ S¹⁵ → S⁸`). -/
def hopfOctonionIndex : ℕ := 3

/-- Hopf **fiber–base shape** `n/(n+2)` at winding `n`. -/
noncomputable def hopfFibrationShape (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 2)

theorem hopfFibrationShape_pos {n : ℕ} (hn : 0 < n) : 0 < hopfFibrationShape n := by
  unfold hopfFibrationShape
  apply div_pos (Nat.cast_pos.mpr hn)
  have : (0 : ℝ) < (n + 2 : ℝ) := by positivity
  exact this

theorem hopfFibrationShape_one : hopfFibrationShape 1 = (1 : ℝ) / 3 := by
  unfold hopfFibrationShape; norm_num

theorem hopfFibrationShape_two : hopfFibrationShape 2 = (1 : ℝ) / 2 := by
  unfold hopfFibrationShape; norm_num

theorem hopfFibrationShape_three : hopfFibrationShape 3 = (3 : ℝ) / 5 := by
  unfold hopfFibrationShape; norm_num

/-- Lock-in chart shell `n + 1` at the octonionic Hopf winding `n = 3`. -/
def hopfLockinWinding : ℕ := 3

theorem hopfFibrationShape_lockin : hopfFibrationShape hopfLockinWinding = (3 : ℝ) / 5 := by
  rw [hopfLockinWinding, hopfFibrationShape_three]

theorem hopfFibrationShape_lt_one {n : ℕ} (hn : 0 < n) : hopfFibrationShape n < 1 := by
  unfold hopfFibrationShape
  have hden : (0 : ℝ) < (n + 2 : ℝ) := by positivity
  rw [div_lt_one hden]
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

theorem hopfLockin_chartShell : hopfLockinWinding + 1 = referenceM := rfl

theorem hopfLockin_base_eq_carrier :
    hopfBaseDim hopfOctonionIndex = carrierMultiplicity :=
  octonionic_base_eq_carrier

theorem hopfLockin_fiber_eq_imaginary :
    hopfFiberDim hopfOctonionIndex = imaginaryDim :=
  octonionic_fiber_eq_imaginaryDim

/-- **Phase-lift coefficient** `φ(m)/6` on the `(e₁,e₇)` generator `Δ`. -/
noncomputable def phaseLiftCoeff (m : ℕ) : ℝ := (phi m : ℝ) / 6

theorem phaseLiftCoeff_pos (m : ℕ) : 0 < phaseLiftCoeff m := by
  unfold phaseLiftCoeff phi
  positivity

theorem phaseLiftCoeff_referenceM :
    phaseLiftCoeff referenceM = (phi referenceM : ℝ) / 6 := rfl

/-! ## Capstone: closure action discharged -/

/-- The proved **closure action** bundle: budget potential, gradient–deficit identity,
Hopf chart at lock-in, and `Δ ⊂ 𝔰𝔬(8)`. -/
structure ClosureActionClosure where
  /-- `V(m) = 0` iff `m = referenceM`. -/
  budget_unique_min : ∀ m, closureBudgetPotential m = 0 ↔ m = referenceM
  /-- `∂V/∂m = −8·modeDeficit/C`. -/
  gradient_eq_mode_deficit : ∀ m,
    closureBudgetGradient m =
      -(8 : ℝ) * (modeDeficit m : ℝ) / (sectorClosureCapacity : ℝ)
  /-- Overdamped gradient flow matches `lockInDrive` (parallel outward/inward/neutral tests). -/
  gradient_matches_lock_in :
    (∀ m, shellGradientDrive m = .outward ↔ lockInDrive m = .outward) ∧
    (∀ m, shellGradientDrive m = .inward ↔ lockInDrive m = .inward) ∧
    (∀ m, shellGradientDrive m = .neutral ↔ lockInDrive m = .neutral)
  /-- Hopf lock-in chart: winding `3` ⇒ shell `4`. -/
  hopf_chart : hopfLockinWinding + 1 = referenceM
  /-- Phase lift lies in the genuine carrier algebra. -/
  delta_in_so8 : foundationDelta ∈ skewMatrices 8

/-- **The closure action is fully discharged** on the spine. -/
def closureAction : ClosureActionClosure where
  budget_unique_min := closureBudgetPotential_eq_zero_iff
  gradient_eq_mode_deficit := closureBudgetGradient_eq_neg_eight_modeDeficit
  gradient_matches_lock_in :=
    ⟨shellGradientDrive_outward_iff_lockIn, shellGradientDrive_inward_iff_lockIn,
      shellGradientDrive_neutral_iff_lockIn⟩
  hopf_chart := hopfLockin_chartShell
  delta_in_so8 := foundationDelta_mem

/-- **Selector + variational closure:** lock-in mechanism bundled with the budget action. -/
structure ReferenceMClosureAction where
  mechanism : ReferenceMLockInMechanism
  action : ClosureActionClosure

/-- **Lock-in at shell `4` from sector balance *and* the closure action.** -/
noncomputable def referenceMClosureAction : ReferenceMClosureAction where
  mechanism := referenceMLockInMechanism
  action := closureAction

end HqivSpine.Physics
