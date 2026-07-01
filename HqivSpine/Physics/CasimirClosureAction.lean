import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.TrappedCasimir
import HqivSpine.Physics.NeutrinoCurvatureSuppression
import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.NowSliceFromLattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.CasimirClosureAction` — dynamic inner/outer Casimir pins `ξ_lock = 5`

The open item in `LockInMechanism` — dynamic emergence of `ξ_lock = referenceM + 1` — closes
here as the **unique minimum** of an inner/outer Casimir budget built only from spine objects:

* **inner (trapped T12):** `trappedCasimirEnergy m = availableModes(m)·φ(m)/2`
  (`TrappedCasimir`);
* **outer (T13 plate):** `outerHorizonArea m / γ = S(m)/γ` with `S(m)=latticeSimplexCount m`
  (`NeutrinoCurvatureSuppression` — the chargeless outer horizon, not a fit);
* **balance ratio** `inner·ξ·γ/S(m) = 8(m+1)²/5`, which equals the sector capacity `C=40`
  **only** at `m = referenceM`;
* **emission chart** `ξ = m+1` (`ContinuousHorizon.xiOfShell`) then gives `ξ_lock = 5`, matching
  blackbody horizon emission (`horizonCount`, `proton_emission_count`) and lock-in lapse
  (`lockin_massUnit_eq_xiLockin`).

No spring toward `5`: the restoring law is the Euler–Lagrange slope of the Casimir budget
potential, parallel to `ClosureAction` for shell `4`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation
open HqivSpine.Physics.NeutrinoCurvatureSuppression
open ContinuousHorizon
open NowSliceFromLattice

/-! ## Inner/outer Casimir balance ratio -/

/-- **Outer Casimir plate scale** `S(m)/γ`: outer-horizon area over the monogamy complement. -/
noncomputable def outerCasimirPlate (m : ℕ) : ℝ :=
  outerHorizonArea m / gammaHQIV

theorem outerCasimirPlate_pos (m : ℕ) : 0 < outerCasimirPlate m := by
  unfold outerCasimirPlate
  exact div_pos (outerHorizonArea_pos m) (by rw [gammaHQIV_eq]; norm_num)

/-- **Dynamic inner/outer Casimir balance ratio** at shell `m`
(`inner·ξ·γ/S` with `ξ = m+1`). -/
noncomputable def casimirBalanceRatio (m : ℕ) : ℝ :=
  trappedCasimirEnergy m * xiOfShell m * gammaHQIV / outerHorizonArea m

theorem casimirBalanceRatio_eq_trapped_times_gamma_over_area (m : ℕ) :
    casimirBalanceRatio m =
      trappedCasimirEnergy m * xiOfShell m * gammaHQIV / outerHorizonArea m := rfl

private theorem trappedCasimirEnergy_mul_xi_div_outerHorizonArea (m : ℕ) :
    trappedCasimirEnergy m * xiOfShell m / outerHorizonArea m =
      (4 : ℝ) * ((m : ℝ) + 1) ^ 2 := by
  have hden : (shellNumer m : ℝ) ≠ 0 := by
    unfold shellNumer; push_cast; positivity
  unfold trappedCasimirEnergy availableModes outerHorizonArea xiOfShell
  rw [latticeSimplexCount_eq_shellNumer]
  unfold shellNumer
  simp only [casimirPerMode]
  rw [show (phi m : ℝ) / 2 = (m : ℝ) + 1 from by unfold phi; push_cast; ring]
  push_cast
  field_simp [hden]

/-- Closed form: `8(m+1)²/5 = carrierMultiplicity·γ·(m+1)²/2`. -/
theorem casimirBalanceRatio_eq (m : ℕ) :
    casimirBalanceRatio m = (8 : ℝ) * ((m : ℝ) + 1) ^ 2 / 5 := by
  unfold casimirBalanceRatio
  have h := trappedCasimirEnergy_mul_xi_div_outerHorizonArea m
  calc
    trappedCasimirEnergy m * xiOfShell m * gammaHQIV / outerHorizonArea m
        = (trappedCasimirEnergy m * xiOfShell m / outerHorizonArea m) * gammaHQIV := by ring
    _ = (4 : ℝ) * ((m : ℝ) + 1) ^ 2 * gammaHQIV := by rw [h]
    _ = (8 : ℝ) * ((m : ℝ) + 1) ^ 2 / 5 := by rw [gammaHQIV_eq]; ring

theorem casimirBalanceRatio_pos (m : ℕ) : 0 < casimirBalanceRatio m := by
  rw [casimirBalanceRatio_eq]
  positivity

/-- **At lock-in the inner/outer balance equals sector capacity** `C = 40`. -/
theorem casimirBalanceRatio_referenceM :
    casimirBalanceRatio referenceM = (sectorClosureCapacity : ℝ) := by
  rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty]
  norm_num [referenceM]

/-- **Unique shell where trapped/outer Casimir balance closes the sector budget.** -/
theorem casimirBalanceRatio_eq_capacity_iff (m : ℕ) :
    casimirBalanceRatio m = (sectorClosureCapacity : ℝ) ↔ m = referenceM := by
  rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty]
  constructor
  · intro h
    have hsqrt : (m : ℝ) + 1 = 5 := by nlinarith
    have hm : m + 1 = 5 := by exact_mod_cast hsqrt
    unfold referenceM at hm ⊢
    omega
  · intro hm
    subst hm
    norm_num [referenceM]

/-! ## Casimir budget potential (variational closure on the shell ladder) -/

/-- Signed Casimir **surplus** `inner·γ/S − C`. -/
noncomputable def casimirBudgetMismatch (m : ℕ) : ℝ :=
  casimirBalanceRatio m - (sectorClosureCapacity : ℝ)

theorem casimirBudgetMismatch_eq_zero_iff (m : ℕ) :
    casimirBudgetMismatch m = 0 ↔ m = referenceM := by
  unfold casimirBudgetMismatch
  constructor
  · intro h
    exact (casimirBalanceRatio_eq_capacity_iff m).mp (eq_of_sub_eq_zero h)
  · intro hm
    subst hm
    simp [casimirBudgetMismatch, casimirBalanceRatio_referenceM, sectorClosureCapacity_eq_forty]

/-- **Casimir budget potential** `V_C(m) = (inner·γ/S − C)²/(2C)`. -/
noncomputable def casimirBudgetPotential (m : ℕ) : ℝ :=
  (casimirBudgetMismatch m) ^ 2 / (2 * (sectorClosureCapacity : ℝ))

theorem casimirBudgetPotential_nonneg (m : ℕ) : 0 ≤ casimirBudgetPotential m := by
  unfold casimirBudgetPotential
  apply div_nonneg (sq_nonneg _) (by norm_num [sectorClosureCapacity_eq_forty])

theorem casimirBudgetPotential_eq_zero_iff (m : ℕ) :
    casimirBudgetPotential m = 0 ↔ m = referenceM := by
  constructor
  · intro h
    unfold casimirBudgetPotential at h
    have hC : (0 : ℝ) < 2 * (sectorClosureCapacity : ℝ) := by
      rw [sectorClosureCapacity_eq_forty]; norm_num
    rw [div_eq_zero_iff] at h
    rcases h with hnum | hden
    · rcases sq_eq_zero_iff.mp hnum with h0
      exact (casimirBudgetMismatch_eq_zero_iff m).mp h0
    · linarith
  · intro hm
    subst hm
    unfold casimirBudgetPotential casimirBudgetMismatch
    rw [casimirBalanceRatio_referenceM, sub_self, zero_pow two_ne_zero, zero_div]

/-- **Analytic Casimir gradient** `∂V_C/∂m = 16(m+1)/5 · mismatch/C` at integer shells. -/
noncomputable def casimirBudgetGradient (m : ℕ) : ℝ :=
  (16 : ℝ) * ((m : ℝ) + 1) / 5 * casimirBudgetMismatch m /
    (sectorClosureCapacity : ℝ)

theorem casimirBudgetGradient_eq_zero_iff (m : ℕ) :
    casimirBudgetGradient m = 0 ↔ m = referenceM := by
  rw [casimirBudgetGradient]
  constructor
  · intro h
    by_cases hm : m = referenceM
    · exact hm
    · have hpos : (0 : ℝ) < (16 : ℝ) * ((m : ℝ) + 1) / 5 := by
        have : (0 : ℝ) < (m : ℝ) + 1 := by exact_mod_cast Nat.succ_pos m
        positivity
      have hC : (sectorClosureCapacity : ℝ) ≠ 0 := by
        rw [sectorClosureCapacity_eq_forty]; norm_num
      have hmis : casimirBudgetMismatch m ≠ 0 := by
        intro h0
        exact hm ((casimirBudgetMismatch_eq_zero_iff m).mp h0)
      field_simp [hC] at h
      have h0 : casimirBudgetMismatch m = 0 := by nlinarith [hmis, hpos]
      exact absurd ((casimirBudgetMismatch_eq_zero_iff m).mp h0) hm
  · intro hm
    subst hm
    simp [casimirBudgetMismatch, casimirBalanceRatio_referenceM, sectorClosureCapacity_eq_forty]

/-! ## Gradient flow matches sector closure (parallel to `ClosureAction`) -/

/-- Direction of overdamped Casimir gradient flow on the shell ladder. -/
inductive CasimirGradientDrive
  | outward
  | neutral
  | inward
  deriving DecidableEq, Repr

theorem casimirBudgetMismatch_neg_iff (m : ℕ) :
    casimirBudgetMismatch m < 0 ↔ m < referenceM := by
  unfold casimirBudgetMismatch
  constructor
  · intro h
    rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty] at h
    have hlt : (m : ℝ) + 1 < 5 := by nlinarith
    have hm : m < 4 := (Nat.succ_lt_succ_iff).mp (by exact_mod_cast hlt)
    rwa [show referenceM = 4 from rfl]
  · intro hlt
    rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty]
    have : (m : ℝ) + 1 < 5 := by
      rw [show referenceM = 4 from rfl] at hlt
      exact_mod_cast (Nat.succ_lt_succ hlt)
    nlinarith

theorem casimirBudgetMismatch_pos_iff (m : ℕ) :
    0 < casimirBudgetMismatch m ↔ referenceM < m := by
  unfold casimirBudgetMismatch
  constructor
  · intro h
    rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty] at h
    have _ : (5 : ℝ) < (m : ℝ) + 1 := by nlinarith
    have hm : (4 : ℝ) < (m : ℝ) := by linarith
    rw [show referenceM = 4 from rfl]
    exact_mod_cast hm
  · intro hgt
    rw [casimirBalanceRatio_eq, sectorClosureCapacity_eq_forty]
    have : (5 : ℝ) < (m : ℝ) + 1 := by
      rw [show referenceM = 4 from rfl] at hgt
      exact_mod_cast ((Nat.lt_succ_iff).mpr (Nat.succ_le_of_lt hgt))
    nlinarith

noncomputable def casimirGradientDrive (m : ℕ) : CasimirGradientDrive :=
  if casimirBudgetMismatch m < 0 then .outward
  else if 0 < casimirBudgetMismatch m then .inward
  else .neutral

theorem casimirGradientDrive_eq_outward {m : ℕ} (h : m < referenceM) :
    casimirGradientDrive m = .outward := by
  unfold casimirGradientDrive
  simp only [(casimirBudgetMismatch_neg_iff m).mpr h, ite_true]

theorem casimirGradientDrive_eq_inward {m : ℕ} (h : referenceM < m) :
    casimirGradientDrive m = .inward := by
  unfold casimirGradientDrive
  split_ifs with hneg hpos
  · linarith [(casimirBudgetMismatch_neg_iff m).mp hneg, h]
  · rfl
  · have h0 : casimirBudgetMismatch m = 0 := by linarith
    linarith [(casimirBudgetMismatch_eq_zero_iff m).mp h0, h]

theorem casimirGradientDrive_eq_neutral {m : ℕ} (h : m = referenceM) :
    casimirGradientDrive m = .neutral := by
  subst h
  unfold casimirGradientDrive
  simp [casimirBudgetMismatch, casimirBalanceRatio_referenceM, sectorClosureCapacity_eq_forty]

theorem casimirGradientDrive_eq_outward_iff (m : ℕ) :
    casimirGradientDrive m = .outward ↔ m < referenceM := by
  constructor
  · intro hdrive
    by_cases h : m < referenceM
    · exact h
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with heq | hgt
      · rw [casimirGradientDrive_eq_neutral heq.symm] at hdrive
        cases hdrive
      · rw [casimirGradientDrive_eq_inward hgt] at hdrive
        cases hdrive
  · intro h
    exact casimirGradientDrive_eq_outward h

theorem casimirGradientDrive_eq_inward_iff (m : ℕ) :
    casimirGradientDrive m = .inward ↔ referenceM < m := by
  constructor
  · intro hdrive
    by_cases h : referenceM < m
    · exact h
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt h) with heq | hlt
      · rw [casimirGradientDrive_eq_neutral heq] at hdrive
        cases hdrive
      · rw [casimirGradientDrive_eq_outward hlt] at hdrive
        cases hdrive
  · intro h
    exact casimirGradientDrive_eq_inward h

theorem casimirGradientDrive_eq_neutral_iff (m : ℕ) :
    casimirGradientDrive m = .neutral ↔ m = referenceM := by
  constructor
  · intro hdrive
    by_cases h : m = referenceM
    · exact h
    · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
      · rw [casimirGradientDrive_eq_outward hlt] at hdrive
        cases hdrive
      · rw [casimirGradientDrive_eq_inward hgt] at hdrive
        cases hdrive
  · intro h
    exact casimirGradientDrive_eq_neutral h

theorem casimirGradientDrive_eq_lockInDrive (m : ℕ) :
    (casimirGradientDrive m = .outward ↔ lockInDrive m = .outward) ∧
    (casimirGradientDrive m = .inward ↔ lockInDrive m = .inward) ∧
    (casimirGradientDrive m = .neutral ↔ lockInDrive m = .neutral) :=
  ⟨(casimirGradientDrive_eq_outward_iff m).trans (lockInDrive_outward_iff m).symm,
    ⟨(casimirGradientDrive_eq_inward_iff m).trans (lockInDrive_inward_iff m).symm,
      (casimirGradientDrive_eq_neutral_iff m).trans (lockInDrive_neutral_iff m).symm⟩⟩

/-! ## Emission chart: `ξ_lock = m+1 = 5` -/

theorem emissionHorizon_eq_xiOfShell (m : ℕ) :
    (m + 1 : ℝ) = xiOfShell m := by
  unfold xiOfShell; rfl

theorem xiOfShell_eq_xiLockin_iff (m : ℕ) :
    xiOfShell m = xiLockin ↔ m = referenceM := by
  rw [xiLockin, ← emissionHorizon_eq_xiOfShell m, ← emissionHorizon_eq_xiOfShell referenceM]
  constructor
  · intro h
    have hm : m + 1 = referenceM + 1 := by exact_mod_cast h
    omega
  · intro hm; subst hm; rfl

theorem casimirBudgetPotential_eq_zero_iff_xiLockin (m : ℕ) :
    casimirBudgetPotential m = 0 ↔ xiOfShell m = xiLockin := by
  rw [casimirBudgetPotential_eq_zero_iff, xiOfShell_eq_xiLockin_iff]

theorem proton_emission_count_eq_xiLockin :
    (referenceM + 1 : ℝ) = xiLockin := by
  unfold xiLockin
  exact emissionHorizon_eq_xiOfShell referenceM

theorem lockin_massUnit_eq_xiLockin :
    lockinNowSlice.massUnit = xiLockin := by
  rw [lockinNowSlice_massUnit, xiLockin_eq_five]

theorem lockin_massUnit_eq_horizon_emission :
    lockinNowSlice.massUnit = (referenceM + 1 : ℝ) := by
  rw [lockinNowSlice_massUnit, referenceM_add_one_eq_five]

/-! ## Capstone -/

/-- The proved **dynamic Casimir closure** bundle. -/
structure CasimirClosureActionClosure where
  /-- Inner/outer balance equals `C` iff `m = referenceM`. -/
  balance_unique : ∀ m, casimirBalanceRatio m = (sectorClosureCapacity : ℝ) ↔ m = referenceM
  /-- Casimir budget potential vanishes iff `m = referenceM`. -/
  potential_unique_min : ∀ m, casimirBudgetPotential m = 0 ↔ m = referenceM
  /-- Casimir gradient flow matches `lockInDrive`. -/
  gradient_matches_lock_in :
    (∀ m, casimirGradientDrive m = .outward ↔ lockInDrive m = .outward) ∧
    (∀ m, casimirGradientDrive m = .inward ↔ lockInDrive m = .inward) ∧
    (∀ m, casimirGradientDrive m = .neutral ↔ lockInDrive m = .neutral)
  /-- Emission chart: `ξ_lock` is the horizon count at lock-in. -/
  xi_lock_emission : (referenceM + 1 : ℝ) = xiLockin
  /-- Lock-in lapse equals emission horizon coordinate. -/
  mass_unit_eq_xi : lockinNowSlice.massUnit = xiLockin
  /-- Sector closure at `4` and Casimir balance at `5` are the same lock-in. -/
  closure_casimir_parallel :
    closureBudgetPotential referenceM = 0 ∧
      casimirBudgetPotential referenceM = 0 ∧
      xiOfShell referenceM = xiLockin

def casimirClosureAction : CasimirClosureActionClosure where
  balance_unique := casimirBalanceRatio_eq_capacity_iff
  potential_unique_min := casimirBudgetPotential_eq_zero_iff
  gradient_matches_lock_in :=
    ⟨fun m => (casimirGradientDrive_eq_lockInDrive m).1,
      fun m => (casimirGradientDrive_eq_lockInDrive m).2.1,
      fun m => (casimirGradientDrive_eq_lockInDrive m).2.2⟩
  xi_lock_emission := proton_emission_count_eq_xiLockin
  mass_unit_eq_xi := lockin_massUnit_eq_xiLockin
  closure_casimir_parallel :=
    ⟨(closureBudgetPotential_eq_zero_iff referenceM).mpr rfl,
      (casimirBudgetPotential_eq_zero_iff referenceM).mpr rfl,
      by unfold xiLockin; rfl⟩

/-- **Sector closure + dynamic Casimir + emission chart** at lock-in. -/
structure ReferenceMCasimirClosureAction where
  closure : ReferenceMClosureAction
  casimir : CasimirClosureActionClosure

noncomputable def referenceMCasimirClosureAction : ReferenceMCasimirClosureAction where
  closure := referenceMClosureAction
  casimir := casimirClosureAction

end HqivSpine.Physics
