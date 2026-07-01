import HqivSpine.Physics.Shell

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `HqivSpine.Physics.AlphaRunning` — the GUT coupling and its shell running

The unification coupling is a foundation number: `1/α_GUT = 42 = 6 · 7 = 6 · imaginaryDim`.
From it the effective coupling runs along the shell ladder via the `log φ(m)` form
already in `Shell`. We record the GUT tie and the monotone running of the inverse
coupling.

## What "the fine-structure constant" means here

HQIV derives the **naked, high-scale** coupling — the value read off at the
**electroweak shell** `referenceM + 1`, "naked on the W". Its closed form is

`1/α_eff(EW, c) = 42 · (1 + c·(3/5)·log 13)`,

an `O(1/128)` number set entirely by foundation integers (`42`, `α = 3/5`) and the
shell `log` argument `φ(referenceM+1)+1 = 13`. The familiar low-energy `1/137`
(Thomson / hydrogen) is the **screened** value after vacuum polarisation; it is
*not* a spine target and is never chased on hydrogen — low-energy/screened-α
phenomenology lives in a separate chemistry/spectroscopy comparison layer, outside
this spine. Both the screened `1/137` and any precise high-scale decimal are
quarantined as comparison numbers in `Frontiers`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Inverse GUT coupling** `1/α_GUT = 42`, equal to the bare shell coupling. -/
noncomputable def alphaGUTinv : ℝ := oneOverAlphaBare

theorem alphaGUTinv_eq_42 : alphaGUTinv = 42 := rfl

/-- `1/α_GUT = 6 · imaginaryDim = 6 · 7`: the unification coupling is set by the
seven imaginary directions. -/
theorem alphaGUTinv_eq_six_mul_imaginaryDim : alphaGUTinv = 6 * (imaginaryDim : ℝ) :=
  oneOverAlphaBare_eq_six_mul_imaginaryDim

/-- **GUT coupling** `α_GUT = 1/42`. -/
noncomputable def alphaGUT : ℝ := alphaGUTinv⁻¹

theorem alphaGUT_eq : alphaGUT = (42 : ℝ)⁻¹ := by rw [alphaGUT, alphaGUTinv_eq_42]

/-- At zero running coefficient the inverse effective coupling is exactly the GUT
value: the ladder starts at unification. -/
theorem oneOverAlphaEff_at_zero_coupling (m : ℕ) :
    oneOverAlphaEffAtShell m 0 = alphaGUTinv := by
  simp [oneOverAlphaEffAtShell, alphaGUTinv, oneOverAlphaBare]

/-- **The inverse effective coupling runs above the GUT value** for positive
running coefficient `c` and any shell (the `log φ(m)` term is nonnegative). -/
theorem oneOverAlphaEff_ge_GUT (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    alphaGUTinv ≤ oneOverAlphaEffAtShell m c := by
  unfold oneOverAlphaEffAtShell alphaGUTinv oneOverAlphaBare
  have hphi : (1 : ℝ) ≤ (phi m : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (phi m); linarith
  have hlog : 0 ≤ Real.log ((phi m : ℝ) + 1) := Real.log_nonneg hphi
  have hα : (0 : ℝ) ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  have hterm : 0 ≤ c * alphaEM * Real.log ((phi m : ℝ) + 1) := by positivity
  nlinarith [hterm]

/-! ## The naked, high-scale coupling at the electroweak shell -/

/-- **Electroweak shell** = one step outward from lock-in, `referenceM + 1 = 5`. -/
def electroweakShell : ℕ := referenceM + 1

theorem electroweakShell_eq_five : electroweakShell = 5 := rfl

/-- **Naked (high-scale) inverse coupling** read off at the electroweak shell —
"naked on the W". This is the HQIV fine-structure constant target, *not* the
screened `1/137`. -/
noncomputable def oneOverAlphaNakedW (c : ℝ := 1) : ℝ :=
  oneOverAlphaEffAtShell electroweakShell c

/-- **Closed form of the naked-W coupling:** `42·(1 + c·(3/5)·log 13)`, every factor a
foundation number (`42 = 1/α_GUT`, `3/5 = α`, log argument `φ(5)+1 = 13`). -/
theorem oneOverAlphaNakedW_closed_form (c : ℝ) :
    oneOverAlphaNakedW c = 42 * (1 + c * (3 / 5) * Real.log 13) := by
  unfold oneOverAlphaNakedW oneOverAlphaEffAtShell oneOverAlphaBare
  rw [show phi electroweakShell = 12 from rfl, alphaEM_eq]
  norm_num

/-- The naked-W coupling sits strictly above unification for any positive running
coefficient (`log 13 > 0`): the ladder has genuinely run out from `1/α_GUT = 42`. -/
theorem oneOverAlphaNakedW_gt_GUT {c : ℝ} (hc : 0 < c) :
    alphaGUTinv < oneOverAlphaNakedW c := by
  rw [oneOverAlphaNakedW_closed_form, alphaGUTinv_eq_42]
  have hlog : 0 < Real.log 13 := Real.log_pos (by norm_num)
  nlinarith [hlog, hc]

end HqivSpine.Physics
