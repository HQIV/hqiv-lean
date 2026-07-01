import HqivSpine.Foundation.Carrier
import HqivSpine.Physics.Shell
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.CarrierMonogamySuppression` — chargeless mode on the octonionic carrier

The chargeless neutrino has no inner binding well (`neutrinoTreeMass = 0`). Its residual mass is
the **monogamy complement** `γ = 2/5` spread over the **octonionic carrier closure budget**
`imaginaryDim · carrierMultiplicity = 7 · 8` — the same algebra objects that define the
`so(8)` carrier, not an "outside curvature" shell readout.

  `carrierMonogamySuppression = γ / (imaginaryDim · carrierMultiplicity) = 1/140`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.CarrierMonogamySuppression

open HqivSpine.Foundation
open HqivSpine.Physics

/-! ## Carrier closure budget -/

noncomputable def carrierClosureBudget : ℝ :=
  (imaginaryDim : ℝ) * (carrierMultiplicity : ℝ)

theorem carrierClosureBudget_eq_fifty_six :
    carrierClosureBudget = 56 := by
  unfold carrierClosureBudget
  norm_num [imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]

theorem carrierClosureBudget_pos : 0 < carrierClosureBudget := by
  rw [carrierClosureBudget_eq_fifty_six]
  norm_num

/-! ## Monogamy suppression on the carrier -/

noncomputable def carrierMonogamySuppression : ℝ := gammaHQIV / carrierClosureBudget

theorem carrierMonogamySuppression_pos : 0 < carrierMonogamySuppression := by
  unfold carrierMonogamySuppression
  exact div_pos (by rw [gammaHQIV_eq]; norm_num) carrierClosureBudget_pos

theorem carrierMonogamySuppression_lt_one : carrierMonogamySuppression < 1 := by
  unfold carrierMonogamySuppression carrierClosureBudget
  rw [gammaHQIV_eq, imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]
  norm_num

theorem carrierMonogamySuppression_eq_inv_140 : carrierMonogamySuppression = 1 / 140 := by
  unfold carrierMonogamySuppression carrierClosureBudget
  rw [gammaHQIV_eq, imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]
  norm_num

theorem carrierMonogamySuppression_eq_one_sub_alpha_over_carrier :
    carrierMonogamySuppression =
      (1 - alphaEM) / ((imaginaryDim : ℝ) * (carrierMultiplicity : ℝ)) := by
  rw [carrierMonogamySuppression_eq_inv_140, alphaEM_eq]
  norm_num [imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]

/-! ## Bridge: same number as lattice closure shell, different interpretation -/

theorem latticeSimplexCount_closure_eq_carrierBudget :
    (latticeSimplexCount (referenceM + 2) : ℝ) = carrierClosureBudget := by
  rw [carrierClosureBudget_eq_fifty_six]
  norm_num [latticeSimplexCount, shellNumer, referenceM]

theorem carrierMonogamySuppression_eq_gamma_over_closureShell :
    carrierMonogamySuppression = gammaHQIV / (latticeSimplexCount (referenceM + 2) : ℝ) := by
  unfold carrierMonogamySuppression
  rw [latticeSimplexCount_closure_eq_carrierBudget]

/-! ## Neutrino mass from charged anchor -/

noncomputable def neutrinoAbsoluteMassFromAnchor (mℓ : ℝ) : ℝ :=
  mℓ * carrierMonogamySuppression

theorem neutrinoAbsoluteMassFromAnchor_eq_over_140 (mℓ : ℝ) :
    neutrinoAbsoluteMassFromAnchor mℓ = mℓ / 140 := by
  unfold neutrinoAbsoluteMassFromAnchor
  rw [carrierMonogamySuppression_eq_inv_140]
  field_simp

theorem neutrinoAbsoluteMassFromAnchor_lt_anchor {mℓ : ℝ} (hℓ : 0 < mℓ) :
    0 < neutrinoAbsoluteMassFromAnchor mℓ ∧ neutrinoAbsoluteMassFromAnchor mℓ < mℓ := by
  refine ⟨mul_pos hℓ carrierMonogamySuppression_pos, ?_⟩
  calc neutrinoAbsoluteMassFromAnchor mℓ = mℓ * carrierMonogamySuppression := rfl
    _ < mℓ * 1 := mul_lt_mul_of_pos_left carrierMonogamySuppression_lt_one hℓ
    _ = mℓ := by ring

/-! ## Capstone -/

structure CarrierMonogamySuppressionClosure where
  budget : carrierClosureBudget = 56
  suppression : carrierMonogamySuppression = 1 / 140
  foundational :
    carrierMonogamySuppression =
      (1 - alphaEM) / ((imaginaryDim : ℝ) * (carrierMultiplicity : ℝ))
  lattice_consistency :
    carrierMonogamySuppression = gammaHQIV / (latticeSimplexCount (referenceM + 2) : ℝ)

noncomputable def carrierMonogamySuppressionClosure : CarrierMonogamySuppressionClosure where
  budget := carrierClosureBudget_eq_fifty_six
  suppression := carrierMonogamySuppression_eq_inv_140
  foundational := carrierMonogamySuppression_eq_one_sub_alpha_over_carrier
  lattice_consistency := carrierMonogamySuppression_eq_gamma_over_closureShell

end HqivSpine.Physics.CarrierMonogamySuppression
