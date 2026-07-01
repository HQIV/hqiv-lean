import HqivSpine.Foundation.ThreeGrowth
import Mathlib.Data.Real.Basic

/-!
# `HqivSpine.Physics.ColorCasimir` — colour Casimirs from the `N_c = 3` chart

The colour count on the carrier's colour chart is `N_c = transverseDim = 3`: the
three transverse directions are the three colour states, not an externally chosen
gauge rank. From that single integer the textbook colour Casimirs follow as pure
arithmetic:

* **adjoint** `C_A = N_c = 3`;
* **fundamental** `C_F = (N_c² − 1)/(2 N_c) = 4/3`;
* **ratio** `C_A / C_F = 9/4` — the non-abelian soft-splitting weight, here a
  derived consequence of `N_c = 3` rather than an input.

These are the colour-algebra labels the gluon-curvature note proves at theorem
level; they sit on the same carrier whose strong sector is the four channels of
`Forces`, with no propagating gluon field introduced.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Colour count** `N_c = transverseDim = 3`: the three transverse directions. -/
def colourCount : ℕ := transverseDim

theorem colourCount_eq_three : colourCount = 3 := rfl

/-- **Adjoint colour Casimir** `C_A = N_c`. -/
noncomputable def casimirAdjoint : ℝ := (colourCount : ℝ)

/-- **Fundamental colour Casimir** `C_F = (N_c² − 1)/(2 N_c)`. -/
noncomputable def casimirFundamental (Nc : ℕ) : ℝ :=
  ((Nc : ℝ) ^ 2 - 1) / (2 * (Nc : ℝ))

theorem casimirAdjoint_eq_three : casimirAdjoint = 3 := by
  unfold casimirAdjoint; rw [colourCount_eq_three]; norm_num

theorem casimirFundamental_three : casimirFundamental 3 = (4 : ℝ) / 3 := by
  unfold casimirFundamental; norm_num

theorem casimirFundamental_pos : 0 < casimirFundamental colourCount := by
  rw [colourCount_eq_three, casimirFundamental_three]; norm_num

/-- **Non-abelian splitting ratio** `C_A / C_F = 9/4` at `N_c = 3` — derived, not fit. -/
theorem casimir_ratio_nine_quarters :
    casimirAdjoint / casimirFundamental colourCount = (9 : ℝ) / 4 := by
  rw [casimirAdjoint_eq_three, colourCount_eq_three, casimirFundamental_three]; norm_num

/-! ## Quark electric charge quantization from loop multiplicity over colour rank -/

/-- The two residual charge channels of a colour-composed (quark) rung. -/
inductive ResidualChargeChannel
  | upLike
  | downLike
  deriving DecidableEq, Repr

/-- **Loop quanta** carried by each residual channel: up-like `+2`, down-like `−1`. -/
def quarkLoopMultiplicity : ResidualChargeChannel → ℤ
  | .upLike => 2
  | .downLike => -1

/-- Up-like carries exactly double the down-like magnitude (and opposite sign). -/
theorem upLike_double_downLike_magnitude :
    quarkLoopMultiplicity .upLike = -2 * quarkLoopMultiplicity .downLike := by decide

/-- **Quark electric charge** = loop multiplicity over the colour rank `N_c = 3`. The
familiar `2/3` and `−1/3` are forced once the colour denominator is `3`. -/
noncomputable def quarkElectricCharge (ch : ResidualChargeChannel) : ℚ :=
  (quarkLoopMultiplicity ch : ℚ) / (colourCount : ℚ)

theorem quarkElectricCharge_up : quarkElectricCharge .upLike = 2 / 3 := by
  unfold quarkElectricCharge quarkLoopMultiplicity; rw [colourCount_eq_three]; norm_num

theorem quarkElectricCharge_down : quarkElectricCharge .downLike = -1 / 3 := by
  unfold quarkElectricCharge quarkLoopMultiplicity; rw [colourCount_eq_three]; norm_num

/-- The up-like charge is `−2 ×` the down-like charge (`2/3 = −2·(−1/3)`). -/
theorem upLike_charge_double_downLike :
    quarkElectricCharge .upLike = -2 * quarkElectricCharge .downLike := by
  rw [quarkElectricCharge_up, quarkElectricCharge_down]; norm_num

end HqivSpine.Physics
