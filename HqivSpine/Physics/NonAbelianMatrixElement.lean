import HqivSpine.Physics.Binding
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.TrappedCasimir
import HqivSpine.Physics.Forces
import HqivSpine.Physics.ForceCarrier
import HqivSpine.Algebra.StrongColorSu3
import HqivSpine.Algebra.StrongColorSu3LieLaw
import HqivSpine.Algebra.StrongColorEmbed
import HqivSpine.Foundation.Carrier

/-!
# `HqivSpine.Physics.NonAbelianMatrixElement` — matrix-element pipeline from abelian kinetic + colour filter

Non-abelian strong-sector matrix elements are **not** an independent gluon-exchange sector. They
factor as:

* **abelian kinetic slot** — the shell running coupling `α_eff(m)` (O-Maxwell / lattice spine);
* **colour-chart filter** — the derived Casimir ratio `C_A/C_F = 9/4` at `N_c = 3`;
* **network emission weight** — `w_k · bindingCouplingAtShell(m,k)` (trapped Casimir × trace selection);
* optional **carrier envelope** — the S2 force-carrier amplitude from `ForceCarrier`.

The `su(3)` Lie algebra chart (`StrongColorSu3` + `StrongColorSu3LieLaw`) supplies the
eight-generator `f^{abc}` closure; this module supplies the **phenomenological readout pipeline**
that turns abelian kinetic strength into non-abelian emission weights.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NonAbelianMatrixElement

open HqivSpine.Foundation
open HqivSpine.Algebra.StrongColor
open HqivSpine.Physics.ForceCarrier

/-! ## Colour filter (derived `C_A/C_F`) -/

/-- **Colour-chart filter:** adjoint/fundamental Casimir ratio at `N_c = 3`. -/
noncomputable def colourChartFilter : ℝ :=
  casimirAdjoint / casimirFundamental colourCount

theorem colourChartFilter_eq_nine_quarters :
    colourChartFilter = (9 : ℝ) / 4 :=
  casimir_ratio_nine_quarters

theorem colourChartFilter_pos : 0 < colourChartFilter := by
  rw [colourChartFilter_eq_nine_quarters]; norm_num

/-! ## Abelian kinetic slot -/

/-- **Abelian kinetic slot** at shell `m`: the running effective coupling. -/
noncomputable def abelianKineticSlot (m : ℕ) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c

/-! ## Generator emission weights (network binding cells) -/

/-- **Single-generator emission weight** at shell `m` (one strong-channel deposit). -/
noncomputable def generatorEmissionWeight (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ := 1) : ℝ :=
  w k * bindingCouplingAtShell m k c

theorem generatorEmissionWeight_eq_network_cell (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ) :
    generatorEmissionWeight m w k c =
      w k * (latticeSimplexCount m : ℝ) * alphaEffAtShell m c := by
  unfold generatorEmissionWeight bindingCouplingAtShell
  ring

theorem E_bind_from_network_eq_sum_generatorEmissionWeight (m : ℕ) (w : NetworkWeight) (c : ℝ) :
    E_bind_from_network m w c = ∑ k : So8Index, generatorEmissionWeight m w k c := by
  unfold E_bind_from_network generatorEmissionWeight
  rfl

theorem generatorEmissionWeight_eq_trapped_factorisation (m : ℕ) (w : NetworkWeight) (k : So8Index)
    (c : ℝ) :
    generatorEmissionWeight m w k c =
      w k * trappedCasimirEnergy m / 4 * normalizedSelection m c := by
  unfold generatorEmissionWeight
  rw [bindingCouplingAtShell_eq_trappedEnergy_quarter_normalizedSelection]
  ring

/-! ## Non-abelian matrix-element factor -/

/-- **Non-abelian matrix-element factor** = abelian kinetic × colour filter. -/
noncomputable def matrixElementFactor (m : ℕ) (c : ℝ := 1) : ℝ :=
  abelianKineticSlot m c * colourChartFilter

theorem matrixElementFactor_eq_alpha_times_nine_quarters (m : ℕ) (c : ℝ) :
    matrixElementFactor m c = alphaEffAtShell m c * ((9 : ℝ) / 4) := by
  unfold matrixElementFactor abelianKineticSlot colourChartFilter
  rw [casimir_ratio_nine_quarters]

/-- **Full non-abelian matrix element** on generator `k` with network weight `w`. -/
noncomputable def nonAbelianMatrixElement (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ := 1) : ℝ :=
  generatorEmissionWeight m w k c * colourChartFilter

theorem nonAbelianMatrixElement_eq_emission_times_filter (m : ℕ) (w : NetworkWeight) (k : So8Index)
    (c : ℝ) :
    nonAbelianMatrixElement m w k c =
      generatorEmissionWeight m w k c * colourChartFilter := rfl

theorem nonAbelianMatrixElement_eq_abelian_factorisation (m : ℕ) (w : NetworkWeight) (k : So8Index)
    (c : ℝ) :
    nonAbelianMatrixElement m w k c =
      w k * bindingCouplingAtShell m k c * (casimirAdjoint / casimirFundamental colourCount) := by
  unfold nonAbelianMatrixElement generatorEmissionWeight colourChartFilter
  ring_nf

/-! ## Carrier-dressed pipeline -/

/-- **Dressed matrix element:** S2 carrier envelope × non-abelian matrix element. -/
noncomputable def dressedMatrixElement (step span p : ℝ) (m : ℕ) (w : NetworkWeight) (k : So8Index)
    (n src j : ℕ) (c : ℝ := 1) : ℝ :=
  carrierAmplitude step span p n src j * nonAbelianMatrixElement m w k c

/-! ## Strong-channel mask (four octonion directions) -/

theorem strongChannelFraction_eq_half : (strongComponents.card : ℝ) / 8 = (1 : ℝ) / 2 := by
  rw [strongComponents_card]; norm_num

/-! ## Sequential emission (parton-shower scaffold) -/

/-- Product weight after `s` sequential emission steps on generator `k`. -/
noncomputable def sequentialEmissionWeight (m : ℕ) (w : NetworkWeight) (k : So8Index) (s : ℕ)
    (c : ℝ := 1) : ℝ :=
  (nonAbelianMatrixElement m w k c) ^ s

theorem sequentialEmissionWeight_zero (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ) :
    sequentialEmissionWeight m w k 0 c = 1 := by
  unfold sequentialEmissionWeight; simp

theorem sequentialEmissionWeight_succ (m : ℕ) (w : NetworkWeight) (k : So8Index) (s : ℕ) (c : ℝ) :
    sequentialEmissionWeight m w k (s + 1) c =
      sequentialEmissionWeight m w k s c * nonAbelianMatrixElement m w k c := by
  unfold sequentialEmissionWeight; ring

/-! ## PETRA structural lemma (emission steps beyond dipole) -/

/-- Minimum strong-channel emission steps beyond a back-to-back dipole for `n` visible axes. -/
def minStrongEmissionStepsBeyondDipole (nVisibleAxes : ℕ) : ℕ :=
  if nVisibleAxes ≤ 2 then 0 else nVisibleAxes - 2

theorem minStrongEmissionStepsBeyondDipole_three : minStrongEmissionStepsBeyondDipole 3 = 1 := rfl

theorem petraThreeJet_requires_emissionStep :
    minStrongEmissionStepsBeyondDipole 3 = 1 :=
  minStrongEmissionStepsBeyondDipole_three

/-! ## Standard one-loop QCD β witness at `N_c = 3`, `n_f = 6` -/

/-- Standard one-loop `β₀` coefficient at `N_c = 3`, `n_f = 6`. -/
noncomputable def qcdBeta0OneLoop : ℝ :=
  -(11 : ℝ) / 3 * (colourCount : ℝ) + (2 : ℝ) / 3 * 6

theorem qcdBeta0OneLoop_eq_neg_seven : qcdBeta0OneLoop = -7 := by
  rw [qcdBeta0OneLoop, colourCount_eq_three]; norm_num

/-! ## Discharged bundle -/

structure nonAbelianMatrixElementDischarged : Prop where
  colour_filter : colourChartFilter = (9 : ℝ) / 4
  bind_is_sum_emission :
    ∀ (m : ℕ) (w : NetworkWeight) (c : ℝ),
      E_bind_from_network m w c = ∑ k : So8Index, generatorEmissionWeight m w k c
  su3_lie_law :
    ∀ a b : Fin 8,
      lieBracketMat3 (halfGellMannFull a) (halfGellMannFull b) =
        Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • halfGellMannFull c
  petra_threeJet : minStrongEmissionStepsBeyondDipole 3 = 1
  beta0_standard : qcdBeta0OneLoop = -7
  carrier_embed :
    ∀ a b : Fin 8,
      lieBracketMat8 (colorGellMannEmbed (halfGellMannFull a))
          (colorGellMannEmbed (halfGellMannFull b)) =
        Complex.I • ∑ c : Fin 8, (su3fStructure a b c : ℂ) • colorGellMannEmbed (halfGellMannFull c)

theorem nonAbelianMatrixElementDischarged_holds : nonAbelianMatrixElementDischarged where
  colour_filter := colourChartFilter_eq_nine_quarters
  bind_is_sum_emission := E_bind_from_network_eq_sum_generatorEmissionWeight
  su3_lie_law := halfGellMannFull_lieBracket_eq_I_smul_f_sum
  petra_threeJet := petraThreeJet_requires_emissionStep
  beta0_standard := qcdBeta0OneLoop_eq_neg_seven
  carrier_embed := halfGellMannEmbed_carrier_lieBracket_eq_I_smul_f_sum

end HqivSpine.Physics.NonAbelianMatrixElement
