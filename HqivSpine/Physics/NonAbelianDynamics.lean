import HqivSpine.Physics.LockIn
import HqivSpine.Physics.Forces
import HqivSpine.Physics.ColorCasimir
import HqivSpine.Physics.NonAbelianMatrixElement
import HqivSpine.Physics.PlaquetteCurvature
import HqivSpine.Algebra.Triality
import HqivSpine.Algebra.SkewChartBridgeSu3Closure
import HqivSpine.Algebra.StrongColorEmbed
import HqivSpine.Foundation.ThreeGrowth
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NonAbelianDynamics` — lock-in `4+4` chart and discharged strong sector

The remaining non-abelian frontier item is packaged here using **`m = referenceM = 4` lock-in**
and the **`3+1` base** already in `LockIn.sectorClosureCapacity = dim 𝔰𝔬(8) + carrier + spacetimeDim`:

* at lock-in, **`N(4) = 40 = C`** (`newModes_referenceM`);
* the eight carrier channels split **`4 + 4`**: EM+weak `{0,1,2,3}` and strong `{4,5,6,7}`, each block
  of size **`spacetimeDim = 4`**;
* **`colourCount = generationCount = 3`**: transverse colour rank matches Spin(8) triality order;
* a **lock-in complex structure** `J` on `ℝ⁸` (standard `4+4` block) with `J² = −1`, mapping the gauge
  block onto the strong block — the preferred real slice tying the complex `colorGellMannEmbed` chart
  to the carrier octonion directions;
* **`su(3) ↪ 𝔰𝔬(6) ↪ 𝔰𝔬(8)`**, matrix-element pipeline, plaquette curvature, and carrier Lie embed
  are bundled from existing discharge modules.

Honest scope: the complex structure is the **lock-in block chart** on `Fin 8`, not a full Spin(8)
triality automorphism on 𝔰𝔬(8) or a dynamical QCD Lagrangian.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NonAbelianDynamics

open Matrix
open HqivSpine.Foundation
open HqivSpine.Algebra
open HqivSpine.Algebra.StrongColor
open HqivSpine.Algebra.Su3RealSkew
open HqivSpine.Physics
open HqivSpine.Physics.NonAbelianMatrixElement
open PlaquetteCurvature

/-! ## Lock-in balance at `m = 4` -/

theorem lockin_modes_eq_sector_capacity :
    newModes referenceM = sectorClosureCapacity :=
  newModes_referenceM

/-! ## Carrier `4+4` split aligned with `spacetimeDim` -/

/-- EM + weak channels `{0,1,2,3}` — the gauge block matched to the `3+1` base. -/
def lockinGaugeBlock : Finset (Fin 8) := emComponents ∪ weakComponents

theorem lockinGaugeBlock_eq :
    lockinGaugeBlock = ({0, 1, 2, 3} : Finset (Fin 8)) := by decide

theorem lockinGaugeBlock_card : lockinGaugeBlock.card = 4 := by decide

theorem lockinGaugeBlock_card_eq_spacetimeDim : lockinGaugeBlock.card = spacetimeDim := by
  rw [lockinGaugeBlock_card, spacetimeDim_eq_four]

theorem strong_block_card_eq_spacetimeDim : strongComponents.card = spacetimeDim := by
  rw [strongComponents_card, spacetimeDim_eq_four]

theorem lockin_carrier_4plus4 :
    lockinGaugeBlock.card = strongComponents.card ∧
      lockinGaugeBlock.card = spacetimeDim ∧
        strongComponents.card = spacetimeDim :=
  ⟨rfl, lockinGaugeBlock_card_eq_spacetimeDim, strong_block_card_eq_spacetimeDim⟩

theorem lockin_blocks_partition :
    lockinGaugeBlock ∪ strongComponents = (Finset.univ : Finset (Fin 8)) ∧
      Disjoint lockinGaugeBlock strongComponents := by
  decide

def gaugeSlot (j : Fin 4) : Fin 8 := ⟨j.val, by omega⟩

def strongSlot (j : Fin 4) : Fin 8 := ⟨j.val + 4, by omega⟩

theorem mem_lockinGaugeBlock_gaugeSlot (j : Fin 4) : gaugeSlot j ∈ lockinGaugeBlock := by
  fin_cases j <;> decide

theorem mem_strongComponents_strongSlot (j : Fin 4) : strongSlot j ∈ strongComponents := by
  fin_cases j <;> decide

/-! ## Triality order matches colour rank -/

theorem colourCount_eq_generationCount :
    colourCount = Algebra.generationCount := by
  rw [colourCount_eq_three, Algebra.generationCount_eq_three]

/-! ## Lock-in complex structure on the carrier (`4+4` block) -/

/-- Standard complex structure on `ℝ⁴ ⊕ ℝ⁴`: `J e_j = e_{j+4}`, `J e_{j+4} = −e_j`. -/
def lockinComplexStructure : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j =>
    if hj : j.val < 4 then
      if hi : i.val = j.val + 4 then (1 : ℝ) else 0
    else if hi' : i.val < 4 then
      if hk : j.val = i.val + 4 then (-1 : ℝ) else 0
    else 0

theorem lockinComplexStructure_mulVec_gauge (j : Fin 4) :
    lockinComplexStructure *ᵥ e (gaugeSlot j) = e (strongSlot j) := by
  funext i
  rw [mulVec_e]
  fin_cases j <;> fin_cases i <;>
    simp [lockinComplexStructure, gaugeSlot, strongSlot, Matrix.of_apply, e, Pi.single_apply]

theorem lockinComplexStructure_mulVec_strong (j : Fin 4) :
    lockinComplexStructure *ᵥ e (strongSlot j) = -(e (gaugeSlot j)) := by
  funext i
  rw [mulVec_e, Pi.neg_apply]
  fin_cases j <;> fin_cases i <;>
    simp [lockinComplexStructure, gaugeSlot, strongSlot, Matrix.of_apply, e, Pi.single_apply]

theorem lockinComplexStructure_mem_skew : lockinComplexStructure ∈ skewMatrices 8 := by
  rw [mem_skewMatrices]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lockinComplexStructure, Matrix.of_apply, transpose_apply, neg_apply]

theorem lockinComplexStructure_sq :
    lockinComplexStructure * lockinComplexStructure = (-1 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lockinComplexStructure, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight, smul_apply,
      one_apply, neg_smul, neg_neg]

/-! ## `su(3)` inside `𝔰𝔬(8)` -/

private theorem six_le_eight : (6 : ℕ) ≤ 8 := by decide

theorem su3RealGen_mem_so8 (a : Fin 8) :
    su3RealGenPad 8 six_le_eight a ∈ skewMatrices 8 :=
  su3RealGenPad_mem 8 six_le_eight a

/-! ## Capstone bundle -/

structure NonAbelianDynamicsClosure where
  lockin_balance : newModes referenceM = sectorClosureCapacity
  carrier_4plus4 :
    lockinGaugeBlock.card = strongComponents.card ∧
      lockinGaugeBlock.card = spacetimeDim
  triality_colour : colourCount = Algebra.generationCount
  complex_structure_skew : lockinComplexStructure ∈ skewMatrices 8
  complex_structure_square :
    lockinComplexStructure * lockinComplexStructure = (-1 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)
  complex_structure_gauge_to_strong :
    ∀ j : Fin 4, lockinComplexStructure *ᵥ e (gaugeSlot j) = e (strongSlot j)
  matrix_element : nonAbelianMatrixElementDischarged
  plaquette_curvature : PlaquetteCurvatureDischarged
  carrier_embed : strongColorEmbedDischarged
  su3_real_skew :
    (∀ a, su3RealGen a ∈ skewMatrices 6) ∧
      (∀ a b,
        bracket (su3RealGen a) (su3RealGen b) =
          ∑ c : Fin 8, (-su3fStructure a b c : ℝ) • su3RealGen c)
  su3_in_so8 : ∀ a : Fin 8, su3RealGenPad 8 six_le_eight a ∈ skewMatrices 8

noncomputable def nonAbelianDynamicsClosure : NonAbelianDynamicsClosure where
  lockin_balance := lockin_modes_eq_sector_capacity
  carrier_4plus4 := ⟨rfl, lockinGaugeBlock_card_eq_spacetimeDim⟩
  triality_colour := colourCount_eq_generationCount
  complex_structure_skew := lockinComplexStructure_mem_skew
  complex_structure_square := lockinComplexStructure_sq
  complex_structure_gauge_to_strong := lockinComplexStructure_mulVec_gauge
  matrix_element := nonAbelianMatrixElementDischarged_holds
  plaquette_curvature := plaquetteCurvatureDischarged_holds
  carrier_embed := strongColorEmbedDischarged_holds
  su3_real_skew := su3RealSkewDischarged_holds
  su3_in_so8 := su3RealGen_mem_so8

theorem referenceM_non_abelian_dynamics_closed : Nonempty NonAbelianDynamicsClosure :=
  ⟨nonAbelianDynamicsClosure⟩

end HqivSpine.Physics.NonAbelianDynamics
