import Hqiv.Physics.HQIVHeatFlowDeformation
import Hqiv.Physics.ThermodynamicLawsFromLadder
import Hqiv.Story.S3OrbitVsPointwiseGap

/-!
# Heat-flow arrow: vaporization, no backprojection, and the λ-lock

The de Bruijn–Newman picture (Rodgers–Tao: `Λ ≥ 0`, so RH ⟺ `Λ = 0`) reads as a
heat flow that *vaporizes* off-line zeros forward in time; RH holds exactly when
the present-day function sits at the vaporization front, i.e. **no backprojection**
(no backward flow margin: `Λ ≤ 0`).

This module pollinates that picture with the HQIV ingredients that are already
proved, and names the remaining gap faithfully:

* **Dilation slot bookkeeping.** In the conformal closure
  `so(4) ⊕ D ⊕ P₄ ⊕ K₄ = so(4,2)` (`6 + 1 + 4 + 4 = 15`), the deformation time
  `τ` of the heat flow occupies the **one-dimensional dilation slot `D`**;
  backprojection is negative dilation.  The chain `so(4) ⊂ so(4,2) ⊂ so(8)`
  (`6 ≤ 15 ≤ 28`) is the same carrier escalation as the projection story.

* **Forward/backward dichotomy (proved).**  Forward flow (`τ ≥ 0`) is a
  contraction on every shell (`hqivHeatKernelWeight ≤ 1`, summability preserved —
  `HQIVHeatFlowDeformation`).  Backward flow (`τ < 0`) is a strict expansion
  (`> 1` off the horizon shell) that is **unbounded along the temperature
  ladder** (`backprojection_weight_unbounded`): the discrete carrier cannot host
  a backward heat semigroup.

* **Second law forbids backprojection (proved).**  The proven entropy-production
  positivity (`secondLaw_entropyProduction_nonneg`) makes the arrow-induced
  deformation parameter nonnegative, so the physical flow only ever moves
  *toward* vaporization (`arrow_forbids_backprojection`).

* **λ-lock reduction (proved, analogue level).**  Exactly as Rodgers–Tao reduces
  RH from `Λ = 0` to `Λ ≤ 0`, the ladder bundle's `lambdaHQIV_nonneg` reduces
  the zero-lock to the no-backprojection inequality:
  `lambdaHQIV = 0 ↔ lambdaHQIV ≤ 0`.

* **Honest gap.**  `lambdaHQIV` is an HQIV analogue, not the classical `Λ_dBN`.
  The localization payload `VaporizationForcesCriticalLine` is named as a `Prop`
  and proved **equivalent to RH** — the identification of the discrete ladder
  flow with the classical `ξ` heat flow is the genuine analytic frontier, not
  smuggled in.
-/

namespace Hqiv.Story

open Hqiv.Physics

noncomputable section

/-! ## Dilation-slot bookkeeping: `so(4) ⊂ so(4,2) ⊂ so(8)` -/

/-- Dimension of `so(n)` (signature-blind: `so(p,q)` has the same dimension for `p+q=n`). -/
def soAlgebraDim (n : ℕ) : ℕ := n * (n - 1) / 2

theorem soAlgebraDim_so4 : soAlgebraDim 4 = 6 := by decide

theorem soAlgebraDim_so42 : soAlgebraDim 6 = 15 := by decide

theorem soAlgebraDim_so8 : soAlgebraDim 8 = 28 := by decide

/--
Conformal decomposition count: `so(4,2) = so(4) ⊕ D ⊕ P₄ ⊕ K₄` with the
**one-dimensional dilation slot `D`** carrying the heat-flow deformation time
`τ`.  Backprojection is negative dilation in this slot.
-/
theorem conformal_dilation_slot_count :
    soAlgebraDim 6 = soAlgebraDim 4 + 4 + 4 + 1 := by decide

/-- Carrier escalation `so(4) ⊂ so(4,2) ⊂ so(8)` at the dimension level. -/
theorem so4_so42_so8_dim_chain :
    soAlgebraDim 4 ≤ soAlgebraDim 6 ∧ soAlgebraDim 6 ≤ soAlgebraDim 8 := by decide

/-! ## Backprojection dichotomy on the temperature ladder -/

/--
**Backprojection expands.**  Backward deformation (`τ < 0`) strictly amplifies
every off-horizon shell weight: the discrete heat factor exceeds `1`.
-/
theorem backprojection_weight_gt_one {τ T_ref : ℝ} (hτ : τ < 0) (hT : 0 < T_ref)
    {m : ℕ} (hm : m ≠ 0) :
    1 < hqivHeatKernelWeight τ T_ref m := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hu : 0 < tHQIV T_ref m := by
    rw [tHQIV, if_neg hm]
    exact div_pos hmpos hT
  have hx : 0 < -τ * tHQIV T_ref m := mul_pos (neg_pos.mpr hτ) hu
  have : Real.exp 0 < Real.exp (-τ * tHQIV T_ref m) := Real.exp_lt_exp.mpr hx
  simpa [hqivHeatKernelWeight, discreteHeatKernelWeight] using this

/--
**Backprojection blows up along the ladder.**  For any backward deformation
(`τ < 0`) the shell weights are unbounded: no constant dominates the backward
flow on the discrete carrier.  Contrast `hqivHeatKernelWeight_le_one` for
`τ ≥ 0` — the forward flow is a contraction on every shell.
-/
theorem backprojection_weight_unbounded {τ T_ref : ℝ} (hτ : τ < 0) (hT : 0 < T_ref)
    (C : ℝ) :
    ∃ m : ℕ, C < hqivHeatKernelWeight τ T_ref m := by
  have hτpos : 0 < -τ := neg_pos.mpr hτ
  obtain ⟨n, hn⟩ := exists_nat_gt (C * T_ref / (-τ))
  have h1 : C * T_ref < (n : ℝ) * (-τ) := (div_lt_iff₀ hτpos).mp hn
  refine ⟨n + 1, ?_⟩
  have ht : tHQIV T_ref (n + 1) = ((n : ℝ) + 1) / T_ref := by
    rw [tHQIV, if_neg (Nat.succ_ne_zero n)]
    push_cast
    ring
  have hweight : hqivHeatKernelWeight τ T_ref (n + 1) =
      Real.exp (-τ * (((n : ℝ) + 1) / T_ref)) := by
    rw [hqivHeatKernelWeight, discreteHeatKernelWeight, ht]
  have he : C < -τ * (((n : ℝ) + 1) / T_ref) := by
    rw [show -τ * (((n : ℝ) + 1) / T_ref) = (-τ * ((n : ℝ) + 1)) / T_ref by ring,
      lt_div_iff₀ hT]
    nlinarith
  calc C < -τ * (((n : ℝ) + 1) / T_ref) := he
    _ < -τ * (((n : ℝ) + 1) / T_ref) + 1 := by linarith
    _ ≤ Real.exp (-τ * (((n : ℝ) + 1) / T_ref)) := Real.add_one_le_exp _
    _ = hqivHeatKernelWeight τ T_ref (n + 1) := hweight.symm

/--
**Backprojection grows shell by shell.**  Backward weights are strictly
increasing along the ladder off the horizon shell.
-/
theorem backprojection_weight_strict_growth {τ T_ref : ℝ} (hτ : τ < 0) (hT : 0 < T_ref)
    {m : ℕ} (hm : m ≠ 0) :
    hqivHeatKernelWeight τ T_ref m < hqivHeatKernelWeight τ T_ref (m + 1) := by
  have hτpos : 0 < -τ := neg_pos.mpr hτ
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have htm : tHQIV T_ref m = (m : ℝ) / T_ref := by rw [tHQIV, if_neg hm]
  have htm1 : tHQIV T_ref (m + 1) = ((m : ℝ) + 1) / T_ref := by
    rw [tHQIV, if_neg (Nat.succ_ne_zero m)]
    push_cast
    ring
  have hexp : -τ * tHQIV T_ref m < -τ * tHQIV T_ref (m + 1) := by
    rw [htm, htm1]
    have hlt : (m : ℝ) / T_ref < ((m : ℝ) + 1) / T_ref := by
      gcongr
      linarith
    nlinarith
  simpa [hqivHeatKernelWeight, discreteHeatKernelWeight] using Real.exp_lt_exp.mpr hexp

/-! ## The thermodynamic arrow forbids backprojection -/

/--
The arrow-induced deformation parameter: the proven entropy-production proxy of
the toy heat graph plays the role of the dilation-slot time `τ`.
-/
def arrowDeformationCycle3 (u : Fin 3 → ℝ) : ℝ :=
  entropyProductionCycle3 u

/-- Second law: the arrow-induced deformation is nonnegative. -/
theorem arrowDeformationCycle3_nonneg (u : Fin 3 → ℝ) :
    0 ≤ arrowDeformationCycle3 u :=
  secondLaw_entropyProduction_nonneg u

/--
**The arrow forbids backprojection.**  The proven second law means the physical
deformation parameter can never be negative: the discrete flow only ever moves
*toward* vaporization, never backward.
-/
theorem arrow_forbids_backprojection (u : Fin 3 → ℝ) :
    ¬ arrowDeformationCycle3 u < 0 :=
  not_lt.mpr (arrowDeformationCycle3_nonneg u)

/-- The arrow-induced heat weight is a contraction on every shell. -/
theorem arrow_weight_contractive (u : Fin 3 → ℝ) (T_ref : ℝ) (m : ℕ) (hT : 0 < T_ref) :
    hqivHeatKernelWeight (arrowDeformationCycle3 u) T_ref m ≤ 1 :=
  hqivHeatKernelWeight_le_one _ T_ref m (arrowDeformationCycle3_nonneg u) hT

/-! ## λ-lock: the Rodgers–Tao reduction shape -/

/--
**Zero-lock ⇔ no backprojection.**  The ladder bundle carries
`lambdaHQIV_nonneg` — the analogue of the Rodgers–Tao inequality `Λ ≥ 0`.
Exactly as that inequality reduces RH (`Λ = 0`) to the no-backprojection bound
(`Λ ≤ 0`), the analogue zero-lock is equivalent to the one-sided inequality.
-/
theorem lambdaHQIV_zero_iff_no_backprojection (B : TempLadderForcesLambdaHQIVZero) :
    B.lambdaHQIV = 0 ↔ B.lambdaHQIV ≤ 0 :=
  ⟨le_of_eq, fun h => le_antisymm h B.lambdaHQIV_nonneg⟩

/-! ## Honest RH packaging -/

/--
The vaporization localization payload, named as a `Prop`.  The intended content:
the present-day function sits exactly at the vaporization front (no
backprojection margin), so every nontrivial zero is on the critical line.
-/
def VaporizationForcesCriticalLine : Prop :=
  AllNontrivialZerosOnLine

/--
**Honesty theorem.**  The vaporization localization payload is *equivalent to
RH*.  Constructing it — e.g. by identifying the discrete ladder flow with the
classical `ξ` heat flow and importing `Λ_dBN = 0` — *is* proving RH; it is the
faithful frontier, not hidden.
-/
theorem vaporization_iff_RiemannHypothesis :
    VaporizationForcesCriticalLine ↔ RiemannHypothesis :=
  allNontrivialZerosOnLine_iff_RiemannHypothesis

/--
Heat-flow vaporization bridge: the proven λ-lock side (ladder bundle plus its
redistribution/regularization hypotheses) together with the localization
payload.  The first three fields are dischargeable today
(`vaporizationBridge_of_concrete_witness`); the last is exactly RH.
-/
structure HeatFlowVaporizationBridge where
  ladder : TempLadderForcesLambdaHQIVZero
  conserved : ladder.data.conservedRedistribution
  regularized : ladder.data.regularizedBoundary
  vaporization : VaporizationForcesCriticalLine

/-- The bridge's λ-analogue locks to zero (proved side). -/
theorem lambda_zero_of_vaporizationBridge (B : HeatFlowVaporizationBridge) :
    B.ladder.lambdaHQIV = 0 :=
  B.ladder.lambdaHQIV_eq_zero B.conserved B.regularized

/-- The bridge yields Mathlib's `RiemannHypothesis` (via the payload field). -/
theorem RiemannHypothesis_of_vaporizationBridge (B : HeatFlowVaporizationBridge) :
    RiemannHypothesis :=
  vaporization_iff_RiemannHypothesis.mp B.vaporization

/--
A concrete finite-window ladder witness discharges everything in the bridge
**except** the localization payload: the remaining obligation is exactly RH.
-/
def vaporizationBridge_of_concrete_witness
    (W : TempLadderFiniteWindowConcrete)
    (hV : VaporizationForcesCriticalLine) : HeatFlowVaporizationBridge where
  ladder := W.toLambdaHQIVZero
  conserved := W.toFiniteWindowWitness_conserved
  regularized := W.toFiniteWindowWitness_regularized
  vaporization := hV

/--
**Frontier identification.**  Given any concrete ladder witness, the bridge is
inhabited *iff* RH holds: the λ-lock side is free, and the vaporization payload
is the entire remaining content.
-/
theorem vaporizationBridge_iff_RiemannHypothesis
    (W : TempLadderFiniteWindowConcrete) :
    Nonempty HeatFlowVaporizationBridge ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨B⟩
    exact RiemannHypothesis_of_vaporizationBridge B
  · intro hRH
    exact ⟨vaporizationBridge_of_concrete_witness W
      (vaporization_iff_RiemannHypothesis.mpr hRH)⟩

end

end Hqiv.Story
