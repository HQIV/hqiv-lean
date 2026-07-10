import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.QuantumChemistry.CoupledRelaxation
import Mathlib.Tactic

/-!
# Bond rearrangement paths on the contact graph

A discrete reaction / dissociation path is a finite sequence of contact-edge
gates.  Each step carries a binding depth \(D\) and a coordination excess
\(\delta\) from the break / reform / vacancy stress; the path barrier is the
maximum edge gate (Lean ``discreteSaddleBarrierEv``).

No continuum transition-state search; no fitted Arrhenius prefactor.

Python: ``scripts/hqiv_bond_rearrangement_path.py``,
``scripts/hqiv_discrete_saddle_defect_readout.py`` (GMTKN activation subset).
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics

noncomputable section

/-- Kind of contact-graph rearrangement at one edge. -/
inductive RearrangementKind
  | breakBond
  | reformBond
  | vacancy
  deriving DecidableEq, Repr

/-- One step on a bond-rearrangement path. -/
structure BondRearrangementStep where
  /-- Binding depth of the stressed contact [eV]. -/
  bindingEv : ℝ
  /-- Coordination excess \(\delta\) at the stressed endpoint(s). -/
  deltaCoord : ℝ
  kind : RearrangementKind := .breakBond

/-- Finite path = list of rearrangement steps. -/
abbrev BondRearrangementPath := List BondRearrangementStep

/-- Edge gate for one step (= defect formation on that contact). -/
noncomputable def bondRearrangementStepGate (s : BondRearrangementStep) : ℝ :=
  contactEdgeGateEv s.bindingEv s.deltaCoord

/-- Path barrier = max edge gate (empty → 0). -/
noncomputable def bondRearrangementPathBarrier (path : BondRearrangementPath) : ℝ :=
  discreteSaddleBarrierEv (path.map bondRearrangementStepGate)

theorem bondRearrangementPathBarrier_nil :
    bondRearrangementPathBarrier [] = 0 := by
  unfold bondRearrangementPathBarrier
  exact discreteSaddleBarrierEv_nil

theorem bondRearrangementPathBarrier_nonneg (path : BondRearrangementPath) :
    0 ≤ bondRearrangementPathBarrier path := by
  unfold bondRearrangementPathBarrier
  exact discreteSaddleBarrierEv_nonneg _

/-- Single-bond break path: one step with the given \(D\) and \(\delta\). -/
def singleBondBreakPath (bindingEv δ : ℝ) : BondRearrangementPath :=
  [{ bindingEv := bindingEv, deltaCoord := δ, kind := .breakBond }]

/-- Activation rate from a bond-rearrangement path. -/
noncomputable def activationRateFromPath
    (contactRate : ℝ) (path : BondRearrangementPath) (scaleEv : ℝ) : ℝ :=
  activationRateFromSaddle contactRate (bondRearrangementPathBarrier path) scaleEv

theorem activationRateFromPath_nil (contactRate scaleEv : ℝ) :
    activationRateFromPath contactRate [] scaleEv = contactRate := by
  unfold activationRateFromPath
  rw [bondRearrangementPathBarrier_nil, activationRateFromSaddle_open]

/-- Coordination excess after removing one neighbour from reference CN:
`δ = |CN' − CN| / max(CN, 1)` with `CN' = CN − 1`, i.e. `1 / max(CN, 1)`.
Same algebra as ``coordinationExcessVsReference`` / vacancy excess. -/
noncomputable def breakCoordinationExcess (cnRef : ℝ) : ℝ :=
  1 / max cnRef 1

/-- Endpoint excess on a break: max of the two endpoint CN drops. -/
noncomputable def breakEdgeDelta (cnI cnJ : ℝ) : ℝ :=
  max (breakCoordinationExcess cnI) (breakCoordinationExcess cnJ)

theorem breakCoordinationExcess_unit :
    breakCoordinationExcess 1 = 1 := by
  unfold breakCoordinationExcess; norm_num

theorem breakCoordinationExcess_tetrahedral :
    breakCoordinationExcess 4 = 1 / 4 := by
  unfold breakCoordinationExcess; norm_num

theorem breakCoordinationExcess_bent :
    breakCoordinationExcess 2 = 1 / 2 := by
  unfold breakCoordinationExcess; norm_num

theorem breakEdgeDelta_diatomic :
    breakEdgeDelta 1 1 = 1 := by
  unfold breakEdgeDelta
  rw [breakCoordinationExcess_unit]
  simp

/-- Monovalent break (\(\delta = 1\)): `E_def = D · γ · (4/8) = D/5`.
When the strong-channel scale is above the numerical floor,
`T = 1 / (1 + (D/5) / ((4/8)·D)) = 5/7` independent of \(D\). -/
theorem barrierTransmission_monovalent_break
    (bindingEv : ℝ) (h : 0 < bindingEv)
    (hfloor : (1e-30 : ℝ) ≤ (4 : ℝ) / 8 * bindingEv) :
    barrierTransmissionFromGate (contactEdgeGateEv bindingEv 1) bindingEv = 5 / 7 := by
  have hgate : contactEdgeGateEv bindingEv 1 = bindingEv / 5 := by
    unfold contactEdgeGateEv defectFormationEnergyEv localCurvatureDefectExcess
    rw [gamma_eq_2_5, strongChannelFraction_eq_four_eighths]
    have : max (1 : ℝ) 0 = 1 := by norm_num
    rw [this]; ring
  rw [hgate]
  unfold barrierTransmissionFromGate
  have hb : max bindingEv 0 = bindingEv := max_eq_left h.le
  rw [hb, strongChannelFraction_eq_four_eighths]
  have hscale : max ((4 : ℝ) / 8 * bindingEv) 1e-30 = (4 : ℝ) / 8 * bindingEv :=
    max_eq_left hfloor
  rw [hscale]
  field_simp
  ring

/-! ## Atomization ladders (multi-edge sequential breaks)

Sequential removal of terminal contacts from a centre with initial coordination
`cn₀`.  Step `k` stresses the centre at remaining CN `cn₀ − k` against a
monovalent terminal (`CN = 1`), so
`δ_k = breakEdgeDelta(cn₀ − k, 1) = max(1/(cn₀−k), 1)`.
The ladder barrier is the path maximum over those steps.
-/

/-- One ladder step: centre CN after `k` prior breaks, against a terminal H. -/
noncomputable def atomizationLadderStep
    (bindingEv centreCn0 : ℝ) (k : ℕ) : BondRearrangementStep where
  bindingEv := bindingEv
  deltaCoord := breakEdgeDelta (centreCn0 - k) 1
  kind := .breakBond

/-- Atomization ladder of `n` equal-depth breaks from centre CN `cn₀`. -/
noncomputable def atomizationLadderPath
    (bindingEv centreCn0 : ℝ) (n : ℕ) : BondRearrangementPath :=
  (List.range n).map (atomizationLadderStep bindingEv centreCn0)

theorem atomizationLadderPath_nil (bindingEv centreCn0 : ℝ) :
    atomizationLadderPath bindingEv centreCn0 0 = [] := by
  unfold atomizationLadderPath; simp

theorem atomizationLadderPath_barrier_nil (bindingEv centreCn0 : ℝ) :
    bondRearrangementPathBarrier (atomizationLadderPath bindingEv centreCn0 0) = 0 := by
  rw [atomizationLadderPath_nil, bondRearrangementPathBarrier_nil]

/-- Tetrahedral first break: `δ = max(1/4, 1) = 1`. -/
theorem atomizationLadderStep_tetrahedral_first (bindingEv : ℝ) :
    (atomizationLadderStep bindingEv 4 0).deltaCoord = 1 := by
  unfold atomizationLadderStep breakEdgeDelta breakCoordinationExcess
  norm_num

/-- Bent first break: `δ = max(1/2, 1) = 1`. -/
theorem atomizationLadderStep_bent_first (bindingEv : ℝ) :
    (atomizationLadderStep bindingEv 2 0).deltaCoord = 1 := by
  unfold atomizationLadderStep breakEdgeDelta breakCoordinationExcess
  norm_num

end

end Hqiv.QuantumChemistry
