import Mathlib.Tactic
import Hqiv.Physics.HomogeneousCurvatureSecondOrder

/-!
# Coupled relaxation slots for chemistry readouts

Several chemistry witnesses are intentionally feed-forward: a density slot feeds an
optical slot, or a binding-depth/contact slot feeds a spectroscopy slot.  This module
records the smallest algebra needed for a finite coupled update without adding a fit
coefficient: the coupling weight is an explicit structural input supplied by another
proved/readout layer.

Also wires discrete-saddle barriers into ``activationRateSlot`` via an HQIV-rational
transmission softener (no fitted Arrhenius prefactor).

Python mirror: `scripts/hqiv_chemistry_coupled_readout.py`,
`scripts/hqiv_discrete_saddle_defect_readout.py`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv.Physics

noncomputable section

/-- One finite relaxation step from a feed-forward value toward a coupled target. -/
def coupledRelaxationStep (feedForward coupledTarget lam : ℝ) : ℝ :=
  feedForward + lam * (coupledTarget - feedForward)

/-- Zero coupling recovers the feed-forward readout exactly. -/
theorem coupledRelaxationStep_zero (feedForward coupledTarget : ℝ) :
    coupledRelaxationStep feedForward coupledTarget 0 = feedForward := by
  unfold coupledRelaxationStep
  ring

/-- Unit coupling recovers the coupled target exactly. -/
theorem coupledRelaxationStep_one (feedForward coupledTarget : ℝ) :
    coupledRelaxationStep feedForward coupledTarget 1 = coupledTarget := by
  unfold coupledRelaxationStep
  ring

/-- The signed gap to the target is scaled by `1 - λ`. -/
theorem coupledRelaxationStep_target_gap
    (feedForward coupledTarget lam : ℝ) :
    coupledRelaxationStep feedForward coupledTarget lam - coupledTarget =
      (1 - lam) * (feedForward - coupledTarget) := by
  unfold coupledRelaxationStep
  ring

/-- The update stays in the interval spanned by its two inputs for `0 ≤ lam ≤ 1`. -/
theorem coupledRelaxationStep_between
    {feedForward coupledTarget lam : ℝ}
    (hff : feedForward ≤ coupledTarget) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    feedForward ≤ coupledRelaxationStep feedForward coupledTarget lam ∧
      coupledRelaxationStep feedForward coupledTarget lam ≤ coupledTarget := by
  unfold coupledRelaxationStep
  constructor <;> nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr hff),
    mul_le_mul_of_nonneg_right hlam1 (sub_nonneg.mpr hff)]

/-- Symmetric two-slot relaxation: each slot moves toward the other by the same weight. -/
def twoSlotCoupledRelaxation (x y lam : ℝ) : ℝ × ℝ :=
  (coupledRelaxationStep x y lam, coupledRelaxationStep y x lam)

/-- Two-way relaxation conserves the total slot budget. -/
theorem twoSlotCoupledRelaxation_sum (x y lam : ℝ) :
    (twoSlotCoupledRelaxation x y lam).1 + (twoSlotCoupledRelaxation x y lam).2 = x + y := by
  unfold twoSlotCoupledRelaxation coupledRelaxationStep
  ring

/-- Zero coupling leaves both slots unchanged. -/
theorem twoSlotCoupledRelaxation_zero (x y : ℝ) :
    twoSlotCoupledRelaxation x y 0 = (x, y) := by
  unfold twoSlotCoupledRelaxation coupledRelaxationStep
  ext <;> ring

/-- Half coupling equalizes the two slots at their arithmetic mean. -/
theorem twoSlotCoupledRelaxation_half (x y : ℝ) :
    twoSlotCoupledRelaxation x y (1 / 2) = ((x + y) / 2, (x + y) / 2) := by
  unfold twoSlotCoupledRelaxation coupledRelaxationStep
  ext <;> ring

/--
Structural coupling weight used by Python readouts:

`λ = clamp01(missingCoupling * responseFraction)`.

`missingCoupling` is a derived classification flag (0 for one-way diagnostic, 1 for
the rows whose residual audit points at missing coupled relaxation); `responseFraction`
is a derived finite fraction such as concentration weight or curvature-density
participation.  No comparison residual enters this slot.
-/
def structuralCouplingWeight (missingCoupling responseFraction : ℝ) : ℝ :=
  min 1 (max 0 (missingCoupling * responseFraction))

theorem structuralCouplingWeight_nonneg (missingCoupling responseFraction : ℝ) :
    0 ≤ structuralCouplingWeight missingCoupling responseFraction := by
  unfold structuralCouplingWeight
  exact le_min (by norm_num) (le_max_left _ _)

theorem structuralCouplingWeight_le_one (missingCoupling responseFraction : ℝ) :
    structuralCouplingWeight missingCoupling responseFraction ≤ 1 := by
  unfold structuralCouplingWeight
  exact min_le_left _ _

/-- Clamp a real readout to the finite branch interval `[0,1]`. -/
def clampUnitInterval (x : ℝ) : ℝ := min 1 (max 0 x)

theorem clampUnitInterval_nonneg (x : ℝ) : 0 ≤ clampUnitInterval x := by
  unfold clampUnitInterval
  exact le_min (by norm_num) (le_max_left _ _)

theorem clampUnitInterval_le_one (x : ℝ) : clampUnitInterval x ≤ 1 := by
  unfold clampUnitInterval
  exact min_le_left _ _

/--
Bounded branch-fraction relaxation, used for LDL/HDL or allotrope fractions:
relax toward a coupled target and then clamp back to the finite branch interval.
-/
def branchFractionCoupledStep (feedForward target lam : ℝ) : ℝ :=
  clampUnitInterval (coupledRelaxationStep feedForward target lam)

theorem branchFractionCoupledStep_nonneg (feedForward target lam : ℝ) :
    0 ≤ branchFractionCoupledStep feedForward target lam :=
  clampUnitInterval_nonneg _

theorem branchFractionCoupledStep_le_one (feedForward target lam : ℝ) :
    branchFractionCoupledStep feedForward target lam ≤ 1 :=
  clampUnitInterval_le_one _

/--
Cage-limited transport slot: a finite carrier diffusivity `D` is multiplied by the
survival fraction `1 - cage`, where `cage ∈ [0,1]` is derived from contact persistence
or network coordination.
-/
def cageLimitedTransport (D cage : ℝ) : ℝ := D * (1 - cage)

theorem cageLimitedTransport_zero_of_full_cage (D : ℝ) :
    cageLimitedTransport D 1 = 0 := by
  unfold cageLimitedTransport
  ring

theorem cageLimitedTransport_identity_of_no_cage (D : ℝ) :
    cageLimitedTransport D 0 = D := by
  unfold cageLimitedTransport
  ring

theorem cageLimitedTransport_nonneg
    (D cage : ℝ) (hD : 0 ≤ D) (hc1 : cage ≤ 1) :
    0 ≤ cageLimitedTransport D cage := by
  unfold cageLimitedTransport
  exact mul_nonneg hD (sub_nonneg.mpr hc1)

/--
Activation-gated contact rate: finite reaction gates still provide the contact rate;
the activation slot is a derived barrier transmission in `[0,1]`.
-/
def activationRateSlot (contactRate barrierTransmission : ℝ) : ℝ :=
  contactRate * barrierTransmission

theorem activationRateSlot_zero_of_closed_barrier (contactRate : ℝ) :
    activationRateSlot contactRate 0 = 0 := by
  unfold activationRateSlot
  ring

theorem activationRateSlot_identity_of_open_barrier (contactRate : ℝ) :
    activationRateSlot contactRate 1 = contactRate := by
  unfold activationRateSlot
  ring

theorem activationRateSlot_nonneg
    (contactRate barrierTransmission : ℝ)
    (hr : 0 ≤ contactRate) (hb : 0 ≤ barrierTransmission) :
    0 ≤ activationRateSlot contactRate barrierTransmission := by
  unfold activationRateSlot
  exact mul_nonneg hr hb

/-! ## Discrete-saddle → activation transmission

Barrier height from ``discreteSaddleBarrierEv`` / ``defectFormationEnergyEv``
softens the contact rate with the same rational pattern as ionic optical softeners:
`T = 1 / (1 + B / max(strong · D, ε))`.  Zero barrier recovers identity.
-/

/-- HQIV-rational barrier transmission in `(0,1]`.
`T = 1 / (1 + B / max(strong · D_scale, ε))`. -/
noncomputable def barrierTransmissionFromGate
    (barrierEv scaleEv : ℝ) : ℝ :=
  1 / (1 + barrierEv / max (strongChannelFraction * max scaleEv 0) 1e-30)

theorem barrierTransmissionFromGate_zero_barrier (scaleEv : ℝ) :
    barrierTransmissionFromGate 0 scaleEv = 1 := by
  unfold barrierTransmissionFromGate
  simp

/-- Activation rate from a discrete-saddle barrier on the contact graph. -/
noncomputable def activationRateFromSaddle
    (contactRate barrierEv scaleEv : ℝ) : ℝ :=
  activationRateSlot contactRate (barrierTransmissionFromGate barrierEv scaleEv)

theorem activationRateFromSaddle_open
    (contactRate scaleEv : ℝ) :
    activationRateFromSaddle contactRate 0 scaleEv = contactRate := by
  unfold activationRateFromSaddle
  rw [barrierTransmissionFromGate_zero_barrier, activationRateSlot_identity_of_open_barrier]

/-- Build edge gates from binding depths and coordination excesses, then take the
path maximum (discrete saddle). -/
noncomputable def discreteSaddleFromContacts
    (bindings : List ℝ) (excesses : List ℝ) : ℝ :=
  Hqiv.Physics.discreteSaddleBarrierEv
    ((bindings.zip excesses).map fun p =>
      Hqiv.Physics.contactEdgeGateEv p.1 p.2)

/--
One graph-neighbour propagation step: a local slot relaxes toward the neighbour mean.
This is the finite-register analogue of cooperative/allosteric propagation; no
continuum field is required.
-/
def networkPropagationStep (localSlot neighbourMean lam : ℝ) : ℝ :=
  coupledRelaxationStep localSlot neighbourMean lam

theorem networkPropagationStep_zero (localSlot neighbourMean : ℝ) :
    networkPropagationStep localSlot neighbourMean 0 = localSlot := by
  unfold networkPropagationStep
  exact coupledRelaxationStep_zero localSlot neighbourMean

theorem networkPropagationStep_gap
    (localSlot neighbourMean lam : ℝ) :
    networkPropagationStep localSlot neighbourMean lam - neighbourMean =
      (1 - lam) * (localSlot - neighbourMean) := by
  unfold networkPropagationStep
  exact coupledRelaxationStep_target_gap localSlot neighbourMean lam

/--
Geometry-binding co-relaxation: the reported geometry length is a bounded finite
relaxation from the one-way geometry toward a network/contact target.
-/
def geometryBindingRelaxedLength (oneWayLength targetLength lam : ℝ) : ℝ :=
  coupledRelaxationStep oneWayLength targetLength lam

theorem geometryBindingRelaxedLength_zero (oneWayLength targetLength : ℝ) :
    geometryBindingRelaxedLength oneWayLength targetLength 0 = oneWayLength := by
  unfold geometryBindingRelaxedLength
  exact coupledRelaxationStep_zero oneWayLength targetLength

theorem geometryBindingRelaxedLength_one (oneWayLength targetLength : ℝ) :
    geometryBindingRelaxedLength oneWayLength targetLength 1 = targetLength := by
  unfold geometryBindingRelaxedLength
  exact coupledRelaxationStep_one oneWayLength targetLength

end

end Hqiv.QuantumChemistry
