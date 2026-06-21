import Hqiv.Physics.CkmHolonomyReadout
import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.Forces

/-!
# Rare decay readout ledger

Finite-patch branching slots for rare and FCNC channels, routed through
the proved CKM holonomy matrix and spine discharge weights.

Python mirror: extend `scripts/hqiv_hep_anomaly_discharge.py`.
-/

namespace Hqiv.Physics

/-! ## Channel registry -/

inductive RareDecayChannel where
  | KToPiNuNu
  | BsToMuMu
  | BToSGamma
  deriving DecidableEq, Repr, Inhabited

/-- CKM weight for rare FCNC channel (second-order rung product). -/
noncomputable def rareDecayCkmWeight : RareDecayChannel → ℝ
  | .KToPiNuNu => ckmSlotUS2 ^ 2
  | .BsToMuMu => ckmSlotCB2 ^ 2
  | .BToSGamma => ckmSlotUS2

theorem rareDecayCkmWeight_K_pos :
    0 < rareDecayCkmWeight .KToPiNuNu := by
  simp [rareDecayCkmWeight, ckmSlotUS2_pos, pow_pos]

theorem rareDecayCkmWeight_Bs_pos :
    0 < rareDecayCkmWeight .BsToMuMu := by
  simp [rareDecayCkmWeight, ckmSlotCB2_pos, pow_pos]

/-- OZI / strong suppression on radiative FCNC. -/
noncomputable def rareDecayStrongSuppression : RareDecayChannel → ℝ
  | .KToPiNuNu => 1
  | .BsToMuMu => doubleMonogamyExclusionFactor
  | .BToSGamma => oziSuppressedStrongContact

/-- Phase-space and CP routing factor from holonomy. -/
noncomputable def rareDecayHolonomyFactor (ch : RareDecayChannel) : ℝ :=
  match ch with
  | .KToPiNuNu => 1
  | .BsToMuMu => ckmJarlskog
  | .BToSGamma => cpOddFanoHolonomySkew

/--
Branching ratio slot before normalization:
`W = g_K · g_γ^{e_γ} · CKM · strong · holonomy`.
Reuses spine discharge exponent discipline.
-/
noncomputable def rareDecayBranchingSlot (ch : RareDecayChannel) : ℝ :=
  rareDecayCkmWeight ch * rareDecayStrongSuppression ch * rareDecayHolonomyFactor ch

theorem rareDecayBranchingSlot_K_pos :
    0 < rareDecayBranchingSlot .KToPiNuNu := by
  simp [rareDecayBranchingSlot, rareDecayCkmWeight, rareDecayStrongSuppression,
    rareDecayHolonomyFactor, ckmSlotUS2_pos, pow_pos]

structure RareDecayReadoutCertificate where
  channels : List RareDecayChannel
  k_slot_pos : 0 < rareDecayBranchingSlot .KToPiNuNu
  bs_ckm : rareDecayCkmWeight .BsToMuMu = ckmSlotCB2 ^ 2
  bsgamma_ckm : rareDecayCkmWeight .BToSGamma = ckmSlotUS2

def rareDecayReadoutCertificate_holds : RareDecayReadoutCertificate where
  channels := [.KToPiNuNu, .BsToMuMu, .BToSGamma]
  k_slot_pos := rareDecayBranchingSlot_K_pos
  bs_ckm := rfl
  bsgamma_ckm := rfl

end Hqiv.Physics
