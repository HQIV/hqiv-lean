import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.CoronalEstarSIAnchorWitness
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.InformationalEnergyMass
import Hqiv.Physics.OMaxwellLongitudinalMomentumBridge

/-!
# L2 phase-gradient torsion balance witness (primary $E_∗$ laboratory anchor)

**Purpose:** formalize Experiment L2 from the longitudinal EM programme: a
Cavendish-class torsion balance with controlled axial $\partial_s\varphi$, negligible
Joule background, and the TUFT lock-in longitudinal/transverse ratio slot
$\gamma\,\Theta_{\mathrm{local}}^{-1}$.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex`
§lab-experiments (L2), §e-star; TUFT synthesis lock-in torsion paragraph.

## Proof status (algebraic + hypothesis bundles, zero `sorry`)

* **§1.** Longitudinal/transverse ratio slots ($\gamma/\Theta$, lab $0.08\,T/T_{\rm Pl}$ form).
* **§2.** Lock-in chart identities at `xiLockin = referenceM + 1`.
* **§3.** Force denominator and $E_∗$ inversion from measured torsion force.
* **§4.** L2 experiment witness (zero-Joule hypothesis + boundary force).
* **§5.** Programme force band + joint $\kappa_6$ falsifier slot.
* **§6.** Discharged honesty ledger.

**Not claimed:** Cavendish apparatus model; unique effective $n_q$ for solids;
automatic derivation of $10^{-14}$--$10^{-13}\,\mathrm{N}$ from first principles;
replacement of dedicated torsion-balance GR tests. The programme force band is a
quarantined readout target (same honesty pattern as coronal flux calibration).
-/

namespace Hqiv.Physics

open Hqiv
open InformationalEnergyMass
open ContinuousXiPath

noncomputable section

/-!
## §1. Longitudinal / transverse ratio slots
-/

/-- TUFT synthesis slot: $\gamma\,\Theta_{\mathrm{local}}^{-1}$ at positive localization temperature. -/
def longitudinalToTransverseRatioTheta (thetaLocal : ℝ) : ℝ :=
  gamma_HQIV / thetaLocal

theorem longitudinalToTransverseRatioTheta_eq_gamma_times_inv_theta
    (thetaLocal : ℝ) :
    longitudinalToTransverseRatioTheta thetaLocal = gamma_HQIV * (1 / thetaLocal) := by
  unfold longitudinalToTransverseRatioTheta
  ring

/-- Continuous-chart form using `localizationEnergy = 1/Θ_local`. -/
def longitudinalToTransverseRatioAtXi (ξ : ℝ) : ℝ :=
  gamma_HQIV * localizationEnergy ξ

theorem longitudinalToTransverseRatioAtXi_eq_gamma_div_theta
    (ξ : ℝ) :
    longitudinalToTransverseRatioAtXi ξ =
      longitudinalToTransverseRatioTheta (thetaLocal_xi ξ) := by
  unfold longitudinalToTransverseRatioAtXi longitudinalToTransverseRatioTheta
    localizationEnergy
  ring

/-- Laboratory readout form from the TUFT paragraph: $(\gamma/5)\,(T/T_{\rm Pl})$. -/
def longitudinalToTransverseRatioLab (T_local : ℝ) : ℝ :=
  (gamma_HQIV / 5) * (T_local / T_Pl)

theorem longitudinalToTransverseRatioLab_eq_gamma_over_five_times_T
    (T_local : ℝ) :
    longitudinalToTransverseRatioLab T_local = (gamma_HQIV / 5) * T_local := by
  unfold longitudinalToTransverseRatioLab
  rw [T_Pl_eq]
  ring

theorem longitudinalToTransverseRatioLab_zero_of_zero_temperature
    (T_local : ℝ) (h : T_local = 0) :
    longitudinalToTransverseRatioLab T_local = 0 := by
  rw [h, longitudinalToTransverseRatioLab_eq_gamma_over_five_times_T, mul_zero]

/-!
## §2. Lock-in chart
-/

theorem longitudinalToTransverseRatioAtLockin_eq_gamma_times_five :
    longitudinalToTransverseRatioAtXi xiLockin = gamma_HQIV * 5 := by
  unfold longitudinalToTransverseRatioAtXi
  rw [localizationEnergy_eq_xi_over_T_Pl xiLockin (by rw [xiLockin_eq_five]; norm_num),
    xiLockin_eq_five, T_Pl_eq, gamma_eq_2_5]
  norm_num

theorem longitudinalToTransverseRatioAtLockin_eq_two :
    longitudinalToTransverseRatioAtXi xiLockin = 2 := by
  rw [longitudinalToTransverseRatioAtLockin_eq_gamma_times_five, gamma_eq_2_5]
  norm_num

/-- One-shell φ step above lock-in: $\Delta\varphi = 2$. -/
def l2LockinOneShellJump : ℝ := coronalPhiJump ⟨referenceM, referenceM + 1, by decide⟩

theorem l2LockinOneShellJump_eq_two :
    l2LockinOneShellJump = 2 := by
  unfold l2LockinOneShellJump
  rw [coronalPhiJump_closed_form]
  simp [referenceM]

/-!
## §3. Force denominator and $E_∗$ inversion
-/

/-- Denominator in `coronalLongitudinalForceBoundary` at unit `E_∗` (α inlined). -/
def l2TorsionForceDenominator
    (A nq couplingLog deltaPhi : ℝ) : ℝ :=
  A * nq * (3 / (20 * Real.pi)) * couplingLog * deltaPhi

theorem l2TorsionForceDenominator_eq_boundary_at_unit_estar
    (A nq couplingLog phi_photo phi_corona : ℝ) :
    l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) =
      coronalLongitudinalForceBoundary A nq 1 couplingLog phi_photo phi_corona := by
  unfold l2TorsionForceDenominator coronalLongitudinalForceBoundary
  ring

theorem l2TorsionForceDenominator_eq_boundary_with_estar
    (A nq Estar couplingLog phi_photo phi_corona : ℝ) :
    coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona =
      Estar * l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) := by
  unfold l2TorsionForceDenominator coronalLongitudinalForceBoundary
  ring

theorem l2TorsionForceDenominator_eq_force_over_estar
    (A nq Estar couplingLog phi_photo phi_corona : ℝ)
    (hE : Estar ≠ 0) :
    l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) =
      coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona / Estar := by
  unfold l2TorsionForceDenominator coronalLongitudinalForceBoundary
  field_simp [hE]

/-- $E_∗$ that reproduces a measured L2 torsion force (boundary identity). -/
def estarFromL2TorsionForce
    (F_measured A nq couplingLog deltaPhi : ℝ) : ℝ :=
  if l2TorsionForceDenominator A nq couplingLog deltaPhi = 0 then 0
  else F_measured / l2TorsionForceDenominator A nq couplingLog deltaPhi

theorem coronalLongitudinalForceBoundary_l2_estar_calibration
    (F_measured A nq couplingLog phi_photo phi_corona : ℝ)
    (hd : l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0)
    (hE : estarFromL2TorsionForce F_measured A nq couplingLog (phi_corona - phi_photo) =
        F_measured / l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo)) :
    coronalLongitudinalForceBoundary A nq
        (estarFromL2TorsionForce F_measured A nq couplingLog (phi_corona - phi_photo))
        couplingLog phi_photo phi_corona = F_measured := by
  rw [l2TorsionForceDenominator_eq_boundary_with_estar, hE]
  field_simp [hd]

theorem coronalLongitudinalForceBoundary_l2_estar_calibration_direct
    (F_measured A nq Estar couplingLog phi_photo phi_corona : ℝ)
    (hd : l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0)
    (hE : Estar = F_measured / l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo)) :
    coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona = F_measured := by
  rw [l2TorsionForceDenominator_eq_boundary_with_estar, hE]
  field_simp [hd]

/-!
## §4. L2 experiment witness
-/

/-- Negligible Joule / Ohmic background (L2 design target). -/
structure L2JouleBackgroundNegligible (J sigma : ℝ) : Prop where
  ohmic_zero : ohmicAxialField J sigma = 0

theorem L2JouleBackgroundNegligible.carrier_force_is_hqiv
    {nq Estar couplingLog dphi_ds : ℝ} {J sigma : ℝ}
    (hJ : L2JouleBackgroundNegligible J sigma) :
    longitudinalCarrierForceDensity nq J sigma Estar couplingLog dphi_ds =
      nq * coronalLongitudinalHQIVField Estar couplingLog dphi_ds := by
  rw [longitudinalCarrierForceDensity_add_decomposition, hJ.ohmic_zero]
  simp

/-- Full L2 torsion-balance row tying measured force to boundary identity + $E_∗$. -/
structure L2TorsionBalanceWitness where
  F_measured : ℝ
  A : ℝ
  nq : ℝ
  couplingLog : ℝ
  phi_photo : ℝ
  phi_corona : ℝ
  estar : ℝ
  denom_ne_zero :
    l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0
  estar_eq :
    estar = F_measured / l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo)
  force_eq :
    coronalLongitudinalForceBoundary A nq estar couplingLog phi_photo phi_corona = F_measured
  joulenegligible : L2JouleBackgroundNegligible 0 1

def L2TorsionBalanceWitness.mk'
    (F_measured A nq couplingLog phi_photo phi_corona : ℝ)
    (hd : l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0) :
    L2TorsionBalanceWitness where
  F_measured := F_measured
  A := A
  nq := nq
  couplingLog := couplingLog
  phi_photo := phi_photo
  phi_corona := phi_corona
  estar := F_measured / l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo)
  denom_ne_zero := hd
  estar_eq := rfl
  force_eq := coronalLongitudinalForceBoundary_l2_estar_calibration_direct F_measured A nq _ couplingLog
    phi_photo phi_corona hd (by rfl)
  joulenegligible := ⟨by simp [ohmicAxialField]⟩

theorem L2TorsionBalanceWitness.estar_eq_force_over_denom
    (w : L2TorsionBalanceWitness) :
    w.estar = w.F_measured / l2TorsionForceDenominator w.A w.nq w.couplingLog (w.phi_corona - w.phi_photo) :=
  w.estar_eq

/-- Lock-in one-shell jump specialization. -/
def L2TorsionBalanceWitness.mkLockinOneShell
    (F_measured A nq couplingLog : ℝ)
    (hd : l2TorsionForceDenominator A nq couplingLog l2LockinOneShellJump ≠ 0) :
    L2TorsionBalanceWitness :=
  L2TorsionBalanceWitness.mk' F_measured A nq couplingLog
    (phi_of_shell referenceM) (phi_of_shell (referenceM + 1)) hd

/-!
## §5. Programme band + joint $\kappa_6$ falsifier slot
-/

/-- Programme target band for L2 axial force (paper readout; not derived here). -/
def l2TorsionForceProgramBandLow : ℝ := 1 / 10 ^ 14

def l2TorsionForceProgramBandHigh : ℝ := 1 / 10 ^ 13

theorem l2TorsionForceProgramBand_ordered :
    l2TorsionForceProgramBandLow < l2TorsionForceProgramBandHigh := by
  unfold l2TorsionForceProgramBandLow l2TorsionForceProgramBandHigh
  norm_num

structure L2TorsionForceInProgramBand (F : ℝ) : Prop where
  low_le : l2TorsionForceProgramBandLow ≤ F
  le_high : F ≤ l2TorsionForceProgramBandHigh

/-- Witness that a measured L2 force lies in the programme band. -/
structure L2TorsionProgramBandWitness where
  balance : L2TorsionBalanceWitness
  in_band : L2TorsionForceInProgramBand balance.F_measured

/-- Joint falsifier slot: static $\kappa_6$ dressing at lock-in + L2 force witness. -/
structure L2Kappa6JointFalsifierWitness where
  balance : L2TorsionBalanceWitness
  kappa6_at_lockin : ℝ
  kappa6_at_lockin_eq : kappa6_at_lockin = tuftHopfKappa6
  ratio_lockin : longitudinalToTransverseRatioAtXi xiLockin = 2

theorem L2Kappa6JointFalsifierWitness.ratio_lockin_discharged :
    longitudinalToTransverseRatioAtXi xiLockin = 2 :=
  longitudinalToTransverseRatioAtLockin_eq_two

def L2Kappa6JointFalsifierWitness.mk'
    (F_measured A nq couplingLog phi_photo phi_corona : ℝ)
    (hd : l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0) :
    L2Kappa6JointFalsifierWitness where
  balance := L2TorsionBalanceWitness.mk' F_measured A nq couplingLog phi_photo phi_corona hd
  kappa6_at_lockin := tuftHopfKappa6
  kappa6_at_lockin_eq := rfl
  ratio_lockin := longitudinalToTransverseRatioAtLockin_eq_two

/-!
## §6. Honesty ledger
-/

structure L2TorsionBalanceHonestyLedger : Prop where
  ratio_lab_form :
    ∀ T_local, longitudinalToTransverseRatioLab T_local = (gamma_HQIV / 5) * T_local
  ratio_lockin :
    longitudinalToTransverseRatioAtXi xiLockin = 2
  force_calibration :
    ∀ (F_measured A nq Estar couplingLog phi_photo phi_corona : ℝ)
      (_hd : l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo) ≠ 0)
      (hE : Estar = F_measured / l2TorsionForceDenominator A nq couplingLog (phi_corona - phi_photo)),
      coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona = F_measured
  witness_force :
    ∀ (w : L2TorsionBalanceWitness),
      coronalLongitudinalForceBoundary w.A w.nq w.estar w.couplingLog w.phi_photo w.phi_corona =
        w.F_measured

theorem l2TorsionBalanceHonestyLedger_discharged : L2TorsionBalanceHonestyLedger where
  ratio_lab_form := longitudinalToTransverseRatioLab_eq_gamma_over_five_times_T
  ratio_lockin := longitudinalToTransverseRatioAtLockin_eq_two
  force_calibration := fun F A nq Estar couplingLog phi_photo phi_corona hd hE =>
    coronalLongitudinalForceBoundary_l2_estar_calibration_direct F A nq Estar couplingLog phi_photo phi_corona hd hE
  witness_force := fun w => w.force_eq

end

end Hqiv.Physics
