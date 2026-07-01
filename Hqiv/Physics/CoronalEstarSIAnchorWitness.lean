import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.SolarDynamics

/-!
# Coronal `E_∗` SI anchor witness (target heating-flux calibration)

**Purpose:** discharge the algebraic inverse used in the longitudinal EM programme
and `scripts/hqiv_coronal_plasma_backreaction.py`: given a target area-normalised
boundary heating flux `Q/A`, solve for the dimensionless→SI slot `E_∗` that reproduces
the proved `coronalHeatingFluxBoundary` identity.

Companion: `papers/longitudinal_em_force_hqiv/hqiv_longitudinal_em_force.tex` §e-star;
Python: `e_star_for_target_flux` in `hqiv_coronal_plasma_backreaction.py`.

## Proof status (all definitional / algebraic, zero `sorry`)

* **§1.** Denominator slot `nq v_∥ (3/20π) Λ_s Δφ`.
* **§2.** Inverse `E_∗ = (Q/A) / denom` and calibration equality.
* **§3.** Shell-ladder and work-rate corollaries.
* **§4.** Witness bundle + discharged honesty ledger.

**Not claimed:** unique coronal `(n_q, v_∥, Λ_s, Δφ)` assignment; observational
closure without an explicit target-flux witness; derivation of `E_∗` from lock-in
mass units alone. The target flux is supplied at the readout layer (parametric or
quarantined observational slot).
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Denominator slot
-/

/-- Algebraic denominator in `coronalHeatingFluxBoundary` (α = 3/5 inlined). -/
def coronalHeatingFluxDenominator
    (nq v_parallel couplingLog phi_photo phi_corona : ℝ) : ℝ :=
  nq * v_parallel * (3 / (20 * Real.pi)) * couplingLog * (phi_corona - phi_photo)

theorem coronalHeatingFluxDenominator_eq_boundary_without_estar
    (nq Estar v_parallel couplingLog phi_photo phi_corona : ℝ) :
    coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi_photo phi_corona =
      Estar * coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona := by
  unfold coronalHeatingFluxBoundary coronalHeatingFluxDenominator
  ring

theorem coronalHeatingFluxDenominator_zero_of_equal_phi
    (nq v_parallel couplingLog phi : ℝ) :
    coronalHeatingFluxDenominator nq v_parallel couplingLog phi phi = 0 := by
  unfold coronalHeatingFluxDenominator; ring

theorem coronalHeatingFluxDenominator_shells
    (nq v_parallel couplingLog : ℝ) (cols : CoronalColumnShells) :
    coronalHeatingFluxDenominator nq v_parallel couplingLog
        (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona) =
      nq * v_parallel * (3 / (20 * Real.pi)) * couplingLog * coronalPhiJump cols := by
  unfold coronalHeatingFluxDenominator coronalPhiJump
  ring

/-!
## §2. Inverse calibration
-/

/-- `E_∗` that calibrates the boundary flux to `targetFlux` when the denominator is nonzero. -/
def estarForTargetHeatingFlux
    (targetFlux nq v_parallel couplingLog phi_photo phi_corona : ℝ) : ℝ :=
  if coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona = 0 then
    0
  else
    targetFlux /
      coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona

theorem coronalHeatingFluxBoundary_estar_calibration
    (targetFlux nq v_parallel couplingLog phi_photo phi_corona : ℝ)
    (hd : coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona ≠ 0)
    (hE : estarForTargetHeatingFlux targetFlux nq v_parallel couplingLog phi_photo phi_corona =
        targetFlux /
          coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona) :
    coronalHeatingFluxBoundary nq
        (estarForTargetHeatingFlux targetFlux nq v_parallel couplingLog phi_photo phi_corona)
        couplingLog v_parallel phi_photo phi_corona = targetFlux := by
  rw [coronalHeatingFluxDenominator_eq_boundary_without_estar, hE]
  field_simp [hd]

theorem coronalHeatingFluxBoundary_estar_calibration_direct
    (targetFlux nq Estar v_parallel couplingLog phi_photo phi_corona : ℝ)
    (hd : coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona ≠ 0)
    (hE : Estar = targetFlux / coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona) :
    coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi_photo phi_corona = targetFlux := by
  rw [coronalHeatingFluxDenominator_eq_boundary_without_estar, hE]
  field_simp [hd]

theorem coronalHeatingFluxBoundaryShells_estar_calibration
    (targetFlux nq v_parallel couplingLog : ℝ) (cols : CoronalColumnShells)
    (hd : coronalHeatingFluxDenominator nq v_parallel couplingLog
            (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona) ≠ 0)
    (hE : estarForTargetHeatingFlux targetFlux nq v_parallel couplingLog
            (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona) =
          targetFlux /
            coronalHeatingFluxDenominator nq v_parallel couplingLog
              (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona)) :
    coronalHeatingFluxBoundaryShells nq
        (estarForTargetHeatingFlux targetFlux nq v_parallel couplingLog
          (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona))
        couplingLog v_parallel cols = targetFlux := by
  rw [coronalHeatingFluxBoundaryShells_eq]
  exact coronalHeatingFluxBoundary_estar_calibration targetFlux nq v_parallel couplingLog
    (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona) hd hE

/-!
## §3. Witness bundle
-/

structure CoronalEstarCalibrationWitness where
  targetFlux : ℝ
  nq : ℝ
  v_parallel : ℝ
  couplingLog : ℝ
  phi_photo : ℝ
  phi_corona : ℝ
  estar : ℝ
  denom_ne_zero :
    coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona ≠ 0
  estar_eq :
    estar = targetFlux /
      coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona
  flux_eq :
    coronalHeatingFluxBoundary nq estar couplingLog v_parallel phi_photo phi_corona = targetFlux

def CoronalEstarCalibrationWitness.mk'
    (targetFlux nq v_parallel couplingLog phi_photo phi_corona : ℝ)
    (hd : coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona ≠ 0) :
    CoronalEstarCalibrationWitness where
  targetFlux := targetFlux
  nq := nq
  v_parallel := v_parallel
  couplingLog := couplingLog
  phi_photo := phi_photo
  phi_corona := phi_corona
  estar := targetFlux /
    coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona
  denom_ne_zero := hd
  estar_eq := rfl
  flux_eq := coronalHeatingFluxBoundary_estar_calibration_direct targetFlux nq _ v_parallel
    couplingLog phi_photo phi_corona hd (by rfl)

theorem CoronalEstarCalibrationWitness.flux_eq_target
    (w : CoronalEstarCalibrationWitness) :
    coronalHeatingFluxBoundary w.nq w.estar w.couplingLog w.v_parallel w.phi_photo w.phi_corona =
      w.targetFlux :=
  w.flux_eq

/-!
## §4. Honesty ledger
-/

structure CoronalEstarSIAnchorHonestyLedger : Prop where
  calibration_identity :
    ∀ (targetFlux nq Estar v_parallel couplingLog phi_photo phi_corona : ℝ)
      (hd : coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona ≠ 0)
      (hE : Estar = targetFlux / coronalHeatingFluxDenominator nq v_parallel couplingLog phi_photo phi_corona),
      coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi_photo phi_corona = targetFlux
  witness_flux :
    ∀ (w : CoronalEstarCalibrationWitness),
      coronalHeatingFluxBoundary w.nq w.estar w.couplingLog w.v_parallel w.phi_photo w.phi_corona =
        w.targetFlux

theorem coronalEstarSIAnchorHonestyLedger_discharged : CoronalEstarSIAnchorHonestyLedger where
  calibration_identity := coronalHeatingFluxBoundary_estar_calibration_direct
  witness_flux := CoronalEstarCalibrationWitness.flux_eq_target

end

end Hqiv.Physics
