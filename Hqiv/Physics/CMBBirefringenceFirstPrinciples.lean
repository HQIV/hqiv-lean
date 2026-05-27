import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.QuantumMechanics.BornMeasurementFinite

/-!
# HQIV birefringence proton-anchor imprint (no experimental β input)

The measurement/redshift layer uses `birefringenceRedshiftN betaRad kappaBeta` with independent
real parameters. Here we **define** a distinguished proton-anchor imprint
`betaRad_HQIV_imprint` from the
**already-derived** HQIV objects in this repository:

* the **sole** HQIV curvature-imprint exponent `Hqiv.alpha` (proved `3/5` via `alpha_eq_3_5`;
  physical derivation in the companion HQIV manuscript and Brodie 2026—see `AGENTS/ASSUMPTIONS.md` §1b);
* the reference horizon shell `Hqiv.referenceM` (lock-in shell from the 3D null lattice).

No measured CMB polarization angle is imported.  This is the formal proton-lock-in shell hook used
to populate the birefringence channel in the same bookkeeping identity as `BornMeasurementFinite`.
The observed CMB birefringence angle is a **relative** shell traversal,
`α · log((m_obs+1)/(m_emit+1))`, formalized in `HorizonBlackbodyLadder`.

The closed form `exp(betaRad/κ) = (referenceM+1)^α` (with `κ = 1`) links cosmic birefringence
redshift directly to the discrete shell ladder and α at the proton-anchor shell; it is not a claim
that last scattering sits at `referenceM`.
-/

namespace Hqiv.Physics

open scoped Real

noncomputable section

/-- Bookkeeping normalization for κ_β (dimensionless), matching the paper’s κ_β = 1 display. -/
def kappaBeta_HQIV : ℝ := 1

theorem kappaBeta_HQIV_pos : 0 < kappaBeta_HQIV := by unfold kappaBeta_HQIV; norm_num

/-- **First-principles proton-anchor** birefringence imprint (radians):
α times log(reference shell + 1).

Here `α` is the HQIV curvature imprint exponent and `referenceM` is the derived lock-in shell
(`qcdShell + stepsFromQCDToLockin` in `OctonionicLightCone`).  CMB observations compare two
cosmological shells and therefore use the shell-ratio readout in `HorizonBlackbodyLadder`. -/
noncomputable def betaRad_HQIV_imprint : ℝ :=
  Hqiv.alpha * Real.log ((Hqiv.referenceM + 1 : ℝ))

theorem referenceM_succ_pos : (0 : ℝ) < (Hqiv.referenceM + 1 : ℝ) := by positivity

theorem referenceM_pos : 0 < Hqiv.referenceM := by
  unfold Hqiv.referenceM Hqiv.qcdShell Hqiv.stepsFromQCDToLockin Hqiv.latticeStepCount
  norm_num

theorem betaRad_HQIV_imprint_pos : 0 < betaRad_HQIV_imprint := by
  unfold betaRad_HQIV_imprint
  have hα : 0 < Hqiv.alpha := by
    rw [Hqiv.alpha_eq_3_5]
    norm_num
  have hlog : 0 < Real.log ((Hqiv.referenceM + 1 : ℝ)) := by
    apply Real.log_pos
    have hrm : (0 : ℝ) < (Hqiv.referenceM : ℝ) := by exact_mod_cast referenceM_pos
    linarith
  exact mul_pos hα hlog

/-- Redshift factor identity: `1 + z = exp(β/κ)` equals `(M+1)^α` at `κ = 1`. -/
theorem one_add_birefringence_HQIV_imprint :
    1 + Hqiv.QM.birefringenceRedshiftN betaRad_HQIV_imprint kappaBeta_HQIV
      = ((Hqiv.referenceM + 1 : ℝ) ^ Hqiv.alpha : ℝ) := by
  have hx : 0 < (Hqiv.referenceM + 1 : ℝ) := by positivity
  unfold Hqiv.QM.birefringenceRedshiftN betaRad_HQIV_imprint kappaBeta_HQIV
  -- `rpow_def_of_pos`: `x^y = exp(log x * y)`; commute to match `alpha * log x`.
  have hexp :
      Real.exp ((Hqiv.alpha * Real.log ((Hqiv.referenceM + 1 : ℝ))) / (1 : ℝ))
        = ((Hqiv.referenceM + 1 : ℝ) ^ Hqiv.alpha : ℝ) := by
    simp only [div_one]
    rw [Real.rpow_def_of_pos hx Hqiv.alpha]
    congr 1
    ring
  calc
    1 + (Real.exp ((Hqiv.alpha * Real.log ((Hqiv.referenceM + 1 : ℝ))) / (1 : ℝ)) - 1)
        = Real.exp ((Hqiv.alpha * Real.log ((Hqiv.referenceM + 1 : ℝ))) / (1 : ℝ)) := by ring
    _ = ((Hqiv.referenceM + 1 : ℝ) ^ Hqiv.alpha : ℝ) := hexp

end

end Hqiv.Physics
