import Hqiv.Physics.HiggsSelfCouplingReadout
import Hqiv.Physics.CkmHolonomyReadout
import Hqiv.Physics.FanoHolonomyOverlap

/-!
# SMEFT dimension-6 coefficient exporter (theorem records)

Discrete carrier records for SMEFT operator coefficients fixed by HQIV rules.
Comparison with global fits stays outside the proof layer.
-/

namespace Hqiv.Physics

/-- SMEFT operator label (dimension-6 focus). -/
inductive SMEFTOperator where
  | OQ1    -- (H†H)(q̄q)
  | OQq3   -- (H† i↔D H)(q̄σᵃq)
  | OH     -- (H†H)³
  | OW     -- (H†τᵃH)(W̄σᵃW)
  | Oll    -- (ℓ̄γᵃℓ)(ℓ̄γᵃℓ)
  deriving DecidableEq, Repr, Inhabited

/-- Wilson coefficient record (real, dimensionless). -/
structure SMEFTCoefficient where
  operator : SMEFTOperator
  value : ℝ
  lean_source : String

/-- Coefficient from CKM holonomy skew (flavor-universal dipole slot). -/
noncomputable def smeftCoeffFromHolonomySkew : ℝ :=
  fanoSecondOrderPhaseSkew / gamma_HQIV

theorem smeftCoeffFromHolonomySkew_eq_three_over_thirtytwo :
    smeftCoeffFromHolonomySkew = (3 : ℝ) / 32 := by
  simp [smeftCoeffFromHolonomySkew, fanoSecondOrderPhaseSkew_eq_three_over_eighty, gamma_eq_2_5]
  norm_num

/-- Higgs cubic operator OH coefficient from trilinear readout. -/
noncomputable def smeftCoeffOH : ℝ :=
  higgsTrilinearLambda3 / (8 * Real.pi ^ 2)

/-- W-Higgs operator from κ_W modifier. -/
noncomputable def smeftCoeffOW : ℝ :=
  kappaW * gamma_HQIV / 8

/-- Four-lepton operator from monogamy exclusion. -/
noncomputable def smeftCoeffOll : ℝ :=
  doubleMonogamyExclusionFactor * ckmSlotUS2

noncomputable def smeftDiscreteCoefficients : List SMEFTCoefficient :=
  [ ⟨.OH, smeftCoeffOH, "HiggsSelfCouplingReadout"⟩
  , ⟨.OW, smeftCoeffOW, "HiggsSelfCouplingReadout"⟩
  , ⟨.OQ1, smeftCoeffFromHolonomySkew, "FanoHolonomyOverlap"⟩
  , ⟨.Oll, smeftCoeffOll, "HepDecayReadout"⟩
  ]

structure SMEFTDiscreteExportCertificate where
  count : smeftDiscreteCoefficients.length = 4
  holonomy_coeff : smeftCoeffFromHolonomySkew = (3 : ℝ) / 32

theorem smeftDiscreteExportCertificate_holds : SMEFTDiscreteExportCertificate where
  count := rfl
  holonomy_coeff := smeftCoeffFromHolonomySkew_eq_three_over_thirtytwo

end Hqiv.Physics
