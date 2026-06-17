import Hqiv.Physics.StrongChannelEmissionScaffold
import Hqiv.Physics.HadronS7ConfinementReadout
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.HQIVNuclei
import Hqiv.Geometry.S7MetahorizonCasimir

/-!
# Strong-sector collider phenomenology discharge

Quantitative readouts derived from the proved emission scaffold (`StrongChannelEmissionScaffold`)
and the same zero-knob spine as nucleon binding.  Comparison targets (PETRA, PDG, lattice,
global PDF fits) enter only in Python witnesses — never as prediction inputs.

**Discharged here:**

* Non-abelian soft splitting ratio `C_A/C_F = 9/4` from the colour chart filter.
* One-loop `α_s(μ)` from `beta_3` and the lock-in `alpha_s_at_MZ` witness.
* PETRA structural observables: `R_{23}`, mean thrust, parton-shower step weights.
* Higgs–gluon fusion `σ` proxy, QGP `η/s`, glueball `0^{++}` / `2^{++}` masses, PDF gluon moment.

Python mirror: `scripts/hqiv_strong_sector_collider_discharge.py`.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry

/-!
## Scale inputs (comparison-layer anchors for running only)
-/

/-- PDG `M_Z` in MeV (comparison anchor for running; not a fit knob). -/
noncomputable def mZ_MeV : ℝ := 91187.6

/-- PETRA representative $\sqrt s$ in MeV (35 GeV). -/
noncomputable def petraSqrtS_MeV : ℝ := 35000

/-- LHC Higgs production scale proxy in MeV (125 GeV). -/
noncomputable def lhcHiggsScale_MeV : ℝ := 125000

/-!
## One-loop strong running from `beta_3`
-/

/-- Standard one-loop $\alpha_s(\mu)$ with HQIV `beta_3 = -7` (`(-\beta_3)` is the positive $\beta_0$). -/
noncomputable def alphaStrongRunningLO (alpha0 mu0 mu : ℝ) : ℝ :=
  alpha0 / (1 + (-beta_3) / (2 * Real.pi) * alpha0 * Real.log (mu / mu0))

theorem alphaStrongRunningLO_atMu0 (alpha0 mu0 : ℝ) (hμ0 : 0 < mu0) :
    alphaStrongRunningLO alpha0 mu0 mu0 = alpha0 := by
  unfold alphaStrongRunningLO
  simp [Real.log_one, hμ0.ne']

noncomputable def alphaStrongAtPETRA : ℝ :=
  alphaStrongRunningLO alpha_s_at_MZ mZ_MeV (petraSqrtS_MeV / 2)

noncomputable def alphaStrongAtHiggsScale : ℝ :=
  alphaStrongRunningLO alpha_s_at_MZ mZ_MeV lhcHiggsScale_MeV

/-!
## Non-abelian matrix-element coefficient from abelian kinetic + colour filter
-/

/-- Soft/collinear gluon emission weight ratio (adjoint/fundamental) from the chart filter. -/
noncomputable def nonAbelianSplittingFromFilter : ℝ :=
  colourCasimirAdjoint / colourCasimirFundamental 3

theorem nonAbelianSplittingFromFilter_eq_nine_fourths :
    nonAbelianSplittingFromFilter = (9 : ℝ) / 4 :=
  colourCasimirAdjoint_over_fundamental_three

theorem nonAbelianSplittingFromFilter_eq_cA_over_cF :
    nonAbelianSplittingFromFilter = colourCasimirAdjoint / colourCasimirFundamental 3 := rfl

/-!
## PETRA jets: $R_{23}$, thrust, parton-shower weights
-/

/-- LO $R_{23}$ discharge:
$1 + (\alpha_s/\pi)\,(C_A/N_c)\,(n_{\rm strong}/8)\,\ln(\sqrt s/M_Z)$. -/
noncomputable def petraR23Discharge (alpha_s_at_scale sqrt_s_MeV : ℝ) : ℝ :=
  1 + alpha_s_at_scale / Real.pi *
    (colourCasimirAdjoint / (colourNumColours : ℝ)) *
    ((strongOctonionComponents.card : ℝ) / 8) *
    Real.log (sqrt_s_MeV / mZ_MeV)

noncomputable def petraR23DischargeAtPETRA : ℝ :=
  petraR23Discharge alphaStrongAtPETRA petraSqrtS_MeV

/-- Mean thrust discharge: $1 - n_{\rm strong}\,\gamma\,\alpha_s/\pi$. -/
noncomputable def meanThrustDischarge (alpha_s_at_scale : ℝ) : ℝ :=
  1 - (strongOctonionComponents.card : ℝ) * gamma_HQIV * alpha_s_at_scale / Real.pi

noncomputable def meanThrustDischargeAtPETRA : ℝ :=
  meanThrustDischarge alphaStrongAtPETRA

/-- Parton-shower step weight after `s` sequential strong-channel emissions (same spine as binding). -/
noncomputable def partonShowerStepWeight
    (m : ℕ) (w : NetworkWeight) (k : So8Index) (s : ℕ) (c : ℝ := 1) : ℝ :=
  sequentialEmissionWeight m w k s c

theorem partonShowerStepWeight_zero
    (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ) :
    partonShowerStepWeight m w k 0 c = 1 :=
  sequentialEmissionWeight_zero m w k c

theorem partonShowerThreeJet_stepWeight_eq_sequential_one
    (m : ℕ) (w : NetworkWeight) (k : So8Index) (c : ℝ) :
    partonShowerStepWeight m w k (minStrongEmissionStepsBeyondDipole 3) c =
      sequentialEmissionWeight m w k 1 c := by
  rw [partonShowerStepWeight, minStrongEmissionStepsBeyondDipole_three]

/-!
## Higgs–gluon fusion proxy
-/

/-- Dimensionless $\sigma(ggH)$ proxy: $(\alpha_s/\pi)^2 (m_t/m_H)^2$ × strong-channel × triple budget. -/
noncomputable def ggHSigmaDimensionlessProxy (alpha_s m_top m_H : ℝ) : ℝ :=
  (alpha_s / Real.pi) ^ 2 * (m_top / m_H) ^ 2 *
    ((strongOctonionComponents.card : ℝ) / 8) *
    ((hadronIjkSortedTripleBudget : ℝ) / (colourNumColours : ℝ))

/-!
## QGP transport
-/

/-- $\eta/s$ discharge: $(4\pi)^{-1}\,C_A\,(n_{\rm strong}/8)\,/\,(2\gamma)$. -/
noncomputable def qgpEtaOverSDischarge : ℝ :=
  (1 / (4 * Real.pi)) * colourCasimirAdjoint * strongChannelFraction / (2 * gamma_HQIV)

theorem qgpEtaOverSDischarge_pos : 0 < qgpEtaOverSDischarge := by
  unfold qgpEtaOverSDischarge colourCasimirAdjoint
  rw [colourNumColours_eq_three, strongChannelFraction_eq_four_eighths, gamma_eq_2_5]
  positivity

theorem hadronS7WholeLaplaceRatio_one_zero_pos : 0 < hadronS7WholeLaplaceRatio 1 0 := by
  unfold hadronS7WholeLaplaceRatio hadronWholeExcitationIndex laplaceBeltramiEigenvalueS7
  norm_num

theorem hadronS7WholeModeWeight_one_zero_pos : 0 < hadronS7WholeModeWeight 1 0 := by
  rw [hadronS7WholeModeWeight]
  exact Real.sqrt_pos.mpr hadronS7WholeLaplaceRatio_one_zero_pos

theorem hadronIjkExcitationConfinementFactor_one_zero_pos :
    0 < hadronIjkExcitationConfinementFactor 1 0 := by
  unfold hadronIjkExcitationConfinementFactor hadronIjkSortedTripleBudget
  have hr := radialExcitationDeltaOperational_one_pos
  rw [orbitalExcitationDeltaOperational_zero]
  simp only [add_zero]
  have : 0 < 1 + (radialExcitationDeltaOperational 1 + 0) / derivedProtonMass / 9 := by
    have hinc : 0 < radialExcitationDeltaOperational 1 := hr
    have hp := derivedProtonMass_pos
    positivity
  simpa [div_eq_mul_inv] using this

/-!
## Glueball spectrum (pure strong-channel networks)
-/

/-- Ground $0^{++}$ glueball mass from triple-budget × $\gamma$ on the proton lock-in anchor. -/
noncomputable def glueball0ppMassMeV : ℝ :=
  derivedProtonMass * gamma_HQIV * ((hadronIjkSortedTripleBudget : ℝ) / 2)

/-- First excited $2^{++}$ glueball from whole-hadron $S^7$ + $f^{ijk}$ dressing at $(n,\ell)=(1,0)$. -/
noncomputable def glueball2ppMassMeV : ℝ :=
  hadronWholeS7IjkDressing derivedProtonMass 1 0

theorem glueball0ppMassMeV_pos : 0 < glueball0ppMassMeV := by
  unfold glueball0ppMassMeV hadronIjkSortedTripleBudget
  rw [gamma_eq_2_5]
  positivity [derivedProtonMass_pos]

theorem glueball2ppMassMeV_pos : 0 < glueball2ppMassMeV := by
  unfold glueball2ppMassMeV hadronWholeS7IjkDressing
  exact div_pos (mul_pos derivedProtonMass_pos hadronS7WholeModeWeight_one_zero_pos)
    hadronIjkExcitationConfinementFactor_one_zero_pos

/-!
## PDF gluon moment at shell `m`
-/

/-- PDF gluon first moment at $Q_0=M_Z$:
$\alpha_s(M_Z)\,C_F\,(n_{\rm strong}/8)/2$. -/
noncomputable def pdfGluonFirstMomentDischarge : ℝ :=
  alpha_s_at_MZ * colourCasimirFundamental 3 * strongChannelFraction / 2

/-- Absolute LO $\sigma(ggH)$ in pb from dimless proxy × electroweak scale (Python unit bridge). -/
noncomputable def ggHSigmaPbConversionGeV2ToPb : ℝ := 389379

/-- LO $\sigma(ggH)$ in pb with HEP ledger slots (comparison normalisation). -/
noncomputable def ggHSigmaPbLODischarge (m_top v_EW : ℝ) : ℝ :=
  (alphaStrongAtHiggsScale / Real.pi) ^ 2 * (m_top / v_EW) ^ 2 *
    ((strongOctonionComponents.card : ℝ) / 8) *
    ((hadronIjkSortedTripleBudget : ℝ) / (colourNumColours : ℝ)) *
    (gamma_HQIV / 8) * inclusiveBNLOLedgerFactor * ggHSigmaPbConversionGeV2ToPb

/-- NLO dress: LO × ledger × non-abelian splitting ratio. -/
noncomputable def ggHSigmaPbNLODischarge (m_top v_EW : ℝ) : ℝ :=
  ggHSigmaPbLODischarge m_top v_EW * nonAbelianSplittingFromFilter

/-!
## Bundled quantitative discharge certificate
-/

structure StrongSectorQuantitativeDischargeDischarged where
  nonabelian_splitting : nonAbelianSplittingFromFilter = (9 : ℝ) / 4
  beta3_running_anchor : beta_3 = -(11 : ℝ) / 3 * 3 + (2 : ℝ) / 3 * 6
  petra_threeJet_step : minStrongEmissionStepsBeyondDipole 3 = 1
  glueball0_pos : 0 < glueball0ppMassMeV
  glueball2_pos : 0 < glueball2ppMassMeV
  qgp_eta_pos : 0 < qgpEtaOverSDischarge

noncomputable def strongSectorQuantitativeDischargeDischarged : StrongSectorQuantitativeDischargeDischarged where
  nonabelian_splitting := nonAbelianSplittingFromFilter_eq_nine_fourths
  beta3_running_anchor := beta_3_eq_standardQcd_oneLoop_nc3_nf6
  petra_threeJet_step := petraThreeJet_requires_emissionStep
  glueball0_pos := glueball0ppMassMeV_pos
  glueball2_pos := glueball2ppMassMeV_pos
  qgp_eta_pos := qgpEtaOverSDischarge_pos

structure GluonCurvatureFullDischarge where
  phenomenology : GluonCurvaturePhenomenologyDischarged
  quantitative : StrongSectorQuantitativeDischargeDischarged

noncomputable def gluonCurvatureFullDischarge : GluonCurvatureFullDischarge where
  phenomenology := gluonCurvaturePhenomenologyDischarged
  quantitative := strongSectorQuantitativeDischargeDischarged

#check gluonCurvatureFullDischarge
#check petraR23DischargeAtPETRA
#check meanThrustDischargeAtPETRA
#check glueball0ppMassMeV
#check glueball2ppMassMeV
#check qgpEtaOverSDischarge
#check ggHSigmaDimensionlessProxy

end Hqiv.Physics
