import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.HepDecayChannelRouting
import Hqiv.Physics.SpineDischargeWeight
import Hqiv.Physics.ExcitedMassPanelReadout
import Hqiv.Physics.HepExtendedAnomalyDischarge

/-!
# Heavy-flavour anomaly discharge capstone

Classifies standard heavy-flavour tension classes against the finite three-ledger
readout already discharged in `HepDecayReadout`, `HepDecayChannelRouting`,
`SpineDischargeWeight`, `ExcitedMassPanelReadout`, and `HepExtendedAnomalyDischarge`.

Python mirror: `scripts/hqiv_hep_anomaly_discharge.py`.
-/

namespace Hqiv.Physics

/-! ## Anomaly class registry -/

/-- Standard heavy-flavour tension classes tracked by the discharge ledger. -/
inductive HepAnomalyClass where
  | formFactorExclusive
  | quarkoniumEMWidth
  | productionHierarchy
  | charmedBottomBaryonCompetition
  | ckmInclusiveExclusive
  | excitedSpectroscopy
  | lfuRatios
  | angularObservables
  | rareFCNC
  deriving DecidableEq, Repr, Inhabited

/-- Discharge status for each anomaly class. -/
inductive AnomalyDischargeStatus where
  | discharged
  | readoutOnly
  | outOfScope
  deriving DecidableEq, Repr, Inhabited

def anomalyDischargeStatus (c : HepAnomalyClass) : AnomalyDischargeStatus :=
  match c with
  | .formFactorExclusive | .quarkoniumEMWidth | .productionHierarchy
  | .charmedBottomBaryonCompetition | .ckmInclusiveExclusive | .excitedSpectroscopy
  | .lfuRatios | .angularObservables | .rareFCNC =>
    .discharged

def allHepAnomalyClasses : List HepAnomalyClass :=
  [.formFactorExclusive, .quarkoniumEMWidth, .productionHierarchy,
    .charmedBottomBaryonCompetition, .ckmInclusiveExclusive, .excitedSpectroscopy,
    .lfuRatios, .angularObservables, .rareFCNC]

theorem anomalyDischargeStatus_formFactorExclusive :
    anomalyDischargeStatus .formFactorExclusive = .discharged := rfl

theorem anomalyDischargeStatus_quarkoniumEMWidth :
    anomalyDischargeStatus .quarkoniumEMWidth = .discharged := rfl

theorem anomalyDischargeStatus_productionHierarchy :
    anomalyDischargeStatus .productionHierarchy = .discharged := rfl

theorem anomalyDischargeStatus_charmedBottomBaryonCompetition :
    anomalyDischargeStatus .charmedBottomBaryonCompetition = .discharged := rfl

theorem anomalyDischargeStatus_ckmInclusiveExclusive :
    anomalyDischargeStatus .ckmInclusiveExclusive = .discharged := rfl

theorem anomalyDischargeStatus_excitedSpectroscopy :
    anomalyDischargeStatus .excitedSpectroscopy = .discharged := rfl

theorem anomalyDischargeStatus_lfuRatios :
    anomalyDischargeStatus .lfuRatios = .discharged := rfl

theorem anomalyDischargeStatus_angularObservables :
    anomalyDischargeStatus .angularObservables = .discharged := rfl

theorem anomalyDischargeStatus_rareFCNC :
    anomalyDischargeStatus .rareFCNC = .discharged := rfl

theorem dischargedClasses_are_nine :
    (allHepAnomalyClasses.filter fun c => anomalyDischargeStatus c = .discharged).length = 9 := by
  native_decide

theorem readoutOnlyClasses_are_zero :
    (allHepAnomalyClasses.filter fun c => anomalyDischargeStatus c = .readoutOnly).length = 0 := by
  native_decide

theorem outOfScopeClasses_are_zero :
    (allHepAnomalyClasses.filter fun c => anomalyDischargeStatus c = .outOfScope).length = 0 := by
  native_decide

/-! ## Discharged witnesses -/

structure FormFactorExclusiveDischarged where
  topology_seed : openFlavourTopologySeedWeight = 1
  ckm_hierarchy : ckmSlotCB2 < ckmSlotCD2 ∧ ckmSlotCD2 < ckmSlotUS2
  branching_sum : ∀ (widths : List ℝ) (totalWidth : ℝ),
    totalWidth = widths.sum → totalWidth ≠ 0 → widths.sum / totalWidth = 1
  spine_lambda_c_PKpi :
    spineDischargeWeight .lambda_c .weak [.p, .K_minus, .pi_plus] = (84 : ℝ) / 11

noncomputable def formFactorExclusiveDischarged : FormFactorExclusiveDischarged where
  topology_seed := anomalyBlock_formFactorFreeExclusive_topologySeed
  ckm_hierarchy := anomalyBlock_formFactorFreeExclusive_ckmHierarchy
  branching_sum := anomalyBlock_formFactorFreeExclusive_branchingNormalization
  spine_lambda_c_PKpi := spineDischargeWeight_lambda_c_PKpi

structure QuarkoniumEMDischarged where
  em_contact : hiddenQuarkoniumEMContactFactor = (37 : ℝ) / 10
  em_pos : 0 < hiddenQuarkoniumEMContactFactor
  derived : QuarkoniumEMContactDerived

noncomputable def quarkoniumEMDischarged : QuarkoniumEMDischarged where
  em_contact := anomalyBlock_quarkoniumEMContact
  em_pos := hiddenQuarkoniumEMContactFactor_pos
  derived := quarkoniumEMContactDerived

structure ProductionHierarchyDischarged where
  open_bottom_lt_charm : openBottomProductionWeight < openCharmProductionWeight
  open_charm_weight : openCharmProductionWeight = (1 : ℝ) / 10
  open_bottom_weight : openBottomProductionWeight = (1 : ℝ) / 20
  cascade_factor : heavyQuarkoniumCascadeWeight = 2
  neutral_cascade : neutralLightPairCascadeWeight = (4 : ℝ) / 25
  hidden_bottom_jpsi_boost : hiddenBottomJpsiInclusiveBoost = (98 : ℝ) / 75
  collider_vacuum :
    ∀ referenceTesla, colliderCurvatureWidthFactor 0 referenceTesla 0 = 1
  upsilon_jpsi_pipi_cascade :
    let ds := [HepDecaySpecies.Jpsi, HepDecaySpecies.pi_plus, HepDecaySpecies.pi_minus]
    ds.head? = some HepDecaySpecies.Jpsi ∧ isNeutralLightCascade ds

noncomputable def productionHierarchyDischarged : ProductionHierarchyDischarged where
  open_bottom_lt_charm := anomalyBlock_productionHierarchy_openBottomLtCharm
  open_charm_weight := anomalyBlock_productionHierarchy_openCharmWeight
  open_bottom_weight := anomalyBlock_productionHierarchy_openBottomWeight
  cascade_factor := anomalyBlock_productionHierarchy_cascadeFactor
  neutral_cascade := anomalyBlock_productionHierarchy_neutralCascade
  hidden_bottom_jpsi_boost := anomalyBlock_productionHierarchy_hiddenBottomJpsiBoost
  collider_vacuum := anomalyBlock_productionHierarchy_colliderVacuum
  upsilon_jpsi_pipi_cascade := upsilonNeutralCascade_Jpsi_pipi

structure CharmedBottomBaryonDischarged where
  charmed_semileptonic : openFlavourContactWeight .charmedBaryonSemileptonicHadronic = (84 : ℝ) / 11
  charmed_double_monogamy : openFlavourContactWeight .charmedBaryonDoubleMonogamy = (42 : ℝ) / 5
  bottom_external : openFlavourContactWeight .bottomExternalWeak = (7 : ℝ) / 2
  spine_lambda_c : spineDischargeWeight .lambda_c .weak [.p, .K_minus, .pi_plus] = (84 : ℝ) / 11
  spine_Bplus : spineDischargeWeight .B_plus .weak [.D0, .pi_plus] = (7 : ℝ) / 2

noncomputable def charmedBottomBaryonDischarged : CharmedBottomBaryonDischarged where
  charmed_semileptonic := anomalyBlock_baryonCompetition_charmedSemileptonic
  charmed_double_monogamy := anomalyBlock_baryonCompetition_charmedDoubleMonogamy
  bottom_external := anomalyBlock_baryonCompetition_bottomExternal
  spine_lambda_c := spineDischargeWeight_lambda_c_PKpi
  spine_Bplus := spineDischargeWeight_Bplus_D0piplus

structure CkmInclusiveExclusiveDischarged where
  row_sums :
    ckmURowSlotSquares.sum = 1 ∧
      ckmCRowSlotSquares.sum = 1 ∧
      ckmTRowSlotSquares.sum = 1
  ledger_normalization :
    List.map List.sum ckmUnitaryLedgerSlotSquares = [1, 1, 1] ∧
      ([ (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotUS2 + ckmSlotCB2,
          ckmSlotUS2 + (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotCB2,
          ckmSlotCB2 + ckmSlotCB2 + (1 - 2 * ckmSlotCB2)
        ] = [1, 1, 1])
  slot_us : ckmSlotUS2 = (1 : ℝ) / 20
  cp_skew : cpOddFanoHolonomySkew = (3 : ℝ) / 80
  cp_skew_pos : 0 < cpOddFanoHolonomySkew
  inclusive_bnlo : inclusiveBNLOLedgerFactor = (21 : ℝ) / 20
  inclusive_bnlo_gt : 1 < inclusiveBNLOLedgerFactor
  finite_completion :
    openFlavourContactWeight .finiteChannelCompletion =
      gamma_HQIV * weakBridgeShape defaultBetaWeakBridge

noncomputable def ckmInclusiveExclusiveDischarged : CkmInclusiveExclusiveDischarged where
  row_sums := anomalyBlock_inclusiveExclusive_ckmRows
  ledger_normalization := anomalyBlock_inclusiveExclusive_ckmLedger
  slot_us := anomalyBlock_inclusiveExclusive_ckmSlotUS
  cp_skew := anomalyBlock_inclusiveExclusive_cpSkew
  cp_skew_pos := anomalyBlock_inclusiveExclusive_cpSkewPos
  inclusive_bnlo := anomalyBlock_inclusiveExclusive_inclusiveBNLO
  inclusive_bnlo_gt := anomalyBlock_inclusiveExclusive_inclusiveBNLOGt
  finite_completion := anomalyBlock_inclusiveExclusive_finiteChannelCompletion

structure ExcitedSpectroscopyDischarged where
  open_bottom_dressed :
    ∀ mProtonMeV mPiMeV,
      dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV =
        openBottomMesonMassMeV mProtonMeV mPiMeV * openBottomOutsideMassDressing
  hidden_bottom_dressed :
    ∀ mProtonMeV mPiMeV,
      dressedHiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV =
        hiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV * hiddenQuarkoniumOutsideMassDressing *
          hiddenBottomQuarkoniumGroundSlotFactor
  psi2S_radial :
    ∀ mPiMeV,
      dressedHiddenCharmQuarkoniumExcitedMassMeV mPiMeV 1 =
        dressedHiddenCharmQuarkoniumMassMeV mPiMeV * hiddenCharmQuarkoniumExcitationFactor 1 *
          hiddenCharmQuarkoniumRadialK1SlotFactor

noncomputable def excitedSpectroscopyDischarged : ExcitedSpectroscopyDischarged where
  open_bottom_dressed := excited_panel_openBottom_uses_dressed_readout
  hidden_bottom_dressed := excited_panel_hiddenBottom_uses_dressed_readout
  psi2S_radial := excited_panel_psi2S_uses_radial_factor

/-! ## Capstone bundle -/

structure HepAnomalyDischargeCertificate where
  form_factor : FormFactorExclusiveDischarged
  quarkonium_em : QuarkoniumEMDischarged
  production_hierarchy : ProductionHierarchyDischarged
  charmed_bottom_baryon : CharmedBottomBaryonDischarged
  ckm_inclusive_exclusive : CkmInclusiveExclusiveDischarged
  excited_spectroscopy : ExcitedSpectroscopyDischarged
  lfu_ratios : LfuRatiosDischarged
  angular_observables : AngularObservablesDischarged
  rare_fcnc : RareFcncDischarged
  spine_benchmark : HepDecaySpineBenchmarkDischarged

noncomputable def hepAnomalyDischargeCertificate : HepAnomalyDischargeCertificate where
  form_factor := formFactorExclusiveDischarged
  quarkonium_em := quarkoniumEMDischarged
  production_hierarchy := productionHierarchyDischarged
  charmed_bottom_baryon := charmedBottomBaryonDischarged
  ckm_inclusive_exclusive := ckmInclusiveExclusiveDischarged
  excited_spectroscopy := excitedSpectroscopyDischarged
  lfu_ratios := lfuRatiosDischarged
  angular_observables := angularObservablesDischarged
  rare_fcnc := rareFcncDischarged
  spine_benchmark := hepDecaySpineBenchmarkDischarged

theorem lfuRatios_is_discharged :
    anomalyDischargeStatus .lfuRatios = .discharged ∧ Nonempty LfuRatiosDischarged :=
  ⟨anomalyDischargeStatus_lfuRatios, ⟨lfuRatiosDischarged⟩⟩

theorem angularObservables_is_discharged :
    anomalyDischargeStatus .angularObservables = .discharged ∧
      Nonempty AngularObservablesDischarged :=
  ⟨anomalyDischargeStatus_angularObservables, ⟨angularObservablesDischarged⟩⟩

theorem rareFcnc_is_discharged :
    anomalyDischargeStatus .rareFCNC = .discharged ∧ Nonempty RareFcncDischarged :=
  ⟨anomalyDischargeStatus_rareFCNC, ⟨rareFcncDischarged⟩⟩

#check hepAnomalyDischargeCertificate
#check lfuRatios_is_discharged
#check angularObservables_is_discharged
#check rareFcnc_is_discharged
#check dischargedClasses_are_nine

end Hqiv.Physics
