import Hqiv.Physics.HepDecayChannelRouting

/-!
# Unified spine discharge weight (ledger observables → single product law)

Decay contact weights are not a species-specific ``if parent = K⁺ then …`` table.
Each edge carries **ledger observables** (integers from patch discharge).  A fixed
finite product of spine generators always has the form

`W = ∏_k g_k^{e_k(obs)}`

with `e_k = 0` ⟹ `g_k^0 = 1`.  Inactive slots are unity.

When no light-sector generator fires, the weight falls back to the certified
heavy-flavour routing kind (same numerals; heavy rows will be ported to
observable exponents later).

Python mirror: ``scripts/hqiv_spine_discharge_weight.py``.
-/

namespace Hqiv.Physics

/-! ## Ledger observables (measurement layer) -/

/-- Integer discharge observables for the unified spine product. -/
structure DischargeObservables where
  chargedIsospinOutlet : ℕ
  neutralIsospinOutlet : ℕ
  visibleLeptonWeak : ℕ
  lightPseudoscalarTag : ℕ
  monogamyCompetition : ℕ
  semileptonicHadronicCompetition : ℕ
  hiddenStrangenessKk : ℕ
  hiddenStrangenessLeak : ℕ
  deriving DecidableEq, Repr

def isChargedKaonWeakSpanParent (parent : HepDecaySpecies) : Bool :=
  parent == .K_plus || parent == .K_minus

def isVisibleLepton (s : HepDecaySpecies) : Bool :=
  s == .mu_plus || s == .mu_minus || s == .e_plus || s == .e_minus

def parentAdmitsSemileptonicWeak (parent : HepDecaySpecies) : Bool :=
  isLightKaon parent

def countLightPseudoscalarDaughters (ds : List HepDecaySpecies) : ℕ :=
  (ds.filter fun s => isLightHadronDischarge s && !s.isKaon).length

def dischargeObservables (parent : HepDecaySpecies) (channel : HepDecayChannel)
    (ds : List HepDecaySpecies) : DischargeObservables :=
  let chargedOutlet : ℕ :=
    if channel == .weak && isIsospinHalfWeakParent parent &&
        !ds.any isVisibleLepton &&
        !isNeutralIsovectorPionOnlyOutlet ds &&
        (ds.any HepDecaySpecies.isPion || ds.any isLightBaryonDaughter)
      then 1 else 0
  let neutralOutlet : ℕ :=
    if channel == .weak && isIsospinHalfWeakParent parent &&
        !ds.any isVisibleLepton &&
        isNeutralIsovectorPionOnlyOutlet ds
      then 1 else 0
  let visibleLepton : ℕ :=
    if channel == .weak && parentAdmitsSemileptonicWeak parent &&
        ds.length == 1 && ds.any isVisibleLepton
      then 1 else 0
  let monogamy : ℕ :=
    if channel == .weak && parentAdmitsSemileptonicWeak parent &&
        !ds.any isVisibleLepton && (chargedOutlet == 1 || neutralOutlet == 1)
      then 1 else 0
  let semileptonicHadronic : ℕ :=
    if monogamy == 1 && isChargedKaonWeakSpanParent parent then 1 else 0
  let psCount := countLightPseudoscalarDaughters ds
  let psTag : ℕ := if monogamy == 1 && psCount > 0 then 1 else 0
  let kk : ℕ :=
    if channel == .strong && parent == .phi &&
        ds.length == 2 && ds.all HepDecaySpecies.isKaon
      then 1 else 0
  let leak : ℕ :=
    if channel == .strong && parent == .phi &&
        ds.length == 3 && ds.all HepDecaySpecies.isPion
      then 1 else 0
  { chargedIsospinOutlet := chargedOutlet
    neutralIsospinOutlet := neutralOutlet
    visibleLeptonWeak := visibleLepton
    lightPseudoscalarTag := psTag
    monogamyCompetition := monogamy
    semileptonicHadronicCompetition := semileptonicHadronic
    hiddenStrangenessKk := kk
    hiddenStrangenessLeak := leak }

def lightSectorActive (o : DischargeObservables) : Bool :=
  o.chargedIsospinOutlet != 0 || o.neutralIsospinOutlet != 0 || o.visibleLeptonWeak != 0 ||
    o.monogamyCompetition != 0 || o.hiddenStrangenessKk != 0 || o.hiddenStrangenessLeak != 0

/-! ## Unified product law -/

/--
Light-sector spine product (meson default neutral slot).

Baryon neutral outlets use `spineLightProductForParent` in `spineDischargeWeight`.
-/
noncomputable def spineLightProduct (o : DischargeObservables) : ℝ :=
  (isospinHalfWeakContact ^ o.chargedIsospinOutlet) *
    (isospinHalfNeutralOutletContact ^ o.neutralIsospinOutlet) *
    (doubleMonogamyExclusionFactor ^ o.monogamyCompetition) *
    (chiralPseudoscalarFactor ^ o.lightPseudoscalarTag) *
    (lightHadronicSemileptonicCompetitionAperture ^ o.semileptonicHadronicCompetition) *
    (semileptonicNeutrinoChannelCompletion ^ o.visibleLeptonWeak) *
    (hiddenStrangenessKkRetentionContact ^ o.hiddenStrangenessKk) *
    (hiddenStrangenessVectorLeakContact ^ o.hiddenStrangenessLeak)

/-- Neutral isospin generator: baryon $\Delta I=1/2$ slot when monogamy inactive. -/
noncomputable def neutralOutletSpineGenerator (parent : HepDecaySpecies) (o : DischargeObservables) : ℝ :=
  if o.monogamyCompetition != 0 then isospinHalfNeutralOutletContact
  else if isLightStrangeBaryon parent && o.neutralIsospinOutlet != 0 then
    lightBaryonNeutralIsospinOutletContact
  else isospinHalfNeutralOutletContact

/-- Visible-lepton spine generator: kaon semileptonic dilution vs generic channel completion. -/
noncomputable def visibleLeptonSpineGenerator (parent : HepDecaySpecies) : ℝ :=
  if parent == .K_plus || parent == .K_minus then lightKaonSemileptonicNeutrinoCompletion
  else semileptonicNeutrinoChannelCompletion

/-- Parent-aware light spine product (baryon neutral isospin correction). -/
noncomputable def spineLightProductForParent (parent : HepDecaySpecies) (o : DischargeObservables) : ℝ :=
  (isospinHalfWeakContact ^ o.chargedIsospinOutlet) *
    (neutralOutletSpineGenerator parent o ^ o.neutralIsospinOutlet) *
    (doubleMonogamyExclusionFactor ^ o.monogamyCompetition) *
    (chiralPseudoscalarFactor ^ o.lightPseudoscalarTag) *
    (lightHadronicSemileptonicCompetitionAperture ^ o.semileptonicHadronicCompetition) *
    (visibleLeptonSpineGenerator parent ^ o.visibleLeptonWeak) *
    (hiddenStrangenessKkRetentionContact ^ o.hiddenStrangenessKk) *
    (hiddenStrangenessVectorLeakContact ^ o.hiddenStrangenessLeak)

/--
Unified spine discharge contact weight for topology seeds and certificates.
-/
noncomputable def spineDischargeWeight (parent : HepDecaySpecies) (channel : HepDecayChannel)
    (ds : List HepDecaySpecies) : ℝ :=
  let o := dischargeObservables parent channel ds
  if lightSectorActive o then spineLightProductForParent parent o
  else openFlavourContactWeight (openFlavourContactKind parent channel ds)

theorem spineDischargeWeight_eq_product_when_light_active
    (parent : HepDecaySpecies) (channel : HepDecayChannel) (ds : List HepDecaySpecies)
    (h : lightSectorActive (dischargeObservables parent channel ds) = true) :
    spineDischargeWeight parent channel ds =
      spineLightProductForParent parent (dischargeObservables parent channel ds) := by
  unfold spineDischargeWeight
  simp [h]

theorem spineDischargeWeight_eq_spineLightProductForParent_when_light_active
    (parent : HepDecaySpecies) (channel : HepDecayChannel) (ds : List HepDecaySpecies)
    (h : lightSectorActive (dischargeObservables parent channel ds) = true) :
    spineDischargeWeight parent channel ds =
      spineLightProductForParent parent (dischargeObservables parent channel ds) :=
  spineDischargeWeight_eq_product_when_light_active parent channel ds h

theorem spineDischargeWeight_eq_openFlavourContactWeight_when_inactive
    (parent : HepDecaySpecies) (channel : HepDecayChannel) (ds : List HepDecaySpecies)
    (h : lightSectorActive (dischargeObservables parent channel ds) = false) :
    spineDischargeWeight parent channel ds =
      openFlavourContactWeight (openFlavourContactKind parent channel ds) := by
  unfold spineDischargeWeight
  simp [h]

/-! ## Benchmark reconciliation (product law = routing kind on certified rows) -/

private theorem dischargeObservables_Kplus_mu :
    dischargeObservables .K_plus .weak [.mu_plus] =
      { chargedIsospinOutlet := 0, neutralIsospinOutlet := 0, visibleLeptonWeak := 1,
        lightPseudoscalarTag := 0, monogamyCompetition := 0, semileptonicHadronicCompetition := 0,
        hiddenStrangenessKk := 0, hiddenStrangenessLeak := 0 } := by decide

private theorem dischargeObservables_Kplus_piplus :
    dischargeObservables .K_plus .weak [.pi_plus] =
      { chargedIsospinOutlet := 1, neutralIsospinOutlet := 0, visibleLeptonWeak := 0,
        lightPseudoscalarTag := 1, monogamyCompetition := 1, semileptonicHadronicCompetition := 1,
        hiddenStrangenessKk := 0, hiddenStrangenessLeak := 0 } := by decide

private theorem dischargeObservables_lambda_piminus :
    dischargeObservables .lambda .weak [.p, .pi_minus] =
      { chargedIsospinOutlet := 1, neutralIsospinOutlet := 0, visibleLeptonWeak := 0,
        lightPseudoscalarTag := 0, monogamyCompetition := 0, semileptonicHadronicCompetition := 0,
        hiddenStrangenessKk := 0, hiddenStrangenessLeak := 0 } := by decide

private theorem dischargeObservables_lambda_npi0 :
    dischargeObservables .lambda .weak [.n, .pi_zero] =
      { chargedIsospinOutlet := 0, neutralIsospinOutlet := 1, visibleLeptonWeak := 0,
        lightPseudoscalarTag := 0, monogamyCompetition := 0, semileptonicHadronicCompetition := 0,
        hiddenStrangenessKk := 0, hiddenStrangenessLeak := 0 } := by decide

private theorem dischargeObservables_phi_KK :
    dischargeObservables .phi .strong [.K_plus, .K_minus] =
      { chargedIsospinOutlet := 0, neutralIsospinOutlet := 0, visibleLeptonWeak := 0,
        lightPseudoscalarTag := 0, monogamyCompetition := 0, semileptonicHadronicCompetition := 0,
        hiddenStrangenessKk := 1, hiddenStrangenessLeak := 0 } := by decide

private theorem dischargeObservables_phi_three_pion :
    dischargeObservables .phi .strong [.pi_plus, .pi_minus, .pi_zero] =
      { chargedIsospinOutlet := 0, neutralIsospinOutlet := 0, visibleLeptonWeak := 0,
        lightPseudoscalarTag := 0, monogamyCompetition := 0, semileptonicHadronicCompetition := 0,
        hiddenStrangenessKk := 0, hiddenStrangenessLeak := 1 } := by decide

theorem spineDischargeWeight_eq_routing_Kplus_mu :
    spineDischargeWeight .K_plus .weak [.mu_plus] =
      openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.mu_plus]) := by
  have hact : lightSectorActive (dischargeObservables .K_plus .weak [.mu_plus]) = true := by
    rw [dischargeObservables_Kplus_mu]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact]
  rw [dischargeObservables_Kplus_mu]
  unfold spineLightProductForParent visibleLeptonSpineGenerator neutralOutletSpineGenerator
  rw [if_pos (by decide : (HepDecaySpecies.K_plus == HepDecaySpecies.K_plus ||
      HepDecaySpecies.K_plus == HepDecaySpecies.K_minus) = true)]
  simp only [pow_zero, one_mul, mul_one, pow_one]
  rw [lightKaonSemileptonicNeutrinoCompletion_eq_209_over_1800,
    contactWeight_Kplus_muplus_eq_209_over_1800]

theorem spineDischargeWeight_eq_routing_Kplus_piplus :
    spineDischargeWeight .K_plus .weak [.pi_plus] =
      openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.pi_plus]) := by
  have hact : lightSectorActive (dischargeObservables .K_plus .weak [.pi_plus]) = true := by
    rw [dischargeObservables_Kplus_piplus]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact]
  simp only [spineLightProductForParent, dischargeObservables_Kplus_piplus, pow_one, mul_one,
    pow_zero, neutralOutletSpineGenerator]
  rw [isospinHalfWeakContact_eq_seven_fifths, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive,
    chiralPseudoscalarFactor_eq_four_ninths_squared,
    lightHadronicSemileptonicCompetitionAperture_eq_thirteen_tenths,
    contactWeight_Kplus_piplus_eq_30576_over_101250]
  norm_num

theorem spineDischargeWeight_eq_routing_lambda_piminus :
    spineDischargeWeight .lambda .weak [.p, .pi_minus] =
      openFlavourContactWeight (openFlavourContactKind .lambda .weak [.p, .pi_minus]) := by
  have hact : lightSectorActive (dischargeObservables .lambda .weak [.p, .pi_minus]) = true := by
    rw [dischargeObservables_lambda_piminus]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact]
  simp only [spineLightProductForParent, dischargeObservables_lambda_piminus, pow_one, pow_zero, one_mul, mul_one]
  rw [isospinHalfWeakContact_eq_seven_fifths, ← contactWeight_lambda_piminus_eq_seven_fifths]

theorem spineDischargeWeight_eq_routing_lambda_npi0 :
    spineDischargeWeight .lambda .weak [.n, .pi_zero] =
      openFlavourContactWeight (openFlavourContactKind .lambda .weak [.n, .pi_zero]) := by
  have hact : lightSectorActive (dischargeObservables .lambda .weak [.n, .pi_zero]) = true := by
    rw [dischargeObservables_lambda_npi0]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact,
    contactWeight_lambda_npi0_eq_eighteen_twenty_thirds]
  unfold spineLightProductForParent neutralOutletSpineGenerator
  rw [dischargeObservables_lambda_npi0]
  simp only [isLightStrangeBaryon, pow_one, pow_zero, one_mul, mul_one]
  exact lightBaryonNeutralIsospinOutletContact_eq_eighteen_twenty_thirds

theorem spineDischargeWeight_eq_routing_phi_KK :
    spineDischargeWeight .phi .strong [.K_plus, .K_minus] =
      openFlavourContactWeight (openFlavourContactKind .phi .strong [.K_plus, .K_minus]) := by
  have hact : lightSectorActive (dischargeObservables .phi .strong [.K_plus, .K_minus]) = true := by
    rw [dischargeObservables_phi_KK]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact]
  simp only [spineLightProductForParent, dischargeObservables_phi_KK, pow_one, pow_zero, one_mul, mul_one,
    neutralOutletSpineGenerator]
  rw [hiddenStrangenessKkRetentionContact_eq_twentyone_twentyfive,
    ← contactWeight_phi_KK_retention_eq_twentyone_twentyfive]

theorem spineDischargeWeight_eq_routing_phi_three_pion :
    spineDischargeWeight .phi .strong [.pi_plus, .pi_minus, .pi_zero] =
      openFlavourContactWeight
        (openFlavourContactKind .phi .strong [.pi_plus, .pi_minus, .pi_zero]) := by
  have hact : lightSectorActive
      (dischargeObservables .phi .strong [.pi_plus, .pi_minus, .pi_zero]) = true := by
    rw [dischargeObservables_phi_three_pion]; decide
  rw [spineDischargeWeight_eq_product_when_light_active _ _ _ hact]
  simp only [spineLightProductForParent, dischargeObservables_phi_three_pion, pow_one, pow_zero, one_mul, mul_one,
    neutralOutletSpineGenerator]
  rw [hiddenStrangenessVectorLeakContact_eq_four_twentyfive, routing_phi_strong_three_pion_leak,
    ← openFlavourContactWeight_hiddenStrangenessVectorLeak]

theorem spineDischargeWeight_eq_routing_B0 :
    spineDischargeWeight .B0 .weak [.D0, .pi_zero] =
      openFlavourContactWeight (openFlavourContactKind .B0 .weak [.D0, .pi_zero]) := by
  have hinact : lightSectorActive (dischargeObservables .B0 .weak [.D0, .pi_zero]) = false := by
    decide
  unfold spineDischargeWeight
  simp [hinact]

theorem spineDischargeWeight_Kplus_muplus :
    spineDischargeWeight .K_plus .weak [.mu_plus] = (209 : ℝ) / 1800 := by
  rw [spineDischargeWeight_eq_routing_Kplus_mu, contactWeight_Kplus_muplus_eq_209_over_1800]

theorem spineDischargeWeight_Kplus_piplus :
    spineDischargeWeight .K_plus .weak [.pi_plus] = (30576 : ℝ) / 101250 := by
  rw [spineDischargeWeight_eq_routing_Kplus_piplus, contactWeight_Kplus_piplus_eq_30576_over_101250]

theorem spineDischargeWeight_lambda_piminus :
    spineDischargeWeight .lambda .weak [.p, .pi_minus] = (7 : ℝ) / 5 := by
  rw [spineDischargeWeight_eq_routing_lambda_piminus, contactWeight_lambda_piminus_eq_seven_fifths]

theorem spineDischargeWeight_lambda_npi0 :
    spineDischargeWeight .lambda .weak [.n, .pi_zero] = (18 : ℝ) / 23 := by
  rw [spineDischargeWeight_eq_routing_lambda_npi0, contactWeight_lambda_npi0_eq_eighteen_twenty_thirds]

theorem spineDischargeWeight_phi_KK :
    spineDischargeWeight .phi .strong [.K_plus, .K_minus] = (21 : ℝ) / 25 := by
  rw [spineDischargeWeight_eq_routing_phi_KK, contactWeight_phi_KK_retention_eq_twentyone_twentyfive]

theorem spineDischargeWeight_phi_three_pion_leak :
    spineDischargeWeight .phi .strong [.pi_plus, .pi_minus, .pi_zero] = (4 : ℝ) / 25 := by
  rw [spineDischargeWeight_eq_routing_phi_three_pion, routing_phi_strong_three_pion_leak,
    openFlavourContactWeight_hiddenStrangenessVectorLeak]

theorem spineDischargeWeight_B0_D0pi0 :
    spineDischargeWeight .B0 .weak [.D0, .pi_zero] = (3 : ℝ) / 2 := by
  rw [spineDischargeWeight_eq_routing_B0, routing_B0_D0pi0_bottomNeutralSpectator,
    openFlavourContactWeight_bottomNeutralSpectator]

/-! ## Heavy-flavour spine reconciliation (routing fallback = product law) -/

theorem spineDischargeWeight_eq_routing_Dplus_mu :
    spineDischargeWeight .D_plus .weak [.mu_plus] =
      openFlavourContactWeight (openFlavourContactKind .D_plus .weak [.mu_plus]) := by
  have hinact : lightSectorActive (dischargeObservables .D_plus .weak [.mu_plus]) = false := by
    decide
  unfold spineDischargeWeight
  simp [hinact]

theorem spineDischargeWeight_eq_routing_lambda_c_PKpi :
    spineDischargeWeight .lambda_c .weak [.p, .K_minus, .pi_plus] =
      openFlavourContactWeight
        (openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_plus]) := by
  have hinact :
      lightSectorActive (dischargeObservables .lambda_c .weak [.p, .K_minus, .pi_plus]) = false := by
    decide
  unfold spineDischargeWeight
  simp [hinact]

theorem spineDischargeWeight_eq_routing_Bplus_D0piplus :
    spineDischargeWeight .B_plus .weak [.D0, .pi_plus] =
      openFlavourContactWeight (openFlavourContactKind .B_plus .weak [.D0, .pi_plus]) := by
  have hinact : lightSectorActive (dischargeObservables .B_plus .weak [.D0, .pi_plus]) = false := by
    decide
  unfold spineDischargeWeight
  simp [hinact]

theorem spineDischargeWeight_eq_routing_Bs_DsK :
    spineDischargeWeight .Bs .weak [.Ds_plus, .K_minus] =
      openFlavourContactWeight (openFlavourContactKind .Bs .weak [.Ds_plus, .K_minus]) := by
  have hinact : lightSectorActive (dischargeObservables .Bs .weak [.Ds_plus, .K_minus]) = false := by
    decide
  unfold spineDischargeWeight
  simp [hinact]

theorem spineDischargeWeight_Dplus_muplus :
    spineDischargeWeight .D_plus .weak [.mu_plus] = (2 : ℝ) / 9 := by
  rw [spineDischargeWeight_eq_routing_Dplus_mu, contactWeight_Dplus_muplus_eq_two_ninths]

theorem spineDischargeWeight_lambda_c_PKpi :
    spineDischargeWeight .lambda_c .weak [.p, .K_minus, .pi_plus] = (84 : ℝ) / 11 := by
  rw [spineDischargeWeight_eq_routing_lambda_c_PKpi, contactWeight_lambda_c_PKpi_eq_eightyfour_elevenths]

theorem spineDischargeWeight_Bplus_D0piplus :
    spineDischargeWeight .B_plus .weak [.D0, .pi_plus] = (7 : ℝ) / 2 := by
  rw [spineDischargeWeight_eq_routing_Bplus_D0piplus, contactWeight_Bplus_D0piplus_eq_seven_halves]

theorem spineDischargeWeight_Bs_DsK :
    spineDischargeWeight .Bs .weak [.Ds_plus, .K_minus] = (25 : ℝ) / 4 := by
  rw [spineDischargeWeight_eq_routing_Bs_DsK, contactWeight_Bs_DsK_eq_twentyfive_fourths]

/-! ## Benchmark discharge bundle (spine + routing reconciliation) -/

structure HepDecaySpineBenchmarkDischarged where
  hidden_quarkonium_em : hiddenQuarkoniumEMContactFactor = (37 : ℝ) / 10
  branching_sum : ∀ (widths : List ℝ) (totalWidth : ℝ),
    totalWidth = widths.sum → totalWidth ≠ 0 → widths.sum / totalWidth = 1
  spine_Kplus_piplus : spineDischargeWeight .K_plus .weak [.pi_plus] = (30576 : ℝ) / 101250
  spine_B0_D0pi0 : spineDischargeWeight .B0 .weak [.D0, .pi_zero] = (3 : ℝ) / 2
  spine_Dplus_mu : spineDischargeWeight .D_plus .weak [.mu_plus] = (2 : ℝ) / 9
  spine_lambda_c_PKpi : spineDischargeWeight .lambda_c .weak [.p, .K_minus, .pi_plus] = (84 : ℝ) / 11
  spine_Bplus_D0pi : spineDischargeWeight .B_plus .weak [.D0, .pi_plus] = (7 : ℝ) / 2
  spine_Bs_DsK : spineDischargeWeight .Bs .weak [.Ds_plus, .K_minus] = (25 : ℝ) / 4

noncomputable def hepDecaySpineBenchmarkDischarged : HepDecaySpineBenchmarkDischarged where
  hidden_quarkonium_em := hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths
  branching_sum := branchingRatios_sum_one
  spine_Kplus_piplus := spineDischargeWeight_Kplus_piplus
  spine_B0_D0pi0 := spineDischargeWeight_B0_D0pi0
  spine_Dplus_mu := spineDischargeWeight_Dplus_muplus
  spine_lambda_c_PKpi := spineDischargeWeight_lambda_c_PKpi
  spine_Bplus_D0pi := spineDischargeWeight_Bplus_D0piplus
  spine_Bs_DsK := spineDischargeWeight_Bs_DsK

/-- On Λ weak hadronic rows the monogamy exponent vanishes: plain isospin slot. -/
theorem dischargeObservables_lambda_piminus_monogamy_zero :
    (dischargeObservables .lambda .weak [.p, .pi_minus]).monogamyCompetition = 0 := by
  decide

#check hepDecaySpineBenchmarkDischarged

end Hqiv.Physics
