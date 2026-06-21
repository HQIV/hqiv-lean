import Hqiv.Physics.SpineDischargeWeight

/-!
# Uniqueness of the light-sector spine discharge product

**Scope (honest).**  This does not prove that HQIV axioms alone fix PDG branching.  It proves:

1. **Factorization uniqueness:** any `W : DischargeObservables → ℝ` that multiplies the eight
   canonical spine slots (inactive = 1, active = generator) equals `spineLightProduct`.
2. **Generator registry:** those slot values are the proved γ-rationals from `HepDecayReadout`.
3. **Certificate separation:** distinct certified K⁺ weak rows carry distinct observable vectors.
4. **Coupling lemmas** on concrete benchmark edges (mutual exclusion / monogamy linkage).

Heavy-flavour fallback routing is unchanged.
-/

namespace Hqiv.Physics

/-! ## Factorized form (competitor-law target) -/

noncomputable def spineLightProductFactorized (o : DischargeObservables) : ℝ :=
  (isospinHalfWeakContact ^ o.chargedIsospinOutlet) *
    (isospinHalfNeutralOutletContact ^ o.neutralIsospinOutlet) *
    (doubleMonogamyExclusionFactor ^ o.monogamyCompetition) *
    (chiralPseudoscalarFactor ^ o.lightPseudoscalarTag) *
    (lightHadronicSemileptonicCompetitionAperture ^ o.semileptonicHadronicCompetition) *
    (semileptonicNeutrinoChannelCompletion ^ o.visibleLeptonWeak) *
    (hiddenStrangenessKkRetentionContact ^ o.hiddenStrangenessKk) *
    (hiddenStrangenessVectorLeakContact ^ o.hiddenStrangenessLeak)

theorem spineLightProduct_eq_factorized (o : DischargeObservables) :
    spineLightProduct o = spineLightProductFactorized o := rfl

/-! ## Slot registry -/

inductive SpineLightSlot where
  | chargedIsospin
  | neutralIsospin
  | monogamy
  | chiralPseudoscalar
  | semileptonicHadronic
  | semileptonicNeutrino
  | hiddenStrangenessKk
  | hiddenStrangenessLeak
  deriving DecidableEq, Repr, Inhabited

def allSpineLightSlots : List SpineLightSlot :=
  [.chargedIsospin, .neutralIsospin, .monogamy, .chiralPseudoscalar,
    .semileptonicHadronic, .semileptonicNeutrino, .hiddenStrangenessKk, .hiddenStrangenessLeak]

noncomputable def spineLightSlotExponent (s : SpineLightSlot) (o : DischargeObservables) : ℕ :=
  match s with
  | .chargedIsospin => o.chargedIsospinOutlet
  | .neutralIsospin => o.neutralIsospinOutlet
  | .monogamy => o.monogamyCompetition
  | .chiralPseudoscalar => o.lightPseudoscalarTag
  | .semileptonicHadronic => o.semileptonicHadronicCompetition
  | .semileptonicNeutrino => o.visibleLeptonWeak
  | .hiddenStrangenessKk => o.hiddenStrangenessKk
  | .hiddenStrangenessLeak => o.hiddenStrangenessLeak

noncomputable def spineLightSlotGenerator (s : SpineLightSlot) : ℝ :=
  match s with
  | .chargedIsospin => isospinHalfWeakContact
  | .neutralIsospin => isospinHalfNeutralOutletContact
  | .monogamy => doubleMonogamyExclusionFactor
  | .chiralPseudoscalar => chiralPseudoscalarFactor
  | .semileptonicHadronic => lightHadronicSemileptonicCompetitionAperture
  | .semileptonicNeutrino => semileptonicNeutrinoChannelCompletion
  | .hiddenStrangenessKk => hiddenStrangenessKkRetentionContact
  | .hiddenStrangenessLeak => hiddenStrangenessVectorLeakContact

noncomputable def spineLightProductFromSlots (o : DischargeObservables) : ℝ :=
  (allSpineLightSlots.map fun s => spineLightSlotGenerator s ^ spineLightSlotExponent s o).prod

theorem spineLightProductFactorized_eq_slot_product (o : DischargeObservables) :
    spineLightProductFactorized o = spineLightProductFromSlots o := by
  unfold spineLightProductFactorized spineLightProductFromSlots
  simp only [allSpineLightSlots, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    one_mul, spineLightSlotExponent, spineLightSlotGenerator]
  ring_nf

theorem spineLightProduct_eq_slot_product (o : DischargeObservables) :
    spineLightProduct o = spineLightProductFromSlots o := by
  rw [spineLightProduct_eq_factorized, spineLightProductFactorized_eq_slot_product]

/-! ## Uniqueness of factorizing competitor laws -/

/--
A competitor law satisfies **spine factorization** when it equals the canonical slot product
on every observable pattern (inactive exponent ⟹ factor 1, active ⟹ `g_k^{e_k}`).
-/
def SatisfiesSpineFactorization (W : DischargeObservables → ℝ) : Prop :=
  ∀ o, W o = spineLightProductFactorized o

theorem spineLightProduct_satisfies_factorization :
    SatisfiesSpineFactorization spineLightProduct := by
  intro o
  simpa using (spineLightProduct_eq_factorized o).symm

theorem spineLightProduct_unique_factorization {W : DischargeObservables → ℝ}
    (h : SatisfiesSpineFactorization W) (o : DischargeObservables) :
    W o = spineLightProduct o := by
  rw [h o, spineLightProduct_eq_factorized o]

theorem spineLightProduct_unique_factorization_fn {W : DischargeObservables → ℝ}
    (h : SatisfiesSpineFactorization W) : W = spineLightProduct := by
  funext o
  exact spineLightProduct_unique_factorization h o

/-! ## Canonical γ-spine generator values (no free parameters in slots) -/

theorem spineLightSlotGenerators_are_gamma_rationals :
    spineLightSlotGenerator .chargedIsospin = (7 : ℝ) / 5 ∧
      spineLightSlotGenerator .neutralIsospin = (3 : ℝ) / 5 ∧
        spineLightSlotGenerator .monogamy = (21 : ℝ) / 25 ∧
          spineLightSlotGenerator .chiralPseudoscalar = ((4 : ℝ) / 9) ^ 2 ∧
            spineLightSlotGenerator .semileptonicHadronic = (13 : ℝ) / 10 ∧
            spineLightSlotGenerator .semileptonicNeutrino = (11 : ℝ) / 90 ∧
              spineLightSlotGenerator .hiddenStrangenessKk = (21 : ℝ) / 25 ∧
                spineLightSlotGenerator .hiddenStrangenessLeak = (4 : ℝ) / 25 := by
  constructor
  · exact isospinHalfWeakContact_eq_seven_fifths
  constructor
  · exact isospinHalfNeutralOutletContact_eq_three_fifths
  constructor
  · exact doubleMonogamyExclusionFactor_eq_twentyone_twentyfive
  constructor
  · exact chiralPseudoscalarFactor_eq_four_ninths_squared
  constructor
  · exact lightHadronicSemileptonicCompetitionAperture_eq_thirteen_tenths
  constructor
  · exact semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths
  constructor
  · exact hiddenStrangenessKkRetentionContact_eq_twentyone_twentyfive
  · exact hiddenStrangenessVectorLeakContact_eq_four_twentyfive

/-! ## Certificate coupling / separation (benchmark rows) -/

theorem dischargeObservables_Kplus_piplus_charged_not_neutral :
    (dischargeObservables .K_plus .weak [.pi_plus]).chargedIsospinOutlet = 1 ∧
      (dischargeObservables .K_plus .weak [.pi_plus]).neutralIsospinOutlet = 0 := by
  native_decide

theorem dischargeObservables_Kplus_mu_no_hadronic_isospin :
    (dischargeObservables .K_plus .weak [.mu_plus]).visibleLeptonWeak = 1 ∧
      (dischargeObservables .K_plus .weak [.mu_plus]).chargedIsospinOutlet = 0 ∧
        (dischargeObservables .K_plus .weak [.mu_plus]).neutralIsospinOutlet = 0 := by
  native_decide

theorem dischargeObservables_lambda_piminus_no_monogamy :
    (dischargeObservables .lambda .weak [.p, .pi_minus]).monogamyCompetition = 0 := by
  native_decide

theorem dischargeObservables_phi_KK_not_leak :
    (dischargeObservables .phi .strong [.K_plus, .K_minus]).hiddenStrangenessKk = 1 ∧
      (dischargeObservables .phi .strong [.K_plus, .K_minus]).hiddenStrangenessLeak = 0 := by
  native_decide

theorem dischargeObservables_injective_Kplus_weak_pi :
    dischargeObservables .K_plus .weak [.pi_plus] ≠
      dischargeObservables .K_plus .weak [.mu_plus] := by
  native_decide

theorem dischargeObservables_injective_Kplus_weak_mu_vs_pi0 :
    dischargeObservables .K_plus .weak [.mu_plus] ≠
      dischargeObservables .K_plus .weak [.pi_zero] := by
  native_decide

/--
On any light-active edge, a factorizing competitor law agreeing with spine slot values
must match `spineDischargeWeight`.

Kaon visible-lepton rows use `lightKaonSemileptonicNeutrinoCompletion` in routing/spine
(excluded by `hkaonVis`); generic semileptonic slot remains `semileptonicNeutrinoChannelCompletion`.
-/
theorem spineDischargeWeight_unique_light_factorizing
    (W : DischargeObservables → ℝ) (h : SatisfiesSpineFactorization W)
    (parent : HepDecaySpecies) (channel : HepDecayChannel) (ds : List HepDecaySpecies)
    (hact : lightSectorActive (dischargeObservables parent channel ds) = true)
    (hbar : ¬ (isLightStrangeBaryon parent ∧
        (dischargeObservables parent channel ds).neutralIsospinOutlet ≠ 0 ∧
          (dischargeObservables parent channel ds).monogamyCompetition = 0))
    (hkaonVis : ¬ (parentAdmitsSemileptonicWeak parent = true ∧
        (dischargeObservables parent channel ds).visibleLeptonWeak ≠ 0 ∧
          (parent == .K_plus || parent == .K_minus) = true)) :
    W (dischargeObservables parent channel ds) =
      spineDischargeWeight parent channel ds := by
  let o := dischargeObservables parent channel ds
  have hgen : neutralOutletSpineGenerator parent o = isospinHalfNeutralOutletContact := by
    unfold neutralOutletSpineGenerator
    rcases hbar with hbar
    by_cases hm : o.monogamyCompetition ≠ 0
    · simp [hm]
    · simp [hm]
      by_cases hn : o.neutralIsospinOutlet ≠ 0
      · have hls : ¬ isLightStrangeBaryon parent := by
          intro hls
          have hm0 : o.monogamyCompetition = 0 := by omega
          exact hbar ⟨hls, hn, hm0⟩
        simp [hn, hls]
      · simp [hn]
  have hvisgen :
      visibleLeptonSpineGenerator parent ^ o.visibleLeptonWeak =
        semileptonicNeutrinoChannelCompletion ^ o.visibleLeptonWeak := by
    by_cases hv : o.visibleLeptonWeak = 0
    · simp [hv]
    · have hvis0 : o.visibleLeptonWeak ≠ 0 := by omega
      unfold visibleLeptonSpineGenerator
      split_ifs with hk
      · exfalso
        have hvis0' : o.visibleLeptonWeak ≠ 0 := hvis0
        rcases Decidable.eq_or_ne parent .K_plus with hp' | hp'
        · subst hp'
          exact hkaonVis (And.intro (show parentAdmitsSemileptonicWeak HepDecaySpecies.K_plus = true by decide)
            (And.intro hvis0' (show (HepDecaySpecies.K_plus == HepDecaySpecies.K_plus ||
                HepDecaySpecies.K_plus == HepDecaySpecies.K_minus) = true by decide)))
        · rcases Decidable.eq_or_ne parent .K_minus with hm' | hm'
          · subst hm'
            exact hkaonVis (And.intro (show parentAdmitsSemileptonicWeak HepDecaySpecies.K_minus = true by decide)
              (And.intro hvis0' (show (HepDecaySpecies.K_minus == HepDecaySpecies.K_plus ||
                  HepDecaySpecies.K_minus == HepDecaySpecies.K_minus) = true by decide)))
          · simpa [hp', hm'] using hk
      · simp [hvis0, pow_one]
  have heq : spineLightProductForParent parent o = spineLightProduct o := by
    unfold spineLightProductForParent spineLightProduct
    by_cases hz : o.neutralIsospinOutlet = 0
    · simp only [hz, pow_zero, one_mul, hvisgen]
    · have hzpos : o.neutralIsospinOutlet ≠ 0 := by omega
      simp only [hgen, hzpos, pow_one, hvisgen]
  rw [spineDischargeWeight_eq_product_when_light_active parent channel ds hact]
  exact (spineLightProduct_unique_factorization h o).trans heq.symm

end Hqiv.Physics
