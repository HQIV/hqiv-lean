import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.TuftGlobalHadronReadout
import Hqiv.Physics.WeakFanoHopfBridge
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.Forces

/-!
# HEP decay-chain readout (mass gaps, CKM slots, weak widths)

Python mirror: `scripts/hqiv_hep_decay_readout.py` and `scripts/hqiv_hep_decay_chain.py`.

This module **discharges** the formulas used in the decay calculator:

* **Chiral meson factor** — `hadronIntrinsicScale_meson² = (4/9)²` (proved in `HadronMassReadout`).
* **Strangeness gap** — nucleon witness + `(m_K − m_π)` octet lift with `γ/(4 n_s)`.
* **Heavy-flavour gaps** — `(m_c − m_u)` and `(m_b − m_s)` from `QuarkMetaResonance` ladder.
* **CKM slot squares** — second-order Fano rungs `γ/8`, `γ/16`, `γ/32`, assembled into
  row/column-unit finite ledger certificates for the decay graph.
* **CP-odd slot** — oriented Fano holonomy skew from the same second-order rung hierarchy.
* **Inclusive B factorization** — finite-patch NLO ledger factor `(1 + γ/8)` multiplying
  hard/jet/soft readout weights before branching normalization.
* **Weak widths** — reuse `G_F_from_beta`, `beta_decay_rate`, bridge slot from
  `WeakFanoHopfBridge` / `NuclearAndAtomicSpectra`.

All comparison PDG numerals stay **outside** this module.
-/

namespace Hqiv.Physics

open Hqiv

/-! ## Chiral / decay-constant slots (proved elsewhere) -/

/-- Chiral projection `(4/9)²` on TUFT meson ground (`HadronMassReadout`). -/
noncomputable def chiralPseudoscalarFactor : ℝ :=
  hadronIntrinsicScale .meson ^ 2

theorem chiralPseudoscalarFactor_eq_four_ninths_squared :
    chiralPseudoscalarFactor = ((4 : ℝ) / 9) ^ 2 := by
  simp [chiralPseudoscalarFactor, hadronIntrinsicScale_meson_eq_four_ninths]

theorem chiralPseudoscalarFactor_pos : 0 < chiralPseudoscalarFactor := by
  rw [chiralPseudoscalarFactor_eq_four_ninths_squared]
  norm_num

/-- Pion decay constant ratio `f_π/m_π = √(4/9) = 2/3` (chiral limit slot). -/
noncomputable def pionDecayConstantRatio : ℝ :=
  Real.sqrt (hadronIntrinsicScale .meson)

theorem pionDecayConstantRatio_eq_two_thirds :
    pionDecayConstantRatio = (2 : ℝ) / 3 := by
  rw [pionDecayConstantRatio, hadronIntrinsicScale_meson_eq_four_ninths]
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num : 0 ≤ (4 : ℝ) / 9) (by norm_num : 0 ≤ (2 : ℝ) / 3)]
  norm_num

/-! ## CKM / Cabibbo slot squares (second-order weak chart) -/

/-- \|V_us\|² rung: `γ/8`. -/
noncomputable def ckmSlotUS2 : ℝ := gamma_HQIV / 8

/-- \|V_cd\|² rung: `γ/16`. -/
noncomputable def ckmSlotCD2 : ℝ := gamma_HQIV / 16

/-- \|V_cb\|² rung: `γ/32`. -/
noncomputable def ckmSlotCB2 : ℝ := gamma_HQIV / 32

theorem ckmSlotUS2_eq_gamma_over_eight : ckmSlotUS2 = gamma_HQIV / 8 := rfl

theorem ckmSlotCD2_eq_gamma_over_sixteen : ckmSlotCD2 = gamma_HQIV / 16 := rfl

theorem ckmSlotCB2_eq_gamma_over_thirtytwo : ckmSlotCB2 = gamma_HQIV / 32 := rfl

theorem ckmSlotUS2_pos : 0 < ckmSlotUS2 := by
  rw [ckmSlotUS2, gamma_eq_2_5]
  norm_num

theorem ckmSlotCD2_pos : 0 < ckmSlotCD2 := by
  rw [ckmSlotCD2, gamma_eq_2_5]
  norm_num

theorem ckmSlotCB2_pos : 0 < ckmSlotCB2 := by
  rw [ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem ckmSlot_hierarchy_cd_lt_us : ckmSlotCD2 < ckmSlotUS2 := by
  simp [ckmSlotCD2, ckmSlotUS2, gamma_eq_2_5]
  norm_num

theorem ckmSlot_hierarchy_cb_lt_cd : ckmSlotCB2 < ckmSlotCD2 := by
  simp [ckmSlotCB2, ckmSlotCD2, gamma_eq_2_5]
  norm_num

theorem ckmSlot_hierarchy_cb_lt_us : ckmSlotCB2 < ckmSlotUS2 := by
  linarith [ckmSlot_hierarchy_cd_lt_us, ckmSlot_hierarchy_cb_lt_cd]

/-! ### Finite CKM row-unitarity and CP orientation for the decay ledger -/

/--
Squared-slot row for the `u → (d,s,b)` charged-current ledger.
The diagonal complement is determined by the two off-diagonal Fano rungs.
-/
noncomputable def ckmURowSlotSquares : List ℝ :=
  [1 - ckmSlotUS2 - ckmSlotCB2, ckmSlotUS2, ckmSlotCB2]

/--
Squared-slot row for the `c → (d,s,b)` charged-current ledger.
-/
noncomputable def ckmCRowSlotSquares : List ℝ :=
  [ckmSlotCD2, 1 - ckmSlotCD2 - ckmSlotCB2, ckmSlotCB2]

/--
Squared-slot row for the `t → (d,s,b)` charged-current ledger.
The two heavy off-diagonal slots are the same second-order bottom rung.
-/
noncomputable def ckmTRowSlotSquares : List ℝ :=
  [ckmSlotCB2, ckmSlotCB2, 1 - 2 * ckmSlotCB2]

theorem ckmURowSlotSquares_sum_one :
    ckmURowSlotSquares.sum = 1 := by
  simp [ckmURowSlotSquares, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]

theorem ckmCRowSlotSquares_sum_one :
    ckmCRowSlotSquares.sum = 1 := by
  simp [ckmCRowSlotSquares, ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5]

theorem ckmTRowSlotSquares_sum_one :
    ckmTRowSlotSquares.sum = 1 := by
  simp [ckmTRowSlotSquares, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem ckmURowSlotSquares_diag_pos :
    0 < 1 - ckmSlotUS2 - ckmSlotCB2 := by
  simp [ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem ckmCRowSlotSquares_diag_pos :
    0 < 1 - ckmSlotCD2 - ckmSlotCB2 := by
  simp [ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem ckmTRowSlotSquares_diag_pos :
    0 < 1 - 2 * ckmSlotCB2 := by
  simp [ckmSlotCB2, gamma_eq_2_5]
  norm_num

/--
Full finite CKM probability ledger.  Rows and columns are both normalized to one.
The `c ↔ d` rung above remains a separate suppression slot; this ledger records the
unitary charge-conjugate readout used when all three generation rows are present.
-/
noncomputable def ckmUnitaryLedgerSlotSquares : List (List ℝ) :=
  [ [1 - ckmSlotUS2 - ckmSlotCB2, ckmSlotUS2, ckmSlotCB2],
    [ckmSlotUS2, 1 - ckmSlotUS2 - ckmSlotCB2, ckmSlotCB2],
    [ckmSlotCB2, ckmSlotCB2, 1 - 2 * ckmSlotCB2]
  ]

theorem ckmUnitaryLedgerSlotSquares_row_sums_one :
    ckmUnitaryLedgerSlotSquares.map List.sum = [1, 1, 1] := by
  simp [ckmUnitaryLedgerSlotSquares, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem ckmUnitaryLedgerSlotSquares_column_sums_one :
    [ (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotUS2 + ckmSlotCB2,
      ckmSlotUS2 + (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotCB2,
      ckmSlotCB2 + ckmSlotCB2 + (1 - 2 * ckmSlotCB2)
    ] = [1, 1, 1] := by
  simp [ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

/--
CP-odd Fano holonomy skew used by the decay readout.
It is an oriented difference of admissible second-order rungs, not a fitted CKM phase.
-/
noncomputable def cpOddFanoHolonomySkew : ℝ :=
  ckmSlotUS2 - ckmSlotCB2

theorem cpOddFanoHolonomySkew_eq_three_over_eighty :
    cpOddFanoHolonomySkew = (3 : ℝ) / 80 := by
  simp [cpOddFanoHolonomySkew, ckmSlotUS2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

theorem cpOddFanoHolonomySkew_pos :
    0 < cpOddFanoHolonomySkew := by
  rw [cpOddFanoHolonomySkew_eq_three_over_eighty]
  norm_num

/-! ## Hidden-quarkonium EM contact slot -/

/--
Compact `Q Q̄` EM contact density for vector quarkonia.

The three terms are the core inverse-shell contact `1/γ`, the unit vector-current
normalisation, and the second-order Fano return `γ`.
-/
noncomputable def hiddenQuarkoniumEMContactFactor : ℝ :=
  1 / gamma_HQIV + 1 + gamma_HQIV

theorem hiddenQuarkoniumEMContactFactor_eq_thirtynine_tenths :
    hiddenQuarkoniumEMContactFactor = (39 : ℝ) / 10 := by
  simp [hiddenQuarkoniumEMContactFactor, gamma_eq_2_5]
  norm_num

theorem hiddenQuarkoniumEMContactFactor_pos :
    0 < hiddenQuarkoniumEMContactFactor := by
  rw [hiddenQuarkoniumEMContactFactor_eq_thirtynine_tenths]
  norm_num

/-! ## Heavy-flavour gap fractions (octet-style shell opening) -/

/-- Per-heavy-quark lift fraction `½(1 + γ/(4 n))` for `n ≥ 1`. -/
noncomputable def heavyFlavorGapFraction (n : ℕ) : ℝ :=
  (1 + gamma_HQIV / (4 * max n 1)) / 2

theorem heavyFlavorGapFraction_one :
    heavyFlavorGapFraction 1 = (1 + gamma_HQIV / 4) / 2 := by
  simp [heavyFlavorGapFraction]

theorem heavyFlavorGapFraction_pos (n : ℕ) : 0 < heavyFlavorGapFraction n := by
  simp only [heavyFlavorGapFraction, gamma_eq_2_5]
  positivity

/-! ## Quark-ladder gaps (MeV chart) -/

noncomputable def upTypeQuarkGapMeV : ℝ := (m_charm_GeV - m_up_GeV) * 1000

noncomputable def downTypeQuarkGapMeV : ℝ := (m_bottom_GeV - m_strange_GeV) * 1000

noncomputable def bottomAnchorMassMeV : ℝ := m_bottom_GeV * 1000

theorem upTypeQuarkGapMeV_eq : upTypeQuarkGapMeV = (m_charm_GeV - m_up_GeV) * 1000 := rfl

/-! ## Strangeness-gap baryons (Λ, Σ, Ξ, Ω scaffold) -/

noncomputable def strangenessGapMeV (mKMeV mPiMeV : ℝ) : ℝ :=
  max (mKMeV - mPiMeV) 0

/-- Octet baryon mass from nucleon witness + `n_s` strangeness lifts. -/
noncomputable def strangeBaryonMassMeV
    (mProtonMeV mKMeV mPiMeV : ℝ) (nStrange : ℕ) : ℝ :=
  let gap := strangenessGapMeV mKMeV mPiMeV
  let gapFraction := (1 / 2 : ℝ) * (1 + gamma_HQIV / (4 * max nStrange 1))
  let octetWeight := 1 + gamma_HQIV * (max nStrange 1 - 1) / 3
  mProtonMeV + (nStrange : ℝ) * gap * gapFraction * octetWeight

/-! ## Heavy-flavour hadron mass readouts -/

/-- Open charm meson `(D)` from pion ground + up-type gap. -/
noncomputable def openCharmMesonMassMeV (mPiMeV : ℝ) : ℝ :=
  mPiMeV + upTypeQuarkGapMeV * heavyFlavorGapFraction 1 * (1 + gamma_HQIV / 4)

/-- Open charm with one strangeness (`D_s`). -/
noncomputable def openCharmStrangeMesonMassMeV (mPiMeV mKMeV : ℝ) : ℝ :=
  openCharmMesonMassMeV mPiMeV +
    strangenessGapMeV mKMeV mPiMeV * heavyFlavorGapFraction 1 * (1 + gamma_HQIV / 8)

/-- Hidden charm quarkonium (`J/ψ`). -/
noncomputable def hiddenCharmQuarkoniumMassMeV (mPiMeV : ℝ) : ℝ :=
  2 * upTypeQuarkGapMeV * heavyFlavorGapFraction 1 +
    mPiMeV * chiralPseudoscalarFactor

/-- Charmed baryon (`Λ_c`, …) from proton + charm gap. -/
noncomputable def charmedBaryonMassMeV (mProtonMeV mKMeV mPiMeV : ℝ) (nCharm nStrange : ℕ) : ℝ :=
  let base :=
    mProtonMeV + (nCharm : ℝ) * upTypeQuarkGapMeV * heavyFlavorGapFraction nCharm *
      (1 - chiralPseudoscalarFactor)
  if nStrange = 0 then
    base
  else
    base + (nStrange : ℝ) * strangenessGapMeV mKMeV mPiMeV * heavyFlavorGapFraction nStrange *
      (1 + gamma_HQIV / 8)

/-- Open bottom meson (`B`). -/
noncomputable def openBottomMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  bottomAnchorMassMeV + (mProtonMeV - mPiMeV) * (1 + gamma_HQIV / 2)

/-- Hidden bottom quarkonium (`ϒ`). -/
noncomputable def hiddenBottomQuarkoniumMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  let mOpen := openBottomMesonMassMeV mProtonMeV mPiMeV
  bottomAnchorMassMeV + mOpen - mPiMeV

/-- Bottom baryon (`Λ_b`, …). -/
noncomputable def bottomBaryonMassMeV
    (mProtonMeV mPiMeV mKMeV : ℝ) (_nBottom nCharm nStrange : ℕ) : ℝ :=
  let base := bottomAnchorMassMeV + (mProtonMeV - mPiMeV) * (1 + gamma_HQIV)
  let withCharm :=
    if nCharm = 0 then base
    else
      base + (nCharm : ℝ) * upTypeQuarkGapMeV * heavyFlavorGapFraction nCharm *
        (1 - chiralPseudoscalarFactor)
  if nStrange = 0 then withCharm
  else
    withCharm + (nStrange : ℝ) * strangenessGapMeV mKMeV mPiMeV * heavyFlavorGapFraction nStrange *
      (1 + gamma_HQIV / 8)

/-! ## Weak width slots (cross-reference proved spine) -/

/-- Charged-current weak coupling slot used in Python (`Forces.G_F_from_beta`). -/
noncomputable def hepWeakCouplingGeV2 : ℝ := G_F_from_beta

theorem hepWeakCoupling_eq_G_F_from_beta : hepWeakCouplingGeV2 = G_F_from_beta := rfl

/-- β golden-rule width slot (Ledger III); Python uses the same structure. -/
theorem hepBetaDecayRate_eq_golden_rule
    (particle : Fermion) (m_e ℳ : ℝ) :
    beta_decay_rate particle m_e ℳ =
      (G_F_from_beta ^ 2) * m_e ^ 5 * ℳ ^ 2 :=
  beta_decay_rate_def particle m_e ℳ

/-- Topological bridge energy before weak phase space (`WeakFanoHopfBridge`). -/
noncomputable def hepWeakBridgeEnergyMeV (endpointScaleMeV : ℝ) : ℝ :=
  weakBridgeEnergyMeV defaultBetaWeakBridge endpointScaleMeV

theorem hepWeakBridgeEnergy_eq (endpointScaleMeV : ℝ) :
    hepWeakBridgeEnergyMeV endpointScaleMeV =
      weakBridgeEnergyMeV defaultBetaWeakBridge endpointScaleMeV := rfl

/-! ## Collider environment curvature dressing -/

/-- Collider field curvature density: dimensionless positive magnetic stress proxy. -/
noncomputable def colliderFieldCurvatureDensity (bTesla referenceTesla : ℝ) : ℝ :=
  if referenceTesla = 0 then 0 else (bTesla / referenceTesla) ^ 2

/-- Comoving stream curvature density from two particle streams on the same patch. -/
noncomputable def comovingStreamCurvatureDensity (streamFraction : ℝ) : ℝ :=
  streamFraction ^ 2

/--
Finite-patch collider curvature term.  The magnetic and stream densities enter
through the same weak bridge shape and the monogamy split `γ`.
-/
noncomputable def colliderCurvatureWidthFactor
    (bTesla referenceTesla streamFraction : ℝ) : ℝ :=
  1 + gamma_HQIV * weakBridgeShape defaultBetaWeakBridge *
    (colliderFieldCurvatureDensity bTesla referenceTesla +
      comovingStreamCurvatureDensity streamFraction)

theorem colliderFieldCurvatureDensity_zero_field (referenceTesla : ℝ) :
    colliderFieldCurvatureDensity 0 referenceTesla = 0 := by
  simp [colliderFieldCurvatureDensity]

theorem comovingStreamCurvatureDensity_zero :
    comovingStreamCurvatureDensity 0 = 0 := by
  simp [comovingStreamCurvatureDensity]

theorem colliderCurvatureWidthFactor_vacuum (referenceTesla : ℝ) :
    colliderCurvatureWidthFactor 0 referenceTesla 0 = 1 := by
  simp [colliderCurvatureWidthFactor, colliderFieldCurvatureDensity,
    comovingStreamCurvatureDensity]

/-! ## Branching / production slots (Python mirror) -/

/-- Branching ratio from partial widths: `BR_i = Γ_i / Σ Γ_j`. -/
noncomputable def branchingRatioFromPartialWidth (partialWidth totalWidth : ℝ) : ℝ :=
  if totalWidth = 0 then 0 else partialWidth / totalWidth

theorem branchingRatioFromPartialWidth_eq_div (partialWidth totalWidth : ℝ)
    (h : totalWidth ≠ 0) :
    branchingRatioFromPartialWidth partialWidth totalWidth = partialWidth / totalWidth := by
  simp [branchingRatioFromPartialWidth, h]

theorem branchingRatios_sum_one
    (widths : List ℝ) (totalWidth : ℝ)
    (htot : totalWidth = widths.sum) (hz : totalWidth ≠ 0) :
    widths.sum / totalWidth = 1 := by
  rw [← htot]
  field_simp [hz]

/-- Open-charm production weight rung `γ/4`. -/
noncomputable def openCharmProductionWeight : ℝ := gamma_HQIV / 4

/-- Open-bottom production weight rung `γ/8`. -/
noncomputable def openBottomProductionWeight : ℝ := gamma_HQIV / 8

theorem openCharmProductionWeight_eq : openCharmProductionWeight = gamma_HQIV / 4 := rfl

theorem openBottomProductionWeight_eq : openBottomProductionWeight = gamma_HQIV / 8 := rfl

theorem openBottomProductionWeight_lt_openCharm :
    openBottomProductionWeight < openCharmProductionWeight := by
  simp [openBottomProductionWeight, openCharmProductionWeight, gamma_eq_2_5]
  norm_num

/--
Unit seed for topology-only open-flavour mode enumeration.
Open-flavour templates may list admissible daughter topologies, but no relative
partial-width information is assigned at the seed stage; all competition must
come from common ledger factors (CKM, phase space, strangeness, OZI where
applicable) and subsequent normalization.
-/
noncomputable def openFlavourTopologySeedWeight : ℝ := 1

theorem openFlavourTopologySeedWeight_eq_one :
    openFlavourTopologySeedWeight = 1 := rfl

/--
Invisible charged-lepton/neutrino outlet aperture for pseudoscalar weak lines.
The charged lepton occupies the same single open monogamy rung as the open-charm
production aperture (`γ/4`); the neutrino is carried as an implicit neutral weak
ledger daughter in the Python readout.
-/
noncomputable def leptonNeutrinoPairAperture : ℝ := gamma_HQIV / 4

theorem leptonNeutrinoPairAperture_eq_one_tenth :
    leptonNeutrinoPairAperture = (1 : ℝ) / 10 := by
  simp [leptonNeutrinoPairAperture, gamma_eq_2_5]
  norm_num

/--
Bottom-strange spectator coherence for `B_s → D_s K`-type weak transfer.
It is the same open-charm/open-bottom rung ratio used elsewhere in the heavy
flavour ledger, hence exactly `2`.
-/
noncomputable def bottomStrangeSpectatorCoherenceWeight : ℝ :=
  openCharmProductionWeight / openBottomProductionWeight

theorem bottomStrangeSpectatorCoherenceWeight_eq_two :
    bottomStrangeSpectatorCoherenceWeight = 2 := by
  simp [bottomStrangeSpectatorCoherenceWeight, openCharmProductionWeight, openBottomProductionWeight, gamma_eq_2_5]
  norm_num

/--
Charm pion-only weak paths carry the off-diagonal `c→d` Fano rung against the
favoured diagonal charm ledger.
-/
noncomputable def charmPionOnlySuppression : ℝ :=
  ckmSlotCD2 / (1 - ckmSlotCD2 - ckmSlotCB2)

theorem charmPionOnlySuppression_eq_two_over_seventyseven :
    charmPionOnlySuppression = (2 : ℝ) / 77 := by
  simp [charmPionOnlySuppression, ckmSlotCD2, ckmSlotCB2, gamma_eq_2_5]
  norm_num

/--
Three-body charmed-baryon contact: the inverse of the open-charm aperture.
This is used for `Λ_c → p K π`-type baryon-plus-strangeness outlets.
-/
noncomputable def charmedBaryonThreeBodyContact : ℝ :=
  1 / openCharmProductionWeight

theorem charmedBaryonThreeBodyContact_eq_ten :
    charmedBaryonThreeBodyContact = 10 := by
  simp [charmedBaryonThreeBodyContact, openCharmProductionWeight, gamma_eq_2_5]
  norm_num

/--
External bottom weak contact for spectator-preserving open-bottom outlets.
It is the inverse monogamy access plus the unit current channel.
-/
noncomputable def bottomExternalWeakContact : ℝ :=
  1 / gamma_HQIV + 1

theorem bottomExternalWeakContact_eq_seven_halves :
    bottomExternalWeakContact = (7 : ℝ) / 2 := by
  simp [bottomExternalWeakContact, gamma_eq_2_5]
  norm_num

/--
Bottom-strange double-monogamy coherence for `B_s → D_s K`.
The strange spectator and bottom-to-charm transfer each open an inverse
monogamy access, giving `1/γ²`.
-/
noncomputable def bottomStrangeDoubleMonogamyCoherence : ℝ :=
  1 / gamma_HQIV ^ 2

theorem bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths :
    bottomStrangeDoubleMonogamyCoherence = (25 : ℝ) / 4 := by
  simp [bottomStrangeDoubleMonogamyCoherence, gamma_eq_2_5]
  norm_num

/-
## Spine-derived gap-closure candidates

These are not fitted weights. They are exact apertures already available from
the HQIV spine (`γ`, monogamy complement, and the weak bridge shape). Python may
use them as diagnostic candidate terms for residual branching/lifetime gaps.
-/

/-- Missing finite-channel aperture carried by the weak Fano/Hopf bridge. -/
noncomputable def finiteChannelCompletionAperture : ℝ :=
  gamma_HQIV / 18

theorem finiteChannelCompletionAperture_eq_one_fortyfive :
    finiteChannelCompletionAperture = (1 : ℝ) / 45 := by
  simp [finiteChannelCompletionAperture, gamma_eq_2_5]
  norm_num

/-- Double-monogamy exclusion factor for over-counted charm/baryon family outlets. -/
noncomputable def doubleMonogamyExclusionFactor : ℝ :=
  1 - gamma_HQIV ^ 2

theorem doubleMonogamyExclusionFactor_eq_twentyone_twentyfive :
    doubleMonogamyExclusionFactor = (21 : ℝ) / 25 := by
  simp [doubleMonogamyExclusionFactor, gamma_eq_2_5]
  norm_num

/-- Half-monogamy spectator contact for charged open-bottom spectator channels. -/
noncomputable def spectatorHalfMonogamyContact : ℝ :=
  1 + gamma_HQIV / 2

theorem spectatorHalfMonogamyContact_eq_six_fifths :
    spectatorHalfMonogamyContact = (6 : ℝ) / 5 := by
  simp [spectatorHalfMonogamyContact, gamma_eq_2_5]
  norm_num

/-- Neutral spectator complement for missing neutral/oscillating bottom channels. -/
noncomputable def neutralSpectatorMonogamyComplement : ℝ :=
  1 / (1 - gamma_HQIV)

theorem neutralSpectatorMonogamyComplement_eq_five_thirds :
    neutralSpectatorMonogamyComplement = (5 : ℝ) / 3 := by
  simp [neutralSpectatorMonogamyComplement, gamma_eq_2_5]
  norm_num

/-- Finite contact kinds used by open-flavour topology templates. -/
inductive OpenFlavourContactKind where
  | unitSeed
  | charmPionOnly
  | charmedBaryonThreeBody
  | bottomExternalWeak
  | bottomStrangeDoubleMonogamy
  | finiteChannelCompletion
  | spectatorHalfMonogamy
  | neutralSpectatorComplement
  deriving DecidableEq, Repr

/--
Uniform open-flavour contact ledger.  Python selects one of these finite kinds per
generated template; no channel receives an independent fitted prior.
-/
noncomputable def openFlavourContactWeight : OpenFlavourContactKind → ℝ
  | .unitSeed => openFlavourTopologySeedWeight
  | .charmPionOnly => charmPionOnlySuppression
  | .charmedBaryonThreeBody => charmedBaryonThreeBodyContact
  | .bottomExternalWeak => bottomExternalWeakContact
  | .bottomStrangeDoubleMonogamy => bottomStrangeDoubleMonogamyCoherence
  | .finiteChannelCompletion => finiteChannelCompletionAperture
  | .spectatorHalfMonogamy => spectatorHalfMonogamyContact
  | .neutralSpectatorComplement => neutralSpectatorMonogamyComplement

theorem openFlavourContactWeight_unitSeed :
    openFlavourContactWeight .unitSeed = 1 := by
  simp [openFlavourContactWeight, openFlavourTopologySeedWeight]

theorem openFlavourContactWeight_charmPionOnly :
    openFlavourContactWeight .charmPionOnly = (2 : ℝ) / 77 := by
  simp [openFlavourContactWeight, charmPionOnlySuppression_eq_two_over_seventyseven]

theorem openFlavourContactWeight_charmedBaryonThreeBody :
    openFlavourContactWeight .charmedBaryonThreeBody = 10 := by
  simp [openFlavourContactWeight, charmedBaryonThreeBodyContact_eq_ten]

theorem openFlavourContactWeight_bottomExternalWeak :
    openFlavourContactWeight .bottomExternalWeak = (7 : ℝ) / 2 := by
  simp [openFlavourContactWeight, bottomExternalWeakContact_eq_seven_halves]

theorem openFlavourContactWeight_bottomStrangeDoubleMonogamy :
    openFlavourContactWeight .bottomStrangeDoubleMonogamy = (25 : ℝ) / 4 := by
  simp [openFlavourContactWeight, bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths]

theorem openFlavourContactWeight_finiteChannelCompletion :
    openFlavourContactWeight .finiteChannelCompletion = (1 : ℝ) / 45 := by
  simp [openFlavourContactWeight, finiteChannelCompletionAperture_eq_one_fortyfive]

theorem openFlavourContactWeight_spectatorHalfMonogamy :
    openFlavourContactWeight .spectatorHalfMonogamy = (6 : ℝ) / 5 := by
  simp [openFlavourContactWeight, spectatorHalfMonogamyContact_eq_six_fifths]

theorem openFlavourContactWeight_neutralSpectatorComplement :
    openFlavourContactWeight .neutralSpectatorComplement = (5 : ℝ) / 3 := by
  simp [openFlavourContactWeight, neutralSpectatorMonogamyComplement_eq_five_thirds]

/-! ## Inclusive bottom finite-patch NLO factorization -/

/--
Finite-patch NLO ledger factor for inclusive `B` decays.
It is the first curvature return on the bottom weak rung; continuum QCD is only a
comparison language for this discrete multiplicative certificate.
-/
noncomputable def inclusiveBNLOLedgerFactor : ℝ :=
  1 + gamma_HQIV / 8

theorem inclusiveBNLOLedgerFactor_eq_twentyone_over_twenty :
    inclusiveBNLOLedgerFactor = (21 : ℝ) / 20 := by
  simp [inclusiveBNLOLedgerFactor, gamma_eq_2_5]
  norm_num

theorem inclusiveBNLOLedgerFactor_gt_one :
    1 < inclusiveBNLOLedgerFactor := by
  rw [inclusiveBNLOLedgerFactor_eq_twentyone_over_twenty]
  norm_num

/--
Inclusive `B` readout factorizes into hard, jet, soft, bottom-rung, and NLO ledger slots.
-/
noncomputable def inclusiveBDecayFactorizedWeight (hard jet soft : ℝ) : ℝ :=
  hard * jet * soft * openBottomProductionWeight * inclusiveBNLOLedgerFactor

theorem inclusiveBDecayFactorizedWeight_eq
    (hard jet soft : ℝ) :
    inclusiveBDecayFactorizedWeight hard jet soft =
      hard * jet * soft * openBottomProductionWeight * inclusiveBNLOLedgerFactor := rfl

/-- Hadronic phase-space threshold `(1 − (2m/√s)²)^{3/2}` at `m/√s`. -/
noncomputable def hadronicPhaseSpaceFactor (massOverSqrtS : ℝ) : ℝ :=
  max (1 - (2 * massOverSqrtS) ^ 2) 0 ^ (3 / 2 : ℝ)

theorem hadronicPhaseSpaceFactor_zero_at_threshold :
    hadronicPhaseSpaceFactor (1 / 2) = 0 := by
  simp [hadronicPhaseSpaceFactor]

/-- OZI / Zweig suppression for hidden quarkonia → light hadrons (`γ/4` leading slot). -/
noncomputable def oziSuppressionFactor (nVectorModes : ℕ) : ℝ :=
  (gamma_HQIV / 4) * (1 + gamma_HQIV * nVectorModes / 8)

theorem oziSuppressionFactor_pos (nVectorModes : ℕ) : 0 < oziSuppressionFactor nVectorModes := by
  simp [oziSuppressionFactor, gamma_eq_2_5]
  positivity

/--
Heavy-quarkonium cascade weight on the production ladder:
open-charm rung over open-bottom rung (`(γ/4)/(γ/8) = 2`).
Used for e.g. `ϒ → J/ψ` prior; OZI suppression does not apply to all-heavy final states.
-/
noncomputable def heavyQuarkoniumCascadeWeight : ℝ :=
  openCharmProductionWeight / openBottomProductionWeight

theorem heavyQuarkoniumCascadeWeight_eq :
    heavyQuarkoniumCascadeWeight = 2 := by
  simp [heavyQuarkoniumCascadeWeight, openCharmProductionWeight, openBottomProductionWeight, gamma_eq_2_5]
  norm_num

/--
Neutral light-pair cascade aperture for inclusive heavy quarkonium readout.
It is two monogamy openings, hence `γ²`, used for charge/strangeness-neutral
`ϒ → J/ψ + h h` candidates before phase-space and branching normalization.
-/
noncomputable def neutralLightPairCascadeWeight : ℝ :=
  gamma_HQIV ^ 2

theorem neutralLightPairCascadeWeight_eq_four_twentyfive :
    neutralLightPairCascadeWeight = (4 : ℝ) / 25 := by
  simp [neutralLightPairCascadeWeight, gamma_eq_2_5]
  norm_num

#check oziSuppressionFactor_pos
#check heavyQuarkoniumCascadeWeight_eq
#check neutralLightPairCascadeWeight_eq_four_twentyfive
#check openFlavourTopologySeedWeight_eq_one
#check leptonNeutrinoPairAperture_eq_one_tenth
#check bottomStrangeSpectatorCoherenceWeight_eq_two
#check charmPionOnlySuppression_eq_two_over_seventyseven
#check charmedBaryonThreeBodyContact_eq_ten
#check bottomExternalWeakContact_eq_seven_halves
#check bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths
#check colliderCurvatureWidthFactor_vacuum
#check finiteChannelCompletionAperture_eq_one_fortyfive
#check doubleMonogamyExclusionFactor_eq_twentyone_twentyfive
#check spectatorHalfMonogamyContact_eq_six_fifths
#check neutralSpectatorMonogamyComplement_eq_five_thirds
#check openFlavourContactWeight_unitSeed
#check openFlavourContactWeight_finiteChannelCompletion
#check openFlavourContactWeight_neutralSpectatorComplement
#check branchingRatios_sum_one
#check hiddenQuarkoniumEMContactFactor_eq_thirtynine_tenths
#check ckmURowSlotSquares_sum_one
#check ckmUnitaryLedgerSlotSquares_column_sums_one
#check cpOddFanoHolonomySkew_pos
#check inclusiveBNLOLedgerFactor_eq_twentyone_over_twenty

end Hqiv.Physics
