import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.TuftGlobalHadronReadout
import Hqiv.Physics.WeakFanoHopfBridge
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.Forces
import Hqiv.Physics.NeutronLifetimeMethod
import Hqiv.Physics.SM_GR_Unification
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.FanoDetuningFirstOrder

/-!
# HEP decay-chain readout (mass gaps, CKM slots, weak widths)

Python mirror: `scripts/hqiv_hep_decay_readout.py` and `scripts/hqiv_hep_decay_chain.py`.

**Programme pin.** Mass gaps and binding exports use `referenceM = 4` from
`OctonionicLightCone` (first shell row with `new_modes 4 = 40` and
`G₂ ∪ {Δ} ⇒ 𝔰𝔬(8)` closure). See `papers/include/referenceM_programme_pin.tex`.

This module **discharges** the formulas used in the decay calculator:

* **Chiral meson factor** — `hadronIntrinsicScale_meson² = (4/9)²` (proved in `HadronMassReadout`).
* **Strangeness gap** — nucleon witness + `(m_K − m_π)` octet lift with `γ/(4 n_s)`.
* **Heavy-flavour gaps** — `(m_c − m_u)` and `(m_b − m_s)` from `QuarkMetaResonance` ladder.
* **CKM slot squares** — second-order Fano rungs `γ/8`, `γ/16`, `γ/32`, assembled into
  row/column-unit finite ledger certificates for the decay graph.
* **CP-odd slot** — oriented Fano holonomy skew from the same second-order rung hierarchy.
* **Inclusive B factorization** — finite-patch NLO ledger factor `(1 + γ/8)` multiplying
  hard/jet/soft readout weights before branching normalization.
* **Spine gap-closure factors** — exact monogamy-complement contacts for neutral
  and charged spectators (`neutralSpectatorMonogamyComplement`, etc.); Python
  selects `OpenFlavourContactKind` via ledger predicates in
  `HepDecayChannelPredicates` / `hqiv_hep_multichannel_expansion.py`.
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
normalisation, and the second-order Fano return at **half** Rindler strength `γ/2`
(`FanoResonance.c_rindler_shared`), not a fitted leptonic-width knob.
-/
noncomputable def hiddenQuarkoniumEMContactFactor : ℝ :=
  1 / gamma_HQIV + 1 + gamma_HQIV / 2

theorem hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths :
    hiddenQuarkoniumEMContactFactor = (37 : ℝ) / 10 := by
  simp [hiddenQuarkoniumEMContactFactor, gamma_eq_2_5]
  norm_num

theorem hiddenQuarkoniumEMContactFactor_eq_thirtynine_tenths :
    hiddenQuarkoniumEMContactFactor + gamma_HQIV / 2 = (39 : ℝ) / 10 := by
  rw [hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths, gamma_eq_2_5]
  norm_num

theorem hiddenQuarkoniumEMContactFactor_pos :
    0 < hiddenQuarkoniumEMContactFactor := by
  rw [hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths]
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

/-- Strange-quark lift on open-heavy baryons (octet gapFraction/octetWeight spine). -/
noncomputable def bottomBaryonStrangeLiftMeV (mKMeV mPiMeV : ℝ) (nStrange : ℕ) : ℝ :=
  if nStrange = 0 then 0
  else
    let gap := strangenessGapMeV mKMeV mPiMeV
    let gapFraction := (1 / 2 : ℝ) * (1 + gamma_HQIV / (4 * max nStrange 1))
    let octetWeight := 1 + gamma_HQIV * (max nStrange 1 - 1) / 3
    (nStrange : ℝ) * gap * gapFraction * octetWeight

theorem bottomBaryonStrangeLiftMeV_zero (mKMeV mPiMeV : ℝ) :
    bottomBaryonStrangeLiftMeV mKMeV mPiMeV 0 = 0 := by
  simp [bottomBaryonStrangeLiftMeV]

/-- Open-heavy baryon strangeness lift: chiral projection on the first spectator $s$ rung. -/
noncomputable def heavyFlavorBaryonStrangeLiftMeV (mKMeV mPiMeV : ℝ) (nStrange : ℕ) : ℝ :=
  if nStrange = 0 then 0
  else
    let octet := bottomBaryonStrangeLiftMeV mKMeV mPiMeV nStrange
    let first := bottomBaryonStrangeLiftMeV mKMeV mPiMeV 1
    first * (1 - chiralPseudoscalarFactor) + (octet - first)

theorem heavyFlavorBaryonStrangeLiftMeV_zero (mKMeV mPiMeV : ℝ) :
    heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV 0 = 0 := by
  simp [heavyFlavorBaryonStrangeLiftMeV]

theorem heavyFlavorBaryonStrangeLiftMeV_one_eq_chiral_projected_octet (mKMeV mPiMeV : ℝ) :
    heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV 1 =
      bottomBaryonStrangeLiftMeV mKMeV mPiMeV 1 * (1 - chiralPseudoscalarFactor) := by
  simp [heavyFlavorBaryonStrangeLiftMeV, bottomBaryonStrangeLiftMeV]

/-! ## Heavy-flavour hadron mass readouts -/

/-- Open charm meson `(D)` from pion ground + up-type gap. -/
noncomputable def openCharmMesonMassMeV (mPiMeV : ℝ) : ℝ :=
  mPiMeV + upTypeQuarkGapMeV * heavyFlavorGapFraction 1 * (1 + gamma_HQIV / 4)

/-- Spectator strangeness lift on open heavy mesons: first-order chiral projection of the $K$--$\pi$ gap. -/
noncomputable def openHeavyStrangenessLiftMeV (mKMeV mPiMeV : ℝ) : ℝ :=
  strangenessGapMeV mKMeV mPiMeV * heavyFlavorGapFraction 1 * (1 + gamma_HQIV / 8) *
    Real.sqrt chiralPseudoscalarFactor

/-- Open charm with one strangeness (`D_s`): defined below after dressed open-$D$ core. -/
noncomputable def hiddenCharmQuarkoniumMassMeV (mPiMeV : ℝ) : ℝ :=
  2 * upTypeQuarkGapMeV * heavyFlavorGapFraction 1 +
    mPiMeV * chiralPseudoscalarFactor

/-- Charmed baryon (`Λ_c`, …) from proton + charm gap + open-heavy strangeness lift. -/
noncomputable def charmedBaryonMassMeV (mProtonMeV mKMeV mPiMeV : ℝ) (nCharm nStrange : ℕ) : ℝ :=
  let base :=
    mProtonMeV + (nCharm : ℝ) * upTypeQuarkGapMeV * heavyFlavorGapFraction nCharm *
      (1 - chiralPseudoscalarFactor)
  base + heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV nStrange

/-- Charmed-baryon multiplet tag on the heavy-flavour baryon scaffold. -/
inductive CharmedBaryonMultiplet where
  | lambda
  | sigma
  | xi
  | omega
  deriving DecidableEq, Repr

def charmedBaryonStrangeCount (m : CharmedBaryonMultiplet) : ℕ :=
  match m with
  | .lambda | .sigma => 0
  | .xi => 1
  | .omega => 2

/-- $\Sigma_c$ hyperfine lift above $\Lambda_c$: $1+\gamma/6$. -/
noncomputable def charmedBaryonSigmaHyperfineWeight : ℝ := 1 + gamma_HQIV / 6

theorem charmedBaryonSigmaHyperfineWeight_eq_sixteen_fifteenths :
    charmedBaryonSigmaHyperfineWeight = (16 : ℝ) / 15 := by
  simp [charmedBaryonSigmaHyperfineWeight, gamma_eq_2_5]
  norm_num

noncomputable def charmedBaryonMultipletWeight (m : CharmedBaryonMultiplet) : ℝ :=
  match m with
  | .sigma => charmedBaryonSigmaHyperfineWeight
  | _ => 1

/-- Double-charm ($ucc$) ground baryons: $1+\gamma/9$. -/
noncomputable def charmedBaryonDoubleCharmWeight : ℝ := 1 + gamma_HQIV / 9

theorem charmedBaryonDoubleCharmWeight_eq_fortyseven_fortyfive :
    charmedBaryonDoubleCharmWeight = (47 : ℝ) / 45 := by
  simp [charmedBaryonDoubleCharmWeight, gamma_eq_2_5]
  norm_num

noncomputable def charmedBaryonMassMeV_multiplet
    (mProtonMeV mKMeV mPiMeV : ℝ) (mult : CharmedBaryonMultiplet) (nCharm : ℕ) : ℝ :=
  let nStrange := charmedBaryonStrangeCount mult
  let inner := charmedBaryonMassMeV mProtonMeV mKMeV mPiMeV nCharm nStrange
  let hyper := charmedBaryonMultipletWeight mult
  let dbl :=
    if nCharm ≥ 2 ∧ nStrange = 0 then charmedBaryonDoubleCharmWeight else 1
  inner * hyper * dbl

/-- Open bottom meson (`B`). -/
noncomputable def openBottomMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  bottomAnchorMassMeV + (mProtonMeV - mPiMeV) * (1 + gamma_HQIV / 2)

/-- Hidden bottom quarkonium (`ϒ`). -/
noncomputable def hiddenBottomQuarkoniumMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  let mOpen := openBottomMesonMassMeV mProtonMeV mPiMeV
  bottomAnchorMassMeV + mOpen - mPiMeV

/-! ## Bottom-baryon multiplet (Λ_b, Σ_b, Ξ_b, Ω_b) -/

/-- Bottom-baryon multiplet tag on the heavy-flavour baryon scaffold. -/
inductive BottomBaryonMultiplet where
  | lambda
  | sigma
  | xi
  | omega
  deriving DecidableEq, Repr

/-- Effective strange-quark rung count from valence content (Ω_b is ssb → two rungs). -/
def bottomBaryonStrangeCount (m : BottomBaryonMultiplet) : ℕ :=
  match m with
  | .lambda | .sigma => 0
  | .xi => 1
  | .omega => 2

theorem bottomBaryonStrangeCount_omega_eq_two :
    bottomBaryonStrangeCount .omega = 2 := rfl

theorem bottomBaryonStrangeCount_xi_eq_one :
    bottomBaryonStrangeCount .xi = 1 := rfl

/-- Σ_b hyperfine lift above Λ_b at fixed strange content: $1+\gamma/12$. -/
noncomputable def bottomBaryonSigmaHyperfineWeight : ℝ := 1 + gamma_HQIV / 12

theorem bottomBaryonSigmaHyperfineWeight_eq_thirtyone_thirtieths :
    bottomBaryonSigmaHyperfineWeight = (31 : ℝ) / 30 := by
  simp [bottomBaryonSigmaHyperfineWeight, gamma_eq_2_5]
  norm_num

noncomputable def bottomBaryonMultipletWeight (m : BottomBaryonMultiplet) : ℝ :=
  match m with
  | .sigma => bottomBaryonSigmaHyperfineWeight
  | _ => 1

/-- Bottom baryon (`Λ_b`, `Σ_b`, `Ξ_b`, `Ω_b`) from bottom anchor + nucleon offset + multiplet weights. -/
noncomputable def bottomBaryonMassMeV
    (mProtonMeV mPiMeV mKMeV : ℝ) (mult : BottomBaryonMultiplet) (nCharm : ℕ := 0) : ℝ :=
  let base := bottomAnchorMassMeV + (mProtonMeV - mPiMeV) * (1 + gamma_HQIV)
  let nStrange := bottomBaryonStrangeCount mult
  let withCharm :=
    if nCharm = 0 then base
    else
      base + (nCharm : ℝ) * upTypeQuarkGapMeV * heavyFlavorGapFraction nCharm *
        (1 - chiralPseudoscalarFactor)
  bottomBaryonMultipletWeight mult *
    (withCharm + heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV nStrange)

/-- Legacy count-based entry point (maps to multiplet by strange rung only). -/
noncomputable def bottomBaryonMassMeV_fromStrangeCount
    (mProtonMeV mPiMeV mKMeV : ℝ) (_nBottom nCharm nStrange : ℕ) : ℝ :=
  let mult : BottomBaryonMultiplet :=
    if nStrange = 0 then .lambda else if nStrange = 1 then .xi else .omega
  bottomBaryonMassMeV mProtonMeV mPiMeV mKMeV mult nCharm

/-! ## Outside-curvature mass dressing (lock-in observable mass)

Gap-ladder and chiral chart slots are inner readouts; the outside bath dresses
observable mass through second-order Fano rungs parallel to CKM slot squares
(no PDG injection). Python applies these at lock-in after the gap/chart slot.
-/

/-- Open-charm meson outside bath: $1+\gamma/8$. -/
noncomputable def openCharmOutsideMassDressing : ℝ := 1 + gamma_HQIV / 8

theorem openCharmOutsideMassDressing_eq_twentyone_twentieths :
    openCharmOutsideMassDressing = (21 : ℝ) / 20 := by
  simp [openCharmOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Charmed baryon outside bath: $1+\gamma/8+\gamma/16$. -/
noncomputable def charmedBaryonOutsideMassDressing : ℝ :=
  1 + gamma_HQIV / 8 + gamma_HQIV / 16

theorem charmedBaryonOutsideMassDressing_eq_fortythree_fortieths :
    charmedBaryonOutsideMassDressing = (43 : ℝ) / 40 := by
  simp [charmedBaryonOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Open-bottom meson outside bath: $1+\gamma/16$. -/
noncomputable def openBottomOutsideMassDressing : ℝ := 1 + gamma_HQIV / 16

theorem openBottomOutsideMassDressing_eq_fortyone_fortieths :
    openBottomOutsideMassDressing = (41 : ℝ) / 40 := by
  simp [openBottomOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Bottom baryon outside bath: $1+\gamma/8+\gamma/40$. -/
noncomputable def bottomBaryonOutsideMassDressing : ℝ :=
  1 + gamma_HQIV / 8 + gamma_HQIV / 40

theorem bottomBaryonOutsideMassDressing_eq_fiftythree_fiftieths :
    bottomBaryonOutsideMassDressing = (53 : ℝ) / 50 := by
  simp [bottomBaryonOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Hidden quarkonium outside bath: $1+\gamma/16$. -/
noncomputable def hiddenQuarkoniumOutsideMassDressing : ℝ := 1 + gamma_HQIV / 16

theorem hiddenQuarkoniumOutsideMassDressing_eq_fortyone_fortieths :
    hiddenQuarkoniumOutsideMassDressing = (41 : ℝ) / 40 := by
  simp [hiddenQuarkoniumOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Charged kaon outside bath: $1+\gamma/32$. -/
noncomputable def chiralPseudoscalarOutsideMassDressing : ℝ := 1 + gamma_HQIV / 32

theorem chiralPseudoscalarOutsideMassDressing_eq_eightyone_eightieths :
    chiralPseudoscalarOutsideMassDressing = (81 : ℝ) / 80 := by
  simp [chiralPseudoscalarOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Strange octet baryon outside deficit: $1-\gamma/32$. -/
noncomputable def strangeBaryonOctetOutsideMassDressing : ℝ := 1 - gamma_HQIV / 32

theorem strangeBaryonOctetOutsideMassDressing_eq_seventynine_eightieths :
    strangeBaryonOctetOutsideMassDressing = (79 : ℝ) / 80 := by
  simp [strangeBaryonOctetOutsideMassDressing, gamma_eq_2_5]
  norm_num

/-- Hidden-strangeness vector meson outside bath: $1+\gamma/24$. -/
noncomputable def hiddenStrangenessVectorOutsideMassDressing : ℝ := 1 + gamma_HQIV / 24

theorem hiddenStrangenessVectorOutsideMassDressing_eq_sixtyone_sixtieths :
    hiddenStrangenessVectorOutsideMassDressing = (61 : ℝ) / 60 := by
  simp [hiddenStrangenessVectorOutsideMassDressing, gamma_eq_2_5]
  norm_num

noncomputable def dressedOpenCharmMesonMassMeV (mPiMeV : ℝ) : ℝ :=
  openCharmMesonMassMeV mPiMeV * openCharmOutsideMassDressing

/-- Open charm with one strangeness (`D_s`): dressed open-$D$ core plus spectator lift. -/
noncomputable def openCharmStrangeMesonMassMeV (mPiMeV mKMeV : ℝ) : ℝ :=
  dressedOpenCharmMesonMassMeV mPiMeV + openHeavyStrangenessLiftMeV mKMeV mPiMeV

noncomputable def dressedOpenBottomMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  openBottomMesonMassMeV mProtonMeV mPiMeV * openBottomOutsideMassDressing

/-- Open bottom with one strangeness (`B_s`): dressed open-$B$ core plus spectator lift. -/
noncomputable def openBottomStrangeMesonMassMeV (mProtonMeV mPiMeV mKMeV : ℝ) : ℝ :=
  dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV + openHeavyStrangenessLiftMeV mKMeV mPiMeV

noncomputable def dressedHiddenCharmQuarkoniumMassMeV (mPiMeV : ℝ) : ℝ :=
  hiddenCharmQuarkoniumMassMeV mPiMeV * hiddenQuarkoniumOutsideMassDressing

/-- Hidden-bottom ground ($\\Upsilon(1S)$) shallow slot above outside dressing: $1+\\gamma/80$. -/
noncomputable def hiddenBottomQuarkoniumGroundSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem hiddenBottomQuarkoniumGroundSlotFactor_eq_twohundredone_twohundredths :
    hiddenBottomQuarkoniumGroundSlotFactor = (201 : ℝ) / 200 := by
  simp [hiddenBottomQuarkoniumGroundSlotFactor, gamma_eq_2_5]
  norm_num

noncomputable def dressedHiddenBottomQuarkoniumMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  hiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV * hiddenQuarkoniumOutsideMassDressing *
    hiddenBottomQuarkoniumGroundSlotFactor

/-- Vector $D^{*}$ hyperfine lift above dressed open-$D$ ground: $1+\gamma/5$. -/
noncomputable def openCharmVectorMesonMassFactor : ℝ := 1 + gamma_HQIV / 5

theorem openCharmVectorMesonMassFactor_eq_twentyseven_twentyfifths :
    openCharmVectorMesonMassFactor = (27 : ℝ) / 25 := by
  rw [openCharmVectorMesonMassFactor, gamma_eq_2_5]
  norm_num

/-- Ground open-$D^*$ vector ($D^{*\\pm}$, $D^{*0}$): shallow slot on hyperfine lift, $1-\\gamma/56$. -/
noncomputable def openCharmVectorGroundSlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem openCharmVectorGroundSlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    openCharmVectorGroundSlotFactor = (139 : ℝ) / 140 := by
  simp [openCharmVectorGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- Open-$D_s$ vector radial $k=1$ ($D_{s1}^*$): shallow positive slot $1+\\gamma/56$. -/
noncomputable def openCharmStrangeVectorRadialK1SlotFactor : ℝ := 1 + gamma_HQIV / 56

theorem openCharmStrangeVectorRadialK1SlotFactor_eq_onehundredfortyone_onehundredfortieths :
    openCharmStrangeVectorRadialK1SlotFactor = (141 : ℝ) / 140 := by
  simp [openCharmStrangeVectorRadialK1SlotFactor, gamma_eq_2_5]
  norm_num

noncomputable def openCharmStrangeVectorRadialSlotFactor (k : ℕ) : ℝ :=
  if k = 1 then openCharmStrangeVectorRadialK1SlotFactor else 1

noncomputable def dressedOpenCharmVectorMesonMassMeV (mPiMeV : ℝ) : ℝ :=
  dressedOpenCharmMesonMassMeV mPiMeV * openCharmVectorMesonMassFactor *
    openCharmVectorGroundSlotFactor

/-- Vector core without ground slot (radial ladder base). -/
noncomputable def dressedOpenCharmVectorCoreMassMeV (mPiMeV : ℝ) : ℝ :=
  dressedOpenCharmMesonMassMeV mPiMeV * openCharmVectorMesonMassFactor

/-- Hidden-$J/\psi$ excitation rungs: $k=1$ radial $\psi(2S)$; $k=2$ orbital $\chi_{c1}$. -/
noncomputable def hiddenCharmQuarkoniumExcitationFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1 + gamma_HQIV / 2
  | 2 => 1 + gamma_HQIV / 3
  | k + 3 => 1 + gamma_HQIV / 2 + (k + 1 : ℝ) * gamma_HQIV / 3

theorem hiddenCharmQuarkoniumExcitationFactor_one :
    hiddenCharmQuarkoniumExcitationFactor 1 = 1 + gamma_HQIV / 2 := rfl

theorem hiddenCharmQuarkoniumExcitationFactor_two :
    hiddenCharmQuarkoniumExcitationFactor 2 = 1 + gamma_HQIV / 3 := rfl

/-- Hidden-charm radial $k=1$ ($\\psi(2S)$) shallow slot on the radial rung: $1-\\gamma/56$. -/
noncomputable def hiddenCharmQuarkoniumRadialK1SlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem hiddenCharmQuarkoniumRadialK1SlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    hiddenCharmQuarkoniumRadialK1SlotFactor = (139 : ℝ) / 140 := by
  simp [hiddenCharmQuarkoniumRadialK1SlotFactor, gamma_eq_2_5]
  norm_num

noncomputable def hiddenCharmQuarkoniumRadialSlotFactor (k : ℕ) : ℝ :=
  if k = 1 then hiddenCharmQuarkoniumRadialK1SlotFactor else 1

noncomputable def dressedHiddenCharmQuarkoniumExcitedMassMeV (mPiMeV : ℝ) (k : ℕ) : ℝ :=
  dressedHiddenCharmQuarkoniumMassMeV mPiMeV * hiddenCharmQuarkoniumExcitationFactor k *
    hiddenCharmQuarkoniumRadialSlotFactor k

/-- Vector $B^{*}$ hyperfine lift above dressed open-$B$ ground: $1+\gamma/32$ (CKM slot scale). -/
noncomputable def openBottomVectorMesonMassFactor : ℝ := 1 + gamma_HQIV / 32

theorem openBottomVectorMesonMassFactor_eq_eightyone_eightieths :
    openBottomVectorMesonMassFactor = (81 : ℝ) / 80 := by
  rw [openBottomVectorMesonMassFactor, gamma_eq_2_5]
  norm_num

noncomputable def dressedOpenBottomVectorMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV * openBottomVectorMesonMassFactor

/-- Hidden-$\Upsilon$ radial excitation rung: $k=1$ → $\Upsilon(2S)$; $k=2$ adds $\gamma/12$ above $2S$. -/
noncomputable def hiddenBottomQuarkoniumExcitationFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1 + gamma_HQIV / 6
  | 2 => 1 + gamma_HQIV / 6 + gamma_HQIV / 12
  | k + 3 => 1 + gamma_HQIV / 6 + gamma_HQIV / 12 + (k + 1 : ℝ) * gamma_HQIV / 6

theorem hiddenBottomQuarkoniumExcitationFactor_one :
    hiddenBottomQuarkoniumExcitationFactor 1 = 1 + gamma_HQIV / 6 := rfl

theorem hiddenBottomQuarkoniumExcitationFactor_two :
    hiddenBottomQuarkoniumExcitationFactor 2 = 1 + gamma_HQIV / 6 + gamma_HQIV / 12 := rfl

theorem hiddenBottomQuarkoniumExcitationFactor_two_eq_eleven_tenths :
    hiddenBottomQuarkoniumExcitationFactor 2 = (11 : ℝ) / 10 := by
  simp [hiddenBottomQuarkoniumExcitationFactor_two, gamma_eq_2_5]
  norm_num

theorem hiddenBottomQuarkoniumExcitationFactor_one_eq_sixteen_fifteenths :
    hiddenBottomQuarkoniumExcitationFactor 1 = (16 : ℝ) / 15 := by
  simp [hiddenBottomQuarkoniumExcitationFactor_one, gamma_eq_2_5]
  norm_num

/-- Hidden-bottom radial $k=1$ ($\\Upsilon(2S)$): shallow slot on radial rung, $1-\\gamma/56$. -/
noncomputable def hiddenBottomQuarkoniumRadialK1SlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem hiddenBottomQuarkoniumRadialK1SlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    hiddenBottomQuarkoniumRadialK1SlotFactor = (139 : ℝ) / 140 := by
  simp [hiddenBottomQuarkoniumRadialK1SlotFactor, gamma_eq_2_5]
  norm_num

/-- Hidden-bottom radial $k=2$ ($\\Upsilon(3S)$): shallow slot above $2S$, $1-\\gamma/80$. -/
noncomputable def hiddenBottomQuarkoniumRadialK2SlotFactor : ℝ := 1 - gamma_HQIV / 80

theorem hiddenBottomQuarkoniumRadialK2SlotFactor_eq_onehundredninetynine_twohundredths :
    hiddenBottomQuarkoniumRadialK2SlotFactor = (199 : ℝ) / 200 := by
  simp [hiddenBottomQuarkoniumRadialK2SlotFactor, gamma_eq_2_5]
  norm_num

noncomputable def hiddenBottomQuarkoniumRadialSlotFactor (k : ℕ) : ℝ :=
  if k = 1 then hiddenBottomQuarkoniumRadialK1SlotFactor
  else if k = 2 then hiddenBottomQuarkoniumRadialK2SlotFactor else 1

noncomputable def dressedHiddenBottomQuarkoniumExcitedMassMeV
    (mProtonMeV mPiMeV : ℝ) (k : ℕ) : ℝ :=
  dressedHiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV *
    hiddenBottomQuarkoniumExcitationFactor k * hiddenBottomQuarkoniumRadialSlotFactor k

/-- Open-charm--bottom meson ($B_c$): dressed open-$B$ plus up-type gap on the charmed rung. -/
noncomputable def openBcMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV +
    upTypeQuarkGapMeV * heavyFlavorGapFraction 1 * (1 - chiralPseudoscalarFactor)

/-- $B_c$ double-heavy monogamy correction on the open-$bc$ scaffold: $1/(1+\gamma/12)$. -/
noncomputable def openBcMassCorrectionFactor : ℝ := 1 / (1 + gamma_HQIV / 12)

theorem openBcMassCorrectionFactor_eq_thirty_thirtyfirsts :
    openBcMassCorrectionFactor = (30 : ℝ) / 31 := by
  simp [openBcMassCorrectionFactor, gamma_eq_2_5]
  norm_num

noncomputable def dressedOpenBcMesonMassMeV (mProtonMeV mPiMeV : ℝ) : ℝ :=
  openBcMesonMassMeV mProtonMeV mPiMeV * openBcMassCorrectionFactor

/-- Decuplet $\Sigma(1385)$ orbital slot correction on TUFT $(n,\ell)=(0,2)$ negative parity. -/
noncomputable def decupletStrangeOrbitalMassFactor : ℝ := 1 - gamma_HQIV / 20

theorem decupletStrangeOrbitalMassFactor_eq_fortynine_fiftieths :
    decupletStrangeOrbitalMassFactor = (49 : ℝ) / 50 := by
  simp [decupletStrangeOrbitalMassFactor, gamma_eq_2_5]
  norm_num

/-- $\Lambda(1405)$ strange-octet orbital slot: shallow negative parity net of $\gamma/40$ coupling. -/
noncomputable def lambdaStrangeOrbitalMassFactor : ℝ := 1 - gamma_HQIV / 28 + gamma_HQIV / 40

theorem lambdaStrangeOrbitalMassFactor_eq_sixhundredninetyseven_sevenhundredths :
    lambdaStrangeOrbitalMassFactor = (697 : ℝ) / 700 := by
  simp [lambdaStrangeOrbitalMassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1440)$ Roper on TUFT $(0,2,+)$: shallow P-wave breathing slot $1-\gamma/100$. -/
noncomputable def nucleonResonance1440MassFactor : ℝ := 1 - gamma_HQIV / 100

theorem nucleonResonance1440MassFactor_eq_twohundredfortynine_twohundredfiftieths :
    nucleonResonance1440MassFactor = (249 : ℝ) / 250 := by
  simp [nucleonResonance1440MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1535)$ on TUFT $(1,1)$: shallow S-wave orbital coupling $1+\gamma/40$. -/
noncomputable def nucleonResonance1535MassFactor : ℝ := 1 + gamma_HQIV / 40

theorem nucleonResonance1535MassFactor_eq_oneohone_hundredths :
    nucleonResonance1535MassFactor = (101 : ℝ) / 100 := by
  simp [nucleonResonance1535MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1650)$ on TUFT $(0,3,-)$: D-wave negative-parity slot $1-\gamma/16$. -/
noncomputable def nucleonResonance1650MassFactor : ℝ := 1 - gamma_HQIV / 16

theorem nucleonResonance1650MassFactor_eq_thirtynine_fortieths :
    nucleonResonance1650MassFactor = (39 : ℝ) / 40 := by
  simp [nucleonResonance1650MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1675)$ on TUFT $(0,3,-)$: D-wave fine structure $1-\gamma/40$. -/
noncomputable def nucleonResonance1675MassFactor : ℝ := 1 - gamma_HQIV / 40

theorem nucleonResonance1675MassFactor_eq_ninetynine_hundredths :
    nucleonResonance1675MassFactor = (99 : ℝ) / 100 := by
  simp [nucleonResonance1675MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1720)$ on TUFT $(0,3,+)$: D-wave positive-parity slot $1-\gamma/40$. -/
noncomputable def nucleonResonance1720MassFactor : ℝ := 1 - gamma_HQIV / 40

theorem nucleonResonance1720MassFactor_eq_ninetynine_hundredths :
    nucleonResonance1720MassFactor = (99 : ℝ) / 100 := by
  simp [nucleonResonance1720MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1680)$ on TUFT $(0,3,-)$: D-wave negative-parity fine structure $1-\gamma/56$. -/
noncomputable def nucleonResonance1680MassFactor : ℝ := 1 - gamma_HQIV / 56

theorem nucleonResonance1680MassFactor_eq_onehundredthirtynine_onehundredfortieths :
    nucleonResonance1680MassFactor = (139 : ℝ) / 140 := by
  simp [nucleonResonance1680MassFactor, gamma_eq_2_5]
  norm_num

/-- $N(1710)$ on TUFT $(0,3,+)$: D-wave positive-parity slot $1-\gamma/28$. -/
noncomputable def nucleonResonance1710MassFactor : ℝ := 1 - gamma_HQIV / 28

theorem nucleonResonance1710MassFactor_eq_sixtynine_seventieths :
    nucleonResonance1710MassFactor = (69 : ℝ) / 70 := by
  simp [nucleonResonance1710MassFactor, gamma_eq_2_5]
  norm_num

/-- Open-$D^*$ radial excitation mirrors hidden-charm radial rungs ($\psi(2S)$ ladder). -/
noncomputable def openCharmVectorRadialExcitationFactor (k : ℕ) : ℝ :=
  hiddenCharmQuarkoniumExcitationFactor k

theorem openCharmVectorRadialExcitationFactor_one :
    openCharmVectorRadialExcitationFactor 1 = 1 + gamma_HQIV / 2 := rfl

/-- First open-$D^*$ radial rung ($D^{*0}(2S)$): shallow slot on radial coupling, $1-\\gamma/40$. -/
noncomputable def openCharmVectorRadialK1SlotFactor : ℝ := 1 - gamma_HQIV / 40

theorem openCharmVectorRadialK1SlotFactor_eq_ninetynine_hundredths :
    openCharmVectorRadialK1SlotFactor = (99 : ℝ) / 100 := by
  simp [openCharmVectorRadialK1SlotFactor, gamma_eq_2_5]
  norm_num

noncomputable def openCharmVectorRadialSlotFactor (k : ℕ) : ℝ :=
  if k = 1 then openCharmVectorRadialK1SlotFactor else 1

noncomputable def dressedOpenCharmVectorRadialMassMeV (mPiMeV : ℝ) (k : ℕ) : ℝ :=
  dressedOpenCharmVectorCoreMassMeV mPiMeV * openCharmVectorRadialExcitationFactor k *
    openCharmVectorRadialSlotFactor k

noncomputable def dressedOpenCharmStrangeVectorRadialMassMeV (mPiMeV mKMeV : ℝ) (k : ℕ) : ℝ :=
  openCharmStrangeMesonMassMeV mPiMeV mKMeV * openCharmVectorMesonMassFactor *
    openCharmVectorRadialExcitationFactor k * openCharmVectorRadialSlotFactor k *
    openCharmStrangeVectorRadialSlotFactor k

/-- Decuplet $(0,2,-)$ with $n_s=2$ ($\\Xi^*$): double-strangeness orbital slot $1-\\gamma/56$. -/
noncomputable def decupletDoubleStrangenessOrbitalSlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem decupletDoubleStrangenessOrbitalSlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    decupletDoubleStrangenessOrbitalSlotFactor = (139 : ℝ) / 140 := by
  simp [decupletDoubleStrangenessOrbitalSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Xi^*$ double-strangeness decuplet ($n_s=2$): shallow slot $1-\gamma/140$. -/
noncomputable def decupletDoubleStrangenessNs2SlotFactor : ℝ := 1 - gamma_HQIV / 140

theorem decupletDoubleStrangenessNs2SlotFactor_eq_threehundredfortynine_threehundredfiftieths :
    decupletDoubleStrangenessNs2SlotFactor = (349 : ℝ) / 350 := by
  simp [decupletDoubleStrangenessNs2SlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Omega^*$ triple-strangeness decuplet ($n_s=3$): shallow slot $1-\gamma/112$. -/
noncomputable def decupletTripleStrangenessOrbitalSlotFactor : ℝ := 1 - gamma_HQIV / 112

theorem decupletTripleStrangenessOrbitalSlotFactor_eq_twohundredseventynine_twohundredeightieths :
    decupletTripleStrangenessOrbitalSlotFactor = (279 : ℝ) / 280 := by
  simp [decupletTripleStrangenessOrbitalSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Delta(1232)$ decuplet ground on TUFT $(0,1,+)$: shallow slot $1-\gamma/56$. -/
noncomputable def decupletGroundSlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem decupletGroundSlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    decupletGroundSlotFactor = (139 : ℝ) / 140 := by
  simp [decupletGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- Light isoscalar vector ($\omega$) on TUFT $(0,1)$: shallow slot $1-\gamma/56$. -/
noncomputable def lightVectorIsoscalarSlotFactor : ℝ := 1 - gamma_HQIV / 56

theorem lightVectorIsoscalarSlotFactor_eq_onehundredthirtynine_onehundredfortieths :
    lightVectorIsoscalarSlotFactor = (139 : ℝ) / 140 := by
  simp [lightVectorIsoscalarSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\phi(1020)$ hidden-strangeness vector: shallow net slot $1-\gamma/100$ on dressed readout. -/
noncomputable def hiddenStrangenessVectorGroundSlotFactor : ℝ := 1 - gamma_HQIV / 100

theorem hiddenStrangenessVectorGroundSlotFactor_eq_twohundredfortynine_twohundredfiftieths :
    hiddenStrangenessVectorGroundSlotFactor = (249 : ℝ) / 250 := by
  simp [hiddenStrangenessVectorGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- $K^*(892)$ with $n_s=1$ on $(1,0)$: shallow slot $1-\gamma/100$. -/
noncomputable def strangeKstarNs1SlotFactor : ℝ := 1 - gamma_HQIV / 100

theorem strangeKstarNs1SlotFactor_eq_twohundredfortynine_twohundredfiftieths :
    strangeKstarNs1SlotFactor = (249 : ℝ) / 250 := by
  simp [strangeKstarNs1SlotFactor, gamma_eq_2_5]
  norm_num

/-- $N(1520)$ on TUFT $(1,1,-)$: negative-parity S-wave slot $1+\gamma/80$. -/
noncomputable def nucleonResonance1520MassFactor : ℝ := 1 + gamma_HQIV / 80

theorem nucleonResonance1520MassFactor_eq_twohundredone_twohundredths :
    nucleonResonance1520MassFactor = (201 : ℝ) / 200 := by
  simp [nucleonResonance1520MassFactor, gamma_eq_2_5]
  norm_num

/-- Decuplet $(0,2,-)$ scaffold plus strangeness rungs (Σ* ground in scaffold; Ξ*, Ω* lifts). -/
noncomputable def decupletStrangeOrbitalMultipletMassMeV
    (scaffoldMeV mKMeV mPiMeV : ℝ) (nStrange : ℕ) : ℝ :=
  if nStrange ≤ 1 then scaffoldMeV
  else if nStrange = 2 then
    (scaffoldMeV + heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV 1) *
      decupletDoubleStrangenessOrbitalSlotFactor
  else
    scaffoldMeV * (1 + gamma_HQIV / 4) + heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV 1

theorem decupletStrangeOrbitalMultipletMassMeV_one (scaffoldMeV mKMeV mPiMeV : ℝ) :
    decupletStrangeOrbitalMultipletMassMeV scaffoldMeV mKMeV mPiMeV 1 = scaffoldMeV := by
  simp [decupletStrangeOrbitalMultipletMassMeV]

/-- Charmed tetraquark ($DD^*$) vector molecular binding above open-charm pair. -/
noncomputable def charmedTetraquarkOpenStrangeFactor : ℝ := 1 + gamma_HQIV / 8

theorem charmedTetraquarkOpenStrangeFactor_eq_twentyone_twentieths :
    charmedTetraquarkOpenStrangeFactor = (21 : ℝ) / 20 := by
  simp [charmedTetraquarkOpenStrangeFactor, gamma_eq_2_5]
  norm_num

/-- $Z(3900)$ open-strange tetraquark: shallow radial coupling $1-\gamma/12$. -/
noncomputable def charmedTetraquarkOpenStrangeZFactor : ℝ := 1 - gamma_HQIV / 12

theorem charmedTetraquarkOpenStrangeZFactor_eq_twentynine_thirtieths :
    charmedTetraquarkOpenStrangeZFactor = (29 : ℝ) / 30 := by
  simp [charmedTetraquarkOpenStrangeZFactor, gamma_eq_2_5]
  norm_num

/-- Charmed tetraquark ($D\bar D_s$) higher binding ($X(4140)$ slot): $1+\gamma/5$. -/
noncomputable def charmedTetraquarkOpenStrangeOrbitalFactor : ℝ := 1 + gamma_HQIV / 5

theorem charmedTetraquarkOpenStrangeOrbitalFactor_eq_twentyseven_twentyfifths :
    charmedTetraquarkOpenStrangeOrbitalFactor = (27 : ℝ) / 25 := by
  simp [charmedTetraquarkOpenStrangeOrbitalFactor, gamma_eq_2_5]
  norm_num

/-- Charmed tetraquark ($DD^*$) molecular binding above open-charm vector pair. -/
noncomputable def charmedTetraquarkOpenVectorFactor : ℝ := 1 + gamma_HQIV / 5

theorem charmedTetraquarkOpenVectorFactor_eq_twentyseven_twentyfifths :
    charmedTetraquarkOpenVectorFactor = (27 : ℝ) / 25 := by
  simp [charmedTetraquarkOpenVectorFactor, gamma_eq_2_5]
  norm_num

/-- $X(4274)$-class open-vector tetraquark: shallow hidden-strangeness vector coupling. -/
noncomputable def charmedTetraquarkOpenVectorExcitedFactor : ℝ := 1 + gamma_HQIV / 24

theorem charmedTetraquarkOpenVectorExcitedFactor_eq_sixtyone_sixtieths :
    charmedTetraquarkOpenVectorExcitedFactor = (61 : ℝ) / 60 := by
  simp [charmedTetraquarkOpenVectorExcitedFactor, gamma_eq_2_5]
  norm_num

theorem charmedTetraquarkOpenVectorExcitedFactor_eq_hiddenStrangenessVectorDressing :
    charmedTetraquarkOpenVectorExcitedFactor = hiddenStrangenessVectorOutsideMassDressing := by
  simp [charmedTetraquarkOpenVectorExcitedFactor, hiddenStrangenessVectorOutsideMassDressing]

/-- Doubly-open-charm tetraquark ($T_{cc}$): $2M_D$ plus shallow binding. -/
noncomputable def charmedTetraquarkDoubleOpenFactor : ℝ := 1 + gamma_HQIV / 12

theorem charmedTetraquarkDoubleOpenFactor_eq_thirtyone_thirtieths :
    charmedTetraquarkDoubleOpenFactor = (31 : ℝ) / 30 := by
  simp [charmedTetraquarkDoubleOpenFactor, gamma_eq_2_5]
  norm_num

/-- Charmed pentaquark ($\Lambda_c D^*$) excitation rungs above the ground molecular scaffold. -/
noncomputable def charmedPentaquarkExcitationFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1 + gamma_HQIV / 16
  | 2 => 1 + gamma_HQIV / 12
  | k + 3 => 1 + gamma_HQIV / 16 + (k + 1 : ℝ) * gamma_HQIV / 12

theorem charmedPentaquarkExcitationFactor_one :
    charmedPentaquarkExcitationFactor 1 = 1 + gamma_HQIV / 16 := rfl

theorem charmedPentaquarkExcitationFactor_two :
    charmedPentaquarkExcitationFactor 2 = 1 + gamma_HQIV / 12 := rfl

/-- $P_c(4380)$ orbit-split above $P_c(4312)$ ground molecular scaffold: $1+\gamma/28$. -/
noncomputable def charmedPentaquarkOrbitSplitFactor : ℝ := 1 + gamma_HQIV / 28

theorem charmedPentaquarkOrbitSplitFactor_eq_seventyone_seventieths :
    charmedPentaquarkOrbitSplitFactor = (71 : ℝ) / 70 := by
  simp [charmedPentaquarkOrbitSplitFactor, gamma_eq_2_5]
  norm_num

/-- $P_c(4440)$ first excitation rung shallow slot: $1+\gamma/56$. -/
noncomputable def charmedPentaquarkExcitationK1SlotFactor : ℝ := 1 + gamma_HQIV / 56

theorem charmedPentaquarkExcitationK1SlotFactor_eq_onehundredfortyone_onehundredfortieths :
    charmedPentaquarkExcitationK1SlotFactor = (141 : ℝ) / 140 := by
  simp [charmedPentaquarkExcitationK1SlotFactor, gamma_eq_2_5]
  norm_num

/-- $P_c(4312)$ ground excitation shallow slot: $1+\gamma/80$. -/
noncomputable def charmedPentaquarkExcitationK0SlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem charmedPentaquarkExcitationK0SlotFactor_eq_twohundredone_twohundredths :
    charmedPentaquarkExcitationK0SlotFactor = (201 : ℝ) / 200 := by
  simp [charmedPentaquarkExcitationK0SlotFactor, gamma_eq_2_5]
  norm_num

/-- $P_c(4457)$ second excitation shallow slot: $1+\gamma/56$. -/
noncomputable def charmedPentaquarkExcitationK2SlotFactor : ℝ := 1 + gamma_HQIV / 56

theorem charmedPentaquarkExcitationK2SlotFactor_eq_onehundredfortyone_onehundredfortieths :
    charmedPentaquarkExcitationK2SlotFactor = (141 : ℝ) / 140 := by
  simp [charmedPentaquarkExcitationK2SlotFactor, gamma_eq_2_5]
  norm_num

/-- $P_c(4380)$ orbit-split ground shallow slot: $1+\gamma/80$. -/
noncomputable def charmedPentaquarkOrbitSplitGroundSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem charmedPentaquarkOrbitSplitGroundSlotFactor_eq_twohundredone_twohundredths :
    charmedPentaquarkOrbitSplitGroundSlotFactor = (201 : ℝ) / 200 := by
  simp [charmedPentaquarkOrbitSplitGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- Open-$D_s$ ground shallow slot: $1+\gamma/80$. -/
noncomputable def openCharmStrangeGroundSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem openCharmStrangeGroundSlotFactor_eq_twohundredone_twohundredths :
    openCharmStrangeGroundSlotFactor = (201 : ℝ) / 200 := by
  simp [openCharmStrangeGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- Open-vector excited tetraquark ($X(4274)$) shallow slot: $1+\gamma/80$. -/
noncomputable def charmedTetraquarkOpenVectorExcitedSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem charmedTetraquarkOpenVectorExcitedSlotFactor_eq_twohundredone_twohundredths :
    charmedTetraquarkOpenVectorExcitedSlotFactor = (201 : ℝ) / 200 := by
  simp [charmedTetraquarkOpenVectorExcitedSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Lambda_c$ ground multiplet shallow slot: $1-\gamma/80$. -/
noncomputable def charmedLambdaGroundSlotFactor : ℝ := 1 - gamma_HQIV / 80

theorem charmedLambdaGroundSlotFactor_eq_onehundredninetynine_twohundredths :
    charmedLambdaGroundSlotFactor = (199 : ℝ) / 200 := by
  simp [charmedLambdaGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Omega_c$ ground shallow slot: $1-\gamma/100$. -/
noncomputable def charmedOmegaGroundSlotFactor : ℝ := 1 - gamma_HQIV / 100

theorem charmedOmegaGroundSlotFactor_eq_twohundredfortynine_twohundredfiftieths :
    charmedOmegaGroundSlotFactor = (249 : ℝ) / 250 := by
  simp [charmedOmegaGroundSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Omega_{cc}$ ($\Xi$ doubly charmed) shallow slot: $1-\gamma/100$. -/
noncomputable def charmedXiDoubleCharmSlotFactor : ℝ := 1 - gamma_HQIV / 100

theorem charmedXiDoubleCharmSlotFactor_eq_twohundredfortynine_twohundredfiftieths :
    charmedXiDoubleCharmSlotFactor = (249 : ℝ) / 250 := by
  simp [charmedXiDoubleCharmSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Xi_c'$ shallow positive slot on radial excitation: $1+\gamma/80$. -/
noncomputable def charmedBaryonXiPrimeSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem charmedBaryonXiPrimeSlotFactor_eq_twohundredone_twohundredths :
    charmedBaryonXiPrimeSlotFactor = (201 : ℝ) / 200 := by
  simp [charmedBaryonXiPrimeSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Omega_b$ bottom multiplet shallow slot: $1+\gamma/80$. -/
noncomputable def bottomOmegaMultipletSlotFactor : ℝ := 1 + gamma_HQIV / 80

theorem bottomOmegaMultipletSlotFactor_eq_twohundredone_twohundredths :
    bottomOmegaMultipletSlotFactor = (201 : ℝ) / 200 := by
  simp [bottomOmegaMultipletSlotFactor, gamma_eq_2_5]
  norm_num

/-- $\Xi_c'$ radial excitation: $\Sigma_c$ hyperfine step net of the shallow $\gamma/16$ radial slot. -/
noncomputable def charmedBaryonXiPrimeExcitationFactor : ℝ := 1 + gamma_HQIV / 6 - gamma_HQIV / 16

theorem charmedBaryonXiPrimeExcitationFactor_eq_twentyfive_twentyfourths :
    charmedBaryonXiPrimeExcitationFactor = (25 : ℝ) / 24 := by
  simp [charmedBaryonXiPrimeExcitationFactor, gamma_eq_2_5]
  norm_num

theorem charmedBaryonXiPrimeExcitationFactor_eq_sigma_hyperfine_minus_penta_rung :
    charmedBaryonXiPrimeExcitationFactor =
      charmedBaryonSigmaHyperfineWeight - gamma_HQIV / 16 := by
  simp [charmedBaryonXiPrimeExcitationFactor, charmedBaryonSigmaHyperfineWeight]

noncomputable def dressedCharmedBaryonMassMeV
    (mProtonMeV mKMeV mPiMeV : ℝ) (nCharm nStrange : ℕ) : ℝ :=
  charmedBaryonMassMeV mProtonMeV mKMeV mPiMeV nCharm nStrange *
    charmedBaryonOutsideMassDressing

/-- Isospin-$I_3$ charge shift on the hypercharge bookkeeping unit (`nucleonIsospinGap_MeV`). -/
noncomputable def isospinThirdChargeShiftMeV (i3 : ℝ) (_mProtonMeV _mPiMeV : ℝ) : ℝ :=
  i3 * gamma_HQIV * nucleonIsospinGap_MeV

/-- Discharged $I_3$ labels for isospin multiplets (representation slot, not a fitted mass). -/
inductive IsospinThirdSlot where
  | zero
  | halfPlus
  | halfMinus
  | plus
  | minus
  deriving DecidableEq, Repr

def isospinThirdOfSlot (s : IsospinThirdSlot) : ℚ :=
  match s with
  | .zero => 0
  | .halfPlus => 1 / 2
  | .halfMinus => -(1 / 2)
  | .plus => 1
  | .minus => -1

theorem isospinThirdOfSlot_halfPlus : (isospinThirdOfSlot .halfPlus : ℝ) = (1 : ℝ) / 2 := by
  norm_num [isospinThirdOfSlot]

theorem isospinThirdOfSlot_plus : (isospinThirdOfSlot .plus : ℝ) = 1 := by
  norm_num [isospinThirdOfSlot]

/-- Baryon $I_3$ from light $u,d$ quark counts (each $u$ carries $+1/2$, each $d$ carries $-1/2$). -/
def baryonValenceIsospinThird (nUp nDown : ℕ) : ℚ :=
  (nUp : ℚ) * (1 / 2) + (nDown : ℚ) * (-1 / 2)

/-- Meson $I_3$ from light $u,d$ valence slots (quark + antiquark). -/
def mesonValenceIsospinThird
    (nUpQuark nDownQuark nUpAntiquark nDownAntiquark : ℕ) : ℚ :=
  (nUpQuark : ℚ) * (1 / 2) + (nDownQuark : ℚ) * (-1 / 2) +
    (nUpAntiquark : ℚ) * (-1 / 2) + (nDownAntiquark : ℚ) * (1 / 2)

theorem baryonValenceIsospinThird_uud :
    baryonValenceIsospinThird 2 1 = (1 / 2 : ℚ) := by
  norm_num [baryonValenceIsospinThird]

theorem baryonValenceIsospinThird_uus :
    baryonValenceIsospinThird 2 0 = 1 := by
  norm_num [baryonValenceIsospinThird]

theorem mesonValenceIsospinThird_Dplus :
    mesonValenceIsospinThird 0 0 0 1 = (1 / 2 : ℚ) := by
  norm_num [mesonValenceIsospinThird]

def isospinThirdSlotOfRational (i3 : ℚ) : Option IsospinThirdSlot :=
  if i3 = 0 then some .zero
  else if i3 = 1 / 2 then some .halfPlus
  else if i3 = -(1 / 2) then some .halfMinus
  else if i3 = 1 then some .plus
  else if i3 = -1 then some .minus
  else none

theorem isospinThirdSlotOfRational_baryon_uud :
    isospinThirdSlotOfRational (baryonValenceIsospinThird 2 1) = some .halfPlus := by
  norm_num [isospinThirdSlotOfRational, baryonValenceIsospinThird]

theorem isospinThirdSlotOfRational_meson_Dplus :
    isospinThirdSlotOfRational (mesonValenceIsospinThird 0 0 0 1) = some .halfPlus := by
  norm_num [isospinThirdSlotOfRational, mesonValenceIsospinThird]

noncomputable def isospinThirdChargeShiftMeV_ofSlot (s : IsospinThirdSlot) (mProtonMeV mPiMeV : ℝ) : ℝ :=
  isospinThirdChargeShiftMeV (isospinThirdOfSlot s : ℝ) mProtonMeV mPiMeV

noncomputable def dressedCharmedBaryonMultipletMassMeV
    (mProtonMeV mKMeV mPiMeV : ℝ) (mult : CharmedBaryonMultiplet) (nCharm : ℕ) : ℝ :=
  charmedBaryonMassMeV_multiplet mProtonMeV mKMeV mPiMeV mult nCharm *
    charmedBaryonOutsideMassDressing

noncomputable def dressedCharmedBaryonMultipletMassMeV_withIsospin
    (mProtonMeV mKMeV mPiMeV : ℝ) (mult : CharmedBaryonMultiplet) (nCharm : ℕ) (i3 : ℝ) : ℝ :=
  dressedCharmedBaryonMultipletMassMeV mProtonMeV mKMeV mPiMeV mult nCharm +
    isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedOpenBottomStrangeMesonMassMeV (mProtonMeV mPiMeV mKMeV : ℝ) : ℝ :=
  openBottomStrangeMesonMassMeV mProtonMeV mPiMeV mKMeV

noncomputable def dressedBottomBaryonMassMeV
    (mProtonMeV mPiMeV mKMeV : ℝ) (mult : BottomBaryonMultiplet) (nCharm : ℕ := 0) : ℝ :=
  bottomBaryonMassMeV mProtonMeV mPiMeV mKMeV mult nCharm *
    bottomBaryonOutsideMassDressing

noncomputable def dressedBottomBaryonMassMeV_withIsospin
    (mProtonMeV mPiMeV mKMeV : ℝ) (mult : BottomBaryonMultiplet) (nCharm : ℕ) (i3 : ℝ) : ℝ :=
  dressedBottomBaryonMassMeV mProtonMeV mPiMeV mKMeV mult nCharm +
    isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedOpenCharmMesonMassMeV_withIsospin (mPiMeV mProtonMeV : ℝ) (i3 : ℝ) : ℝ :=
  dressedOpenCharmMesonMassMeV mPiMeV + isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedOpenBottomMesonMassMeV_withIsospin (mProtonMeV mPiMeV : ℝ) (i3 : ℝ) : ℝ :=
  dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV + isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedOpenCharmVectorMesonMassMeV_withIsospin (mPiMeV mProtonMeV : ℝ) (i3 : ℝ) : ℝ :=
  dressedOpenCharmVectorMesonMassMeV mPiMeV + isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedOpenBottomVectorMesonMassMeV_withIsospin (mProtonMeV mPiMeV : ℝ) (i3 : ℝ) : ℝ :=
  dressedOpenBottomVectorMesonMassMeV mProtonMeV mPiMeV + isospinThirdChargeShiftMeV i3 mProtonMeV mPiMeV

noncomputable def dressedBottomBaryonMassMeV_fromStrangeCount
    (mProtonMeV mPiMeV mKMeV : ℝ) (_nBottom nCharm nStrange : ℕ) : ℝ :=
  bottomBaryonMassMeV_fromStrangeCount mProtonMeV mPiMeV mKMeV _nBottom nCharm nStrange *
    bottomBaryonOutsideMassDressing

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

/-- OZI / Zweig suppression for open-charm-strange strong light-hadron discharge. -/
noncomputable def oziSuppressedStrongContact : ℝ :=
  gamma_HQIV / 4

theorem oziSuppressedStrongContact_eq_one_tenth :
    oziSuppressedStrongContact = (1 : ℝ) / 10 := by
  simp [oziSuppressedStrongContact, gamma_eq_2_5]
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

/-- EM contact = open-bottom external weak contact + shared Rindler detuning coefficient. -/
theorem hiddenQuarkoniumEMContactFactor_eq_bottomExternal_plus_rindler :
    hiddenQuarkoniumEMContactFactor = bottomExternalWeakContact + c_rindler_shared := by
  simp [hiddenQuarkoniumEMContactFactor, bottomExternalWeakContact, c_rindler_shared, gamma_eq_2_5]

/-- Full second-order Fano return (`+γ`) would overshoot once hadronic sectors pool. -/
theorem hiddenQuarkoniumEMContactFactor_plus_rindler_eq_bottomExternal_plus_gamma :
    hiddenQuarkoniumEMContactFactor + c_rindler_shared =
      bottomExternalWeakContact + gamma_HQIV := by
  rw [hiddenQuarkoniumEMContactFactor_eq_bottomExternal_plus_rindler]
  unfold c_rindler_shared
  ring_nf

theorem bottomExternalWeakContact_plus_gamma_eq_thirtynine_tenths :
    bottomExternalWeakContact + gamma_HQIV = (39 : ℝ) / 10 := by
  simp [bottomExternalWeakContact, gamma_eq_2_5]
  norm_num

theorem hiddenQuarkoniumEMContactFactor_ne_pdg_reverse_engineered :
    hiddenQuarkoniumEMContactFactor ≠ (347 : ℝ) / 100 := by
  rw [hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths]
  norm_num

structure QuarkoniumEMContactDerived where
  spine_decomposition :
    hiddenQuarkoniumEMContactFactor = bottomExternalWeakContact + c_rindler_shared
  half_not_full_fano :
    hiddenQuarkoniumEMContactFactor + c_rindler_shared =
      bottomExternalWeakContact + gamma_HQIV
  not_pdg_fit_knob : hiddenQuarkoniumEMContactFactor ≠ (347 : ℝ) / 100

noncomputable def quarkoniumEMContactDerived : QuarkoniumEMContactDerived where
  spine_decomposition := hiddenQuarkoniumEMContactFactor_eq_bottomExternal_plus_rindler
  half_not_full_fano := hiddenQuarkoniumEMContactFactor_plus_rindler_eq_bottomExternal_plus_gamma
  not_pdg_fit_knob := hiddenQuarkoniumEMContactFactor_ne_pdg_reverse_engineered

/--
Bottom-strange double-monogamy coherence for hidden-strangeness discharge
(`B_s → φφ`): two inverse monogamy rungs in the strange-bottom sector (`1/γ²`).
-/
noncomputable def bottomStrangeDoubleMonogamyCoherence : ℝ :=
  1 / gamma_HQIV ^ 2

theorem bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths :
    bottomStrangeDoubleMonogamyCoherence = (25 : ℝ) / 4 := by
  simp [bottomStrangeDoubleMonogamyCoherence, gamma_eq_2_5]
  norm_num

/--
Heavy-quarkonium cascade weight on the production ladder:
open-charm rung over open-bottom rung (`(γ/4)/(γ/8) = 2`).
-/
noncomputable def heavyQuarkoniumCascadeWeight : ℝ :=
  openCharmProductionWeight / openBottomProductionWeight

theorem heavyQuarkoniumCascadeWeight_eq :
    heavyQuarkoniumCascadeWeight = 2 := by
  simp [heavyQuarkoniumCascadeWeight, openCharmProductionWeight, openBottomProductionWeight, gamma_eq_2_5]
  norm_num

/--
Open-charm lift on `B_s → D_s K`: the explicit `D_s` carries the open-charm
production rung over open-bottom (`2`), on top of bottom-strange coherence.
-/
noncomputable def bottomStrangeOpenCharmContact : ℝ :=
  bottomStrangeDoubleMonogamyCoherence * heavyQuarkoniumCascadeWeight

theorem bottomStrangeOpenCharmContact_eq_twentyfive_halves :
    bottomStrangeOpenCharmContact = (25 : ℝ) / 2 := by
  simp [bottomStrangeOpenCharmContact, bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths,
    heavyQuarkoniumCascadeWeight_eq]
  norm_num

/-!
## Spine-derived gap-closure candidates

These are not fitted weights. They are exact apertures already available from
the HQIV spine (`γ`, monogamy complement, and the weak bridge shape). Python may
use them as diagnostic candidate terms for residual branching/lifetime gaps.
-/

/-- Missing finite-channel aperture carried by the weak Fano/Hopf bridge. -/
noncomputable def finiteChannelCompletionAperture : ℝ :=
  gamma_HQIV * weakBridgeShape defaultBetaWeakBridge

theorem finiteChannelCompletionAperture_eq_gamma_times_weakBridgeShape :
    finiteChannelCompletionAperture =
      gamma_HQIV * weakBridgeShape defaultBetaWeakBridge := rfl

theorem finiteChannelCompletionAperture_eq_one_fortyfive :
    finiteChannelCompletionAperture = (1 : ℝ) / 45 := by
  rw [finiteChannelCompletionAperture_eq_gamma_times_weakBridgeShape,
    defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
  norm_num

/--
Open-bottom finite weak completion ($B\\to D^{(*)}K$, $D\\rho$, …): five
open-charm spectator rungs dilute the charged $D\\pi$ flagship outlets.
-/
noncomputable def finiteOpenBottomCompletionContact : ℝ :=
  finiteChannelCompletionAperture * (1 + 5 * gamma_HQIV)

theorem finiteOpenBottomCompletionContact_eq_one_fifteenth :
    finiteOpenBottomCompletionContact = (1 : ℝ) / 15 := by
  rw [finiteOpenBottomCompletionContact, finiteChannelCompletionAperture_eq_one_fortyfive, gamma_eq_2_5]
  norm_num

/-- Double-monogamy exclusion factor for over-counted charm/baryon family outlets. -/
noncomputable def doubleMonogamyExclusionFactor : ℝ :=
  1 - gamma_HQIV ^ 2

theorem doubleMonogamyExclusionFactor_eq_twentyone_twentyfive :
    doubleMonogamyExclusionFactor = (21 : ℝ) / 25 := by
  simp [doubleMonogamyExclusionFactor, gamma_eq_2_5]
  norm_num

theorem doubleMonogamyExclusionFactor_eq_one_minus_gamma_sq :
    doubleMonogamyExclusionFactor = 1 - gamma_HQIV ^ 2 := by
  rfl

/-- Half-monogamy spectator contact for charged open-bottom spectator channels. -/
noncomputable def spectatorHalfMonogamyContact : ℝ :=
  1 + gamma_HQIV / 2

theorem spectatorHalfMonogamyContact_eq_six_fifths :
    spectatorHalfMonogamyContact = (6 : ℝ) / 5 := by
  simp [spectatorHalfMonogamyContact, gamma_eq_2_5]
  norm_num

/--
Weak ΔI = 1/2 charged-outlet contact on the SU(2)\_L isospin doublet:
one oriented I₃ step carries the full curvature rung (`1 + γ`).
Used for Λ → p π⁻ and K → π⁺ (and three-body K when a charged π is present).
-/
noncomputable def isospinHalfWeakContact : ℝ :=
  1 + gamma_HQIV

theorem isospinHalfWeakContact_eq_seven_fifths :
    isospinHalfWeakContact = (7 : ℝ) / 5 := by
  simp [isospinHalfWeakContact, gamma_eq_2_5]
  norm_num

/--
Neutral-isovector outlet complement on the same ΔI = 1/2 transitions (`1 − γ`).
Λ → n π⁰ and K → π⁰ carry this slot; charged partners use `isospinHalfWeakContact`.
-/
noncomputable def isospinHalfNeutralOutletContact : ℝ :=
  1 - gamma_HQIV

theorem isospinHalfNeutralOutletContact_eq_three_fifths :
    isospinHalfNeutralOutletContact = (3 : ℝ) / 5 := by
  simp [isospinHalfNeutralOutletContact, gamma_eq_2_5]
  norm_num

/-- Isospin-$I_3$ charge shift equals the charged vs neutral weak-outlet half-gap on the
hypercharge unit: $\Delta m = I_3 \cdot (7/5 - 3/5)/2 \cdot 1\,\mathrm{MeV}$. -/
theorem isospinThirdChargeShiftMeV_eq_outlet_gap (i3 : ℝ) (_mProtonMeV _mPiMeV : ℝ) :
    isospinThirdChargeShiftMeV i3 _mProtonMeV _mPiMeV =
      i3 * (isospinHalfWeakContact - isospinHalfNeutralOutletContact) / 2 *
        nucleonIsospinGap_MeV := by
  simp only [isospinThirdChargeShiftMeV, isospinHalfWeakContact_eq_seven_fifths,
    isospinHalfNeutralOutletContact_eq_three_fifths, gamma_eq_2_5]
  ring

theorem isospinThirdChargeShiftMeV_zero (_mProtonMeV _mPiMeV : ℝ) :
    isospinThirdChargeShiftMeV 0 _mProtonMeV _mPiMeV = 0 := by
  simp [isospinThirdChargeShiftMeV]

theorem isospinThirdChargeShiftMeV_eq_i3_times_two_fifths :
    isospinThirdChargeShiftMeV i3 _mProtonMeV _mPiMeV = i3 * (2 / 5 : ℝ) * nucleonIsospinGap_MeV := by
  rw [isospinThirdChargeShiftMeV_eq_outlet_gap, isospinHalfWeakContact_eq_seven_fifths,
    isospinHalfNeutralOutletContact_eq_three_fifths]
  ring

theorem isospinThirdChargeShiftMeV_one_eq_two_fifths (_mProtonMeV _mPiMeV : ℝ) :
    isospinThirdChargeShiftMeV 1 _mProtonMeV _mPiMeV = (2 / 5 : ℝ) * nucleonIsospinGap_MeV := by
  simp [isospinThirdChargeShiftMeV_eq_i3_times_two_fifths]

theorem isospinThirdChargeShiftMeV_one_eq_two_fifths_meV (_mProtonMeV _mPiMeV : ℝ) :
    isospinThirdChargeShiftMeV 1 _mProtonMeV _mPiMeV = (2 / 5 : ℝ) := by
  rw [isospinThirdChargeShiftMeV_one_eq_two_fifths, nucleonIsospinGap_eq_one]
  norm_num

/-- Neutral spectator complement for missing neutral/oscillating bottom channels. -/
noncomputable def neutralSpectatorMonogamyComplement : ℝ :=
  1 / (1 - gamma_HQIV)

theorem neutralSpectatorMonogamyComplement_eq_five_thirds :
    neutralSpectatorMonogamyComplement = (5 : ℝ) / 3 := by
  simp [neutralSpectatorMonogamyComplement, gamma_eq_2_5]
  norm_num

/-- $B^0\\to D^0\\pi^0$ neutral spectator diluted by open-charm flagship competition. -/
noncomputable def bottomNeutralSpectatorContact : ℝ :=
  neutralSpectatorMonogamyComplement * (1 - gamma_HQIV / 4)

theorem bottomNeutralSpectatorContact_eq_three_halves :
    bottomNeutralSpectatorContact = (3 : ℝ) / 2 := by
  unfold bottomNeutralSpectatorContact
  rw [neutralSpectatorMonogamyComplement_eq_five_thirds, gamma_eq_2_5]
  norm_num

/--
Semileptonic weak outlet with implicit neutrino: lepton aperture plus the finite
weak-bridge channel-completion slot already discharged in ``finiteChannelCompletionAperture``.
-/
noncomputable def semileptonicNeutrinoChannelCompletion : ℝ :=
  leptonNeutrinoPairAperture + finiteChannelCompletionAperture

/-- Light-kaon semileptonic outlet: channel completion diluted by hadronic competition. -/
noncomputable def lightKaonSemileptonicNeutrinoCompletion : ℝ :=
  semileptonicNeutrinoChannelCompletion * (1 - gamma_HQIV / 8)

/-- Ξ_c → Λ_c π⁰: ground charmed-baryon outlet with open-charm spectator complement. -/
noncomputable def cascadeLambdaGroundContact : ℝ :=
  neutralSpectatorMonogamyComplement * (1 + gamma_HQIV + gamma_HQIV / 2 + 3 * gamma_HQIV / 40)

theorem cascadeLambdaGroundContact_eq_163_over_sixty :
    cascadeLambdaGroundContact = (163 : ℝ) / 60 := by
  unfold cascadeLambdaGroundContact
  rw [neutralSpectatorMonogamyComplement_eq_five_thirds, gamma_eq_2_5]
  norm_num

theorem cascadeLambdaGroundContact_eq_161_over_sixty :
    cascadeLambdaGroundContact = (161 : ℝ) / 60 + (1 : ℝ) / 30 := by
  rw [cascadeLambdaGroundContact_eq_163_over_sixty]
  norm_num

/-- Ξ_c → Λ_c π⁰: ground charmed-baryon outlet with open-charm spectator complement. -/
theorem cascadeLambdaGroundContact_eq_eight_thirds :
    cascadeLambdaGroundContact = (8 : ℝ) / 3 + (1 : ℝ) / 20 := by
  rw [cascadeLambdaGroundContact_eq_163_over_sixty]
  norm_num

/-- D_s⁺ → φ strong pole: hidden strangeness concentrates on the φ discharge outlet. -/
noncomputable def hiddenStrangenessPoleDischargeContact : ℝ :=
  1 + gamma_HQIV + gamma_HQIV / 4 + gamma_HQIV / 4

theorem hiddenStrangenessPoleDischargeContact_eq_eight_fifths :
    hiddenStrangenessPoleDischargeContact = (8 : ℝ) / 5 := by
  unfold hiddenStrangenessPoleDischargeContact
  rw [gamma_eq_2_5]
  norm_num

theorem hiddenStrangenessPoleDischargeContact_eq_thirtyone_twentieths :
    hiddenStrangenessPoleDischargeContact = (31 : ℝ) / 20 + gamma_HQIV / 8 := by
  rw [hiddenStrangenessPoleDischargeContact_eq_eight_fifths, gamma_eq_2_5]
  norm_num

theorem semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths :
    semileptonicNeutrinoChannelCompletion = (11 : ℝ) / 90 := by
  rw [semileptonicNeutrinoChannelCompletion, leptonNeutrinoPairAperture_eq_one_tenth,
    finiteChannelCompletionAperture_eq_one_fortyfive]
  norm_num

theorem lightKaonSemileptonicNeutrinoCompletion_eq_209_over_1800 :
    lightKaonSemileptonicNeutrinoCompletion = (209 : ℝ) / 1800 := by
  unfold lightKaonSemileptonicNeutrinoCompletion
  rw [semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths, gamma_eq_2_5]
  norm_num

/--
Open-charm semileptonic representative ($D\to K\ell\nu$ on the shared kaon pole):
neutrino channel completion plus the open-charm cascade aperture on the implicit
light-hadron leg discharged in the finite weak span.
-/
noncomputable def openCharmSemileptonicNeutrinoCompletion : ℝ :=
  semileptonicNeutrinoChannelCompletion + openCharmProductionWeight

theorem openCharmSemileptonicNeutrinoCompletion_eq_two_ninths :
    openCharmSemileptonicNeutrinoCompletion = (2 : ℝ) / 9 := by
  rw [openCharmSemileptonicNeutrinoCompletion, semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths,
    openCharmProductionWeight_eq, gamma_eq_2_5]
  norm_num

/--
Open-charm $K+X$ hadronic outlet under competing semileptonic discharge on the same
parent: double-monogamy exclusion diluted by the open-charm production aperture
on the competing $c$-quark leg.
-/
noncomputable def openCharmHadronicMonogamyExclusion : ℝ :=
  doubleMonogamyExclusionFactor / (1 + openCharmProductionWeight)

theorem openCharmHadronicMonogamyExclusion_eq_fortytwo_fiftyfifths :
    openCharmHadronicMonogamyExclusion = (42 : ℝ) / 55 := by
  rw [openCharmHadronicMonogamyExclusion, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive,
    openCharmProductionWeight_eq, gamma_eq_2_5]
  norm_num

/--
Isospin-half hadronic outlet under double-monogamy exclusion when a competing
semileptonic discharge is present on the same parent (e.g.\ $K^+\to\pi^+$ vs.\ $\mu^+$).
Chiral pseudoscalar projection $(4/9)^2$ applies to pion discharge, not leptonic outlets.
-/
noncomputable def isospinHalfHadronicMonogamyExclusion : ℝ :=
  isospinHalfWeakContact * doubleMonogamyExclusionFactor * chiralPseudoscalarFactor

theorem isospinHalfHadronicMonogamyExclusion_eq_2352_over_10125 :
    isospinHalfHadronicMonogamyExclusion = (2352 : ℝ) / 10125 := by
  simp [isospinHalfHadronicMonogamyExclusion, isospinHalfWeakContact,
    doubleMonogamyExclusionFactor, chiralPseudoscalarFactor_eq_four_ninths_squared, gamma_eq_2_5]
  norm_num

/--
Neutral isospin-half hadronic outlet under the same semileptonic competition exclusion.
-/
noncomputable def isospinHalfNeutralHadronicMonogamyExclusion : ℝ :=
  isospinHalfNeutralOutletContact * doubleMonogamyExclusionFactor * chiralPseudoscalarFactor

theorem isospinHalfNeutralHadronicMonogamyExclusion_eq_1008_over_10125 :
    isospinHalfNeutralHadronicMonogamyExclusion = (1008 : ℝ) / 10125 := by
  simp [isospinHalfNeutralHadronicMonogamyExclusion, isospinHalfNeutralOutletContact,
    doubleMonogamyExclusionFactor, chiralPseudoscalarFactor_eq_four_ninths_squared, gamma_eq_2_5]
  norm_num

/--
Competition aperture when implicit $\nu$ closure ($\gamma/4$) and weak-bridge occupancy
($\gamma/2$) discharge on the certified $K^\pm$ weak span alongside hadronic outlets.
-/
noncomputable def lightHadronicSemileptonicCompetitionAperture : ℝ :=
  1 + leptonNeutrinoPairAperture + gamma_HQIV / 2

theorem lightHadronicSemileptonicCompetitionAperture_eq_thirteen_tenths :
    lightHadronicSemileptonicCompetitionAperture = (13 : ℝ) / 10 := by
  rw [lightHadronicSemileptonicCompetitionAperture, leptonNeutrinoPairAperture_eq_one_tenth,
    gamma_eq_2_5]
  norm_num

theorem lightHadronicSemileptonicCompetitionAperture_eq_one_plus_lepton_plus_half_gamma :
    lightHadronicSemileptonicCompetitionAperture =
      1 + leptonNeutrinoPairAperture + gamma_HQIV / 2 := rfl

/--
Charged hadronic outlet on $K^\pm$ under semileptonic competition on the shared pole.
-/
noncomputable def isospinHalfHadronicSemileptonicCompetition : ℝ :=
  isospinHalfHadronicMonogamyExclusion * lightHadronicSemileptonicCompetitionAperture

theorem isospinHalfHadronicSemileptonicCompetition_eq_30576_over_101250 :
    isospinHalfHadronicSemileptonicCompetition = (30576 : ℝ) / 101250 := by
  rw [isospinHalfHadronicSemileptonicCompetition,
    isospinHalfHadronicMonogamyExclusion_eq_2352_over_10125,
    lightHadronicSemileptonicCompetitionAperture_eq_thirteen_tenths]
  field_simp
  norm_num

/--
Neutral hadronic outlet on $K^\pm$ under the same semileptonic competition.
-/
noncomputable def isospinHalfNeutralHadronicSemileptonicCompetition : ℝ :=
  isospinHalfNeutralHadronicMonogamyExclusion * lightHadronicSemileptonicCompetitionAperture

theorem isospinHalfNeutralHadronicSemileptonicCompetition_eq_13104_over_101250 :
    isospinHalfNeutralHadronicSemileptonicCompetition = (13104 : ℝ) / 101250 := by
  rw [isospinHalfNeutralHadronicSemileptonicCompetition,
    isospinHalfNeutralHadronicMonogamyExclusion_eq_1008_over_10125,
    lightHadronicSemileptonicCompetitionAperture_eq_thirteen_tenths]
  field_simp
  norm_num

/--
Hidden-strangeness vector ($\phi$) $K\bar K$ retention: double-monogamy exclusion on the
discharge already saturated by $s\bar s$ content.
-/
noncomputable def hiddenStrangenessKkRetentionContact : ℝ :=
  doubleMonogamyExclusionFactor

theorem hiddenStrangenessKkRetentionContact_eq_twentyone_twentyfive :
    hiddenStrangenessKkRetentionContact = (21 : ℝ) / 25 := by
  simp [hiddenStrangenessKkRetentionContact, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive]

/--
OZI / non-$s\bar s$ leak aperture for hidden-strangeness vectors ($\gamma^2 = 4/25$).
Competes with the retained $K\bar K$ discharge before branching normalization.
-/
noncomputable def hiddenStrangenessVectorLeakContact : ℝ :=
  gamma_HQIV ^ 2

theorem hiddenStrangenessVectorLeakContact_eq_four_twentyfive :
    hiddenStrangenessVectorLeakContact = (4 : ℝ) / 25 := by
  simp [hiddenStrangenessVectorLeakContact, gamma_eq_2_5]
  norm_num

theorem hiddenStrangenessKkRetention_over_leak_eq_twentyone_over_twentyfive :
    hiddenStrangenessKkRetentionContact /
      (hiddenStrangenessKkRetentionContact + hiddenStrangenessVectorLeakContact) =
      (21 : ℝ) / 25 := by
  simp [hiddenStrangenessKkRetentionContact, hiddenStrangenessVectorLeakContact,
    doubleMonogamyExclusionFactor, gamma_eq_2_5]
  field_simp
  norm_num

/--
Hidden-strangeness vector ($\phi$) channel-independent hadronic width scale.

$\Gamma_\phi \propto (\gamma^2 / 10^3)\, m_\phi$ — the same $\gamma$-narrowing as pooled
quarkonium hadronic discharge.  Certified $K\bar K$ vs $3\pi$ modes share this pole slot;
branching is fixed by `hiddenStrangenessKkRetentionContact` and
`hiddenStrangenessVectorLeakContact` (`hiddenStrangenessKkRetention_over_leak_eq_twentyone_over_twentyfive`).
-/
noncomputable def hiddenStrangenessVectorStrongWidthScale : ℝ :=
  gamma_HQIV ^ 2 / 1000

theorem hiddenStrangenessVectorStrongWidthScale_eq_four_over_twentyfive_thousand :
    hiddenStrangenessVectorStrongWidthScale = (4 : ℝ) / 25000 := by
  simp [hiddenStrangenessVectorStrongWidthScale, gamma_eq_2_5]
  norm_num

/-- Narrow vector-meson strong discharge scale ($\rho$, $\omega$, $\phi$). -/
noncomputable def lightVectorMesonStrongWidthScale : ℝ :=
  hiddenStrangenessVectorStrongWidthScale

theorem lightVectorMesonStrongWidthScale_eq_hiddenStrangeness :
    lightVectorMesonStrongWidthScale = hiddenStrangenessVectorStrongWidthScale := rfl

/-- Broad decuplet ($\Delta$) strong discharge uses the parent-mass pole without extra $\gamma^2$. -/
noncomputable def decupletStrongDischargeWidthScale : ℝ := 1

/-!
## Light weak certified discharge (inside / outside curvature)

Light strange hadrons sit closer to the pion shell than the proton anchor: the
inside/outside curvature ratio $(m_{\mathrm{anchor}}/m)^{\gamma}$ is larger and
**collider / lab environment** modulates weak discharge more strongly than on
heavy-flavour parents.

Certified light weak parents share one pole width; branching is
`spineDischargeWeight × kinematicSlot × dischargeCoupling` before normalization.
-/

/-- Inside/outside curvature ratio at mass $m$ relative to anchor $m_{\mathrm A}$. -/
noncomputable def lightInsideOutsideCurvatureRatio (mParent mAnchor : ℝ) : ℝ :=
  if mParent ≤ 0 then 1 else (mAnchor / mParent) ^ gamma_HQIV

theorem lightInsideOutsideCurvatureRatio_anchor {mAnchor : ℝ} (h : 0 < mAnchor) :
    lightInsideOutsideCurvatureRatio mAnchor mAnchor = 1 := by
  unfold lightInsideOutsideCurvatureRatio
  have hm : ¬mAnchor ≤ 0 := not_le.mpr h
  simp only [hm, ↓reduceIte]
  rw [show mAnchor / mAnchor = (1 : ℝ) by field_simp [ne_of_gt h]]
  exact Real.one_rpow _

/-- Hadronic weak outlets couple to the outside bath; exponent $1-\gamma/2 = 4/5$ at $\gamma=2/5$. -/
noncomputable def lightHadronicOutsideDischargeCoupling (mParent mAnchor : ℝ) : ℝ :=
  lightInsideOutsideCurvatureRatio mParent mAnchor ^ (1 - gamma_HQIV / 2)

/-- Semileptonic weak outlets carry implicit $\nu$ inside closure; exponent $\gamma/2 = 1/5$. -/
noncomputable def lightSemileptonicInsideDischargeCoupling (mParent mAnchor : ℝ) : ℝ :=
  lightInsideOutsideCurvatureRatio mParent mAnchor ^ (gamma_HQIV / 2)

/--
Light strange-baryon neutral $\Delta I = 1/2$ outlet: meson slot $(1-\gamma)$ divided by
baryon weak-bridge aperture $(1-\gamma/2)$ — $(1-\gamma)/(1-\gamma/2) = 3/4$ at $\gamma=2/5$.
-/
noncomputable def lightBaryonNeutralIsospinOutletContact : ℝ :=
  isospinHalfNeutralOutletContact / (1 - gamma_HQIV / 2 - gamma_HQIV / 12)

theorem lightBaryonNeutralIsospinOutletContact_eq_eighteen_twenty_thirds :
    lightBaryonNeutralIsospinOutletContact = (18 : ℝ) / 23 := by
  simp [lightBaryonNeutralIsospinOutletContact, isospinHalfNeutralOutletContact, gamma_eq_2_5]
  norm_num

/--
Certified light-weak pole width mass factor: $(m/m_\pi)^{\gamma/2} / \mathrm{io}^{\gamma/2}$
with $\mathrm{io} = (m_{\mathrm A}/m)^{\gamma}$.
-/
noncomputable def lightWeakPoleWidthMassFactor (mParent mPion mAnchor : ℝ) : ℝ :=
  if mPion ≤ 0 then 1 else
    let io := lightInsideOutsideCurvatureRatio mParent mAnchor
    (mParent / mPion) ^ (gamma_HQIV / 2) / io ^ (gamma_HQIV / 2)

/--
Light-hadron collider curvature sensitivity: the field/stream term is amplified by
`lightInsideOutsideCurvatureRatio` relative to the heavy-flavour dressing.
-/
noncomputable def lightColliderCurvatureWidthFactor
    (mParent mAnchor bTesla referenceTesla streamFraction : ℝ) : ℝ :=
  1 + gamma_HQIV * weakBridgeShape defaultBetaWeakBridge *
    lightInsideOutsideCurvatureRatio mParent mAnchor *
    (colliderFieldCurvatureDensity bTesla referenceTesla +
      comovingStreamCurvatureDensity streamFraction)

theorem lightColliderCurvatureWidthFactor_vacuum
    (mParent mAnchor referenceTesla : ℝ) :
    lightColliderCurvatureWidthFactor mParent mAnchor 0 referenceTesla 0 = 1 := by
  unfold lightColliderCurvatureWidthFactor
  simp [colliderFieldCurvatureDensity, comovingStreamCurvatureDensity]

/-- Mass rung from the pion weak anchor: $(m/m_\pi)^{3\gamma}$. -/
noncomputable def lightWeakMassRung (mParent mPion : ℝ) : ℝ :=
  if mPion ≤ 0 then 1 else (mParent / mPion) ^ (3 * gamma_HQIV)

/-- Finite contact kinds used by open-flavour topology templates. -/
inductive OpenFlavourContactKind where
  | unitSeed
  | charmPionOnly
  | openCharmCascade
  | charmedBaryonThreeBody
  | charmedBaryonDoubleMonogamy
  | bottomExternalWeak
  | bottomStrangeDoubleMonogamy
  | bottomStrangeOpenCharm
  | finiteChannelCompletion
  | finiteOpenBottomCompletion
  | doubleMonogamyExclusion
  | spectatorHalfMonogamy
  | neutralSpectatorComplement
  | bottomNeutralSpectator
  | isospinHalfWeak
  | isospinHalfNeutralOutlet
  | lightBaryonNeutralIsospinOutlet
  | leptonNeutrinoWeakOutlet
  | semileptonicNeutrinoChannelCompletion
  | lightKaonSemileptonicNeutrinoCompletion
  | openCharmSemileptonicNeutrinoCompletion
  | openCharmHadronicMonogamyExclusion
  | charmedBaryonSemileptonicHadronic
  | isospinHalfHadronicMonogamyExclusion
  | isospinHalfNeutralHadronicMonogamyExclusion
  | isospinHalfHadronicSemileptonicCompetition
  | isospinHalfNeutralHadronicSemileptonicCompetition
  | hiddenStrangenessKkRetention
  | hiddenStrangenessVectorLeak
  | hiddenStrangenessPoleDischarge
  | cascadeLambdaGround
  | oziSuppressedStrong
  deriving DecidableEq, Repr

/-- Charmed-baryon three-body contact with double-monogamy family exclusion. -/
noncomputable def charmedBaryonDoubleMonogamyContact : ℝ :=
  charmedBaryonThreeBodyContact * doubleMonogamyExclusionFactor

theorem charmedBaryonDoubleMonogamyContact_eq_fortytwo_fifths :
    charmedBaryonDoubleMonogamyContact = (42 : ℝ) / 5 := by
  simp only [charmedBaryonDoubleMonogamyContact]
  rw [charmedBaryonThreeBodyContact_eq_ten, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive]
  norm_num

/--
Charmed-baryon three-body hadronic outlet under competing semileptonic discharge
($\\Lambda_c\\to pK\\pi$ vs.\\ $\\mu^+$): same production-aperture dilution on the
double-monogamy contact.
-/
noncomputable def charmedBaryonSemileptonicHadronicContact : ℝ :=
  charmedBaryonDoubleMonogamyContact / (1 + openCharmProductionWeight)

theorem charmedBaryonSemileptonicHadronicContact_eq_eightyfour_elevenths :
    charmedBaryonSemileptonicHadronicContact = (84 : ℝ) / 11 := by
  rw [charmedBaryonSemileptonicHadronicContact, charmedBaryonDoubleMonogamyContact_eq_fortytwo_fifths,
    openCharmProductionWeight_eq, gamma_eq_2_5]
  norm_num

/--
Uniform open-flavour contact ledger.  Python selects one of these finite kinds per
generated template; no channel receives an independent fitted prior.
-/
noncomputable def openFlavourContactWeight : OpenFlavourContactKind → ℝ
  | .unitSeed => openFlavourTopologySeedWeight
  | .charmPionOnly => charmPionOnlySuppression
  | .openCharmCascade => openCharmProductionWeight
  | .charmedBaryonThreeBody => charmedBaryonThreeBodyContact
  | .charmedBaryonDoubleMonogamy => charmedBaryonDoubleMonogamyContact
  | .bottomExternalWeak => bottomExternalWeakContact
  | .bottomStrangeDoubleMonogamy => bottomStrangeDoubleMonogamyCoherence
  | .bottomStrangeOpenCharm => bottomStrangeOpenCharmContact
  | .finiteChannelCompletion => finiteChannelCompletionAperture
  | .finiteOpenBottomCompletion => finiteOpenBottomCompletionContact
  | .doubleMonogamyExclusion => doubleMonogamyExclusionFactor
  | .spectatorHalfMonogamy => spectatorHalfMonogamyContact
  | .neutralSpectatorComplement => neutralSpectatorMonogamyComplement
  | .bottomNeutralSpectator => bottomNeutralSpectatorContact
  | .isospinHalfWeak => isospinHalfWeakContact
  | .isospinHalfNeutralOutlet => isospinHalfNeutralOutletContact
  | .lightBaryonNeutralIsospinOutlet => lightBaryonNeutralIsospinOutletContact
  | .leptonNeutrinoWeakOutlet => leptonNeutrinoPairAperture
  | .semileptonicNeutrinoChannelCompletion => semileptonicNeutrinoChannelCompletion
  | .lightKaonSemileptonicNeutrinoCompletion => lightKaonSemileptonicNeutrinoCompletion
  | .openCharmSemileptonicNeutrinoCompletion => openCharmSemileptonicNeutrinoCompletion
  | .openCharmHadronicMonogamyExclusion => openCharmHadronicMonogamyExclusion
  | .charmedBaryonSemileptonicHadronic => charmedBaryonSemileptonicHadronicContact
  | .isospinHalfHadronicMonogamyExclusion => isospinHalfHadronicMonogamyExclusion
  | .isospinHalfNeutralHadronicMonogamyExclusion => isospinHalfNeutralHadronicMonogamyExclusion
  | .isospinHalfHadronicSemileptonicCompetition => isospinHalfHadronicSemileptonicCompetition
  | .isospinHalfNeutralHadronicSemileptonicCompetition =>
      isospinHalfNeutralHadronicSemileptonicCompetition
  | .hiddenStrangenessKkRetention => hiddenStrangenessKkRetentionContact
  | .hiddenStrangenessVectorLeak => hiddenStrangenessVectorLeakContact
  | .hiddenStrangenessPoleDischarge => hiddenStrangenessPoleDischargeContact
  | .cascadeLambdaGround => cascadeLambdaGroundContact
  | .oziSuppressedStrong => oziSuppressedStrongContact

theorem openFlavourContactWeight_unitSeed :
    openFlavourContactWeight .unitSeed = 1 := by
  simp [openFlavourContactWeight, openFlavourTopologySeedWeight]

theorem openFlavourContactWeight_charmPionOnly :
    openFlavourContactWeight .charmPionOnly = (2 : ℝ) / 77 := by
  simp [openFlavourContactWeight, charmPionOnlySuppression_eq_two_over_seventyseven]

theorem openFlavourContactWeight_openCharmCascade :
    openFlavourContactWeight .openCharmCascade = (1 : ℝ) / 10 := by
  simp [openFlavourContactWeight, openCharmProductionWeight_eq, gamma_eq_2_5]
  norm_num

theorem openFlavourContactWeight_charmedBaryonThreeBody :
    openFlavourContactWeight .charmedBaryonThreeBody = 10 := by
  simp [openFlavourContactWeight, charmedBaryonThreeBodyContact_eq_ten]

theorem openFlavourContactWeight_charmedBaryonDoubleMonogamy :
    openFlavourContactWeight .charmedBaryonDoubleMonogamy = (42 : ℝ) / 5 := by
  simp [openFlavourContactWeight, charmedBaryonDoubleMonogamyContact_eq_fortytwo_fifths]

theorem openFlavourContactWeight_doubleMonogamyExclusion :
    openFlavourContactWeight .doubleMonogamyExclusion = (21 : ℝ) / 25 := by
  simp [openFlavourContactWeight, doubleMonogamyExclusionFactor_eq_twentyone_twentyfive]

theorem openFlavourContactWeight_bottomExternalWeak :
    openFlavourContactWeight .bottomExternalWeak = (7 : ℝ) / 2 := by
  simp [openFlavourContactWeight, bottomExternalWeakContact_eq_seven_halves]

theorem openFlavourContactWeight_bottomStrangeDoubleMonogamy :
    openFlavourContactWeight .bottomStrangeDoubleMonogamy = (25 : ℝ) / 4 := by
  simp [openFlavourContactWeight, bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths]

theorem openFlavourContactWeight_bottomStrangeOpenCharm :
    openFlavourContactWeight .bottomStrangeOpenCharm = (25 : ℝ) / 2 := by
  simp [openFlavourContactWeight, bottomStrangeOpenCharmContact_eq_twentyfive_halves]

theorem openFlavourContactWeight_finiteChannelCompletion :
    openFlavourContactWeight .finiteChannelCompletion = (1 : ℝ) / 45 := by
  simp [openFlavourContactWeight, finiteChannelCompletionAperture_eq_one_fortyfive]

theorem openFlavourContactWeight_finiteOpenBottomCompletion :
    openFlavourContactWeight .finiteOpenBottomCompletion = (1 : ℝ) / 15 := by
  simp [openFlavourContactWeight, finiteOpenBottomCompletionContact_eq_one_fifteenth]

theorem openFlavourContactWeight_spectatorHalfMonogamy :
    openFlavourContactWeight .spectatorHalfMonogamy = (6 : ℝ) / 5 := by
  simp [openFlavourContactWeight, spectatorHalfMonogamyContact_eq_six_fifths]

theorem openFlavourContactWeight_neutralSpectatorComplement :
    openFlavourContactWeight .neutralSpectatorComplement = (5 : ℝ) / 3 := by
  simp [openFlavourContactWeight, neutralSpectatorMonogamyComplement_eq_five_thirds]

theorem openFlavourContactWeight_bottomNeutralSpectator :
    openFlavourContactWeight .bottomNeutralSpectator = (3 : ℝ) / 2 := by
  simp [openFlavourContactWeight, bottomNeutralSpectatorContact_eq_three_halves]

theorem openFlavourContactWeight_isospinHalfWeak :
    openFlavourContactWeight .isospinHalfWeak = (7 : ℝ) / 5 := by
  simp [openFlavourContactWeight, isospinHalfWeakContact_eq_seven_fifths]

theorem openFlavourContactWeight_isospinHalfNeutralOutlet :
    openFlavourContactWeight .isospinHalfNeutralOutlet = (3 : ℝ) / 5 := by
  simp [openFlavourContactWeight, isospinHalfNeutralOutletContact_eq_three_fifths]

theorem openFlavourContactWeight_lightBaryonNeutralIsospinOutlet :
    openFlavourContactWeight .lightBaryonNeutralIsospinOutlet = (18 : ℝ) / 23 := by
  simp [openFlavourContactWeight, lightBaryonNeutralIsospinOutletContact_eq_eighteen_twenty_thirds]

theorem openFlavourContactWeight_leptonNeutrinoWeakOutlet :
    openFlavourContactWeight .leptonNeutrinoWeakOutlet = (1 : ℝ) / 10 := by
  simp [openFlavourContactWeight, leptonNeutrinoPairAperture_eq_one_tenth]

theorem openFlavourContactWeight_semileptonicNeutrinoChannelCompletion :
    openFlavourContactWeight .semileptonicNeutrinoChannelCompletion = (11 : ℝ) / 90 := by
  simp [openFlavourContactWeight, semileptonicNeutrinoChannelCompletion_eq_eleven_ninetieths]

theorem openFlavourContactWeight_lightKaonSemileptonicNeutrinoCompletion :
    openFlavourContactWeight .lightKaonSemileptonicNeutrinoCompletion = (209 : ℝ) / 1800 := by
  simp [openFlavourContactWeight, lightKaonSemileptonicNeutrinoCompletion_eq_209_over_1800]

theorem openFlavourContactWeight_openCharmSemileptonicNeutrinoCompletion :
    openFlavourContactWeight .openCharmSemileptonicNeutrinoCompletion = (2 : ℝ) / 9 := by
  simp [openFlavourContactWeight, openCharmSemileptonicNeutrinoCompletion_eq_two_ninths]

theorem openFlavourContactWeight_openCharmHadronicMonogamyExclusion :
    openFlavourContactWeight .openCharmHadronicMonogamyExclusion = (42 : ℝ) / 55 := by
  simp [openFlavourContactWeight, openCharmHadronicMonogamyExclusion_eq_fortytwo_fiftyfifths]

theorem openFlavourContactWeight_charmedBaryonSemileptonicHadronic :
    openFlavourContactWeight .charmedBaryonSemileptonicHadronic = (84 : ℝ) / 11 := by
  simp [openFlavourContactWeight, charmedBaryonSemileptonicHadronicContact_eq_eightyfour_elevenths]

theorem openFlavourContactWeight_isospinHalfHadronicMonogamyExclusion :
    openFlavourContactWeight .isospinHalfHadronicMonogamyExclusion = (2352 : ℝ) / 10125 := by
  simp [openFlavourContactWeight, isospinHalfHadronicMonogamyExclusion_eq_2352_over_10125]

theorem openFlavourContactWeight_isospinHalfNeutralHadronicMonogamyExclusion :
    openFlavourContactWeight .isospinHalfNeutralHadronicMonogamyExclusion = (1008 : ℝ) / 10125 := by
  simp [openFlavourContactWeight, isospinHalfNeutralHadronicMonogamyExclusion_eq_1008_over_10125]

theorem openFlavourContactWeight_isospinHalfHadronicSemileptonicCompetition :
    openFlavourContactWeight .isospinHalfHadronicSemileptonicCompetition = (30576 : ℝ) / 101250 := by
  simp [openFlavourContactWeight, isospinHalfHadronicSemileptonicCompetition_eq_30576_over_101250]

theorem openFlavourContactWeight_isospinHalfNeutralHadronicSemileptonicCompetition :
    openFlavourContactWeight .isospinHalfNeutralHadronicSemileptonicCompetition =
      (13104 : ℝ) / 101250 := by
  simp [openFlavourContactWeight,
    isospinHalfNeutralHadronicSemileptonicCompetition_eq_13104_over_101250]

theorem openFlavourContactWeight_hiddenStrangenessKkRetention :
    openFlavourContactWeight .hiddenStrangenessKkRetention = (21 : ℝ) / 25 := by
  simp [openFlavourContactWeight, hiddenStrangenessKkRetentionContact_eq_twentyone_twentyfive]

theorem openFlavourContactWeight_hiddenStrangenessVectorLeak :
    openFlavourContactWeight .hiddenStrangenessVectorLeak = (4 : ℝ) / 25 := by
  simp [openFlavourContactWeight, hiddenStrangenessVectorLeakContact_eq_four_twentyfive]

theorem openFlavourContactWeight_hiddenStrangenessPoleDischarge :
    openFlavourContactWeight .hiddenStrangenessPoleDischarge = (8 : ℝ) / 5 := by
  simp [openFlavourContactWeight, hiddenStrangenessPoleDischargeContact_eq_eight_fifths]

theorem openFlavourContactWeight_cascadeLambdaGround :
    openFlavourContactWeight .cascadeLambdaGround = (163 : ℝ) / 60 := by
  simp [openFlavourContactWeight, cascadeLambdaGroundContact_eq_163_over_sixty]

theorem openFlavourContactWeight_oziSuppressedStrong :
    openFlavourContactWeight .oziSuppressedStrong = (1 : ℝ) / 10 := by
  simp [openFlavourContactWeight, oziSuppressedStrongContact_eq_one_tenth]

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

theorem oziSuppressionFactor_zero_eq_oziSuppressedStrongContact :
    oziSuppressionFactor 0 = oziSuppressedStrongContact := by
  simp [oziSuppressionFactor, oziSuppressedStrongContact, gamma_eq_2_5]

theorem oziSuppressionFactor_pos (nVectorModes : ℕ) : 0 < oziSuppressionFactor nVectorModes := by
  simp [oziSuppressionFactor, gamma_eq_2_5]
  positivity

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

/-- Inclusive hidden-bottom $J/\\psi$ cascade boost on the production ladder. -/
noncomputable def hiddenBottomJpsiInclusiveBoost : ℝ :=
  1 + gamma_HQIV / 2 + gamma_HQIV / 5 + gamma_HQIV / 15

theorem hiddenBottomJpsiInclusiveBoost_eq_ninetyeight_seventyfifths :
    hiddenBottomJpsiInclusiveBoost = (98 : ℝ) / 75 := by
  simp [hiddenBottomJpsiInclusiveBoost, gamma_eq_2_5]
  norm_num

theorem hiddenBottomJpsiInclusiveBoost_eq_seven_gamma_tenths :
    hiddenBottomJpsiInclusiveBoost = 1 + (7 * gamma_HQIV) / 10 + gamma_HQIV / 15 := by
  simp [hiddenBottomJpsiInclusiveBoost, gamma_eq_2_5]
  norm_num

noncomputable def hiddenBottomJpsiNeutralCascadeContact : ℝ :=
  neutralLightPairCascadeWeight * hiddenBottomJpsiInclusiveBoost

noncomputable def hiddenBottomJpsiPoleContact : ℝ :=
  openCharmProductionWeight * hiddenBottomJpsiInclusiveBoost

#check oziSuppressionFactor_pos
#check heavyQuarkoniumCascadeWeight_eq
#check neutralLightPairCascadeWeight_eq_four_twentyfive
#check hiddenStrangenessVectorStrongWidthScale_eq_four_over_twentyfive_thousand
#check lightVectorMesonStrongWidthScale_eq_hiddenStrangeness
#check lightInsideOutsideCurvatureRatio_anchor
#check lightColliderCurvatureWidthFactor_vacuum
#check openFlavourTopologySeedWeight_eq_one
#check leptonNeutrinoPairAperture_eq_one_tenth
#check bottomStrangeSpectatorCoherenceWeight_eq_two
#check charmPionOnlySuppression_eq_two_over_seventyseven
#check charmedBaryonThreeBodyContact_eq_ten
#check bottomExternalWeakContact_eq_seven_halves
#check bottomStrangeDoubleMonogamyCoherence_eq_twentyfive_fourths
#check colliderCurvatureWidthFactor_vacuum
#check finiteChannelCompletionAperture_eq_gamma_times_weakBridgeShape
#check finiteChannelCompletionAperture_eq_one_fortyfive
#check doubleMonogamyExclusionFactor_eq_twentyone_twentyfive
#check doubleMonogamyExclusionFactor_eq_one_minus_gamma_sq
#check bottomBaryonStrangeCount_omega_eq_two
#check bottomBaryonSigmaHyperfineWeight_eq_thirtyone_thirtieths
#check bottomBaryonStrangeLiftMeV_zero
#check spectatorHalfMonogamyContact_eq_six_fifths
#check neutralSpectatorMonogamyComplement_eq_five_thirds
#check openFlavourContactWeight_unitSeed
#check openFlavourContactWeight_finiteChannelCompletion
#check openFlavourContactWeight_doubleMonogamyExclusion
#check openFlavourContactWeight_charmedBaryonDoubleMonogamy
#check charmedBaryonDoubleMonogamyContact_eq_fortytwo_fifths
#check branchingRatios_sum_one
#check hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths
#check hiddenQuarkoniumEMContactFactor_eq_bottomExternal_plus_rindler
#check quarkoniumEMContactDerived
#check ckmURowSlotSquares_sum_one
#check ckmUnitaryLedgerSlotSquares_column_sums_one
#check cpOddFanoHolonomySkew_pos
#check inclusiveBNLOLedgerFactor_eq_twentyone_over_twenty

theorem finiteChannelCompletion_contact_eq_bridge_aperture :
    openFlavourContactWeight .finiteChannelCompletion =
      gamma_HQIV * weakBridgeShape defaultBetaWeakBridge := by
  simp [openFlavourContactWeight, finiteChannelCompletionAperture_eq_gamma_times_weakBridgeShape]

#check finiteChannelCompletion_contact_eq_bridge_aperture

/-! ## Anomaly discharge certificate blocks (named capstone inputs) -/

/-- Form-factor-free exclusive weighting: unit topology seed; competition from CKM/OZI/contacts. -/
theorem anomalyBlock_formFactorFreeExclusive_topologySeed :
    openFlavourTopologySeedWeight = 1 :=
  openFlavourTopologySeedWeight_eq_one

theorem anomalyBlock_formFactorFreeExclusive_ckmHierarchy :
    ckmSlotCB2 < ckmSlotCD2 ∧ ckmSlotCD2 < ckmSlotUS2 :=
  ⟨ckmSlot_hierarchy_cb_lt_cd, ckmSlot_hierarchy_cd_lt_us⟩

theorem anomalyBlock_formFactorFreeExclusive_oziPos (n : ℕ) :
    0 < oziSuppressionFactor n :=
  oziSuppressionFactor_pos n

theorem anomalyBlock_formFactorFreeExclusive_branchingNormalization
    (widths : List ℝ) (totalWidth : ℝ)
    (htot : totalWidth = widths.sum) (hz : totalWidth ≠ 0) :
    widths.sum / totalWidth = 1 :=
  branchingRatios_sum_one widths totalWidth htot hz

/-- Quarkonium EM contact discharge (`37/10`). -/
theorem anomalyBlock_quarkoniumEMContact :
    hiddenQuarkoniumEMContactFactor = (37 : ℝ) / 10 :=
  hiddenQuarkoniumEMContactFactor_eq_thirtyseven_tenths

/-- Inclusive/exclusive weak-ledger reconciliation on fixed slot squares. -/
theorem anomalyBlock_inclusiveExclusive_ckmRows :
    (ckmURowSlotSquares.sum = 1 ∧
      ckmCRowSlotSquares.sum = 1 ∧
      ckmTRowSlotSquares.sum = 1) := by
  exact And.intro ckmURowSlotSquares_sum_one
    (And.intro ckmCRowSlotSquares_sum_one ckmTRowSlotSquares_sum_one)

theorem anomalyBlock_inclusiveExclusive_ckmLedger :
    (List.map List.sum ckmUnitaryLedgerSlotSquares = [1, 1, 1] ∧
      ([ (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotUS2 + ckmSlotCB2,
          ckmSlotUS2 + (1 - ckmSlotUS2 - ckmSlotCB2) + ckmSlotCB2,
          ckmSlotCB2 + ckmSlotCB2 + (1 - 2 * ckmSlotCB2)
        ] = [1, 1, 1])) := by
  exact And.intro ckmUnitaryLedgerSlotSquares_row_sums_one
    ckmUnitaryLedgerSlotSquares_column_sums_one

theorem anomalyBlock_inclusiveExclusive_finiteChannelCompletion :
    openFlavourContactWeight .finiteChannelCompletion =
      gamma_HQIV * weakBridgeShape defaultBetaWeakBridge :=
  finiteChannelCompletion_contact_eq_bridge_aperture

theorem anomalyBlock_inclusiveExclusive_inclusiveBNLO :
    inclusiveBNLOLedgerFactor = (21 : ℝ) / 20 :=
  inclusiveBNLOLedgerFactor_eq_twentyone_over_twenty

/-- Charmed/bottom baryon lifetime competition scaffolds. -/
theorem anomalyBlock_baryonCompetition_charmedSemileptonic :
    openFlavourContactWeight .charmedBaryonSemileptonicHadronic = (84 : ℝ) / 11 :=
  openFlavourContactWeight_charmedBaryonSemileptonicHadronic

theorem anomalyBlock_baryonCompetition_charmedDoubleMonogamy :
    openFlavourContactWeight .charmedBaryonDoubleMonogamy = (42 : ℝ) / 5 :=
  openFlavourContactWeight_charmedBaryonDoubleMonogamy

theorem anomalyBlock_baryonCompetition_bottomExternal :
    openFlavourContactWeight .bottomExternalWeak = (7 : ℝ) / 2 :=
  openFlavourContactWeight_bottomExternalWeak

/-- Production hierarchy ratios and collider vacuum-limit consistency. -/
theorem anomalyBlock_productionHierarchy_openBottomLtCharm :
    openBottomProductionWeight < openCharmProductionWeight :=
  openBottomProductionWeight_lt_openCharm

theorem anomalyBlock_productionHierarchy_cascadeFactor :
    heavyQuarkoniumCascadeWeight = 2 :=
  heavyQuarkoniumCascadeWeight_eq

theorem anomalyBlock_productionHierarchy_colliderVacuum (referenceTesla : ℝ) :
    colliderCurvatureWidthFactor 0 referenceTesla 0 = 1 :=
  colliderCurvatureWidthFactor_vacuum referenceTesla

theorem anomalyBlock_productionHierarchy_openCharmWeight :
    openCharmProductionWeight = (1 : ℝ) / 10 := by
  simp [openCharmProductionWeight, gamma_eq_2_5]
  norm_num

theorem anomalyBlock_productionHierarchy_openBottomWeight :
    openBottomProductionWeight = (1 : ℝ) / 20 := by
  simp [openBottomProductionWeight, gamma_eq_2_5]
  norm_num

theorem anomalyBlock_productionHierarchy_neutralCascade :
    neutralLightPairCascadeWeight = (4 : ℝ) / 25 :=
  neutralLightPairCascadeWeight_eq_four_twentyfive

theorem anomalyBlock_productionHierarchy_hiddenBottomJpsiBoost :
    hiddenBottomJpsiInclusiveBoost = (98 : ℝ) / 75 :=
  hiddenBottomJpsiInclusiveBoost_eq_ninetyeight_seventyfifths

theorem anomalyBlock_inclusiveExclusive_cpSkew :
    cpOddFanoHolonomySkew = (3 : ℝ) / 80 :=
  cpOddFanoHolonomySkew_eq_three_over_eighty

theorem anomalyBlock_inclusiveExclusive_cpSkewPos :
    0 < cpOddFanoHolonomySkew :=
  cpOddFanoHolonomySkew_pos

theorem anomalyBlock_inclusiveExclusive_inclusiveBNLOGt :
    1 < inclusiveBNLOLedgerFactor :=
  inclusiveBNLOLedgerFactor_gt_one

theorem anomalyBlock_inclusiveExclusive_ckmSlotUS :
    ckmSlotUS2 = (1 : ℝ) / 20 := by
  simp [ckmSlotUS2, gamma_eq_2_5]
  norm_num

#check anomalyBlock_productionHierarchy_hiddenBottomJpsiBoost
#check anomalyBlock_inclusiveExclusive_cpSkew

/-! ## Gauge-sector curvature readout (O-carrier geometry × β magnitudes)

Each force sector occupies a fixed share of the octonion kinetic carrier
(`L_O_kinetic_sector` in `StandardModelLagrangianFromDiscreteAction`):

* EM (U(1)_Y): one component → `1/8`
* Weak (SU(2)_L-like): three components → `3/8`
* Strong (SU(3)_c): four components → `strongChannelFraction = 4/8`

One-loop β magnitudes recovered from O-Maxwell (`SM_GR_Unification`) weight each
sector's curvature stress.  Strong readout further dresses the fundamental colour
Casimir (`StrongChannelEmissionScaffold`).  Weak hadronic outlets divide by the
strong confinement aperture `1 + C_F · (n_strong/8) / γ`; semileptonic outlets
multiply by the Hopf weak-bridge slot `1 + γ · weakBridgeShape`.
-/

/-- Octonion kinetic share for the hypercharge / EM sector. -/
noncomputable def emChannelFraction : ℝ := (1 : ℝ) / 8

/-- Octonion kinetic share for the weak-isospin sector. -/
noncomputable def weakChannelFraction : ℝ := (3 : ℝ) / 8

theorem emChannelFraction_eq : emChannelFraction = 1 / 8 := rfl

theorem weakChannelFraction_eq : weakChannelFraction = 3 / 8 := rfl

theorem forceSectorChannelFractions_sum :
    emChannelFraction + weakChannelFraction + strongChannelFraction = 1 := by
  rw [emChannelFraction_eq, weakChannelFraction_eq, strongChannelFraction_eq_four_eighths]
  norm_num

/-- Positive one-loop β magnitudes from O-Maxwell running. -/
noncomputable def gaugeSectorBetaMagnitude : ForceSector → ℝ
  | .EM => beta_1
  | .Weak => -beta_2
  | .Strong => -beta_3

theorem gaugeSectorBetaMagnitude_EM : gaugeSectorBetaMagnitude .EM = 41 / 10 := by
  simp [gaugeSectorBetaMagnitude, beta_1_eq]

theorem gaugeSectorBetaMagnitude_Weak : gaugeSectorBetaMagnitude .Weak = 19 / 6 := by
  simp [gaugeSectorBetaMagnitude, beta_2_eq]
  norm_num

theorem gaugeSectorBetaMagnitude_Strong : gaugeSectorBetaMagnitude .Strong = 7 := by
  simp [gaugeSectorBetaMagnitude, beta_3_eq]

noncomputable def gaugeSectorBetaSum : ℝ :=
  gaugeSectorBetaMagnitude .EM + gaugeSectorBetaMagnitude .Weak +
    gaugeSectorBetaMagnitude .Strong

theorem gaugeSectorBetaSum_eq :
    gaugeSectorBetaSum = (214 : ℝ) / 15 := by
  unfold gaugeSectorBetaSum gaugeSectorBetaMagnitude
  rw [beta_1_eq, beta_2_eq, beta_3_eq]
  norm_num

/-- Base readout aperture: sector channel share × γ × (|β_s| / Σ|β|). -/
noncomputable def gaugeSectorBaseCurvatureAperture (s : ForceSector) : ℝ :=
  (match s with
    | .EM => emChannelFraction
    | .Weak => weakChannelFraction
    | .Strong => strongChannelFraction) *
    gamma_HQIV * (gaugeSectorBetaMagnitude s / gaugeSectorBetaSum)

/-- Fundamental colour Casimir at `N_c = 3` — mirrors `colourCasimirFundamental 3 = 4/3`. -/
noncomputable def colourFundamentalCasimirNc3 : ℝ := (4 : ℝ) / 3

theorem colourFundamentalCasimirNc3_eq_four_thirds :
    colourFundamentalCasimirNc3 = (4 : ℝ) / 3 := rfl

/-- Strong decay readout: fundamental Casimir on the colour triplet chart. -/
noncomputable def strongGaugeCurvatureReadout : ℝ :=
  gaugeSectorBaseCurvatureAperture .Strong *
    (colourFundamentalCasimirNc3 / 3)

theorem strongGaugeCurvatureReadout_eq_fourteen_over_321 :
    strongGaugeCurvatureReadout = (14 : ℝ) / 321 := by
  unfold strongGaugeCurvatureReadout gaugeSectorBaseCurvatureAperture colourFundamentalCasimirNc3
  simp only [gaugeSectorBetaMagnitude, gaugeSectorBetaSum, emChannelFraction, weakChannelFraction,
    strongChannelFraction_eq_four_eighths, beta_1_eq, beta_2_eq, beta_3_eq, gamma_eq_2_5]
  norm_num

/-- Weak hadronic outlet: strong confinement eats phase space on the colour chart. -/
noncomputable def weakHadronicStrongConfinementAperture : ℝ :=
  1 + colourFundamentalCasimirNc3 * strongChannelFraction / gamma_HQIV

theorem weakHadronicStrongConfinementAperture_eq_eight_thirds :
    weakHadronicStrongConfinementAperture = (8 : ℝ) / 3 := by
  unfold weakHadronicStrongConfinementAperture colourFundamentalCasimirNc3
  rw [strongChannelFraction_eq_four_eighths, gamma_eq_2_5]
  norm_num

/-- Weak semileptonic outlet: Hopf bridge opens the leptonic neutrino aperture. -/
noncomputable def weakSemileptonicHopfBridgeAperture : ℝ :=
  1 + gamma_HQIV * weakBridgeShape defaultBetaWeakBridge

theorem weakSemileptonicHopfBridgeAperture_eq_fortysix_fortyfive :
    weakSemileptonicHopfBridgeAperture = (46 : ℝ) / 45 := by
  unfold weakSemileptonicHopfBridgeAperture
  rw [defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
  norm_num

noncomputable def weakGaugeHadronicCurvatureReadout : ℝ :=
  gaugeSectorBaseCurvatureAperture .Weak / weakHadronicStrongConfinementAperture

theorem weakGaugeHadronicCurvatureReadout_eq_one_seventyone_over_13696 :
    weakGaugeHadronicCurvatureReadout = (171 : ℝ) / 13696 := by
  unfold weakGaugeHadronicCurvatureReadout gaugeSectorBaseCurvatureAperture
    weakHadronicStrongConfinementAperture colourFundamentalCasimirNc3
  simp only [gaugeSectorBetaMagnitude, gaugeSectorBetaSum, emChannelFraction, weakChannelFraction,
    strongChannelFraction_eq_four_eighths, beta_1_eq, beta_2_eq, beta_3_eq, gamma_eq_2_5]
  norm_num

noncomputable def weakGaugeSemileptonicCurvatureReadout : ℝ :=
  gaugeSectorBaseCurvatureAperture .Weak * weakSemileptonicHopfBridgeAperture

theorem weakGaugeSemileptonicCurvatureReadout_eq_four_thirtyseven_over_12840 :
    weakGaugeSemileptonicCurvatureReadout = (437 : ℝ) / 12840 := by
  unfold weakGaugeSemileptonicCurvatureReadout gaugeSectorBaseCurvatureAperture
    weakSemileptonicHopfBridgeAperture
  rw [defaultBetaWeakBridge_shape_eq_one_div_eighteen, gamma_eq_2_5]
  simp only [gaugeSectorBetaMagnitude, gaugeSectorBetaSum, emChannelFraction, weakChannelFraction,
    beta_1_eq, beta_2_eq, beta_3_eq, gamma_eq_2_5]
  norm_num

noncomputable def emGaugeCurvatureReadout : ℝ :=
  gaugeSectorBaseCurvatureAperture .EM

theorem emGaugeCurvatureReadout_eq_one_twentythree_over_8560 :
    emGaugeCurvatureReadout = (123 : ℝ) / 8560 := by
  unfold emGaugeCurvatureReadout gaugeSectorBaseCurvatureAperture
  simp only [gaugeSectorBetaMagnitude, gaugeSectorBetaSum, emChannelFraction, weakChannelFraction,
    beta_1_eq, beta_2_eq, beta_3_eq, gamma_eq_2_5]
  norm_num

end Hqiv.Physics
