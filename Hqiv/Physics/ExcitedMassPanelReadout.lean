import Hqiv.Physics.HepDecayReadout
import Hqiv.Physics.TuftGlobalHadronReadout
import Hqiv.Physics.ExcitedMassComparisonHonesty

/-!
# Excited-state mass panel routing (comparison layer)

The global TUFT readout `tuftExcitedMassGlobalAtXi_MeV` indexes modes by
**chart row** (`tuftHeavyChartShell` vs `tuftStrongChartShell`), radial index `n`,
orbital index `ℓ`, and valence content (`n_strange`, parity, …).
The pair `(n, ℓ)` alone is **not** a unique registry key: e.g. baryon `(2,0)` on the
heavy chart and meson `(2,0)` with one strangeness on the strong chart are distinct
certified slots with different masses.

Heavy-flavour **ground** hadrons ($B$, $B_s$, $\Upsilon$, …) are **not** assigned by
nearest-shell matching on that grid; they discharge from the quark-ladder readouts in
`HepDecayReadout` (`dressedOpenBottomMesonMassMeV`, `dressedHiddenBottomQuarkoniumMassMeV`,
vector and radial excitations above).
-/

namespace Hqiv.Physics

/-- Heavy-chart baryon slot with internal quanta `(n, ℓ)`. -/
def tuftHeavyBaryonChannel (n ℓ : ℕ) : TuftExcitationChannel :=
  { chartShell := tuftHeavyChartShell, n := n, ℓ := ℓ, valenceQuarks := 3 }

/-- Strong-chart meson slot with internal quanta `(n, ℓ)` and strangeness rung. -/
def tuftStrongMesonChannel (n ℓ nStrange : ℕ) : TuftExcitationChannel :=
  { chartShell := tuftStrongChartShell, n := n, ℓ := ℓ, valenceQuarks := 2,
    nStrange := nStrange }

theorem tuftExcitationChannel_shell_not_unique :
    ∃ ch₁ ch₂ : TuftExcitationChannel,
      ch₁.n = ch₂.n ∧ ch₁.ℓ = ch₂.ℓ ∧ ch₁ ≠ ch₂ := by
  refine ⟨tuftHeavyBaryonChannel 2 0, tuftStrongMesonChannel 2 0 1, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp [tuftHeavyBaryonChannel, tuftStrongMesonChannel, tuftHeavyChartShell_eq_four,
      tuftStrongChartShell_eq_three]

theorem excited_panel_openBottom_uses_dressed_readout
    (mProtonMeV mPiMeV : ℝ) :
    dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV =
      openBottomMesonMassMeV mProtonMeV mPiMeV * openBottomOutsideMassDressing := rfl

theorem excited_panel_hiddenBottom_uses_dressed_readout
    (mProtonMeV mPiMeV : ℝ) :
    dressedHiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV =
      hiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV * hiddenQuarkoniumOutsideMassDressing *
        hiddenBottomQuarkoniumGroundSlotFactor := rfl

theorem excited_panel_psi2S_uses_radial_factor (mPiMeV : ℝ) :
    dressedHiddenCharmQuarkoniumExcitedMassMeV mPiMeV 1 =
      dressedHiddenCharmQuarkoniumMassMeV mPiMeV * hiddenCharmQuarkoniumExcitationFactor 1 *
        hiddenCharmQuarkoniumRadialK1SlotFactor := by
  simp [dressedHiddenCharmQuarkoniumExcitedMassMeV, hiddenCharmQuarkoniumRadialSlotFactor]

theorem excited_panel_openCharmVector2S_uses_radial_factor (mPiMeV : ℝ) :
    dressedOpenCharmVectorRadialMassMeV mPiMeV 1 =
      dressedOpenCharmVectorCoreMassMeV mPiMeV * openCharmVectorRadialExcitationFactor 1 *
        openCharmVectorRadialK1SlotFactor := by
  simp [dressedOpenCharmVectorRadialMassMeV, openCharmVectorRadialSlotFactor]

theorem excited_panel_openCharmStrangeVector2S_uses_radial_factor (mPiMeV mKMeV : ℝ) :
    dressedOpenCharmStrangeVectorRadialMassMeV mPiMeV mKMeV 1 =
      openCharmStrangeMesonMassMeV mPiMeV mKMeV * openCharmVectorMesonMassFactor *
        openCharmVectorRadialExcitationFactor 1 * openCharmVectorRadialK1SlotFactor *
        openCharmStrangeVectorRadialK1SlotFactor := by
  simp [dressedOpenCharmStrangeVectorRadialMassMeV, openCharmVectorRadialSlotFactor,
    openCharmStrangeVectorRadialSlotFactor]

theorem excited_panel_chi_c1_uses_orbital_factor (mPiMeV : ℝ) :
    dressedHiddenCharmQuarkoniumExcitedMassMeV mPiMeV 2 =
      dressedHiddenCharmQuarkoniumMassMeV mPiMeV * hiddenCharmQuarkoniumExcitationFactor 2 := by
  simp [dressedHiddenCharmQuarkoniumExcitedMassMeV, hiddenCharmQuarkoniumRadialSlotFactor]

theorem excited_panel_XiStar_uses_double_strangeness_slot
    (scaffoldMeV mKMeV mPiMeV : ℝ) :
    decupletStrangeOrbitalMultipletMassMeV scaffoldMeV mKMeV mPiMeV 2 =
      (scaffoldMeV + heavyFlavorBaryonStrangeLiftMeV mKMeV mPiMeV 1) *
        decupletDoubleStrangenessOrbitalSlotFactor := by
  simp [decupletStrangeOrbitalMultipletMassMeV]

theorem excited_panel_Bstar_uses_vector_factor
    (mProtonMeV mPiMeV : ℝ) :
    dressedOpenBottomVectorMesonMassMeV mProtonMeV mPiMeV =
      dressedOpenBottomMesonMassMeV mProtonMeV mPiMeV * openBottomVectorMesonMassFactor := rfl

theorem excited_panel_Upsilon2S_uses_radial_factor
    (mProtonMeV mPiMeV : ℝ) :
    dressedHiddenBottomQuarkoniumExcitedMassMeV mProtonMeV mPiMeV 1 =
      dressedHiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV *
        hiddenBottomQuarkoniumExcitationFactor 1 *
        hiddenBottomQuarkoniumRadialK1SlotFactor := by
  simp [dressedHiddenBottomQuarkoniumExcitedMassMeV, hiddenBottomQuarkoniumRadialSlotFactor]

theorem excited_panel_Upsilon3S_uses_radial_factor_two
    (mProtonMeV mPiMeV : ℝ) :
    dressedHiddenBottomQuarkoniumExcitedMassMeV mProtonMeV mPiMeV 2 =
      dressedHiddenBottomQuarkoniumMassMeV mProtonMeV mPiMeV *
        hiddenBottomQuarkoniumExcitationFactor 2 *
        hiddenBottomQuarkoniumRadialK2SlotFactor := by
  simp [dressedHiddenBottomQuarkoniumExcitedMassMeV, hiddenBottomQuarkoniumRadialSlotFactor]

theorem excited_panel_Upsilon3S_radial_eq_eleven_tenths :
    hiddenBottomQuarkoniumExcitationFactor 2 = (11 : ℝ) / 10 := by
  exact hiddenBottomQuarkoniumExcitationFactor_two_eq_eleven_tenths

theorem excited_panel_phi_uses_hidden_strangeness_vector_dressing
    (mProtonMeV mPiMeV : ℝ) (mMesonMeV : ℝ) :
    mMesonMeV * hiddenStrangenessVectorOutsideMassDressing =
      mMesonMeV * (1 + gamma_HQIV / 24) := by
  simp [hiddenStrangenessVectorOutsideMassDressing]

theorem excited_panel_Dstar_uses_vector_factor (mPiMeV : ℝ) :
    dressedOpenCharmVectorMesonMassMeV mPiMeV =
      dressedOpenCharmMesonMassMeV mPiMeV * openCharmVectorMesonMassFactor *
        openCharmVectorGroundSlotFactor := rfl

theorem excited_panel_decuplet_ground_slot_eq_onehundredthirtynine_onehundredfortieths :
    decupletGroundSlotFactor = (139 : ℝ) / 140 := by
  exact decupletGroundSlotFactor_eq_onehundredthirtynine_onehundredfortieths

theorem excited_panel_omega_isoscalar_slot_eq_onehundredthirtynine_onehundredfortieths :
    lightVectorIsoscalarSlotFactor = (139 : ℝ) / 140 := by
  exact lightVectorIsoscalarSlotFactor_eq_onehundredthirtynine_onehundredfortieths

theorem excited_panel_N1520_uses_d13_slot_factor (scaffoldMeV : ℝ) :
    scaffoldMeV * nucleonResonance1520MassFactor =
      scaffoldMeV * (1 + gamma_HQIV / 80) := by
  simp [nucleonResonance1520MassFactor]

theorem excited_panel_Pc4440_k1_slot_eq_onehundredfortyone_onehundredfortieths :
    charmedPentaquarkExcitationK1SlotFactor = (141 : ℝ) / 140 := by
  exact charmedPentaquarkExcitationK1SlotFactor_eq_onehundredfortyone_onehundredfortieths

theorem excited_panel_N1680_uses_d13_slot_factor
    (scaffoldMeV : ℝ) :
    scaffoldMeV * nucleonResonance1680MassFactor =
      scaffoldMeV * (1 - gamma_HQIV / 56) := by
  simp [nucleonResonance1680MassFactor]

theorem excited_panel_N1710_uses_d13_slot_factor
    (scaffoldMeV : ℝ) :
    scaffoldMeV * nucleonResonance1710MassFactor =
      scaffoldMeV * (1 - gamma_HQIV / 28) := by
  simp [nucleonResonance1710MassFactor]

theorem excited_panel_Bc_uses_open_bc_correction
    (mProtonMeV mPiMeV : ℝ) :
    dressedOpenBcMesonMassMeV mProtonMeV mPiMeV =
      openBcMesonMassMeV mProtonMeV mPiMeV * openBcMassCorrectionFactor := rfl

#check excited_panel_Bc_uses_open_bc_correction

#check tuftExcitationChannel_shell_not_unique
#check excited_panel_openBottom_uses_dressed_readout
#check excited_panel_Bstar_uses_vector_factor
#check excited_panel_Dstar_uses_vector_factor
#check excited_panel_psi2S_uses_radial_factor

end Hqiv.Physics
