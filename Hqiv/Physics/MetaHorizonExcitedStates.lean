import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.BoundStates
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.DerivedNucleonMass

namespace Hqiv.Physics

open BigOperators

/-!
Excited baryons are modeled as internal meta-horizon harmonics (radial/orbital)
on the same drum-like surface that gives the nucleon ground state.

**Rindler detuning (MeV):** `rindlerDetuningMeV` is **`rindlerDetuningShared`** from `FanoResonance`
with dimensionless argument `2·(massMeV/10000)`, so it expands to `1 + γ·(massMeV/10000)` with
`γ = gamma_HQIV` — the same monogamy coefficient as elsewhere, not a separate numeric convention.
(Distinct name from `ChargedLeptonResonance.rindlerDetuning`, which takes the **shell index** as `ℝ`.)

Surface bookkeeping `internalSurfaceArea`, the constituent masses, and the
shared composite-trace witness live in `QuarkMetaResonance` (imported above).

## Two excitation readouts (do not conflate)

* **Naive composite trace:** `totalModeMass n ℓ = constituent − E_bind_from_composite_trace`
  at `referenceM + n + ℓ`.  Binding grows with `latticeSimplexCount m`, so the first radial
  step **lowers** mass above ground (wrong sign for baryon spectroscopy).
* **Operational meta-horizon:** `metaHorizonExcitedMassReadout` adds
  `radialExcitationDeltaOperational` (internal surface step) and
  `orbitalExcitationDeltaOperational` (detuned `geometricResonanceStep` on the lock-in drum).
  This is the calculator / catalog layer (`scripts/hqiv_excited_states.py`).
-/

/-- Shell used by the `n`-th radial excitation above the lock-in ground state. -/
def radialExcitationShell (n : ℕ) : ℕ := referenceM + n

/-- Shell used by the `ℓ`-th orbital excitation above the lock-in ground state. -/
def orbitalExcitationShell (ℓ : ℕ) : ℕ := referenceM + ℓ

/-- Shared ground-state internal binding on the lock-in shell (MeV). -/
noncomputable def baseQCD_binding : ℝ := nucleonSharedBinding_MeV

/-- Internal Rindler detuning on a **MeV** input: `rindlerDetuningShared (2·massMeV/10000) = 1 + γ·massMeV/10000`. -/
noncomputable def rindlerDetuningMeV (massMeV : ℝ) : ℝ :=
  rindlerDetuningShared (2 * massMeV / 10000)

theorem rindlerDetuningMeV_eq_gamma_mass_over_10k (massMeV : ℝ) :
    rindlerDetuningMeV massMeV = 1 + gamma_HQIV * massMeV / 10000 := by
  unfold rindlerDetuningMeV rindlerDetuningShared c_rindler_shared
  ring

theorem rindlerDetuningMeV_eq_two_fifths_mass_over_10k (massMeV : ℝ) :
    rindlerDetuningMeV massMeV = 1 + (2 / 5) * massMeV / 10000 := by
  rw [rindlerDetuningMeV_eq_gamma_mass_over_10k, gamma_eq_2_5]

/-- Total shell used by a combined radial/orbital mode. -/
def totalModeShell (n ℓ : ℕ) : ℕ :=
  referenceM + n + ℓ

/-- Shell-agnostic modal frequency/horizon wrapper for a combined radial/orbital mode. -/
noncomputable def totalModeFrequencySpec (n ℓ : ℕ) : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal (totalModeShell n ℓ)

theorem totalModeFrequencySpec_quarterPhase_eq_horizonQuarter (n ℓ : ℕ) :
    (totalModeFrequencySpec n ℓ).nominalOmega * (totalModeFrequencySpec n ℓ).interactionQuarterPeriod =
      Hqiv.horizonQuarterPeriod := by
  simpa [totalModeFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal (totalModeShell n ℓ)).quarterPhase_eq_horizonQuarter

theorem totalModeFrequencySpec_detuning_affine (n ℓ m : ℕ) :
    (totalModeFrequencySpec n ℓ).detuning1Jet m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  simpa [totalModeFrequencySpec] using
    (modalFrequencyHorizonFromShellNominal_detuning_affine (totalModeShell n ℓ)) m

/-- Radial mode frequency/horizon wrapper (`ℓ = 0`). -/
noncomputable def radialModeFrequencySpec (n : ℕ) : ModalFrequencyHorizonSpec :=
  totalModeFrequencySpec n 0

/-- Orbital mode frequency/horizon wrapper (`n = 0`). -/
noncomputable def orbitalModeFrequencySpec (ℓ : ℕ) : ModalFrequencyHorizonSpec :=
  totalModeFrequencySpec 0 ℓ

/-- Binding carried by a combined radial/orbital mode. -/
noncomputable def totalModeBinding (n ℓ : ℕ) : ℝ :=
  E_bind_from_composite_trace (totalModeShell n ℓ) nucleonTraceDiagonal nucleonTraceState

/-- Total mode mass for low-lying internal radial/orbital harmonics (MeV). -/
noncomputable def totalModeMass (n ℓ : ℕ) : ℝ :=
  protonConstituentMass_MeV - totalModeBinding n ℓ

/-- Radial harmonic label (n = 0,1,2,...) on the internal meta-horizon. -/
noncomputable def radialHarmonic (n : ℕ) : ℝ :=
  totalModeMass n 0 / derivedProtonMass

/-- Orbital harmonic label (ℓ = 0,1,2,...) on the internal meta-horizon. -/
noncomputable def orbitalHarmonic (ℓ : ℕ) : ℝ :=
  totalModeMass 0 ℓ / derivedProtonMass

/-- Radial harmonic, explicitly presented as a readout from the radial modal-frequency wrapper. -/
noncomputable def radialHarmonicFromModalReadout (n : ℕ) : ℝ :=
  totalModeMass n 0 / derivedProtonMass

/-- Orbital harmonic, explicitly presented as a readout from the orbital modal-frequency wrapper. -/
noncomputable def orbitalHarmonicFromModalReadout (ℓ : ℕ) : ℝ :=
  totalModeMass 0 ℓ / derivedProtonMass

theorem radialHarmonic_eq_modal_readout (n : ℕ) :
    radialHarmonic n = radialHarmonicFromModalReadout n := rfl

theorem orbitalHarmonic_eq_modal_readout (ℓ : ℕ) :
    orbitalHarmonic ℓ = orbitalHarmonicFromModalReadout ℓ := rfl

theorem proton_neutron_from_shared_surface :
    neutronMassFromMetaHarmonics_MeV - protonMassFromMetaHarmonics_MeV = derivedDeltaM :=
  rfl

theorem ground_mode_is_derived_proton :
    totalModeMass 0 0 = derivedProtonMass := by
  simp [totalModeMass, totalModeBinding, totalModeShell, protonConstituentMass_MeV,
    derivedProtonMass, protonConstituentEnergy, sharedBindingEnergy,
    nucleonSharedBinding_MeV]

theorem first_radial_mode_uses_next_shell :
    totalModeBinding 1 0 =
      E_bind_from_composite_trace (referenceM + 1) nucleonTraceDiagonal nucleonTraceState := by
  simp [totalModeBinding, totalModeShell]

theorem first_orbital_mode_uses_next_shell :
    totalModeBinding 0 1 =
      E_bind_from_composite_trace (referenceM + 1) nucleonTraceDiagonal nucleonTraceState := by
  simp [totalModeBinding, totalModeShell]

theorem mixed_mode_adds_radial_and_orbital_steps :
    totalModeShell 1 1 = referenceM + 2 ∧
      totalModeShell 2 1 = referenceM + 3 := by
  exact ⟨by simp [totalModeShell], by simp [totalModeShell]⟩

/-! ## Naive vs operational excitation deltas -/

/-- ΔM from raw `totalModeMass` above `derivedProtonMass` (composite-trace binding law). -/
noncomputable def metaHorizonExcitationDeltaNaive (n ℓ : ℕ) : ℝ :=
  totalModeMass n ℓ - derivedProtonMass

theorem metaHorizonExcitationDeltaNaive_zero :
    metaHorizonExcitationDeltaNaive 0 0 = 0 := by
  simp [metaHorizonExcitationDeltaNaive, ground_mode_is_derived_proton]

theorem metaHorizonExcitationDeltaNaive_one_eq_binding_drop :
    metaHorizonExcitationDeltaNaive 1 0 = baseQCD_binding - totalModeBinding 1 0 := by
  unfold metaHorizonExcitationDeltaNaive totalModeMass derivedProtonMass baseQCD_binding
  simp [protonConstituentMass_MeV, protonConstituentEnergy, sharedBindingEnergy,
    nucleonSharedBinding_MeV]

theorem referenceM_eq_four_local : referenceM = 4 := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem internalSurfaceArea_eq_shellSurface (m : ℕ) :
    internalSurfaceArea m = shellSurface m := rfl

theorem shellSurface_pos (m : ℕ) : 0 < shellSurface m := by
  unfold shellSurface
  norm_cast
  exact mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

theorem shellSurface_referenceM_succ_gt :
    shellSurface (referenceM + 1) > shellSurface referenceM := by
  rw [referenceM_eq_four_local]
  unfold shellSurface
  norm_num

/--
Radial meta-horizon step on the lock-in drum: `m_p · (S(m+n)/S(m) − 1)` with `S(m)=(m+1)(m+2)`.
-/
noncomputable def radialExcitationDeltaOperational (n : ℕ) : ℝ :=
  derivedProtonMass *
    (internalSurfaceArea (referenceM + n) / internalSurfaceArea referenceM - 1)

theorem radialExcitationDeltaOperational_zero :
    radialExcitationDeltaOperational 0 = 0 := by
  unfold radialExcitationDeltaOperational
  rw [internalSurfaceArea_eq_shellSurface, internalSurfaceArea_eq_shellSurface, Nat.add_zero]
  field_simp [ne_of_gt (shellSurface_pos referenceM)]
  ring

theorem radialExcitationDeltaOperational_one_eq_surface_step :
    radialExcitationDeltaOperational 1 =
      derivedProtonMass *
        (internalSurfaceArea (referenceM + 1) / internalSurfaceArea referenceM - 1) := rfl

/--
Orbital / vector-meson step: `m_p · max(0, geometricResonanceStep(m+ℓ, m_lock) − 1)`.
-/
noncomputable def orbitalExcitationDeltaOperational (ℓ : ℕ) : ℝ :=
  derivedProtonMass *
    max 0 (geometricResonanceStep (referenceM + ℓ) referenceM - 1)

theorem geometricResonanceStep_self (m : ℕ) :
    geometricResonanceStep m m = 1 := by
  unfold geometricResonanceStep
  field_simp [(detunedShellSurface_pos m).ne']

theorem orbitalExcitationDeltaOperational_zero :
    orbitalExcitationDeltaOperational 0 = 0 := by
  unfold orbitalExcitationDeltaOperational
  simp [geometricResonanceStep_self, max_eq_left (by norm_num : (0 : ℝ) ≤ 0)]

/-- Catalog / calculator excited mass: ground proton plus operational radial/orbital steps. -/
noncomputable def metaHorizonExcitedMassReadout (n ℓ : ℕ) : ℝ :=
  derivedProtonMass +
    radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ

theorem metaHorizonExcitedMassReadout_ground :
    metaHorizonExcitedMassReadout 0 0 = derivedProtonMass := by
  simp [metaHorizonExcitedMassReadout, radialExcitationDeltaOperational_zero,
    orbitalExcitationDeltaOperational_zero]

/-! ### Composite-trace binding grows at the first radial shell -/

theorem compositeTraceAtGenerator_nucleon_zero :
    compositeTraceAtGenerator nucleonTraceDiagonal nucleonTraceState nucleonTraceGeneratorIndex0 =
      3 := by
  simp [compositeTraceAtGenerator, nucleonTraceDiagonal, nucleonTraceState,
    nucleonTraceGeneratorIndex0, nucleonTraceCarrierIndex0, nucleonTraceCarrierIndex1,
    nucleonTraceCarrierIndex2, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  norm_num

theorem compositeTraceAtGenerator_nucleon_other (k : So8Index)
    (hk : k ≠ nucleonTraceGeneratorIndex0) :
    compositeTraceAtGenerator nucleonTraceDiagonal nucleonTraceState k = 0 := by
  simp [compositeTraceAtGenerator, nucleonTraceDiagonal, nucleonTraceState, hk,
    Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

theorem compositeTraceAtGenerator_nucleon (k : So8Index) :
    compositeTraceAtGenerator nucleonTraceDiagonal nucleonTraceState k =
      if k = nucleonTraceGeneratorIndex0 then (3 : ℝ) else 0 := by
  split_ifs with h
  · subst h; exact compositeTraceAtGenerator_nucleon_zero
  · exact compositeTraceAtGenerator_nucleon_other k h

theorem nucleonTrace_networkWeight (k : So8Index) :
    (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) k =
      if k = nucleonTraceGeneratorIndex0 then (3 : ℝ) else 0 := by
  simpa using compositeTraceAtGenerator_nucleon k

theorem E_bind_nucleon_trace_eq_triple_coupling (m : ℕ) (c : ℝ := 1) :
    E_bind_from_composite_trace m nucleonTraceDiagonal nucleonTraceState c =
      (3 : ℝ) * bindingCouplingAtShell m nucleonTraceGeneratorIndex0 c := by
  simp [E_bind_from_composite_trace, E_bind_from_network, nucleonTrace_networkWeight,
    bindingCouplingAtShell, Finset.sum_ite, Finset.sum_const, Finset.card_fin]

theorem top_at_lockin_eq_referenceM : top_at_lockin = referenceM := rfl

theorem resonanceDropK_zero_gt_one : 1 < resonanceDropK ⟨0, by decide⟩ := by
  unfold resonanceDropK
  simp only [Fin.isValue, top_at_lockin, referenceM_eq_four_local, internalSurfaceArea, shellSurface]
  norm_num

theorem radialExcitationDeltaOperational_one_eq_resonanceDrop :
    radialExcitationDeltaOperational 1 =
      derivedProtonMass * (resonanceDropK ⟨0, by decide⟩ - 1) := by
  simp [radialExcitationDeltaOperational, resonanceDropK, internalSurfaceArea, top_at_lockin,
    referenceM_eq_four_local, shellSurface]

theorem radialExcitationDeltaOperational_one_pos :
    0 < radialExcitationDeltaOperational 1 := by
  rw [radialExcitationDeltaOperational_one_eq_resonanceDrop]
  have hdrop : 1 < resonanceDropK ⟨0, by decide⟩ := resonanceDropK_zero_gt_one
  nlinarith [derivedProtonMass_pos, hdrop]

/-! ### Log-ladder certificate at lock-in → first radial shell -/

theorem phi_of_shell_four_add_one_eq_eleven :
    phi_of_shell referenceM + 1 = 11 := by
  rw [referenceM_eq_four_local, phi_of_shell_closed_form]
  simp [phiTemperatureCoeff]
  norm_num

theorem phi_of_shell_five_add_one_eq_thirteen :
    phi_of_shell (referenceM + 1) + 1 = 13 := by
  rw [referenceM_eq_four_local, phi_of_shell_closed_form]
  simp [phiTemperatureCoeff]
  norm_num

/-- `exp 0.5 = √(exp 1) < 1.65` from `exp_one_lt_d9` (certified bound). -/
private theorem exp_half_lt_165 : Real.exp (0.5 : ℝ) < (1.65 : ℝ) := by
  have h05 : Real.exp (0.5 : ℝ) = Real.sqrt (Real.exp 1) := by
    have hcast : (0.5 : ℝ) = (1 / 2 : ℝ) := by norm_num
    simpa [hcast, div_eq_mul_inv, one_div] using Real.exp_half (1 : ℝ)
  rw [h05]
  have hsqrt := Real.sqrt_lt_sqrt (Real.exp_pos 1).le Real.exp_one_lt_d9
  have hroot : Real.sqrt (2.7182818286 : ℝ) < (1.65 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2.7182818286 by norm_num)]
  exact hsqrt.trans hroot

/-- `exp 1.477 < 5`, hence `log 5 > 1.477` (feeds `log 10 = log 2 + log 5`). -/
private theorem log5_gt_1477 : (1.477 : ℝ) < Real.log 5 := by
  refine (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)).mpr ?_
  have hadd : Real.exp (1.477 : ℝ) = Real.exp 1 * Real.exp (0.477 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  have h0477 : Real.exp (0.477 : ℝ) < (1.65 : ℝ) :=
    (Real.exp_lt_exp.mpr (by norm_num : (0.477 : ℝ) < (0.5 : ℝ))).trans exp_half_lt_165
  have hstep1 : Real.exp 1 * Real.exp (0.477 : ℝ) < Real.exp 1 * (1.65 : ℝ) :=
    mul_lt_mul_of_pos_left h0477 (Real.exp_pos 1)
  have hstep2 : Real.exp 1 * (1.65 : ℝ) < (5 : ℝ) := by nlinarith [Real.exp_one_lt_d9]
  rw [hadd]
  exact hstep1.trans hstep2

/-- `log 10 > 2.17`; with `log 11 > log 10` this is the margin used in `shell_binding_log_cross_inequality`. -/
private theorem log10_gt_217 : (2.17 : ℝ) < Real.log 10 := by
  have hmul : Real.log 2 + Real.log 5 = Real.log 10 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
    norm_num
  linarith [Real.log_two_gt_d9, log5_gt_1477, hmul]

/-- Certified `log 11` lower bound for the shell cross inequality (`12·log11 − 30·(log13 − log11) > 20`). -/
theorem log11_gt_shell_binding : (2.17 : ℝ) < Real.log 11 := by
  have h1011 : Real.log 10 < Real.log 11 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith [log10_gt_217, h1011]

theorem log13_sub_log11_lt_point_two : Real.log 13 - Real.log 11 < (0.2 : ℝ) := by
  have hle : Real.log 13 < Real.log (13.1 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hdiv : Real.log (13.1 : ℝ) - Real.log 11 = Real.log ((13.1 : ℝ) / 11) := by
    symm
    exact Real.log_div (by norm_num) (by norm_num)
  have harg : (13.1 : ℝ) / 11 < Real.exp 0.2 := by
    have hstep : (0.2 : ℝ) + 1 < Real.exp 0.2 := Real.add_one_lt_exp (by norm_num : (0.2 : ℝ) ≠ 0)
    nlinarith
  have hratio : Real.log ((13.1 : ℝ) / 11) < (0.2 : ℝ) :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < (13.1 : ℝ) / 11)).mpr harg
  linarith [hle, hdiv, hratio]

/--
Main log-ladder inequality for nucleon binding at shells `referenceM` and `referenceM + 1`:
`30·(1+α log φ(5)) < 42·(1+α log φ(4))` with `φ(m)=2(m+1)` and `α=3/5`.
-/
theorem shell_binding_log_cross_inequality :
    (30 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 13) < (42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 11) := by
  have hsplit :
      (42 : ℝ) * Real.log 11 - (30 : ℝ) * Real.log 13 =
        (12 : ℝ) * Real.log 11 - (30 : ℝ) * (Real.log 13 - Real.log 11) := by ring
  have hbind_diff : (42 : ℝ) * Real.log 11 - (30 : ℝ) * Real.log 13 > (20 : ℝ) := by
    rw [hsplit]
    nlinarith [log11_gt_shell_binding, log13_sub_log11_lt_point_two]
  nlinarith [hbind_diff]

theorem bindingCoupling_nucleon_referenceM_succ_gt :
    bindingCouplingAtShell referenceM nucleonTraceGeneratorIndex0 <
      bindingCouplingAtShell (referenceM + 1) nucleonTraceGeneratorIndex0 := by
  rw [referenceM_eq_four_local]
  have hφ4 : phi_of_shell 4 + 1 = 11 := by
    rw [← referenceM_eq_four_local]; exact phi_of_shell_four_add_one_eq_eleven
  have hφ5 : phi_of_shell 5 + 1 = 13 := phi_of_shell_five_add_one_eq_thirteen
  have hone4 :
      oneOverAlphaEffAtShell 4 = 42 * (1 + (3 / 5 : ℝ) * Real.log 11) := by
    simp [oneOverAlphaEffAtShell, oneOverAlphaBare, alpha_eq_3_5, hφ4]
  have hone5 :
      oneOverAlphaEffAtShell 5 = 42 * (1 + (3 / 5 : ℝ) * Real.log 13) := by
    simp [oneOverAlphaEffAtShell, oneOverAlphaBare, alpha_eq_3_5, hφ5]
  have hα4 : alphaEffAtShell 4 = (42 * (1 + (3 / 5 : ℝ) * Real.log 11))⁻¹ := by
    simp [alphaEffAtShell, hone4]
  have hα5 : alphaEffAtShell 5 = (42 * (1 + (3 / 5 : ℝ) * Real.log 13))⁻¹ := by
    simp [alphaEffAtShell, hone5]
  have hone11 : 0 < (42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 11) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 11)
    nlinarith
  have hone13 : 0 < (42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 13) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 13)
    nlinarith
  have hdiv :
      (30 : ℝ) / ((42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 11)) <
        (42 : ℝ) / ((42 : ℝ) * (1 + (3 / 5 : ℝ) * Real.log 13)) := by
    field_simp [hone11.ne', hone13.ne']
    nlinarith [shell_binding_log_cross_inequality]
  simpa [bindingCouplingAtShell, latticeSimplexCount, hα4, hα5, div_eq_mul_inv] using hdiv

theorem E_bind_nucleon_trace_referenceM_succ_gt :
    E_bind_from_composite_trace referenceM nucleonTraceDiagonal nucleonTraceState <
      E_bind_from_composite_trace (referenceM + 1) nucleonTraceDiagonal nucleonTraceState := by
  calc
    E_bind_from_composite_trace referenceM nucleonTraceDiagonal nucleonTraceState =
        3 * bindingCouplingAtShell referenceM nucleonTraceGeneratorIndex0 :=
      E_bind_nucleon_trace_eq_triple_coupling referenceM
    _ < 3 * bindingCouplingAtShell (referenceM + 1) nucleonTraceGeneratorIndex0 :=
      mul_lt_mul_of_pos_left bindingCoupling_nucleon_referenceM_succ_gt (by norm_num : (0 : ℝ) < 3)
    _ = E_bind_from_composite_trace (referenceM + 1) nucleonTraceDiagonal nucleonTraceState :=
      (E_bind_nucleon_trace_eq_triple_coupling (referenceM + 1)).symm

theorem totalModeBinding_one_gt_base :
    baseQCD_binding < totalModeBinding 1 0 := by
  simpa [baseQCD_binding, totalModeBinding, totalModeShell, nucleonSharedBinding_MeV] using
    E_bind_nucleon_trace_referenceM_succ_gt

theorem metaHorizonExcitationDeltaNaive_one_lt_zero :
    metaHorizonExcitationDeltaNaive 1 0 < 0 := by
  rw [metaHorizonExcitationDeltaNaive_one_eq_binding_drop]
  exact sub_neg.mpr totalModeBinding_one_gt_base

theorem metaHorizonExcitationDeltaNaive_ne_radialOperational :
    metaHorizonExcitationDeltaNaive 1 0 ≠ radialExcitationDeltaOperational 1 := by
  intro h
  rw [radialExcitationDeltaOperational_one_eq_resonanceDrop, metaHorizonExcitationDeltaNaive_one_eq_binding_drop] at h
  have hpos : 0 < derivedProtonMass * (resonanceDropK ⟨0, by decide⟩ - 1) := by
    nlinarith [derivedProtonMass_pos, resonanceDropK_zero_gt_one]
  linarith [totalModeBinding_one_gt_base, hpos]

/-! ### Orbital step uses lock-in `geometricResonanceStep` -/

theorem geometricResonanceStep_referenceM_succ_referenceM :
    geometricResonanceStep (referenceM + 1) referenceM =
      detunedShellSurface (referenceM + 1) / detunedShellSurface referenceM :=
  rfl

theorem geometricResonanceStep_five_four_gt_one :
    geometricResonanceStep (referenceM + 1) referenceM > 1 := by
  rw [geometricResonanceStep_referenceM_succ_referenceM, referenceM_eq_four_local]
  unfold detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
  rw [gamma_eq_2_5]
  norm_num

theorem orbitalExcitationDeltaOperational_one_pos :
    0 < orbitalExcitationDeltaOperational 1 := by
  unfold orbitalExcitationDeltaOperational
  have hstep : 0 < geometricResonanceStep (referenceM + 1) referenceM - 1 :=
    sub_pos.mpr geometricResonanceStep_five_four_gt_one
  simpa [max_eq_right hstep.le] using mul_pos derivedProtonMass_pos hstep

theorem metaHorizonExcitationDeltaNaive_ne_orbitalOperational :
    metaHorizonExcitationDeltaNaive 1 0 ≠ orbitalExcitationDeltaOperational 1 := by
  intro h
  rw [metaHorizonExcitationDeltaNaive_one_eq_binding_drop] at h
  linarith [totalModeBinding_one_gt_base, orbitalExcitationDeltaOperational_one_pos]

/-- Bundled witness: operational readouts are the certified excitation layer. -/
structure MetaHorizonExcitationReadoutWitness where
  naive_radial_negative : metaHorizonExcitationDeltaNaive 1 0 < 0
  radial_operational_positive : 0 < radialExcitationDeltaOperational 1
  orbital_operational_positive : 0 < orbitalExcitationDeltaOperational 1
  radial_eq_resonance_drop :
    radialExcitationDeltaOperational 1 =
      derivedProtonMass * (resonanceDropK ⟨0, by decide⟩ - 1)
  naive_ne_radial_operational : metaHorizonExcitationDeltaNaive 1 0 ≠ radialExcitationDeltaOperational 1
  naive_ne_orbital_operational : metaHorizonExcitationDeltaNaive 1 0 ≠ orbitalExcitationDeltaOperational 1
  excited_readout_ground : metaHorizonExcitedMassReadout 0 0 = derivedProtonMass

theorem metaHorizonExcitationReadoutWitness_default : MetaHorizonExcitationReadoutWitness where
  naive_radial_negative := metaHorizonExcitationDeltaNaive_one_lt_zero
  radial_operational_positive := radialExcitationDeltaOperational_one_pos
  orbital_operational_positive := orbitalExcitationDeltaOperational_one_pos
  radial_eq_resonance_drop := radialExcitationDeltaOperational_one_eq_resonanceDrop
  naive_ne_radial_operational := metaHorizonExcitationDeltaNaive_ne_radialOperational
  naive_ne_orbital_operational := metaHorizonExcitationDeltaNaive_ne_orbitalOperational
  excited_readout_ground := metaHorizonExcitedMassReadout_ground

end Hqiv.Physics
