import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.DerivedNucleonMass

namespace Hqiv.Physics

/-!
Excited baryons are modeled as internal meta-horizon harmonics (radial/orbital)
on the same drum-like surface that gives the nucleon ground state.

**Rindler detuning (MeV):** `rindlerDetuningMeV` is **`rindlerDetuningShared`** from `FanoResonance`
with dimensionless argument `2·(massMeV/10000)`, so it expands to `1 + γ·(massMeV/10000)` with
`γ = gamma_HQIV` — the same monogamy coefficient as elsewhere, not a separate numeric convention.
(Distinct name from `ChargedLeptonResonance.rindlerDetuning`, which takes the **shell index** as `ℝ`.)

Surface bookkeeping `internalSurfaceArea`, the constituent masses, and the
shared composite-trace witness live in `QuarkMetaResonance` (imported above).

This module now also exposes modal-frequency wrappers for radial/orbital modes.
Current readout-index arithmetic remains the evaluation layer for binding/mass formulas.
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

end Hqiv.Physics
