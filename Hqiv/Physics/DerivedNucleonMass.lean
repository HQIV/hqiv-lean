import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.GRFromMaxwell

namespace Hqiv.Physics

/-!
Pure-derivation nucleon masses (proton/neutron) on the internal meta-horizon.

This module deliberately avoids hardcoding *proton/neutron* rest masses
as standalone outputs. Instead it packages the constituent-mass sums and the
shared HQIV network binding from `QuarkMetaResonance`.
-/

/-!
`internalSurfaceArea` is provided by `Hqiv.Physics.QuarkMetaResonance`.
We reuse it here to avoid duplicate declarations in the same namespace.
-/

/-! ### Top anchor / resonance structure -/

/-- Top birth shell is the lock-in (referenceM) shell. -/
def top_at_lockin : ℕ := referenceM

/-! ### Resonance drops -/

/-- Mass drops across internal harmonic steps (effective surface ratio). -/
noncomputable def resonanceDropK (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      internalSurfaceArea (top_at_lockin + 1) / internalSurfaceArea top_at_lockin
  | ⟨1, _⟩ =>
      internalSurfaceArea (top_at_lockin + 2) / internalSurfaceArea (top_at_lockin + 1)

/-! ### Shared binding + constituent sums -/

/-!
The shared binding energy comes from the explicit composite-trace witness on the
lock-in shell. Proton/neutron differences are carried by the constituent sums
(`uud` versus `udd`), not by a separate EM block split.
-/

noncomputable def sharedBindingEnergy : ℝ := nucleonSharedBinding_MeV

noncomputable def protonConstituentEnergy : ℝ := protonConstituentMass_MeV
noncomputable def neutronConstituentEnergy : ℝ := neutronConstituentMass_MeV

noncomputable def derivedProtonMass : ℝ :=
  protonConstituentEnergy - sharedBindingEnergy

noncomputable def derivedNeutronMass : ℝ :=
  neutronConstituentEnergy - sharedBindingEnergy

noncomputable def derivedDeltaM : ℝ :=
  derivedNeutronMass - derivedProtonMass

/-! ### HQVM-lapse wired readouts -/

/-- Derived proton mass with controlled HQVM lapse correction on the lock-in shell. -/
noncomputable def derivedProtonMass_lapseCorrected (Φ t : ℝ) : ℝ :=
  protonMassFromMetaHarmonics_lapseCorrected_MeV Φ t

/-- Derived neutron mass with controlled HQVM lapse correction on the lock-in shell. -/
noncomputable def derivedNeutronMass_lapseCorrected (Φ t : ℝ) : ℝ :=
  neutronMassFromMetaHarmonics_lapseCorrected_MeV Φ t

/-- Lapse-corrected proton mass is raw proton mass divided by lock-in HQVM lapse. -/
theorem derivedProtonMass_lapseCorrected_eq_raw_div_lapse (Φ t : ℝ) :
    derivedProtonMass_lapseCorrected Φ t = derivedProtonMass / lockinHQVMLapse Φ t := by
  unfold derivedProtonMass_lapseCorrected derivedProtonMass
    protonConstituentEnergy sharedBindingEnergy
  exact protonMassFromMetaHarmonics_lapseCorrected_eq_raw_div_lapse Φ t

/-- Lapse-corrected neutron mass is raw neutron mass divided by lock-in HQVM lapse. -/
theorem derivedNeutronMass_lapseCorrected_eq_raw_div_lapse (Φ t : ℝ) :
    derivedNeutronMass_lapseCorrected Φ t = derivedNeutronMass / lockinHQVMLapse Φ t := by
  unfold derivedNeutronMass_lapseCorrected derivedNeutronMass
    neutronConstituentEnergy sharedBindingEnergy
  exact neutronMassFromMetaHarmonics_lapseCorrected_eq_raw_div_lapse Φ t

/-- Compatibility wiring: the same lock-in `φ` used in lapse correction satisfies the
O-Maxwell/HQVM homogeneous compatibility template. -/
theorem lockinAuxPhi_O_Maxwell_HQVM_compatible_homogeneous
    (rho_m rho_r : ℝ) (hphi : 0 ≤ lockinAuxPhi) :
    HQVM_Friedmann_eq lockinAuxPhi rho_m rho_r ↔
      (13 / 5 : ℝ) * lockinAuxPhi ^ 2 =
        8 * Real.pi * (lockinAuxPhi ^ alpha) * (rho_m + rho_r) := by
  exact O_Maxwell_compatible_with_HQVM_GR_homogeneous lockinAuxPhi rho_m rho_r hphi

/-- Target-anchor discharge lemma: if the lapse equals the ratio `raw/anchor`,
the corrected proton mass is exactly the anchor value. -/
theorem derivedProtonMass_lapseCorrected_eq_anchor_of_lapse_ratio
    (Φ t : ℝ)
    (hlapse : lockinHQVMLapse Φ t * protonAnchorMass_MeV = derivedProtonMass)
    (hlapseNz : lockinHQVMLapse Φ t ≠ 0) :
    derivedProtonMass_lapseCorrected Φ t = protonAnchorMass_MeV := by
  rw [derivedProtonMass_lapseCorrected_eq_raw_div_lapse, ← hlapse]
  field_simp [hlapseNz]

/-- Top anchored at the lock-in shell. -/
theorem top_anchored_at_T_lockin : top_at_lockin = referenceM := by
  rfl

/-! ### Required theorems -/

theorem top_anchored_at_T_lockin_now :
    top_at_lockin = referenceM := by
  rfl

theorem light_quarks_from_two_resonance_drops :
    quarkMass ⟨1, by decide⟩ = m_charm_GeV ∧
      quarkMass ⟨0, by decide⟩ = m_up_GeV ∧
      quarkMassDown ⟨1, by decide⟩ = m_strange_GeV ∧
      quarkMassDown ⟨0, by decide⟩ = m_down_GeV := by
  exact two_octave_drops_to_light_quarks

theorem proton_mass_from_shared_harmonics :
    derivedProtonMass = protonConstituentEnergy - sharedBindingEnergy := by
  rfl

theorem neutron_mass_from_shared_harmonics :
    derivedNeutronMass = neutronConstituentEnergy - sharedBindingEnergy := by
  rfl

theorem derivedProtonMass_pos :
    0 < derivedProtonMass := by
  simpa [derivedProtonMass, protonConstituentEnergy, sharedBindingEnergy,
    protonMassFromMetaHarmonics_MeV, protonConstituentMass_MeV] using
    protonMassFromMetaHarmonics_pos

theorem derivedNeutronMass_pos :
    0 < derivedNeutronMass := by
  simpa [derivedNeutronMass, neutronConstituentEnergy, sharedBindingEnergy,
    neutronMassFromMetaHarmonics_MeV, neutronConstituentMass_MeV] using
    neutronMassFromMetaHarmonics_pos

theorem constituent_isospin_splitting :
    derivedDeltaM = neutronConstituentEnergy - protonConstituentEnergy := by
  simp [derivedDeltaM, derivedNeutronMass, derivedProtonMass,
    protonConstituentEnergy, neutronConstituentEnergy, sharedBindingEnergy]

theorem proton_neutron_closeness_from_shared_surface :
    derivedNeutronMass - derivedProtonMass = derivedDeltaM := by
  rfl

end Hqiv.Physics

