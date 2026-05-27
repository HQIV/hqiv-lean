import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.GRFromMaxwell
import Hqiv.Physics.Forces
import Mathlib.Tactic

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

/-! ### Interaction-aware binding split (self + pair channels) -/

/--
Interaction-aware split of nucleon binding into a self channel and a pair/network
channel. This is intentionally more general than a pure self-well model.
-/
structure InteractionBindingSplit where
  selfInteractionEnergy : ℝ
  pairInteractionEnergy : ℝ
  total_eq_sharedBinding :
    selfInteractionEnergy + pairInteractionEnergy = sharedBindingEnergy

/-- Interaction-aware raw mass: constituent energy minus total interaction energy. -/
noncomputable def interactionAwareMass
    (constituentEnergy : ℝ) (split : InteractionBindingSplit) : ℝ :=
  constituentEnergy - (split.selfInteractionEnergy + split.pairInteractionEnergy)

theorem interactionAwareMass_eq_constituent_minus_shared
    (constituentEnergy : ℝ) (split : InteractionBindingSplit) :
    interactionAwareMass constituentEnergy split =
      constituentEnergy - sharedBindingEnergy := by
  unfold interactionAwareMass
  rw [split.total_eq_sharedBinding]

theorem derivedProtonMass_eq_interactionAware
    (split : InteractionBindingSplit) :
    derivedProtonMass = interactionAwareMass protonConstituentEnergy split := by
  rw [interactionAwareMass_eq_constituent_minus_shared]
  rfl

theorem derivedNeutronMass_eq_interactionAware
    (split : InteractionBindingSplit) :
    derivedNeutronMass = interactionAwareMass neutronConstituentEnergy split := by
  rw [interactionAwareMass_eq_constituent_minus_shared]
  rfl

theorem interactionAware_split_preserves_nucleon_gap
    (split : InteractionBindingSplit) :
    interactionAwareMass neutronConstituentEnergy split -
      interactionAwareMass protonConstituentEnergy split =
      derivedDeltaM := by
  rw [interactionAwareMass_eq_constituent_minus_shared,
    interactionAwareMass_eq_constituent_minus_shared]
  unfold derivedDeltaM derivedNeutronMass derivedProtonMass
  ring

/-- One-parameter interaction split: `η` controls the self-channel share; the
rest is pair/network interaction. -/
noncomputable def interactionBindingSplitFromShare (η : ℝ) :
    InteractionBindingSplit where
  selfInteractionEnergy := η * sharedBindingEnergy
  pairInteractionEnergy := (1 - η) * sharedBindingEnergy
  total_eq_sharedBinding := by ring

theorem interactionBindingSplitFromShare_self_component (η : ℝ) :
    (interactionBindingSplitFromShare η).selfInteractionEnergy =
      η * sharedBindingEnergy := rfl

theorem interactionBindingSplitFromShare_pair_component (η : ℝ) :
    (interactionBindingSplitFromShare η).pairInteractionEnergy =
      (1 - η) * sharedBindingEnergy := rfl

theorem interactionBindingSplitFromShare_recovers_raw_proton (η : ℝ) :
    interactionAwareMass protonConstituentEnergy
      (interactionBindingSplitFromShare η) = derivedProtonMass := by
  rw [interactionAwareMass_eq_constituent_minus_shared]
  rfl

/-! ### Discrete-Maxwell well path budget (interaction + path integration) -/

/-- Single-shell well contribution from the discrete/modified Maxwell effective potential. -/
noncomputable def maxwellWellShellBudget
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) : ℝ :=
  Hqiv.nuclear_effective_potential m config

/-- Integrated well budget along a discrete shell path.

The current placeholder integration is linear in the discrete step count; this keeps
the bookkeeping explicit while higher-fidelity path accumulation is developed.
-/
noncomputable def integratedMaxwellWellBudget
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) (pathSteps : ℕ) : ℝ :=
  (pathSteps : ℝ) * maxwellWellShellBudget m config

theorem integratedMaxwellWellBudget_zero
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) :
    integratedMaxwellWellBudget m config 0 = 0 := by
  unfold integratedMaxwellWellBudget
  norm_num

theorem integratedMaxwellWellBudget_succ
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) (n : ℕ) :
    integratedMaxwellWellBudget m config (n + 1) =
      integratedMaxwellWellBudget m config n + maxwellWellShellBudget m config := by
  unfold integratedMaxwellWellBudget
  simp [Nat.cast_add, Nat.cast_one, add_mul]

/-- Full interaction-aware mass budget including:
1) self interaction, 2) pair/network interaction, 3) integrated Maxwell well path. -/
noncomputable def interactionAndWellAwareMass
    (constituentEnergy : ℝ) (split : InteractionBindingSplit)
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) (pathSteps : ℕ) : ℝ :=
  constituentEnergy - (split.selfInteractionEnergy + split.pairInteractionEnergy)
    - integratedMaxwellWellBudget m config pathSteps

theorem interactionAndWellAwareMass_eq_interactionAware_minus_path
    (constituentEnergy : ℝ) (split : InteractionBindingSplit)
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) (pathSteps : ℕ) :
    interactionAndWellAwareMass constituentEnergy split m config pathSteps =
      interactionAwareMass constituentEnergy split -
        integratedMaxwellWellBudget m config pathSteps := by
  unfold interactionAndWellAwareMass interactionAwareMass
  ring

theorem interactionAndWellAwareMass_eq_constituent_minus_shared_and_path
    (constituentEnergy : ℝ) (split : InteractionBindingSplit)
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) (pathSteps : ℕ) :
    interactionAndWellAwareMass constituentEnergy split m config pathSteps =
      constituentEnergy - sharedBindingEnergy - integratedMaxwellWellBudget m config pathSteps := by
  rw [interactionAndWellAwareMass_eq_interactionAware_minus_path,
    interactionAwareMass_eq_constituent_minus_shared]

theorem interactionAndWellAwareMass_zero_path_recovers_interactionAware
    (constituentEnergy : ℝ) (split : InteractionBindingSplit)
    (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig) :
    interactionAndWellAwareMass constituentEnergy split m config 0 =
      interactionAwareMass constituentEnergy split := by
  rw [interactionAndWellAwareMass_eq_interactionAware_minus_path]
  unfold integratedMaxwellWellBudget
  norm_num

/-- `η = 0` sends all shared binding budget to the pair/network channel, then adds
the integrated Maxwell-well path contribution. -/
theorem interactionAndWellAwareMass_share_zero
    (constituentEnergy : ℝ) (m : Hqiv.ShellIndex) (config : Hqiv.OctonionConfig)
    (pathSteps : ℕ) :
    interactionAndWellAwareMass constituentEnergy (interactionBindingSplitFromShare 0)
        m config pathSteps
      = constituentEnergy - sharedBindingEnergy
        - integratedMaxwellWellBudget m config pathSteps := by
  rw [interactionAndWellAwareMass_eq_constituent_minus_shared_and_path]

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

theorem derivedProtonMass_eq_meta_harmonics :
    derivedProtonMass = protonMassFromMetaHarmonics_MeV := by
  simp [derivedProtonMass, protonConstituentEnergy, sharedBindingEnergy,
    protonMassFromMetaHarmonics_MeV]

theorem derivedNeutronMass_eq_meta_harmonics :
    derivedNeutronMass = neutronMassFromMetaHarmonics_MeV := by
  simp [derivedNeutronMass, neutronConstituentEnergy, sharedBindingEnergy,
    neutronMassFromMetaHarmonics_MeV]

end Hqiv.Physics

