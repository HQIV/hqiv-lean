import Mathlib.Tactic
import Hqiv.Physics.ConservedContentMassBridge
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.InformationalEnergyMass
import Hqiv.Physics.LapseMassReadout
import Hqiv.Physics.MetaHorizonExcitedStates
import Hqiv.Physics.QuarkMetaResonance

/-!
# Hadron mass readout (coupling stack + network binding + content scaling)

This module closes the gap between the **informational-energy / Fano coupling** stack
and the **8×8 composite-trace** hadron formulas already in `LapseMassReadout` and
`MetaHorizonExcitedStates`.

## Ground state

* **Baryons** (`colorComposed`, three valence channels): constituent sum minus
  `E_bind_from_composite_trace` at the readout shell, with binding scaled by
  `valenceChannelFraction`.
* **Mesons** (`chargeDecorated`, two valence quarks): same network binding with
  `2/3` channel fraction and an additional **`l²` factor** `4/9` from
  `intrinsicWaveComplexity .chargedLepton / intrinsicWaveComplexity .quark`
  (proved below — replaces the ad hoc `0.38` scaffold factor).

Proton and neutron at lock-in use the existing `derivedProtonMass` /
`derivedNeutronMass` witnesses (informational readout at vertex `v1` is handled
in `InformationalEnergyMass` + scale witnesses).

## Excitations

* **Decuplet / radial:** `radialExcitationDeltaOperational` — surface-step witness on
  the lock-in drum.  Raw `totalModeMass (n+1) 0` is **below** ground today because
  `E_bind_from_composite_trace` grows with `latticeSimplexCount`; the operational
  delta matches `scripts/hqiv_excited_states.py` until the shell binding law is refined.
* **Vector / orbital:** `orbitalExcitationDeltaOperational` from detuned
  `geometricResonanceStep` on the lock-in shell.

## Informational readout

`hadronMassFromXiAfterGround` applies `hadronMassFromXi` to a **ground** rest slot
already in MeV/GeV chart units (constituent − scaled binding, optionally witness-scaled).
-/

namespace Hqiv.Physics

open InformationalEnergyMass

/-! ## Hadron structure ↔ content class -/

/-- Catalog-level hadron structure (meson through pentaquark). -/
inductive HadronStructure
  | baryon
  | meson
  | tetraquark
  | pentaquark
  deriving DecidableEq, Repr

/-- Mesons are charge-decorated pairs; baryons/tetra/penta use full colour closure. -/
def closureLayerForHadron (h : HadronStructure) : FermionClosureLayer :=
  match h with
  | .meson => .chargeDecorated
  | _ => .colorComposed

theorem closureLayerForHadron_meson :
    closureLayerForHadron .meson = .chargeDecorated := rfl

theorem closureLayerForHadron_baryon :
    closureLayerForHadron .baryon = .colorComposed := rfl

/-- `l²` mass-scaling factor relative to baryon (`colorComposed`, `l = 3`). -/
noncomputable def hadronIntrinsicScale (h : HadronStructure) : ℝ :=
  (FermionClosureLayer.rank (closureLayerForHadron h) : ℝ) ^ 2 /
    (FermionClosureLayer.rank .colorComposed : ℝ) ^ 2

theorem hadronIntrinsicScale_baryon :
    hadronIntrinsicScale .baryon = 1 := by
  simp [hadronIntrinsicScale, closureLayerForHadron, FermionClosureLayer.rank]

theorem hadronIntrinsicScale_meson_eq_four_ninths :
    hadronIntrinsicScale .meson = (4 : ℝ) / 9 := by
  simp [hadronIntrinsicScale, closureLayerForHadron, FermionClosureLayer.rank]
  norm_num

theorem hadronIntrinsicScale_meson_eq_content_complexity_ratio :
    hadronIntrinsicScale .meson =
      intrinsicWaveComplexity .chargedLepton / intrinsicWaveComplexity .quark := by
  rw [hadronIntrinsicScale_meson_eq_four_ninths]
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

/-! ## Valence-channel binding scale -/

/-- Fraction of the nucleon tri-channel composite trace active for `n` valence quarks. -/
noncomputable def valenceChannelFraction (n : ℕ) : ℝ :=
  (n : ℝ) / (nucleonTraceChannelCount : ℝ)

theorem valenceChannelFraction_proton :
    valenceChannelFraction 3 = 1 := by
  simp [valenceChannelFraction, nucleonTraceChannelCount]

theorem valenceChannelFraction_meson_pair :
    valenceChannelFraction 2 = (2 : ℝ) / 3 := by
  simp [valenceChannelFraction, nucleonTraceChannelCount]

/-- QCD binding at shell `m`, scaled to `n` valence channels (same trace witness). -/
noncomputable def hadronBindingMeV (m n : ℕ) (c : ℝ := 1) : ℝ :=
  E_bind_from_composite_trace m nucleonTraceDiagonal nucleonTraceState c *
    valenceChannelFraction n

theorem hadronBindingMeV_proton_eq_shared :
    hadronBindingMeV referenceM 3 = nucleonSharedBinding_MeV := by
  dsimp [hadronBindingMeV, nucleonSharedBinding_MeV]
  simp [valenceChannelFraction_proton]

/-! ## Ground mass (MeV chart) -/

/-- Constituent minus scaled composite-trace binding (MeV). -/
noncomputable def hadronGroundMassMeV
    (m : ℕ) (constituentMeV : ℝ) (h : HadronStructure) (valenceQuarks : ℕ) (c : ℝ := 1) : ℝ :=
  (constituentMeV - hadronBindingMeV m valenceQuarks c) * hadronIntrinsicScale h

theorem hadronGroundMassMeV_proton_chart :
    hadronGroundMassMeV referenceM protonConstituentMass_MeV .baryon 3 =
      protonConstituentMass_MeV - nucleonSharedBinding_MeV := by
  simp [hadronGroundMassMeV, hadronIntrinsicScale_baryon, hadronBindingMeV_proton_eq_shared]

theorem hadronGroundMassMeV_eq_scaled_binding
    (m : ℕ) (constituentMeV : ℝ) (h : HadronStructure) (valenceQuarks : ℕ) (c : ℝ := 1) :
    hadronGroundMassMeV m constituentMeV h valenceQuarks c =
      constituentMeV * hadronIntrinsicScale h -
        hadronBindingMeV m valenceQuarks c * hadronIntrinsicScale h := by
  unfold hadronGroundMassMeV
  ring

theorem hadronGroundMassMeV_baryon_triple_eq_raw_composite
    (m : ℕ) (constituentMeV : ℝ) (c : ℝ := 1) :
    hadronGroundMassMeV m constituentMeV .baryon 3 c =
      rawHadronMassFromCompositeTrace m constituentMeV nucleonTraceDiagonal nucleonTraceState c := by
  simp [hadronGroundMassMeV, hadronIntrinsicScale_baryon, valenceChannelFraction_proton,
    hadronBindingMeV, rawHadronMassFromCompositeTrace]

/-! ## Excitation witnesses

Operational radial/orbital steps and the naive-vs-operational discrepancy witness live in
`MetaHorizonExcitedStates` (`metaHorizonExcitationReadoutWitness_default`).
-/

/-! ## Coupling to informational-energy readout -/

/-- Ground MeV slot after optional excitation tag (operational deltas). -/
noncomputable def hadronGroundWithExcitationMeV
    (m : ℕ) (constituentMeV : ℝ) (h : HadronStructure) (valenceQuarks : ℕ)
    (radialSteps orbitalSteps : ℕ) (c : ℝ := 1) : ℝ :=
  hadronGroundMassMeV m constituentMeV h valenceQuarks c +
    (radialSteps : ℝ) * radialExcitationDeltaOperational 1 +
    (orbitalSteps : ℝ) * orbitalExcitationDeltaOperational 1

/-- Apply hadron informational readout (`m_rest / N`) to a ground mass in chart units. -/
noncomputable def hadronMassFromXiAfterGround
    (groundMeV : ℝ) (ξ Φ t : ℝ) : ℝ :=
  hadronMassFromXi (groundMeV / 1000) ξ Φ t * 1000

theorem hadronMassFromXiAfterGround_eq_MeV_chart
    (groundMeV : ℝ) (ξ Φ t : ℝ) :
    hadronMassFromXiAfterGround groundMeV ξ Φ t =
      1000 * hadronMassFromXi (groundMeV / 1000) ξ Φ t := by
  unfold hadronMassFromXiAfterGround
  ring

/-- Proton lock-in: ground from composite trace matches derived mass. -/
theorem proton_hadronGround_eq_derived :
    hadronGroundMassMeV referenceM protonConstituentMass_MeV .baryon 3 =
      derivedProtonMass := by
  rw [hadronGroundMassMeV_proton_chart, proton_mass_from_shared_harmonics, sharedBindingEnergy]
  rfl

end Hqiv.Physics
