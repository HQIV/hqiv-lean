import Hqiv.QuantumChemistry.BondRearrangementPath
import Hqiv.QuantumChemistry.MolecularReactionGate
import Hqiv.QuantumChemistry.MolecularTransport

/-!
# Molecular reaction transport

This module connects the finite reaction-gate scaffold to the molecular transport
bridge.  The reaction law is intentionally structural:

* a reaction gate supplies stoichiometric availability (`canApply`) and balance;
* phase geometry supplies number density;
* discrete diffusion supplies the shell-scaled contact rate;
* an optional bond-rearrangement path softens the contact rate via
  ``activationRateFromPath`` (discrete saddle transmission).

The result is a finite-patch reaction-rate slot, not a continuum kinetic law and not a
fitted Arrhenius/Stokes table.
-/


namespace Hqiv.QuantumChemistry

open scoped BigOperators

noncomputable section

namespace ReactionGate

variable {n k : ℕ}

/--
Transport-enabled reaction rate.

If the stoichiometric gate cannot consume the required species, the transport channel
is closed.  If it can, the rate is the diffusion-limited contact slot supplied by
`MolecularTransport`.
-/
noncomputable def transportRateSlot
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation : ℝ) : ℝ :=
  by
    classical
    exact
      if g.canApply s then
        diffusionLimitedContactRateSlot D numberDensity contactParticipation
      else
        0

theorem transportRateSlot_eq_of_canApply
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation : ℝ) (hcan : g.canApply s) :
    g.transportRateSlot s D numberDensity contactParticipation =
      diffusionLimitedContactRateSlot D numberDensity contactParticipation := by
  unfold transportRateSlot
  classical
  simp [hcan]

theorem transportRateSlot_zero_of_not_canApply
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation : ℝ) (hcan : ¬ g.canApply s) :
    g.transportRateSlot s D numberDensity contactParticipation = 0 := by
  unfold transportRateSlot
  classical
  simp [hcan]

theorem transportRateSlot_nonneg
    (g : ReactionGate n k) (s : MolecularRegister k)
    {D numberDensity contactParticipation : ℝ}
    (hD : 0 ≤ D) (hn : 0 ≤ numberDensity) (hc : 0 ≤ contactParticipation) :
    0 ≤ g.transportRateSlot s D numberDensity contactParticipation := by
  by_cases hcan : g.canApply s
  · rw [transportRateSlot_eq_of_canApply g s D numberDensity contactParticipation hcan]
    exact diffusionLimitedContactRateSlot_nonneg hD hn hc
  · rw [transportRateSlot_zero_of_not_canApply g s D numberDensity contactParticipation hcan]

/--
Activated transport rate: diffusion-limited contact rate softened by a discrete
bond-rearrangement path barrier (Lean ``activationRateFromPath``).

Empty / zero-barrier paths recover the bare transport slot.
-/
noncomputable def activatedTransportRateSlot
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation : ℝ)
    (path : BondRearrangementPath) (scaleEv : ℝ) : ℝ :=
  activationRateFromPath
    (g.transportRateSlot s D numberDensity contactParticipation) path scaleEv

theorem activatedTransportRateSlot_nil_path
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation scaleEv : ℝ) :
    g.activatedTransportRateSlot s D numberDensity contactParticipation [] scaleEv =
      g.transportRateSlot s D numberDensity contactParticipation := by
  unfold activatedTransportRateSlot
  exact activationRateFromPath_nil _ _

theorem activatedTransportRateSlot_zero_of_not_canApply
    (g : ReactionGate n k) (s : MolecularRegister k)
    (D numberDensity contactParticipation : ℝ)
    (path : BondRearrangementPath) (scaleEv : ℝ)
    (hcan : ¬ g.canApply s) :
    g.activatedTransportRateSlot s D numberDensity contactParticipation path scaleEv = 0 := by
  unfold activatedTransportRateSlot
  rw [transportRateSlot_zero_of_not_canApply g s D numberDensity contactParticipation hcan]
  unfold activationRateFromPath activationRateFromSaddle activationRateSlot
  ring

/-- Phase-geometry version using shell diffusion and unit-cell number density. -/
noncomputable def phaseTransportRateSlot
    (g : ReactionGate n k) (s : MolecularRegister k)
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ) : ℝ :=
  g.transportRateSlot s
    (HqivSpine.Physics.DiscreteDiffusion.shellDiffusionCoeff m ν)
    (molecularNumberDensityPerCm3 cell)
    contactParticipation

/-- Phase transport softened by a bond-rearrangement path. -/
noncomputable def activatedPhaseTransportRateSlot
    (g : ReactionGate n k) (s : MolecularRegister k)
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (path : BondRearrangementPath) (scaleEv : ℝ) : ℝ :=
  g.activatedTransportRateSlot s
    (HqivSpine.Physics.DiscreteDiffusion.shellDiffusionCoeff m ν)
    (molecularNumberDensityPerCm3 cell)
    contactParticipation path scaleEv

theorem phaseTransportRateSlot_eq_of_canApply
    (g : ReactionGate n k) (s : MolecularRegister k)
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (hcan : g.canApply s) :
    g.phaseTransportRateSlot s cell m ν contactParticipation =
      phaseDiffusionContactRateSlot cell m ν contactParticipation := by
  unfold phaseTransportRateSlot phaseDiffusionContactRateSlot
  exact transportRateSlot_eq_of_canApply g s _ _ _ hcan

theorem phaseTransportRateSlot_zero_of_not_canApply
    (g : ReactionGate n k) (s : MolecularRegister k)
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (hcan : ¬ g.canApply s) :
    g.phaseTransportRateSlot s cell m ν contactParticipation = 0 := by
  unfold phaseTransportRateSlot
  exact transportRateSlot_zero_of_not_canApply g s _ _ _ hcan

/--
Balanced transported reactions preserve each element count.  Transport controls the
rate channel; stoichiometry controls the register update.
-/
theorem apply_preserves_totalElementAtoms_of_transport_enabled
    (g : ReactionGate n k) (s : MolecularRegister k)
    (hcan : g.canApply s) (hbal : g.isElementBalanced) (e : Fin n) :
    totalElementAtoms g.atomsPerSpecies (g.apply s) e =
      totalElementAtoms g.atomsPerSpecies s e :=
  apply_preserves_totalElementAtoms g s hcan hbal e

end ReactionGate

/-! ## Water synthesis transport -/

/-- Water synthesis rate using the water gate and phase/diffusion contact slot. -/
noncomputable def waterSynthesisTransportRateSlot
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ) : ℝ :=
  waterSynthesisGate.phaseTransportRateSlot
    (registerOfSpeciesState s) cell m ν contactParticipation

/-- Water synthesis rate softened by a bond-rearrangement path (e.g. reverse
dissociation ladder).  Empty path recovers ``waterSynthesisTransportRateSlot``. -/
noncomputable def waterSynthesisActivatedTransportRateSlot
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (path : BondRearrangementPath) (scaleEv : ℝ) : ℝ :=
  waterSynthesisGate.activatedPhaseTransportRateSlot
    (registerOfSpeciesState s) cell m ν contactParticipation path scaleEv

theorem waterSynthesisActivatedTransportRateSlot_nil_path
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation scaleEv : ℝ) :
    waterSynthesisActivatedTransportRateSlot s cell m ν contactParticipation [] scaleEv =
      waterSynthesisTransportRateSlot s cell m ν contactParticipation := by
  unfold waterSynthesisActivatedTransportRateSlot waterSynthesisTransportRateSlot
    ReactionGate.activatedPhaseTransportRateSlot ReactionGate.phaseTransportRateSlot
  exact ReactionGate.activatedTransportRateSlot_nil_path _ _ _ _ _ _

theorem waterSynthesisTransportRateSlot_eq_of_canApply
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (hcan : waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    waterSynthesisTransportRateSlot s cell m ν contactParticipation =
      phaseDiffusionContactRateSlot cell m ν contactParticipation := by
  unfold waterSynthesisTransportRateSlot
  exact ReactionGate.phaseTransportRateSlot_eq_of_canApply
    waterSynthesisGate (registerOfSpeciesState s) cell m ν contactParticipation hcan

theorem waterSynthesisTransportRateSlot_zero_of_not_canApply
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (hcan : ¬ waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    waterSynthesisTransportRateSlot s cell m ν contactParticipation = 0 := by
  unfold waterSynthesisTransportRateSlot
  exact ReactionGate.phaseTransportRateSlot_zero_of_not_canApply
    waterSynthesisGate (registerOfSpeciesState s) cell m ν contactParticipation hcan

theorem waterSynthesisTransport_preserves_H
    (s : MolecularState)
    (hcan : waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    totalHAtoms (applyWaterGate s) = totalHAtoms s :=
  waterSynthesisGate_apply_preserves_H s hcan

theorem waterSynthesisTransport_preserves_O
    (s : MolecularState)
    (hcan : waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    totalOAtoms (applyWaterGate s) = totalOAtoms s :=
  waterSynthesisGate_apply_preserves_O s hcan

/-- Heat-power readout from a transported reaction rate and molar heat release. -/
noncomputable def reactionHeatPowerSlot (rate heatReleased : ℝ) : ℝ :=
  rate * heatReleased

theorem reactionHeatPowerSlot_zero_of_zero_rate (heatReleased : ℝ) :
    reactionHeatPowerSlot 0 heatReleased = 0 := by
  unfold reactionHeatPowerSlot
  ring

theorem reactionHeatPowerSlot_nonneg
    {rate heatReleased : ℝ} (hr : 0 ≤ rate) (hh : 0 ≤ heatReleased) :
    0 ≤ reactionHeatPowerSlot rate heatReleased := by
  unfold reactionHeatPowerSlot
  exact mul_nonneg hr hh

/-- Water heat-power readout from the transported water synthesis channel. -/
noncomputable def waterSynthesisHeatPowerSlot
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ) : ℝ :=
  reactionHeatPowerSlot
    (waterSynthesisTransportRateSlot s cell m ν contactParticipation)
    waterSynthesisGate.heatReleased_kJmol

theorem waterSynthesisHeatPowerSlot_zero_of_not_canApply
    (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ)
    (hcan : ¬ waterSynthesisGate.canApply (registerOfSpeciesState s)) :
    waterSynthesisHeatPowerSlot s cell m ν contactParticipation = 0 := by
  unfold waterSynthesisHeatPowerSlot
  rw [waterSynthesisTransportRateSlot_zero_of_not_canApply s cell m ν contactParticipation hcan]
  exact reactionHeatPowerSlot_zero_of_zero_rate _

/-! ## Worked finite water-synthesis example -/

/-- Minimal finite register for the structural water gate: two H, one O, no H₂O. -/
def waterSynthesisStoichState : MolecularState
  | .H => 2
  | .O => 1
  | .H2O => 0

theorem waterSynthesisStoichState_canApply :
    waterSynthesisGate.canApply (registerOfSpeciesState waterSynthesisStoichState) := by
  unfold ReactionGate.canApply
  intro i
  fin_cases i <;>
    simp [waterSynthesisGate, registerOfSpeciesState, waterSynthesisStoichState, fin3ToSpecies]

/-- The enabled finite water gate gives exactly the diffusion-limited phase contact rate. -/
theorem waterSynthesisStoichTransportRate_eq_phaseContact
    (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ) :
    waterSynthesisTransportRateSlot waterSynthesisStoichState cell m ν contactParticipation =
      phaseDiffusionContactRateSlot cell m ν contactParticipation :=
  waterSynthesisTransportRateSlot_eq_of_canApply waterSynthesisStoichState cell m ν
    contactParticipation waterSynthesisStoichState_canApply

/-- Applying the minimal water gate produces one H₂O molecule. -/
theorem waterSynthesisStoichState_produces_one_water :
    applyWaterGate waterSynthesisStoichState .H2O = 1 := by
  unfold applyWaterGate waterSynthesisStoichState waterSynthesisGate speciesToFin3
  norm_num

/-- The worked finite state still preserves H atoms under the balanced gate. -/
theorem waterSynthesisStoichState_preserves_H :
    totalHAtoms (applyWaterGate waterSynthesisStoichState) =
      totalHAtoms waterSynthesisStoichState :=
  waterSynthesisTransport_preserves_H waterSynthesisStoichState
    waterSynthesisStoichState_canApply

/-- The worked finite state still preserves O atoms under the balanced gate. -/
theorem waterSynthesisStoichState_preserves_O :
    totalOAtoms (applyWaterGate waterSynthesisStoichState) =
      totalOAtoms waterSynthesisStoichState :=
  waterSynthesisTransport_preserves_O waterSynthesisStoichState
    waterSynthesisStoichState_canApply

/-- Reaction transport bridge bundle for chemistry consumers. -/
structure MolecularReactionTransportClosure : Prop where
  unavailable_rate_zero :
    ∀ {n k : ℕ} (g : ReactionGate n k) (s : MolecularRegister k)
      (D numberDensity contactParticipation : ℝ),
      ¬ g.canApply s →
        g.transportRateSlot s D numberDensity contactParticipation = 0
  enabled_phase_rate :
    ∀ {n k : ℕ} (g : ReactionGate n k) (s : MolecularRegister k)
      (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ),
      g.canApply s →
        g.phaseTransportRateSlot s cell m ν contactParticipation =
          phaseDiffusionContactRateSlot cell m ν contactParticipation
  balanced_transport_preserves_elements :
    ∀ {n k : ℕ} (g : ReactionGate n k) (s : MolecularRegister k),
      g.canApply s → g.isElementBalanced →
        ∀ e : Fin n,
          totalElementAtoms g.atomsPerSpecies (g.apply s) e =
            totalElementAtoms g.atomsPerSpecies s e
  water_preserves_H :
    ∀ s : MolecularState,
      waterSynthesisGate.canApply (registerOfSpeciesState s) →
        totalHAtoms (applyWaterGate s) = totalHAtoms s
  water_preserves_O :
    ∀ s : MolecularState,
      waterSynthesisGate.canApply (registerOfSpeciesState s) →
        totalOAtoms (applyWaterGate s) = totalOAtoms s
  water_heat_zero_unavailable :
    ∀ (s : MolecularState) (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ),
      ¬ waterSynthesisGate.canApply (registerOfSpeciesState s) →
        waterSynthesisHeatPowerSlot s cell m ν contactParticipation = 0
  worked_water_rate :
    ∀ (cell : PhaseUnitCell) (m : ℕ) (ν contactParticipation : ℝ),
      waterSynthesisTransportRateSlot waterSynthesisStoichState cell m ν contactParticipation =
        phaseDiffusionContactRateSlot cell m ν contactParticipation

/-- The reaction transport bridge is discharged from reaction gates plus molecular transport. -/
theorem molecular_reaction_transport_closure : MolecularReactionTransportClosure where
  unavailable_rate_zero := fun g s D numberDensity contactParticipation hcan =>
    ReactionGate.transportRateSlot_zero_of_not_canApply g s D numberDensity contactParticipation hcan
  enabled_phase_rate := fun g s cell m ν contactParticipation hcan =>
    ReactionGate.phaseTransportRateSlot_eq_of_canApply g s cell m ν contactParticipation hcan
  balanced_transport_preserves_elements := fun g s hcan hbal e =>
    ReactionGate.apply_preserves_totalElementAtoms_of_transport_enabled g s hcan hbal e
  water_preserves_H := waterSynthesisTransport_preserves_H
  water_preserves_O := waterSynthesisTransport_preserves_O
  water_heat_zero_unavailable := waterSynthesisHeatPowerSlot_zero_of_not_canApply
  worked_water_rate := waterSynthesisStoichTransportRate_eq_phaseContact

end

end Hqiv.QuantumChemistry
