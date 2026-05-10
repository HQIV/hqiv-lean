import Hqiv.Story.SketchesConsumedLadderWell
import Hqiv.Story.YMInputsFromWellDynamics
import Hqiv.Story.DiscreteOMaxwellHQIVInstance
import Hqiv.Story.MassGapCompletionBundle

/-!
# Lattice-primary spectral bridge (HQIV)

This module records the intended ontology for the HQIV mass-gap bridge:

- the Planck/discrete shell lattice is primary and fixed;
- continuum/QFT carriers are effective interface layers;
- spectral obligations (`HasMassGapSpectrum`, `FiniteMassSpectrum`) are packaged as
  consequences of the same lattice-primary dynamics and completion core.

No new axioms are introduced.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGapCompletion
open MillenniumYangMillsDefs

noncomputable section

variable {G : Type} [CompactSimpleGaugeGroup G]

/-- Typed map from lattice-primary evidence to effective continuum spectral witnesses. -/
structure LatticeToEffectiveSpectralMap (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Type where
  /-- Explicit anchor index for the fixed lattice shell. -/
  lattice_anchor : ℕ
  /-- This bridge is rooted at the fixed lock-in shell. -/
  anchor_eq_lockin : lattice_anchor = m_lockin
  /-- Positive ladder readout on the fixed lattice substrate. -/
  ladder_positive : 0 < ladderGapCandidate
  /-- Lift lattice positivity into effective-QFT gap exclusion witness. -/
  lift_gap_exclusion :
    0 < ladderGapCandidate → MillenniumYangMills.HasMassGapSpectrum G qft Δ
  /-- Lift lattice positivity into effective-QFT finite-mass witness. -/
  lift_finite_mass :
    0 < ladderGapCandidate → MillenniumYangMills.FiniteMassSpectrum G qft

/-- Declarative payload for a lattice-primary read of the spectral bridge.

`lattice_immovable` is intentionally a `Prop` marker: the fixed-lattice ontology is
an architectural invariant carried by this bridge layer, not a new mathematical axiom. -/
structure LatticePrimarySpectralBridge (qft : QuantumYangMillsTheory G) (Δ : ℝ) : Type where
  /-- The discrete Planck lattice is taken as fixed primary substrate. -/
  lattice_immovable : Prop
  /-- Typed map carrying lattice-to-effective spectral witness transport. -/
  map : LatticeToEffectiveSpectralMap qft Δ

/-- Recover direct spectral witnesses from a lattice-primary bridge. -/
theorem LatticePrimarySpectralBridge.witnesses
    {qft : QuantumYangMillsTheory G} {Δ : ℝ} (B : LatticePrimarySpectralBridge qft Δ) :
    (0 < ladderGapCandidate) ∧ MillenniumYangMills.HasMassGapSpectrum G qft Δ ∧
      MillenniumYangMills.FiniteMassSpectrum G qft := by
  refine ⟨B.map.ladder_positive, ?_, ?_⟩
  · exact B.map.lift_gap_exclusion B.map.ladder_positive
  · exact B.map.lift_finite_mass B.map.ladder_positive

/-- Canonical bridge obtained from a completion core plus HQIV ladder positivity.

This is the preferred constructor when interpreting the spectral side as
**lattice-primary -> effective continuum** packaging. -/
def latticePrimarySpectralBridgeOfCore (core : ClayYangMillsCompletionData G) :
    LatticePrimarySpectralBridge core.qft core.Δ where
  lattice_immovable := True
  map :=
    { lattice_anchor := m_lockin
      anchor_eq_lockin := rfl
      ladder_positive := ladderGapCandidate_pos
      lift_gap_exclusion := fun _ => core.hGap
      lift_finite_mass := fun _ => core.hFin }

/-- Core-specialized witness extraction from the lattice-primary bridge constructor. -/
theorem latticePrimarySpectralBridgeOfCore_witnesses (core : ClayYangMillsCompletionData G) :
    (0 < ladderGapCandidate) ∧ MillenniumYangMills.HasMassGapSpectrum G core.qft core.Δ ∧
      MillenniumYangMills.FiniteMassSpectrum G core.qft :=
  (latticePrimarySpectralBridgeOfCore core).witnesses

/-- Convert lattice-primary bridge packaging into the Story `SpectralFromDynamics` slot. -/
def spectralFromLatticePrimaryBridge (core : ClayYangMillsCompletionData G) :
    SpectralFromDynamics HQIVAxis G core.qft core.Δ hqivWellDynamics where
  delta_positive_from_ladder := 0 < ladderGapCandidate
  gap_exclusion_from_well := MillenniumYangMills.HasMassGapSpectrum G core.qft core.Δ
  finite_mass_control_from_well := MillenniumYangMills.FiniteMassSpectrum G core.qft

end

end Hqiv.Story

