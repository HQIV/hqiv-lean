import Hqiv.Physics.ComptonHorizonPhase
import Hqiv.Physics.SurfaceWaveSelfClock
import Hqiv.Physics.FanoOmaxwellSpectrum
import Hqiv.Physics.FanoResonance

namespace Hqiv.Physics

open Hqiv

/-!
# Modal frequency / interaction-horizon interface

This module introduces a **modal-first** interface for the current HQIV story:

- a nominal modal angular frequency,
- an interaction horizon quarter-period,
- a detuning 1-jet map used by downstream mass/readout modules.

The layer is intentionally lightweight: existing `ℕ`-indexed constructions stay intact as **evaluation
charts** for those readouts, while upstream narratives can be phrased in terms of modal frequency and
horizon period data first.
-/

/-- Shell-agnostic modal specification used by frequency/horizon-first consumers. -/
structure ModalFrequencyHorizonSpec where
  nominalOmega : ℝ
  interactionQuarterPeriod : ℝ
  quarterPhase_eq_horizonQuarter :
    nominalOmega * interactionQuarterPeriod = Hqiv.horizonQuarterPeriod
  detuning1Jet : ℕ → ℝ
  sectorLine? : Option FanoLine := none

/-- Derived half-period from the interaction quarter-period. -/
def ModalFrequencyHorizonSpec.interactionHalfPeriod (spec : ModalFrequencyHorizonSpec) : ℝ :=
  2 * spec.interactionQuarterPeriod

/-- Derived full period from the interaction quarter-period. -/
def ModalFrequencyHorizonSpec.interactionFullPeriod (spec : ModalFrequencyHorizonSpec) : ℝ :=
  4 * spec.interactionQuarterPeriod

/-- Compatibility property: the detuning 1-jet follows the affine HQIV law at every readout index. -/
def ModalFrequencyHorizonSpec.HasAffineDetuningLaw (spec : ModalFrequencyHorizonSpec) : Prop :=
  ∀ m : ℕ, spec.detuning1Jet m = 1 + (gamma_HQIV / 2) * (m : ℝ)

/-- Downstream horizon-area readout induced by a modal-frequency specification. -/
noncomputable def ModalFrequencyHorizonSpec.detunedSurfaceReadout
    (spec : ModalFrequencyHorizonSpec) (m : ℕ) : ℝ :=
  shellSurface m / spec.detuning1Jet m

/-- Geometric step readout induced by a modal-frequency specification. -/
noncomputable def ModalFrequencyHorizonSpec.geometricStepReadout
    (spec : ModalFrequencyHorizonSpec) (m_from m_to : ℕ) : ℝ :=
  spec.detunedSurfaceReadout m_from / spec.detunedSurfaceReadout m_to

lemma comptonAngularFrequency_pos (m : ℕ) : 0 < comptonAngularFrequency m := by
  unfold comptonAngularFrequency
  positivity

/--
Canonical frequency/horizon interface read from the shell-nominal self-clock frequency.

This keeps shells as downstream readout while exposing the horizon quarter-period relation directly.
-/
noncomputable def modalFrequencyHorizonFromShellNominal (m : ℕ) : ModalFrequencyHorizonSpec where
  nominalOmega := comptonAngularFrequency m
  interactionQuarterPeriod := deltaTQuarter (comptonAngularFrequency m) (comptonAngularFrequency_pos m)
  quarterPhase_eq_horizonQuarter := by
    simpa using omega_deltaTQuarter_eq_horizonQuarterPeriod
      (comptonAngularFrequency m) (comptonAngularFrequency_pos m)
  detuning1Jet := fun k => rindlerDetuningShared (k : ℝ)

theorem modalFrequencyHorizonFromShellNominal_detuning_affine (m : ℕ) :
    (modalFrequencyHorizonFromShellNominal m).HasAffineDetuningLaw := by
  intro k
  change rindlerDetuningShared (k : ℝ) = 1 + (gamma_HQIV / 2) * (k : ℝ)
  unfold rindlerDetuningShared c_rindler_shared
  ring

theorem detunedSurfaceReadout_fromShellNominal (m shell : ℕ) :
    (modalFrequencyHorizonFromShellNominal m).detunedSurfaceReadout shell = detunedShellSurface shell := by
  unfold ModalFrequencyHorizonSpec.detunedSurfaceReadout modalFrequencyHorizonFromShellNominal
  rfl

theorem geometricStepReadout_fromShellNominal (m shellFrom shellTo : ℕ) :
    (modalFrequencyHorizonFromShellNominal m).geometricStepReadout shellFrom shellTo =
      geometricResonanceStep shellFrom shellTo := by
  unfold ModalFrequencyHorizonSpec.geometricStepReadout geometricResonanceStep
  rw [detunedSurfaceReadout_fromShellNominal, detunedSurfaceReadout_fromShellNominal]

/--
Frequency/horizon interface sourced from a chosen Fano line.

The quarter-period relation is still purely harmonic (`ω·Δt_quarter = horizonQuarterPeriod`), while the
detuning 1-jet is taken from the direct O-Maxwell/Fano spectral source.
-/
noncomputable def modalFrequencyHorizonFromFanoLine
    (L : FanoLine) (ω : ℝ) (hω : 0 < ω) : ModalFrequencyHorizonSpec where
  nominalOmega := ω
  interactionQuarterPeriod := deltaTQuarter ω hω
  quarterPhase_eq_horizonQuarter := omega_deltaTQuarter_eq_horizonQuarterPeriod ω hω
  detuning1Jet := spectralFanoRindler1Jet L
  sectorLine? := some L

theorem modalFrequencyHorizonFromFanoLine_detuning_affine
    (L : FanoLine) (ω : ℝ) (hω : 0 < ω) :
    (modalFrequencyHorizonFromFanoLine L ω hω).HasAffineDetuningLaw := by
  intro m
  change spectralFanoRindler1Jet L m = 1 + (gamma_HQIV / 2) * (m : ℝ)
  simpa using spectralFanoRindler1Jet_eq_one_plus_half_gamma L m

theorem detunedSurfaceReadout_fromFanoLine
    (L : FanoLine) (ω : ℝ) (hω : 0 < ω) (m : ℕ) :
    (modalFrequencyHorizonFromFanoLine L ω hω).detunedSurfaceReadout m = detunedShellSurface m := by
  unfold ModalFrequencyHorizonSpec.detunedSurfaceReadout modalFrequencyHorizonFromFanoLine
  simp [spectralFanoRindler1Jet_eq_rindler]
  rfl

theorem geometricStepReadout_fromFanoLine
    (L : FanoLine) (ω : ℝ) (hω : 0 < ω) (m_from m_to : ℕ) :
    (modalFrequencyHorizonFromFanoLine L ω hω).geometricStepReadout m_from m_to =
      geometricResonanceStep m_from m_to := by
  unfold ModalFrequencyHorizonSpec.geometricStepReadout geometricResonanceStep
  rw [detunedSurfaceReadout_fromFanoLine, detunedSurfaceReadout_fromFanoLine]

/--
Compton-parameter constructor (`m, ħ, c`) for the same interface.

No empirical claim is made here: this is the algebraic quarter-period identification packaged as a
modal-frequency specification.
-/
noncomputable def modalFrequencyHorizonFromCompton
    (m ħ c : ℝ) (hm : 0 < m) (hħ : 0 < ħ) (hc : 0 < c) : ModalFrequencyHorizonSpec where
  nominalOmega := omegaCompton (restEnergy m c) ħ (ne_of_gt hħ)
  interactionQuarterPeriod := deltaTQuarter
    (omegaCompton (restEnergy m c) ħ (ne_of_gt hħ))
    (omegaCompton_pos_of_rest m ħ c hm hħ hc)
  quarterPhase_eq_horizonQuarter := by
    simpa using omega_deltaTQuarter_eq_horizonQuarterPeriod
      (omegaCompton (restEnergy m c) ħ (ne_of_gt hħ))
      (omegaCompton_pos_of_rest m ħ c hm hħ hc)
  detuning1Jet := fun k => rindlerDetuningShared (k : ℝ)

theorem modalFrequencyHorizonFromCompton_detuning_affine
    (m ħ c : ℝ) (hm : 0 < m) (hħ : 0 < ħ) (hc : 0 < c) :
    (modalFrequencyHorizonFromCompton m ħ c hm hħ hc).HasAffineDetuningLaw := by
  intro k
  change rindlerDetuningShared (k : ℝ) = 1 + (gamma_HQIV / 2) * (k : ℝ)
  unfold rindlerDetuningShared c_rindler_shared
  ring

end Hqiv.Physics
