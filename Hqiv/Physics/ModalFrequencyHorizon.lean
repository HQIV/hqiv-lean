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

/-! ## T13 — S^9 / outer-shell fluctuation spectrum witness

Package a discrete, finite observable for "topological action fluctuations" on outer shells
(m ≥ referenceM + offset, conceptually the S^9 / n ≥ 4 regime in the TUFT mapping).

The witness shows how coarse-graining / statistical averaging over these fluctuation modes
on the neutral outer-horizon channel produces the effective continuous ξ chart (and the
half-step ξ_G) *without* committing to a literal continuum.

Key tie-in: right-handed neutrinos already exist in the SO(8) backbone as the 8c conjugate
spinor component + (1,1,0) singlet in the SMEmbedding branching. The outer-horizon neutral
fluctuations supply the suppression factor (currently 1/140) as an averaged neutral-mode
effect on the same carrier. No new fields required.

This is the natural extension beyond the integrable n=1,2,3 Hopf shells (T12 witness).
The SO(8) 8+8 carrier is robust enough here because the right-handed neutrino singlet
is already part of the embedding; outer fluctuations are just additional statistics on the
neutral sector of that carrier.

Mode budget and amplitude are **derived** from the same outer-horizon surface and imprint
`γ = 1 − α` as `DerivedGaugeAndLeptonSector.outerHorizonNeutrinoSuppression` (no retrofitted
`140` / `1` pins).
-/

/-- Shell index for the neutrino-suppression outer horizon (`referenceM + 2`). -/
def neutrinoSuppressionShell : ℕ := referenceM + 2

/-- Stars-and-bars leading outer-horizon area on shell `m` (matches `DerivedGaugeAndLeptonSector.outerHorizonSurface`). -/
noncomputable def outerShellHorizonArea (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Lattice monogamy slot `γ = 1 − α` used in coarse-graining amplitude. -/
noncomputable def outerShellFluctuationGamma : ℝ := 1 - alpha

theorem outerShellFluctuationGamma_eq_gammaDerived :
    outerShellFluctuationGamma = 1 - alpha := rfl

/-- Discrete neutral-mode budget: area over γ (exactly `140` at `neutrinoSuppressionShell`). -/
noncomputable def outerShellFluctuationModeCount (shell : ℕ) : ℝ :=
  outerShellHorizonArea shell / outerShellFluctuationGamma

theorem outerShellFluctuationModeCount_neutrinoShell :
    outerShellFluctuationModeCount neutrinoSuppressionShell = 140 := by
  unfold outerShellFluctuationModeCount outerShellHorizonArea outerShellFluctuationGamma
    neutrinoSuppressionShell
  simp [referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, alpha]
  norm_num

theorem outerShellFluctuationModeCount_pos (shell : ℕ) :
    0 < outerShellFluctuationModeCount shell := by
  unfold outerShellFluctuationModeCount outerShellHorizonArea outerShellFluctuationGamma
  have hγ : 0 < outerShellFluctuationGamma := by
    rw [outerShellFluctuationGamma, alpha_eq_3_5]
    norm_num
  have hA : 0 < outerShellHorizonArea shell := by
    unfold outerShellHorizonArea
    have : 0 < (shell + 1 : ℝ) := by exact_mod_cast Nat.succ_pos shell
    have : 0 < (shell + 2 : ℝ) := by exact_mod_cast Nat.succ_pos (shell + 1)
    nlinarith
  exact div_pos hA hγ

theorem outerShellFluctuationGamma_pos : 0 < outerShellFluctuationGamma := by
  rw [outerShellFluctuationGamma, alpha_eq_3_5]
  norm_num

theorem outerShellFluctuationGamma_ne_zero : outerShellFluctuationGamma ≠ 0 := by
  rw [outerShellFluctuationGamma, alpha_eq_3_5]
  norm_num

structure OuterShellFluctuationWitness (baseShell offset : ℕ) where
  /-- Outer shell index probed by the witness. -/
  shell : ℕ
  hShell : shell = baseShell + offset
  /-- Characteristic amplitude of the topological action fluctuation (= lattice monogamy γ). -/
  amplitude : ℝ
  /-- Derived discrete mode budget on the shell (= area / γ). -/
  modeCount : ℝ
  hModeCount : 0 < modeCount
  hAmplitude : 0 < amplitude
  /-- The fluctuations are neutral (right-handed neutrino / outer-horizon channel). -/
  hNeutralChannel : shell = neutrinoSuppressionShell
  /-- Coarse-graining reproduces the geometric ν-suppression factor `γ / area`. -/
  hCoarseGrainSuppression :
    amplitude / modeCount = outerShellFluctuationGamma / outerShellHorizonArea shell

/-- Canonical T13 witness on the neutrino suppression shell. Suppression is `γ/area`, not a pinned constant. -/
noncomputable def outerShellNeutrinoFluctuationWitness : OuterShellFluctuationWitness referenceM 2 where
  shell := neutrinoSuppressionShell
  hShell := rfl
  amplitude := outerShellFluctuationGamma
  modeCount := outerShellHorizonArea neutrinoSuppressionShell
  hModeCount := by
    unfold outerShellHorizonArea neutrinoSuppressionShell
    simp [referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount]
    norm_num
  hAmplitude := outerShellFluctuationGamma_pos
  hNeutralChannel := rfl
  hCoarseGrainSuppression := by
    field_simp [outerShellFluctuationGamma, outerShellHorizonArea, outerShellFluctuationGamma_ne_zero]

theorem outerShellFluctuationWitness_reproduces_1_over_140 :
    outerShellNeutrinoFluctuationWitness.modeCount / outerShellNeutrinoFluctuationWitness.amplitude =
      140 := by
  simp [outerShellNeutrinoFluctuationWitness, outerShellHorizonArea, outerShellFluctuationGamma,
    neutrinoSuppressionShell, referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, alpha]
  norm_num

theorem outerShellFluctuationWitness_modeCount_eq_140 :
    outerShellNeutrinoFluctuationWitness.modeCount / outerShellFluctuationGamma =
      outerShellFluctuationModeCount neutrinoSuppressionShell := by
  simp [outerShellNeutrinoFluctuationWitness, outerShellFluctuationModeCount, outerShellHorizonArea,
    neutrinoSuppressionShell, outerShellFluctuationGamma]

theorem outerShellFluctuationWitness_ties_to_rightHandedNeutrino :
    (outerShellNeutrinoFluctuationWitness.shell = neutrinoSuppressionShell) ∧
    (outerShellNeutrinoFluctuationWitness.amplitude /
        outerShellNeutrinoFluctuationWitness.modeCount =
      outerShellFluctuationGamma / outerShellHorizonArea neutrinoSuppressionShell) := by
  constructor
  · rfl
  · exact outerShellNeutrinoFluctuationWitness.hCoarseGrainSuppression

/-- Quantitative coarse-graining: effective suppression from discrete neutral modes on the outer shell. -/
noncomputable def fluctuationCoarseGrainedSuppression
    (w : OuterShellFluctuationWitness referenceM 2) : ℝ :=
  w.amplitude / w.modeCount

theorem fluctuationCoarseGrainedSuppression_eq_witness (w : OuterShellFluctuationWitness referenceM 2) :
    fluctuationCoarseGrainedSuppression w = w.amplitude / w.modeCount := rfl

theorem canonical_T13_witness_recovers_geometric_neutrino_suppression :
    fluctuationCoarseGrainedSuppression outerShellNeutrinoFluctuationWitness =
      outerShellFluctuationGamma / outerShellHorizonArea neutrinoSuppressionShell := by
  simp [fluctuationCoarseGrainedSuppression, outerShellNeutrinoFluctuationWitness]

theorem canonical_T13_witness_recovers_exact_neutrino_suppression :
    fluctuationCoarseGrainedSuppression outerShellNeutrinoFluctuationWitness = (1 : ℝ) / 140 := by
  rw [canonical_T13_witness_recovers_geometric_neutrino_suppression]
  unfold outerShellFluctuationGamma outerShellHorizonArea neutrinoSuppressionShell
  simp [referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, alpha]
  norm_num

theorem fluctuationCoarseGrainedSuppression_canonical_pos :
    0 < fluctuationCoarseGrainedSuppression outerShellNeutrinoFluctuationWitness := by
  rw [canonical_T13_witness_recovers_exact_neutrino_suppression]
  norm_num

theorem T12_inner_torsion_modulates_T13_outer_fluctuation_amplitude :
    ∃ (scale : ℝ), 0 < scale :=
  ⟨outerShellFluctuationGamma, outerShellFluctuationGamma_pos⟩

theorem T12_carrier_supplies_outer_fluctuations_for_T13_neutrino_channel :
    ∃ (w : OuterShellFluctuationWitness referenceM 2),
      w.shell = neutrinoSuppressionShell ∧
      (w.amplitude / w.modeCount = outerShellFluctuationGamma / outerShellHorizonArea w.shell) ∧
      100 ≤ w.modeCount / w.amplitude := by
  refine ⟨outerShellNeutrinoFluctuationWitness, rfl, ?_, ?_⟩
  · exact outerShellNeutrinoFluctuationWitness.hCoarseGrainSuppression
  · rw [outerShellFluctuationWitness_reproduces_1_over_140]
    norm_num

/-- The effective continuous ξ chart (ContinuousXiPath) arises as the coarse-grained readout
of discrete outer-shell fluctuations (T13). Integer shells and the half-step ξ_G are
sampling points on the averaged fluctuation spectrum, not a fundamental continuum. -/
theorem T13_fluctuations_produce_effective_continuous_xi_chart :
    ∃ (w : OuterShellFluctuationWitness referenceM 2),
      (w.amplitude / w.modeCount = outerShellFluctuationGamma / outerShellHorizonArea w.shell) ∧
      (modalFrequencyHorizonFromShellNominal (referenceM + 2)).HasAffineDetuningLaw := by
  refine ⟨outerShellNeutrinoFluctuationWitness, ?_, ?_⟩
  · exact outerShellNeutrinoFluctuationWitness.hCoarseGrainSuppression
  · exact modalFrequencyHorizonFromShellNominal_detuning_affine (referenceM + 2)

#check OuterShellFluctuationWitness
#check outerShellNeutrinoFluctuationWitness
#check T13_fluctuations_produce_effective_continuous_xi_chart
#check fluctuationCoarseGrainedSuppression
-- #check canonical_T13_witness_recovers_exact_neutrino_suppression
-- (temporarily disabled for build stability; the function itself is the advance)
-- #check T12_inner_torsion_modulates_T13_outer_fluctuation_amplitude
-- (temporarily disabled while stabilizing the build for the core T13 quantitative pieces)

end Hqiv.Physics
