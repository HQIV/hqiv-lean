import Hqiv.Physics.FanoDetuningFirstOrder
import Hqiv.Physics.FanoOmaxwellSpectrum
import Hqiv.Physics.ModalFrequencyHorizon

namespace Hqiv.Physics

open Hqiv

/-!
# Eight-channel O-Maxwell action → Fano 1-jet → detuned shell (proved chain)

This module closes the **straightforward** emergence packaging requested for ROI/action work:

1. `FanoOmaxwellSpectralMode` on the 8×8 `algebraicMaxwellParentGenerator` ladder with Fano-line
   projection (`fanoLineSelector`, `phaseLiftDeltaMatrix`);
2. scalar mode strength `projectedStrength` and its shell increment;
3. `spectralFanoRindler1Jet` as the **linearized** detuning 1-jet
   `1 + (3γ/2)·Δ(strength)`;
4. `omaxwellFanoDetuning1Jet` on the canonical EM/lepton line and `detunedShellSurface` as
   `shellSurface / jet`;
5. `ModalFrequencyHorizonFromFanoLine` readout agreement.

The **deeper** open step (full mode selection / eigen-shell dynamics replacing the affine scaffold)
remains as in `FanoDetuningFirstOrder`; here we prove the **current** spectral/action identification
end-to-end.
-/

/-! ## Projected strength increment along the shell ladder -/

/-- Shell increment of the Fano-projected O-Maxwell mode strength on line `L`. -/
noncomputable def omaxwellProjectedStrengthIncrement (L : FanoLine) (m : ℕ) : ℝ :=
  let mode : FanoOmaxwellSpectralMode := ⟨L, m⟩
  let base : FanoOmaxwellSpectralMode := ⟨L, 0⟩
  mode.projectedStrength - base.projectedStrength

theorem omaxwellProjectedStrengthIncrement_eq_phaseLift_sub (L : FanoLine) (m : ℕ) :
    omaxwellProjectedStrengthIncrement L m =
      Hqiv.Algebra.phaseLiftCoeff m - Hqiv.Algebra.phaseLiftCoeff 0 := by
  unfold omaxwellProjectedStrengthIncrement FanoOmaxwellSpectralMode.projectedStrength
  have hnorm : spectralProjectionNormalization L = 1 := spectralProjectionNormalization_eq_one L
  simp [hnorm]

theorem omaxwellProjectedStrengthIncrement_eq_one_third_shell (L : FanoLine) (m : ℕ) :
    omaxwellProjectedStrengthIncrement L m = (1 / 3 : ℝ) * (m : ℝ) := by
  rw [omaxwellProjectedStrengthIncrement_eq_phaseLift_sub]
  unfold Hqiv.Algebra.phaseLiftCoeff
  rw [phi_of_shell_closed_form, phi_of_shell_closed_form (m := 0), phiTemperatureCoeff_eq_two]
  ring_nf

/-- Quadratic `Δ` sector energy of the projected mode (trace normalization `= 2`). -/
noncomputable def omaxwellFanoQuadraticSectorEnergy (L : FanoLine) (m : ℕ) : ℝ :=
  phaseLiftDeltaQuadraticTrace * (FanoOmaxwellSpectralMode.projectedStrength ⟨L, m⟩) ^ 2

theorem omaxwellFanoQuadraticSectorEnergy_eq_two_strength_sq (L : FanoLine) (m : ℕ) :
    omaxwellFanoQuadraticSectorEnergy L m =
      2 * (FanoOmaxwellSpectralMode.projectedStrength ⟨L, m⟩) ^ 2 := by
  unfold omaxwellFanoQuadraticSectorEnergy
  rw [phaseLiftDeltaQuadraticTrace_eq_two]

/-! ## Action 1-jet = spectral Fano Rindler jet -/

/-- Detuning 1-jet induced by linearizing the projected O-Maxwell strength along shells. -/
noncomputable def omaxwellActionDetuning1Jet (L : FanoLine) (m : ℕ) : ℝ :=
  1 + ((3 * gamma_HQIV) / 2) * omaxwellProjectedStrengthIncrement L m

theorem omaxwellActionDetuning1Jet_eq_spectralFanoRindler1Jet (L : FanoLine) (m : ℕ) :
    omaxwellActionDetuning1Jet L m = spectralFanoRindler1Jet L m := by
  unfold omaxwellActionDetuning1Jet spectralFanoRindler1Jet omaxwellProjectedStrengthIncrement
    FanoOmaxwellSpectralMode.projectedStrength
  have hnorm : spectralProjectionNormalization L = 1 := spectralProjectionNormalization_eq_one L
  simp only [hnorm]

theorem omaxwellActionDetuning1Jet_eq_rindler (L : FanoLine) (m : ℕ) :
    omaxwellActionDetuning1Jet L m = rindlerDetuningShared (m : ℝ) := by
  rw [omaxwellActionDetuning1Jet_eq_spectralFanoRindler1Jet, spectralFanoRindler1Jet_eq_rindler]

theorem omaxwellActionDetuning1Jet_canonical_eq_hook (m : ℕ) :
    omaxwellActionDetuning1Jet (FanoLine.ofTag canonicalSpectralTag) m =
      omaxwellFanoDetuning1Jet m := by
  rw [omaxwellActionDetuning1Jet_eq_spectralFanoRindler1Jet, omaxwellFanoDetuning1Jet]

theorem detunedShellSurface_eq_shell_over_actionJet_canonical (m : ℕ) :
    detunedShellSurface m =
      shellSurface m / omaxwellActionDetuning1Jet (FanoLine.ofTag canonicalSpectralTag) m := by
  rw [omaxwellActionDetuning1Jet_canonical_eq_hook]
  exact detunedShellSurface_eq_shell_div_omaxwellFanoDetuning1Jet m

/-! ## Modal-frequency readout bundle -/

/-- Eight-channel Fano spectral source packaged for horizon/mass consumers. -/
structure EightChannelFanoDetuningEmergence where
  line : FanoLine
  omega : ℝ
  omega_pos : 0 < omega
  detuning_eq_action : ∀ m, spectralFanoRindler1Jet line m = omaxwellActionDetuning1Jet line m
  detuned_eq_modal : ∀ m,
    detunedShellSurface m =
      (modalFrequencyHorizonFromFanoLine line omega omega_pos).detunedSurfaceReadout m

/-- Canonical emergence witness at the EM/lepton Fano line. -/
noncomputable def eightChannelFanoDetuningEmergenceCanonical (ω : ℝ) (hω : 0 < ω) :
    EightChannelFanoDetuningEmergence where
  line := FanoLine.ofTag canonicalSpectralTag
  omega := ω
  omega_pos := hω
  detuning_eq_action := fun m =>
    (omaxwellActionDetuning1Jet_eq_spectralFanoRindler1Jet _ m).symm
  detuned_eq_modal := fun m =>
    (detunedSurfaceReadout_fromFanoLine (FanoLine.ofTag canonicalSpectralTag) ω hω m).symm

theorem eightChannel_detunedShellSurface_emerges (ω : ℝ) (hω : 0 < ω) (m : ℕ) :
    detunedShellSurface m =
      shellSurface m /
        omaxwellActionDetuning1Jet (FanoLine.ofTag canonicalSpectralTag) m ∧
      detunedShellSurface m =
        ModalFrequencyHorizonSpec.detunedSurfaceReadout
          (modalFrequencyHorizonFromFanoLine (FanoLine.ofTag canonicalSpectralTag) ω hω) m := by
  constructor
  · exact detunedShellSurface_eq_shell_over_actionJet_canonical m
  · exact (eightChannelFanoDetuningEmergenceCanonical ω hω).detuned_eq_modal m

theorem geometricResonanceStep_eq_modal_geometricStep_canonical
    (ω : ℝ) (hω : 0 < ω) (m_from m_to : ℕ) :
    geometricResonanceStep m_from m_to =
      ModalFrequencyHorizonSpec.geometricStepReadout
        (modalFrequencyHorizonFromFanoLine (FanoLine.ofTag canonicalSpectralTag) ω hω)
        m_from m_to := by
  rw [geometricStepReadout_fromFanoLine, geometricResonanceStep]

end Hqiv.Physics
