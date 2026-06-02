import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Physics.QuarterPeriodRelaxation

namespace Hqiv.Physics

open scoped Real

/-!
# Sphere-projected mass transfer (S3/S7 split)

This module adds an explicit Lean place for the research direction:

- spin/charge channels project through `S³`,
- hypercharge channels project through `S⁷`,
- quarks use both channels,
- leptons use only the `S³` channel.

The transfer spec carries explicit `angularMomentum` and `excitation` slots.
-/

noncomputable section

/-- Geometric transfer controls for a standing-wave channel. -/
structure SphereTransferSpec where
  /-- Effective angular momentum index (standing-wave order). -/
  angularMomentum : ℕ
  /-- Excitation level on top of the angular base mode. -/
  excitation : ℕ
  /-- "Now"-slice transfer scale. -/
  lambdaNow : ℝ
  /-- Real-axis angular amplification power. -/
  anglePower : ℕ

/-- Effective spectral index after adding angular momentum, excitation, and pole multiplicity. -/
def effectiveEll (spec : SphereTransferSpec) (poles : ℕ) : ℕ :=
  max 1 (spec.angularMomentum * max 1 poles + spec.excitation)

/-- Angle between a sphere mode and the real axis (modeled by `atan ω`). -/
noncomputable def spherePhaseAngleToRealAxis
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) : ℝ :=
  Real.arctan (spectralModeOmega br (effectiveEll spec poles))

/-- Absolute real-axis projection magnitude for a sphere mode. -/
noncomputable def realAxisProjection
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) : ℝ :=
  |Real.cos (spherePhaseAngleToRealAxis br spec poles)|

/-- Projection floor to avoid singular amplification at exact orthogonality. -/
def realAxisProjectionFloor : ℝ := (1 / (1000000000 : ℝ))

theorem realAxisProjectionFloor_pos : 0 < realAxisProjectionFloor := by
  norm_num [realAxisProjectionFloor]

/-- Clamped real-axis projection used in angular amplification. -/
noncomputable def safeRealAxisProjection
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) : ℝ :=
  max (realAxisProjection br spec poles) realAxisProjectionFloor

theorem safeRealAxisProjection_pos
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) :
    0 < safeRealAxisProjection br spec poles := by
  unfold safeRealAxisProjection
  exact lt_of_lt_of_le realAxisProjectionFloor_pos (le_max_right _ _)

/-- Angular amplification from inverse real-axis projection. -/
noncomputable def angularAmplification
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) : ℝ :=
  (1 / safeRealAxisProjection br spec poles) ^ spec.anglePower

theorem angularAmplification_nonneg
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) :
    0 ≤ angularAmplification br spec poles := by
  unfold angularAmplification
  have hsafe : 0 ≤ safeRealAxisProjection br spec poles := le_of_lt (safeRealAxisProjection_pos br spec poles)
  exact pow_nonneg (one_div_nonneg.2 hsafe) _

/--
Angle-aware complexity threshold used for coordinate-transfer steps.
This is the Lean mirror of the current Python exploration map.
-/
noncomputable def complexityThresholdFromGeometry
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ) : ℝ :=
  let ℓ := effectiveEll spec poles
  1 + spec.lambdaNow * (Real.exp (spectralRelaxationWeight br ℓ) - 1) *
    angularAmplification br spec poles

theorem complexityThresholdFromGeometry_ge_one
    (br : QuarterSpectralBridge) (spec : SphereTransferSpec) (poles : ℕ)
    (hLambda : 0 ≤ spec.lambdaNow) :
    1 ≤ complexityThresholdFromGeometry br spec poles := by
  unfold complexityThresholdFromGeometry
  set ℓ := effectiveEll spec poles
  have hw : 0 ≤ spectralRelaxationWeight br ℓ := spectralRelaxationWeight_nonneg br ℓ
  have hexp : 0 ≤ Real.exp (spectralRelaxationWeight br ℓ) - 1 := by
    have h1 : (1 : ℝ) ≤ Real.exp (spectralRelaxationWeight br ℓ) := by
      have hmono : Real.exp 0 ≤ Real.exp (spectralRelaxationWeight br ℓ) :=
        (Real.exp_le_exp).2 hw
      simpa using hmono
    linarith
  have hang : 0 ≤ angularAmplification br spec poles :=
    angularAmplification_nonneg br spec poles
  have hmul : 0 ≤
      spec.lambdaNow * (Real.exp (spectralRelaxationWeight br ℓ) - 1) *
        angularAmplification br spec poles := by
    exact mul_nonneg (mul_nonneg hLambda hexp) hang
  linarith

/-- `S³` transfer for spin/charge content. -/
noncomputable def s3SpinChargeThreshold (spec : SphereTransferSpec) : ℝ :=
  complexityThresholdFromGeometry .s3 spec 1

/-- `S⁷` transfer for hypercharge content with explicit pole multiplicity. -/
noncomputable def s7HyperchargeThreshold (spec : SphereTransferSpec) (hyperchargePoles : ℕ) : ℝ :=
  complexityThresholdFromGeometry .s7 spec hyperchargePoles

/-- Quark transfer uses both `S³` (spin/charge) and `S⁷` (hypercharge). -/
noncomputable def quarkTransferThreshold (spec : SphereTransferSpec) (hyperchargePoles : ℕ) : ℝ :=
  s3SpinChargeThreshold spec * s7HyperchargeThreshold spec hyperchargePoles

/-- Lepton transfer uses only the `S³` channel (no hypercharge channel factor). -/
noncomputable def leptonTransferThreshold (spec : SphereTransferSpec) : ℝ :=
  s3SpinChargeThreshold spec

theorem leptonTransferThreshold_uses_only_s3 (spec : SphereTransferSpec) :
    leptonTransferThreshold spec = s3SpinChargeThreshold spec := rfl

theorem quarkTransferThreshold_uses_s3_and_s7
    (spec : SphereTransferSpec) (hyperchargePoles : ℕ) :
    quarkTransferThreshold spec hyperchargePoles =
      s3SpinChargeThreshold spec * s7HyperchargeThreshold spec hyperchargePoles := rfl

theorem s3SpinChargeThreshold_ge_one
    (spec : SphereTransferSpec) (hLambda : 0 ≤ spec.lambdaNow) :
    1 ≤ s3SpinChargeThreshold spec :=
  complexityThresholdFromGeometry_ge_one .s3 spec 1 hLambda

theorem s7HyperchargeThreshold_ge_one
    (spec : SphereTransferSpec) (hyperchargePoles : ℕ) (hLambda : 0 ≤ spec.lambdaNow) :
    1 ≤ s7HyperchargeThreshold spec hyperchargePoles :=
  complexityThresholdFromGeometry_ge_one .s7 spec hyperchargePoles hLambda

end

end Hqiv.Physics
