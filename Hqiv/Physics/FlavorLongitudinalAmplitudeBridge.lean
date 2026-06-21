import Hqiv.Physics.FlavorDifferentialReadout
import Hqiv.Physics.PatchScatteringUnitarity
import Hqiv.Physics.ReadoutGaugeSeed
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric
import Mathlib.Data.Real.Basic

/-!
# Longitudinal / inertia correction to rare-decay and 2→2 amplitudes

Shows how the O-Maxwell phase-gradient (longitudinal) channel and the HQIV
inertia screen modify a rare-decay branching slot and a patch 2→2 cross section
by the same discrete monogamy coefficient `γ`.
-/

namespace Hqiv.Physics

open Hqiv

/-- Phase-gradient magnitude slot at lock-in shell (O-Maxwell imprint increment). -/
noncomputable def flavorPhaseGradientLockin : ℝ :=
  abs (imprintWeightedReadoutPhase referenceM)

/-- Inertia screen factor `f(a,φ) = (H/H₀)^α` at unit scale factor. -/
noncomputable def flavorInertiaScreenUnity : ℝ := 1 ^ alpha

theorem flavorInertiaScreenUnity_eq_one : flavorInertiaScreenUnity = 1 := by
  simp [flavorInertiaScreenUnity, alpha_eq_3_5]

/-- Longitudinal correction to rare-decay slot: monogamy × phase gradient. -/
noncomputable def rareDecayLongitudinalCorrection (ch : RareDecayChannel) : ℝ :=
  1 + gamma_HQIV * flavorPhaseGradientLockin * rareDecayBranchingSlot ch

theorem rareDecayLongitudinalCorrection_K_pos :
    0 < rareDecayLongitudinalCorrection .KToPiNuNu := by
  unfold rareDecayLongitudinalCorrection
  have h := rareDecayBranchingSlot_K_pos
  have hphase : 0 ≤ flavorPhaseGradientLockin := abs_nonneg _
  have hg : 0 < gamma_HQIV := by rw [gamma_HQIV, alpha_eq_3_5]; norm_num
  unfold flavorPhaseGradientLockin
  have hterm : 0 ≤ gamma_HQIV * abs (imprintWeightedReadoutPhase referenceM) *
      rareDecayBranchingSlot .KToPiNuNu := by positivity
  linarith [hterm]

theorem rareDecayLongitudinalCorrection_K_eq :
    rareDecayLongitudinalCorrection .KToPiNuNu =
      1 + gamma_HQIV * flavorPhaseGradientLockin * rareDecayBranchingSlot .KToPiNuNu := rfl

/-- Longitudinal correction to patch 2→2 cross section at Mandelstam s. -/
noncomputable def patchCrossSectionLongitudinalCorrection (s : ℝ) : ℝ :=
  1 + gamma_HQIV * flavorPhaseGradientLockin * patchCrossSection2to2 s

theorem patchCrossSectionLongitudinalCorrection_pos (s : ℝ) (hs : 0 < s) :
    0 < patchCrossSectionLongitudinalCorrection s := by
  unfold patchCrossSectionLongitudinalCorrection
  have hc := patchCrossSection2to2_pos s hs
  have hphase : 0 ≤ flavorPhaseGradientLockin := abs_nonneg _
  have hg : 0 < gamma_HQIV := by rw [gamma_HQIV, alpha_eq_3_5]; norm_num
  unfold flavorPhaseGradientLockin
  have hterm : 0 ≤ gamma_HQIV * abs (imprintWeightedReadoutPhase referenceM) * patchCrossSection2to2 s := by
    positivity
  linarith [hterm]

structure FlavorLongitudinalAmplitudeCertificate where
  inertia_unity : flavorInertiaScreenUnity = 1
  rare_k_pos : 0 < rareDecayLongitudinalCorrection .KToPiNuNu
  cross_pos : ∀ s, 0 < s → 0 < patchCrossSectionLongitudinalCorrection s

def flavorLongitudinalAmplitudeCertificate_holds : FlavorLongitudinalAmplitudeCertificate where
  inertia_unity := flavorInertiaScreenUnity_eq_one
  rare_k_pos := rareDecayLongitudinalCorrection_K_pos
  cross_pos := patchCrossSectionLongitudinalCorrection_pos

end Hqiv.Physics
