import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Physics.HomogeneousCurvatureSecondOrder
import Hqiv.ProteinResearch.MiniproteinFoldSpine
import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.QuantumChemistry.DynamicBindingChart

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Macro Ricci flow — contact-network curvature dynamics

Small-molecule readouts stay accurate at dilute ρ because outside ``G_eff`` is unity
at the horizon.  **Larger graphs compound** contact participation along stacked registers
(β i+2 strands, peptide axial slots, linear-chain allotropes): each step carries the
same inward Ricci contraction / outward expansion tug-of-war as ``HqivSpine.Physics.Gravity``,
but on **contact participation** ``η = θ/θ₀`` in the Compton IR window.

This module is the Lean spine for:

* ``scripts/hqiv_curvature_bond_state.py`` (`scale_outside_coupling_for_medium_density`)
* ``scripts/hqiv_homogeneous_curvature_feedback.py`` (``B_hom + δB`` loop)
* ``scripts/hqiv_shell_aware_binding.py`` (electronic compound-error guard)
* ``hqiv_lab/peptide_geometry.py`` (stacked-line outside dress on open β i+2)

**Not claimed:** smooth Perelman Ricci flow on a 3-manifold; this is the **discrete**
``η ↦ η^α`` / ``η ↦ η^(1/α)`` channel on finite contact networks with homogeneous
second-order feedback.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Real

noncomputable section

/-!
## Participation η and medium-density dress
-/

/-- Normalized IR-window participation (``θ/phaseTheta``). -/
noncomputable def contactParticipation (θ : ℝ) : ℝ := contactPhaseParticipation θ

/-- Medium-density scaling for outside couplings ≥ 1: ``1 + (f − 1)·ρ``. -/
noncomputable def scaleOutsideCouplingForMediumDensity (f ρ : ℝ) : ℝ :=
  1 + clampMediumDensity ρ * (f - 1)

theorem scaleOutsideCouplingForMediumDensity_unity (f : ℝ) :
    scaleOutsideCouplingForMediumDensity f 0 = 1 := by
  unfold scaleOutsideCouplingForMediumDensity clampMediumDensity
  simp

theorem scaleOutsideCouplingForMediumDensity_full (f ρ : ℝ) (hρ : ρ = 1) :
    scaleOutsideCouplingForMediumDensity f ρ = f := by
  unfold scaleOutsideCouplingForMediumDensity clampMediumDensity
  simp [hρ]

/-- Outside ``G_eff(θ)`` dressed by bulk medium density ρ (ice reference via phase geometry). -/
noncomputable def outsideContactCouplingAtMediumDensity (θ ρ : ℝ) : ℝ :=
  scaleOutsideCouplingForMediumDensity (outsideContactCoupling θ) ρ

theorem outside_contact_at_medium_dilute (θ : ℝ) :
    outsideContactCouplingAtMediumDensity θ 0 = 1 := by
  unfold outsideContactCouplingAtMediumDensity
  rw [scaleOutsideCouplingForMediumDensity_unity]

theorem outside_contact_at_medium_full (θ ρ : ℝ) (hρ : ρ = 1) :
    outsideContactCouplingAtMediumDensity θ ρ = outsideContactCoupling θ := by
  unfold outsideContactCouplingAtMediumDensity
  rw [scaleOutsideCouplingForMediumDensity_full (outsideContactCoupling θ) ρ hρ]

/-!
## Macro Ricci contraction / expansion on η
-/

/-- **Inward Ricci step** on participation: ``G_eff(η) = η^α``. -/
noncomputable def macroRicciContraction (η : ℝ) : ℝ := G_eff η

/-- **Outward expansion step**: ``η^(1/α)`` (inverse of inward Ricci on the lattice). -/
noncomputable def macroExpansionFlow (η : ℝ) : ℝ := η ^ (1 / alpha)

theorem macro_ricci_contraction_eq_geff (η : ℝ) (hη : 0 ≤ η) :
    macroRicciContraction η = η ^ alpha := by
  unfold macroRicciContraction
  exact G_eff_eq η hη

theorem macro_expansion_flow_eq (η : ℝ) :
    macroExpansionFlow η = η ^ (5 / 3 : ℝ) := by
  unfold macroExpansionFlow
  rw [alpha_eq_3_5]
  norm_num

theorem macro_ricci_contraction_one : macroRicciContraction 1 = 1 := by
  unfold macroRicciContraction
  exact G_eff_one

/-- Interior participation is squeezed between expansion (out) and Ricci contraction (in). -/
theorem macro_tug_of_war_interior {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    macroExpansionFlow η < η ∧ η < macroRicciContraction η := by
  constructor
  · unfold macroExpansionFlow
    have h : η ^ (1 / alpha) < η ^ (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff_of_base_lt_one hη0 hη1).mpr (by rw [alpha_eq_3_5]; norm_num)
    rwa [Real.rpow_one] at h
  · unfold macroRicciContraction
    rw [G_eff_eq η (le_of_lt hη0)]
    have h : η ^ (1 : ℝ) < η ^ alpha :=
      (Real.rpow_lt_rpow_left_iff_of_base_lt_one hη0 hη1).mpr (by rw [alpha_eq_3_5]; norm_num)
    rwa [Real.rpow_one] at h

/-!
## Stacked-line register breathing (open β i+2, axial peptide slots)
-/

/-- Full outside contraction on a stacked in-register contact: ``G_eff(θ/θ₀)``. -/
noncomputable def stackedLineOutsideCurvatureScale (θ : ℝ) : ℝ :=
  outsideContactCoupling θ

theorem stacked_line_scale_eq_outside_coupling (θ : ℝ) :
    stackedLineOutsideCurvatureScale θ = outsideContactCoupling θ := rfl

theorem stacked_line_scale_at_phase_boundary (θ : ℝ) (hθ : θ = phaseTheta) :
    stackedLineOutsideCurvatureScale θ = 1 := by
  unfold stackedLineOutsideCurvatureScale outsideContactCoupling contactPhaseParticipation
  rw [hθ, div_self (ne_of_gt phaseTheta_pos), G_eff_one]

/--
Monogamy γ-channel breathing on stacked lines (sheet i+2 scale uses ``1 + γ/4``):

  ``1 + (γ/2)·(G_eff − 1)``

Full ``G_eff`` over-closes large graphs; the γ/2 channel is the macro Ricci target for
tertiary closure weights (Python ``dress_stacked_line_contact_distance``).
-/
noncomputable def macroRicciStackedLineBreathingScale (θ : ℝ) : ℝ :=
  1 + gamma_HQIV / 2 * (stackedLineOutsideCurvatureScale θ - 1)

theorem macro_ricci_stacked_breathing_at_phase_boundary (θ : ℝ) (hθ : θ = phaseTheta) :
    macroRicciStackedLineBreathingScale θ = 1 := by
  unfold macroRicciStackedLineBreathingScale
  rw [stacked_line_scale_at_phase_boundary θ hθ]
  ring

/-- Alias used by protein folding docs. -/
noncomputable def stackedLineContactBreathingScale (θ : ℝ) : ℝ :=
  macroRicciStackedLineBreathingScale θ

theorem stacked_line_breathing_eq_macro (θ : ℝ) :
    stackedLineContactBreathingScale θ = macroRicciStackedLineBreathingScale θ := rfl

/-- Open-register distance target after one stacked-line breathing dress. -/
noncomputable def macroRicciStackedLineDressedDistance (dOpen θ : ℝ) : ℝ :=
  dOpen * macroRicciStackedLineBreathingScale θ

/-!
## Compounding along n stacked contacts (error accumulation guard)
-/

/--
After ``n`` in-register stacked contacts, breathing compounds multiplicatively on the
open distance slot (log-additive curvature pressure along the line).
-/
noncomputable def macroRicciCompoundBreathingScale (n : ℕ) (θ : ℝ) : ℝ :=
  macroRicciStackedLineBreathingScale θ ^ n

theorem macro_ricci_compound_breathing_zero (θ : ℝ) :
    macroRicciCompoundBreathingScale 0 θ = 1 := by
  unfold macroRicciCompoundBreathingScale
  simp

theorem macro_ricci_compound_breathing_one (θ : ℝ) :
    macroRicciCompoundBreathingScale 1 θ = macroRicciStackedLineBreathingScale θ := by
  unfold macroRicciCompoundBreathingScale
  simp

/--
Electronic (no heavy-nucleus) guard against spurious over-counting when ξ drifts from
lock-in — Python ``curvature_feedback_weight`` without heavy centre.
-/
noncomputable def electronicCompoundErrorGuard (ξ : ℝ) : ℝ :=
  let c2 := tuftLapseConcentrationAtXi ξ 0 0
  let c2Lock := tuftLapseConcentrationAtXi xiLockin 0 0
  1 - strongChannelFraction * (1 - c2 / max c2Lock 1e-30)

theorem electronic_compound_error_guard_at_lockin :
    electronicCompoundErrorGuard xiLockin = 1 := by
  unfold electronicCompoundErrorGuard
  rw [tuftLapseConcentrationAtXi_lockin_zero]
  rw [strongChannelFraction_eq_four_eighths]
  norm_num

/-- Fully dressed macro contact coupling: medium ρ, optional electronic guard at ξ. -/
noncomputable def macroRicciDressedContactCoupling
    (θ ρ ξ : ℝ) (useElectronicGuard : Bool) : ℝ :=
  let base := outsideContactCouplingAtMediumDensity θ ρ
  if useElectronicGuard then base * electronicCompoundErrorGuard ξ else base

/-!
## Homogeneous second-order feedback (one macro Ricci round)
-/

/-- One self-consistent homogeneous-curvature feedback round (``B_hom + δB``). -/
noncomputable def macroRicciHomogeneousFeedbackRound (ξ ρ δ_coord : ℝ) : ℝ :=
  bindingCurvatureFeedbackSecondOrderHomogeneous ξ ρ δ_coord

/-!
## Local BE × mass dress amplitude (per contact, not global)
-/

/-- Mass participation at a contact pair: ``max(m − 1, 0) / max(m, 1)`` with ``m ≥ 1``. -/
noncomputable def contactMassParticipation (m : ℝ) : ℝ :=
  max (m - 1) 0 / max m 1

theorem contact_mass_participation_gly : contactMassParticipation 1 = 0 := by
  unfold contactMassParticipation
  norm_num

theorem contact_mass_participation_pos {m : ℝ} (hm : 1 < m) :
    0 < contactMassParticipation m := by
  unfold contactMassParticipation
  have h1 : 0 < m - 1 := sub_pos.mpr hm
  have hnum : 0 < max (m - 1) 0 := lt_of_lt_of_le h1 (le_max_left (m - 1) 0)
  have hden : 0 < max m 1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right m 1)
  exact div_pos hnum hden

/--
Per-contact macro Ricci dress strength from **binding excess × mass × site energy**.

Python ``macro_ricci_local_dress_amplitude``:

  ``clamp₀¹( (4/8) · (B_eff − 1) · (m − 1)/m · √(E/E_Gly) )``
-/
noncomputable def macroRicciLocalDressAmplitude
    (beExcess massPart siteRatio : ℝ) : ℝ :=
  let raw := strongChannelFraction * beExcess * massPart * siteRatio
  min 1 (max 0 raw)

theorem macro_ricci_local_dress_zero_be (massPart siteRatio : ℝ) :
    macroRicciLocalDressAmplitude 0 massPart siteRatio = 0 := by
  unfold macroRicciLocalDressAmplitude
  norm_num

theorem macro_ricci_local_dress_zero_mass (beExcess siteRatio : ℝ) :
    macroRicciLocalDressAmplitude beExcess 0 siteRatio = 0 := by
  unfold macroRicciLocalDressAmplitude
  norm_num

theorem macro_ricci_local_dress_le_one (beExcess massPart siteRatio : ℝ) :
    macroRicciLocalDressAmplitude beExcess massPart siteRatio ≤ 1 := by
  unfold macroRicciLocalDressAmplitude
  exact min_le_left _ _

/--
Soft NeRF SSE target: open distance + local blend · (dressed − open).

Hard graph targets stay at the open β chord; only the closure objective sees dress.
-/
noncomputable def macroRicciSoftContactTarget (dOpen blend dressed : ℝ) : ℝ :=
  dOpen + blend * (dressed - dOpen)

theorem macro_ricci_soft_target_no_blend (dOpen dressed : ℝ) :
    macroRicciSoftContactTarget dOpen 0 dressed = dOpen := by
  unfold macroRicciSoftContactTarget
  ring

/-!
## System-wide dress (whole contact network + terminus pull)
-/

/--
System-wide macro Ricci dress from homogeneous feedback × mass × log network compound.

Python ``macro_ricci_system_dress_amplitude`` — not a single stacked line.
-/
noncomputable def macroRicciSystemDressAmplitude
    (fbExcess massPart siteRatio compound : ℝ) : ℝ :=
  let raw := strongChannelFraction * fbExcess * massPart * siteRatio * (1 + compound)
  min 1 (max 0 raw)

theorem macro_ricci_system_dress_zero_fb (massPart siteRatio compound : ℝ) :
    macroRicciSystemDressAmplitude 0 massPart siteRatio compound = 0 := by
  unfold macroRicciSystemDressAmplitude
  norm_num

/-- Per-contact share of system dress (terminus = 1, helix axial ≪ 1). -/
noncomputable def macroRicciContactParticipation (kindWeight : ℝ) (systemAmp : ℝ) : ℝ :=
  min 1 (max 0 (systemAmp * kindWeight))

/-- Dynamic participation: live ρ ratio × closure pass weight (Python witness). -/
noncomputable def macroRicciDynamicContactParticipation (ρLocal ρNetwork passWeight : ℝ) : ℝ :=
  min 1 (max 0 (ρLocal / max ρNetwork 1e-30 * passWeight))

/-- Kind-specific inward breathing (terminus strongest). -/
noncomputable def macroRicciInwardBreathingScale (breathing strength : ℝ) : ℝ :=
  1 - strength * max (1 - breathing) 0

/-- Network compound excess: ``macroRicciCompoundBreathingScale n θ − 1``. -/
noncomputable def macroRicciNetworkCompoundExcess (n : ℕ) (breathing : ℝ) : ℝ :=
  macroRicciCompoundBreathingScale n breathing - 1

/-- Inward-strength channel from α, γ, sc only (``MiniproteinChemistryDynamics``). -/
noncomputable def macroRicciInwardStrengthForContactKind
    (k : Hqiv.ProteinResearch.TertiaryContactKind) : ℝ :=
  match k with
  | .helix_i3 | .helix_i4 => 0
  | .terminus => strongChannelFraction
  | .hydrophobic => gamma_HQIV / 2
  | .helix_sheet => alpha
  | .sheet_i2 => gamma_HQIV / 4

theorem macro_ricci_inward_strength_terminus :
    macroRicciInwardStrengthForContactKind .terminus = strongChannelFraction := rfl

theorem macro_ricci_inward_strength_helix_axial :
    macroRicciInwardStrengthForContactKind .helix_i3 = 0 := rfl

end

end Hqiv.QuantumChemistry
