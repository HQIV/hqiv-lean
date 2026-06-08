import Hqiv.Geometry.UniverseAge
import Hqiv.Physics.ConservedContentMassBridge

namespace Hqiv.Physics

open Hqiv

/-!
# Age-normalized heavy mass readouts

This module reverses the old witness direction for the heavy lock-in sector.  A
universe-age input, packaged as `AgeLapseNowScale`, supplies the single
dimensionless now-scale.  The existing content-complexity and Rindler surface
readout then produce top/tau-style heavy masses without using the top or tau
decimal anchors as definitions.
-/

/-- Single heavy-sector normalization induced by an age/lapse now-scale.

It is chosen so that the quark/color-composed heavy lock-in channel reads back
`scale.massUnit`; all other heavy-sector masses are ratios against the same
`l² × effCorrected` surface rule. -/
noncomputable def ageNormalizedMassScale
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ) : ℝ :=
  scale.massUnit /
    (intrinsicWaveComplexity .quark * effCorrected δ m_top_at_lockin)

/-- Age-normalized mass readout for a content class at shell `m`. -/
noncomputable def ageNormalizedHeavyMass
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ)
    (c : FermionContentClass) (m : ℕ) : ℝ :=
  massScalingAnsatz (ageNormalizedMassScale scale δ) δ
    (closureLayerOfContent c).rank m

/-- Expanded form of the age-normalized readout. -/
theorem ageNormalizedHeavyMass_eq_massUnit_times_content_surface_ratio
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ)
    (c : FermionContentClass) (m : ℕ)
    (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    ageNormalizedHeavyMass scale δ c m =
      scale.massUnit *
        (intrinsicWaveComplexity c / intrinsicWaveComplexity .quark) *
        (effCorrected δ m / effCorrected δ m_top_at_lockin) := by
  unfold ageNormalizedHeavyMass ageNormalizedMassScale massScalingAnsatz
  have heff_pos : 0 < effCorrected δ m_top_at_lockin :=
    effCorrected_pos δ m_top_at_lockin hden
  have heff_ne : effCorrected δ m_top_at_lockin ≠ 0 := ne_of_gt heff_pos
  have hq_ne : intrinsicWaveComplexity .quark ≠ 0 := by
    simp [intrinsicWaveComplexity, conservedTripleCount]
  rw [closureLayer_rank_matches_triple_count]
  field_simp [heff_ne, hq_ne]
  rw [intrinsicWaveComplexity_eq_sq c]
  ring_nf

/-- Age-normalized top/color-composed heavy readout. -/
noncomputable def ageNormalizedTopMass
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ) : ℝ :=
  ageNormalizedHeavyMass scale δ .quark m_top_at_lockin

/-- The age-normalized top readout recovers the age/lapse mass unit exactly. -/
theorem ageNormalizedTopMass_eq_massUnit
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ)
    (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    ageNormalizedTopMass scale δ = scale.massUnit := by
  unfold ageNormalizedTopMass
  rw [ageNormalizedHeavyMass_eq_massUnit_times_content_surface_ratio scale δ .quark
    m_top_at_lockin hden]
  have heff_pos : 0 < effCorrected δ m_top_at_lockin :=
    effCorrected_pos δ m_top_at_lockin hden
  have heff_ne : effCorrected δ m_top_at_lockin ≠ 0 := ne_of_gt heff_pos
  have hq_ne : intrinsicWaveComplexity .quark ≠ 0 := by
    simp [intrinsicWaveComplexity, conservedTripleCount]
  field_simp [hq_ne, heff_ne]

/-- Age-normalized heavy charged-lepton/tau readout on the current τ shell. -/
noncomputable def ageNormalizedTauMass
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ) : ℝ :=
  ageNormalizedHeavyMass scale δ .chargedLepton m_tau

/-- Tau/top relation after replacing the top anchor by the age/lapse unit. -/
theorem ageNormalizedTauMass_eq_topUnit_times_content_surface_ratio
    (scale : Hqiv.AgeLapseNowScale) (δ : ℝ)
    (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    ageNormalizedTauMass scale δ =
      scale.massUnit *
        (intrinsicWaveComplexity .chargedLepton / intrinsicWaveComplexity .quark) *
        (effCorrected δ m_tau / effCorrected δ m_top_at_lockin) := by
  exact ageNormalizedHeavyMass_eq_massUnit_times_content_surface_ratio
    scale δ .chargedLepton m_tau hden

/-- Default paper-age top readout, using the age-first now-scale rather than the
legacy `172.57` comparison literal. -/
noncomputable def paperAgeTopMass (δ : ℝ) : ℝ :=
  ageNormalizedTopMass Hqiv.paperAgeNowScale δ

/-- Default paper-age tau readout, parallel to `paperAgeTopMass`. -/
noncomputable def paperAgeTauMass (δ : ℝ) : ℝ :=
  ageNormalizedTauMass Hqiv.paperAgeNowScale δ

end Hqiv.Physics
