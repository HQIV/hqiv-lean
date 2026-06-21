import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.FanoHolonomyOverlap
import Hqiv.Physics.FanoMixingMatrix
import Hqiv.Physics.DerivedGaugeAndLeptonSector

/-!
# PMNS holonomy readout

Canonical PMNS matrix on the shared `FanoMixingMatrix` infrastructure,
wrapping the T10 overlap assembler in `HopfShellBeltramiMassBridge`.

Normal ordering and mass splittings link to the outer-shell Casimir ladder.
No PDG PMNS import in theorem hypotheses.
-/

namespace Hqiv.Physics

open Matrix

/-! ## T10 angles on shared infrastructure -/

theorem pmnsAngle12_sin_sq : Real.sin t10PMNSAngle12 ^ 2 = (1 : ℝ) / 4 :=
  t10PMNSAngle12_sin_sq

theorem pmnsAngle23_sin_sq : Real.sin t10PMNSAngle23 ^ 2 = (1 : ℝ) / 3 :=
  t10PMNSAngle23_sin_sq

/-- PMNS magnitude-squared proxy from T10 sin² values (diagonal dominance slot). -/
noncomputable def pmnsMagnitudeSqMatrix : MixingMagnitudeSq :=
  Matrix.of fun i j =>
    if i = j then
      Real.cos (if i = 0 then t10PMNSAngle12 else if i = 1 then t10PMNSAngle23 else t10PMNSAngle13) ^ 2
    else
      Real.sin (if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 then t10PMNSAngle12
        else if i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1 then t10PMNSAngle23
        else t10PMNSAngle13) ^ 2 / 4

noncomputable def pmnsDeltaCP : ℝ := assembleT10PMNSMixingReadout.deltaCP

theorem pmnsDeltaCP_eq_pi_over_five :
    pmnsDeltaCP = Real.pi / 5 :=
  assembleT10PMNSMixingReadout_deltaCP_eq_pi_over_five

noncomputable def pmnsUnitaryReal : Matrix (Fin 3) (Fin 3) ℝ := t10PMNSUnitaryReal

noncomputable def pmnsUnitary : MixingMatrix3 :=
  mixingApplyCPPhase (mixingRealToComplex pmnsUnitaryReal) pmnsDeltaCP

noncomputable def pmnsJarlskog : ℝ :=
  jarlskogFromAngles t10PMNSAngle12 t10PMNSAngle23 t10PMNSAngle13 pmnsDeltaCP

/-! ## Normal ordering and mass splittings -/

theorem tuftNeutrinoHolonomySplitRatio_light :
    tuftNeutrinoHolonomySplitRatio 0 = (1 : ℝ) / 3 := by
  unfold tuftNeutrinoHolonomySplitRatio
  rw [tuftNeutrinoHolonomyRatio_light, tuftNeutrinoHolonomyRatio_heavy]
  norm_num

theorem tuftNeutrinoHolonomySplitRatio_middle :
    tuftNeutrinoHolonomySplitRatio 1 = (2 : ℝ) / 3 := by
  unfold tuftNeutrinoHolonomySplitRatio
  rw [tuftNeutrinoHolonomyRatio_middle, tuftNeutrinoHolonomyRatio_heavy]
  norm_num

theorem tuftNeutrinoHolonomySplitRatio_heavy :
    tuftNeutrinoHolonomySplitRatio 2 = 1 := by
  unfold tuftNeutrinoHolonomySplitRatio
  rw [tuftNeutrinoHolonomyRatio_heavy]
  norm_num

theorem tuftNeutrinoMassFromT10AtXi_light_lt_middle
    (ξ vev κ6 : ℝ) (hξ : 1 < ξ) (hvev : 0 < vev) (hκ6 : 0 < κ6) :
    tuftNeutrinoMassFromT10AtXi_MeV ξ 0 vev κ6 <
      tuftNeutrinoMassFromT10AtXi_MeV ξ 1 vev κ6 := by
  unfold tuftNeutrinoMassFromT10AtXi_MeV
  have hanchor := tuftOuterNeutrinoFullAnchorAtXi_MeV_pos ξ vev κ6 hξ hvev hκ6
  rw [tuftNeutrinoHolonomySplitRatio_light, tuftNeutrinoHolonomySplitRatio_middle,
    t10MiddleToLightPhaseRatio_eq_three]
  nlinarith [hanchor, t10MiddleToLightPhaseRatio_pos]

theorem tuftNeutrinoMassFromT10AtXi_middle_lt_heavy
    (ξ vev κ6 : ℝ) (hξ : 1 < ξ) (hvev : 0 < vev) (hκ6 : 0 < κ6) :
    tuftNeutrinoMassFromT10AtXi_MeV ξ 1 vev κ6 <
      tuftNeutrinoMassFromT10AtXi_MeV ξ 2 vev κ6 := by
  unfold tuftNeutrinoMassFromT10AtXi_MeV
  have hanchor := tuftOuterNeutrinoFullAnchorAtXi_MeV_pos ξ vev κ6 hξ hvev hκ6
  rw [tuftNeutrinoHolonomySplitRatio_middle, tuftNeutrinoHolonomySplitRatio_heavy]
  nlinarith [hanchor]

theorem pmnsNormalOrdering_holds (ξ : ℝ) (hξ : 1 < ξ) :
    let m := fun g => tuftNeutrinoMassFromT10AtXi_MeV ξ g
    m 0 < m 1 ∧ m 1 < m 2 := by
  intro m
  constructor
  · exact tuftNeutrinoMassFromT10AtXi_light_lt_middle ξ electroweakVev_MeV tuftHopfKappa6 hξ
      electroweakVev_MeV_pos tuftHopfKappa6_pos
  · exact tuftNeutrinoMassFromT10AtXi_middle_lt_heavy ξ electroweakVev_MeV tuftHopfKappa6 hξ
      electroweakVev_MeV_pos tuftHopfKappa6_pos

noncomputable def pmnsDeltaMSquared21_MeV2 (ξ : ℝ) : ℝ :=
  (neutrinoDeltaMSquaredFromT10AtXi_MeV2 ξ).1

noncomputable def pmnsDeltaMSquared31_MeV2 (ξ : ℝ) : ℝ :=
  (neutrinoDeltaMSquaredFromT10AtXi_MeV2 ξ).2.2

theorem pmnsDeltaMSquared21_pos (ξ : ℝ) (hξ : 1 < ξ) :
    0 < pmnsDeltaMSquared21_MeV2 ξ := by
  unfold pmnsDeltaMSquared21_MeV2 neutrinoDeltaMSquaredFromT10AtXi_MeV2
  have h01 := tuftNeutrinoMassFromT10AtXi_light_lt_middle ξ electroweakVev_MeV tuftHopfKappa6 hξ
    electroweakVev_MeV_pos tuftHopfKappa6_pos
  have hm1 := tuftNeutrinoMassFromT10AtXi_MeV_pos ξ electroweakVev_MeV tuftHopfKappa6 1 hξ
    electroweakVev_MeV_pos tuftHopfKappa6_pos
  have hm0 := tuftNeutrinoMassFromT10AtXi_MeV_pos ξ electroweakVev_MeV tuftHopfKappa6 0 hξ
    electroweakVev_MeV_pos tuftHopfKappa6_pos
  dsimp
  nlinarith [sq_pos_of_pos hm1, sq_pos_of_pos hm0, h01]

structure PMNSHolonomyReadout where
  overlap : Matrix (Fin 3) (Fin 3) ℝ
  unitary : MixingMatrix3
  theta12 : ℝ
  theta23 : ℝ
  theta13 : ℝ
  deltaCP : ℝ
  jarlskog : ℝ
  normal_order : ∀ (ξ : ℝ), 1 < ξ →
    let m := fun g => tuftNeutrinoMassFromT10AtXi_MeV ξ g
    m 0 < m 1 ∧ m 1 < m 2

noncomputable def assemblePMNSHolonomyReadout : PMNSHolonomyReadout where
  overlap := t10NeutrinoOverlapMatrix
  unitary := pmnsUnitary
  theta12 := t10PMNSAngle12
  theta23 := t10PMNSAngle23
  theta13 := t10PMNSAngle13
  deltaCP := pmnsDeltaCP
  jarlskog := pmnsJarlskog
  normal_order := pmnsNormalOrdering_holds

theorem assemblePMNSHolonomyReadout_deltaCP :
    assemblePMNSHolonomyReadout.deltaCP = Real.pi / 5 :=
  pmnsDeltaCP_eq_pi_over_five

end Hqiv.Physics
