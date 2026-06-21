import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ReadoutGaugeSeed
import Hqiv.Geometry.HQVMetric

/-!
# Fano holonomy overlap infrastructure

Reusable generation-overlap weights on the three admissible Fano vertices
(`fanoVertex0`, `fanoVertexMiddle`, `fanoVertexHeavyGen`).

This module supplies the **algebraic language** shared by CKM and PMNS readouts.
No PDG comparison numerals enter here.
-/

namespace Hqiv.Physics

open Hqiv

/-- Generation index aligned with the three admissible Fano vertices. -/
abbrev FanoGeneration := Fin 3

/-- Map generation index to the corresponding Fano vertex. -/
def fanoGenerationVertex : FanoGeneration → Fin 7
  | 0 => fanoVertex0
  | 1 => fanoVertexMiddle
  | 2 => fanoVertexHeavyGen

/-- Holonomy row RHS at generation `g`. -/
noncomputable def generationHolonomyRow (g : FanoGeneration) : ℝ :=
  holonomyRowRhs (fanoGenerationVertex g)

theorem generationHolonomyRow_zero :
    generationHolonomyRow 0 = (48 : ℝ) / 91 := holonomyRowRhs_zero

theorem generationHolonomyRow_one :
    generationHolonomyRow 1 = (96 : ℝ) / 91 := holonomyRowRhs_middle

theorem generationHolonomyRow_two :
    generationHolonomyRow 2 = (144 : ℝ) / 91 := holonomyRowRhs_heavyGen

/-- Sum of the three generation holonomy rows (normalization denominator). -/
noncomputable def generationHolonomyRowSum : ℝ :=
  generationHolonomyRow 0 + generationHolonomyRow 1 + generationHolonomyRow 2

theorem generationHolonomyRowSum_pos : 0 < generationHolonomyRowSum := by
  rw [generationHolonomyRowSum, generationHolonomyRow_zero,
    generationHolonomyRow_one, generationHolonomyRow_two]
  norm_num

theorem generationHolonomyRowSum_eq :
    generationHolonomyRowSum = (288 : ℝ) / 91 := by
  rw [generationHolonomyRowSum, generationHolonomyRow_zero,
    generationHolonomyRow_one, generationHolonomyRow_two]
  norm_num

/--
Normalized overlap weight for generation `g`: holonomy row over the three-generation sum.
This is the T10-style overlap denominator used by PMNS and CKM holonomy readouts.
-/
noncomputable def fanoGenerationOverlapWeight (g : FanoGeneration) : ℝ :=
  generationHolonomyRow g / generationHolonomyRowSum

theorem fanoGenerationOverlapWeight_pos (g : FanoGeneration) :
    0 < fanoGenerationOverlapWeight g := by
  unfold fanoGenerationOverlapWeight
  exact div_pos (by
    fin_cases g <;> simp [generationHolonomyRow_zero, generationHolonomyRow_one,
      generationHolonomyRow_two] <;> norm_num)
    generationHolonomyRowSum_pos

theorem fanoGenerationOverlapWeight_sum_one :
    ∑ g : FanoGeneration, fanoGenerationOverlapWeight g = 1 := by
  rw [Fin.sum_univ_three]
  simp only [fanoGenerationOverlapWeight, generationHolonomyRowSum,
    generationHolonomyRow_zero, generationHolonomyRow_one, generationHolonomyRow_two]
  norm_num

/--
Pairwise holonomy ratio between generations (heavy / middle = 3/2 on the admissible cycle).
-/
noncomputable def fanoGenerationHolonomyRatio (gFrom gTo : FanoGeneration) : ℝ :=
  generationHolonomyRow gTo / generationHolonomyRow gFrom

theorem fanoGenerationHolonomyRatio_one_two :
    fanoGenerationHolonomyRatio 1 2 = (3 : ℝ) / 2 := by
  unfold fanoGenerationHolonomyRatio
  rw [generationHolonomyRow_one, generationHolonomyRow_two]
  norm_num

theorem fanoGenerationHolonomyRatio_zero_one :
    fanoGenerationHolonomyRatio 0 1 = 2 := by
  unfold fanoGenerationHolonomyRatio
  rw [generationHolonomyRow_zero, generationHolonomyRow_one]
  norm_num

/--
Phase-lift skew on the second-order Fano rung hierarchy: difference of adjacent slot squares
at the `(us)` and `(cb)` rungs.  Matches `cpOddFanoHolonomySkew` in `HepDecayReadout`.
-/
noncomputable def fanoSecondOrderPhaseSkew : ℝ :=
  gamma_HQIV / 8 - gamma_HQIV / 32

theorem fanoSecondOrderPhaseSkew_eq_three_over_eighty :
    fanoSecondOrderPhaseSkew = (3 : ℝ) / 80 := by
  simp [fanoSecondOrderPhaseSkew, gamma_eq_2_5]
  norm_num

theorem fanoSecondOrderPhaseSkew_pos : 0 < fanoSecondOrderPhaseSkew := by
  rw [fanoSecondOrderPhaseSkew_eq_three_over_eighty]
  norm_num

/--
CP-odd orientation phase from holonomy skew normalized by the horizon coefficient `γ`.
Used as the shared CP-phase scale for CKM and rare-decay routing.
-/
noncomputable def fanoHolonomyCPPhase : ℝ :=
  Real.pi * fanoSecondOrderPhaseSkew / gamma_HQIV

theorem fanoHolonomyCPPhase_eq_three_pi_over_thirtytwo :
    fanoHolonomyCPPhase = (3 : ℝ) * Real.pi / 32 := by
  rw [fanoHolonomyCPPhase, fanoSecondOrderPhaseSkew_eq_three_over_eighty, gamma_eq_2_5]
  field_simp
  ring_nf

theorem fanoHolonomyCPPhase_pos : 0 < fanoHolonomyCPPhase := by
  rw [fanoHolonomyCPPhase_eq_three_pi_over_thirtytwo]
  positivity

/-- Overlap entry: geometric mean of normalized weights (off-diagonal) or weight (diagonal). -/
noncomputable def fanoGenerationOverlapEntry (i j : FanoGeneration) : ℝ :=
  if i = j then
    Real.sqrt (fanoGenerationOverlapWeight i)
  else
    Real.sin fanoHolonomyCPPhase *
      Real.sqrt (fanoGenerationOverlapWeight i * fanoGenerationOverlapWeight j)

theorem fanoGenerationOverlapEntry_diagonal_pos (g : FanoGeneration) :
    0 < fanoGenerationOverlapEntry g g := by
  unfold fanoGenerationOverlapEntry
  simp only [if_pos rfl]
  exact Real.sqrt_pos.mpr (fanoGenerationOverlapWeight_pos g)

structure FanoHolonomyOverlapCertificate where
  admissible_cycle : generationVerticesFormAdmissibleCycle
  overlap_sum_one : ∑ g : FanoGeneration, fanoGenerationOverlapWeight g = 1
  cp_phase_pos : 0 < fanoHolonomyCPPhase

theorem fanoHolonomyOverlapCertificate_holds : FanoHolonomyOverlapCertificate where
  admissible_cycle := the_three_generation_fano_vertices_form_admissible_cycle
  overlap_sum_one := fanoGenerationOverlapWeight_sum_one
  cp_phase_pos := fanoHolonomyCPPhase_pos

end Hqiv.Physics
