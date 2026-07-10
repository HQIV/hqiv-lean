import Hqiv.ProteinResearch.ProteinHKEMinimizer
import Hqiv.ProteinResearch.MiniproteinFoldWitness

/-!
# Cα trace RMSD witnesses (comparison grading only)

Python mirror: ``hqiv_lab/miniprotein_backbone.kabsch_rmsd``.

Witness PDB/COD coordinates are **never** fold inputs — only grading scalars.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Real

/-- Squared Euclidean distance between two Cα sites. -/
def caDistSq (a b : Coord3) : ℝ :=
  (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2

theorem ca_dist_sq_nonneg (a b : Coord3) : 0 ≤ caDistSq a b := by
  unfold caDistSq
  nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2 - b 2)]

/-- Uncentered mean squared Cα error (before Kabsch alignment). -/
noncomputable def uncenteredCaMeanSqError (mobile target : List Coord3) : ℝ :=
  if h : mobile.length = target.length ∧ mobile.length > 0 then
    let n := mobile.length
    (List.range n).foldl (fun acc k =>
      acc + caDistSq (mobile[k]!) (target[k]!)) 0 / n
  else 0

/-- Uncentered Cα RMSD [Å] (non-Kabsch upper envelope). -/
noncomputable def uncenteredCaRmsd (mobile target : List Coord3) : ℝ :=
  Real.sqrt (max 0 (uncenteredCaMeanSqError mobile target))

theorem uncentered_ca_rmsd_nonneg (mobile target : List Coord3) :
    0 ≤ uncenteredCaRmsd mobile target := by
  unfold uncenteredCaRmsd
  exact Real.sqrt_nonneg _

/-- Fold passes witness gate when Kabsch RMSD is strictly below the competitive threshold. -/
def caRmsdPasses (rmsd threshold : ℝ) : Prop :=
  rmsd < threshold

theorem trp_cage_pass_example (rmsd : ℝ) (h : rmsd < trpCageCaRmsdPassAngstrom) :
    caRmsdPasses rmsd trpCageCaRmsdPassAngstrom := h

theorem gly_gly_pass_example (rmsd : ℝ) (h : rmsd < glyGlyCaRmsdPassAngstrom) :
    caRmsdPasses rmsd glyGlyCaRmsdPassAngstrom := h

theorem competitive_pass_example (rmsd : ℝ) (h : rmsd < competitiveCaRmsdPassAngstrom) :
    caRmsdPasses rmsd competitiveCaRmsdPassAngstrom := h

end Hqiv.ProteinResearch
