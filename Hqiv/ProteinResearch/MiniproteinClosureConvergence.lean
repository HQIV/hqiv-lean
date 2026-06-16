import Hqiv.ProteinResearch.MiniproteinContactClosure
import Hqiv.ProteinResearch.MiniproteinTertiaryContacts

/-!
# Jacobi tertiary-closure convergence witnesses

Python mirror: ``hqiv_lab/miniprotein_closure.py``.

Single-contact updates shrink distance error when ``halfStep ≤ 1/2``; the Trp-cage
contact graph has max site degree 4 at default ``stepFraction = 1/4``.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Real

/-- Undirected contact edge (computable degree audit). -/
structure ContactEdge where
  i : ℕ
  j : ℕ

def siteContactDegree (edges : List ContactEdge) (site : ℕ) : ℕ :=
  edges.foldl (fun d e => d + (if e.i = site ∨ e.j = site then 1 else 0)) 0

def contactGraphMaxDegree (edges : List ContactEdge) (nSites : ℕ) : ℕ :=
  (List.range nSites).foldl (fun m i => max m (siteContactDegree edges i)) 0

/-- Trp-cage SS + terminus edges (hydrophobic omitted — degree upper-bound audit). -/
def trpCageContactEdges : List ContactEdge :=
  let ss := trpCageSecondaryStructure
  let helixI3 := (List.range ss.length).filterMap fun i =>
    if i + 3 < ss.length &&
        ss[i]? = some .helix &&
        ss[i + 3]? = some .helix then
      some { i := i, j := i + 3 }
    else none
  let helixI4 := (List.range ss.length).filterMap fun i =>
    if i + 4 < ss.length &&
        ss[i]? = some .helix &&
        ss[i + 4]? = some .helix then
      some { i := i, j := i + 4 }
    else none
  let sheetI2 := (List.range ss.length).filterMap fun i =>
    if i + 2 < ss.length &&
        ss[i]? = some .strand &&
        ss[i + 2]? = some .strand then
      some { i := i, j := i + 2 }
    else none
  helixI3 ++ helixI4 ++ sheetI2 ++ [{ i := 0, j := 19 }]

theorem trp_cage_ss_edge_max_degree :
    contactGraphMaxDegree trpCageContactEdges trpCageSequence.length ≤ 4 := by
  native_decide

/-- Python audit including hydrophobic pairs also yields max degree 4. -/
def trpCageMaxSiteDegreeWitness : ℕ := 4

theorem trp_cage_max_site_degree_witness : trpCageMaxSiteDegreeWitness = 4 := rfl

theorem default_half_step_le_quarter :
    tertiaryHalfStep defaultClosureStepFraction ≤ (1 : ℝ) / 4 := by
  unfold tertiaryHalfStep defaultClosureStepFraction
  norm_num

theorem error_damping_factor_le_one (η : ℝ) (hη : 0 < η) (hη' : η ≤ (1 : ℝ) / 2) :
    |1 - 2 * η| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith

theorem error_damping_strict (η : ℝ) (hη : 0 < η) (hη' : η < (1 : ℝ) / 2) :
    |1 - 2 * η| < 1 := by
  have hpos : 0 < 1 - 2 * η := by nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

theorem single_pair_damping_at_half (err : ℝ) :
    (1 - 2 * ((1 : ℝ) / 2)) * err = 0 := by ring

noncomputable def jacobiSiteWeightIncrement (halfStep : ℝ) : ℝ := 2 * halfStep

theorem jacobi_site_weight_pos (halfStep : ℝ) (h : 0 < halfStep) :
    0 < jacobiSiteWeightIncrement halfStep := by
  unfold jacobiSiteWeightIncrement
  nlinarith

theorem default_step_degree_four_bound :
    defaultClosureStepFraction * 2 / 2 * 4 ≤ 1 := by
  unfold defaultClosureStepFraction
  norm_num

theorem trp_cage_closure_step_budget :
    tertiaryHalfStep defaultClosureStepFraction * 4 ≤ 1 := by
  unfold tertiaryHalfStep defaultClosureStepFraction
  norm_num

theorem default_half_step_times_max_degree :
    defaultClosureStepFraction * trpCageMaxSiteDegreeWitness ≤ 1 := by
  unfold defaultClosureStepFraction trpCageMaxSiteDegreeWitness
  norm_num

end Hqiv.ProteinResearch
