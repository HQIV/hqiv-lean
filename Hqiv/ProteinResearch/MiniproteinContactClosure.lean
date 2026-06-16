import Hqiv.ProteinResearch.ProteinHKEMinimizer
import Hqiv.ProteinResearch.MiniproteinTertiaryContacts

/-!
# Tertiary contact Jacobi closure (fast relaxation spec)

Python mirror: ``hqiv_lab/miniprotein_closure.py``.

Proves the per-pair displacement is antisymmetric (zero net translation per contact)
and records the compiled half-step ``stepFraction / 2`` (uniform across contact kinds).
-/

namespace Hqiv.ProteinResearch

open Hqiv
open Hqiv.QM
open Real

structure TertiaryContactSpec where
  i : ℕ
  j : ℕ
  target : ℝ
  kind : TertiaryContactKind

/-- Compiled half-step for Jacobi pair relaxation (uniform; kind selects pass only). -/
noncomputable def tertiaryHalfStep (stepFraction : ℝ) : ℝ :=
  stepFraction / 2

theorem tertiary_half_step_eq_python (stepFraction : ℝ) :
    tertiaryHalfStep stepFraction = stepFraction * (1 / 2) := by
  unfold tertiaryHalfStep
  ring

/-- Unit direction from site ``i`` toward site ``j``. -/
noncomputable def unitDirection (pi pj : Coord3) : Coord3 :=
  let dx := pj 0 - pi 0
  let dy := pj 1 - pi 1
  let dz := pj 2 - pi 2
  let dist := Real.sqrt (dx ^ 2 + dy ^ 2 + dz ^ 2)
  if dist = 0 then fun _ => (0 : ℝ)
  else fun k =>
    match k with
    | 0 => dx / dist
    | 1 => dy / dist
    | 2 => dz / dist

/-- Scalar distance error ``‖p_j − p_i‖ − target``. -/
noncomputable def distanceError (pi pj : Coord3) (target : ℝ) : ℝ :=
  distanceTerm pi pj - target

/-- Antisymmetric pair displacement along the contact axis. -/
noncomputable def jacobiPairDisp (pi pj : Coord3) (target halfStep : ℝ) : Coord3 × Coord3 :=
  let err := distanceError pi pj target
  let u := unitDirection pi pj
  let disp := smul3 (halfStep * err) u
  (disp, smul3 (-1) disp)

theorem jacobi_pair_disp_antisymmetric (pi pj : Coord3) (target halfStep : ℝ) :
    let (di, dj) := jacobiPairDisp pi pj target halfStep
    add3 di dj = fun _ => 0 := by
  unfold jacobiPairDisp add3 smul3
  funext k
  fin_cases k <;> ring

/-- Default Jacobi step fraction (Python ``step_fraction=0.25``). -/
noncomputable def defaultClosureStepFraction : ℝ := 1 / 4

/-- Default iteration cap (Python ``steps=40``). -/
def defaultClosureMaxSteps : ℕ := 40

/-- Default convergence tolerance [Å] (Python ``1e-4``). -/
noncomputable def defaultClosureToleranceAngstrom : ℝ := 1e-4

theorem default_closure_step_fraction : defaultClosureStepFraction = (1 : ℝ) / 4 := rfl

/-- Hydrophobic pass step: ``default · (1 − α/3)`` (Python ``hydrophobic_step_fraction``). -/
noncomputable def hydrophobicClosureStepFraction : ℝ :=
  defaultClosureStepFraction * (1 - alpha / 3)

theorem hydrophobic_closure_step_fraction_rational :
    hydrophobicClosureStepFraction = (1 : ℝ) / 5 := by
  unfold hydrophobicClosureStepFraction defaultClosureStepFraction
  rw [alpha_eq_3_5]
  norm_num

noncomputable def compiledHalfStep (stepFraction : ℝ) (_c : TertiaryContactSpec) : ℝ :=
  tertiaryHalfStep stepFraction

theorem compiled_half_step_default :
    compiledHalfStep defaultClosureStepFraction
        { i := 0, j := 3, target := 0, kind := .helix_i3 } =
      (1 : ℝ) / 8 := by
  unfold compiledHalfStep tertiaryHalfStep defaultClosureStepFraction
  norm_num

end Hqiv.ProteinResearch
