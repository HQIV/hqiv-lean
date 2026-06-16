import Hqiv.ProteinResearch.ProteinCoord3Ops

/-!
# Kabsch Cα alignment and RMSD (comparison grading)

Python mirror: ``hqiv_lab/miniprotein_backbone.kabsch_rmsd``.

Implements the 3×3 covariance power iteration used in Python (24 steps) and
defines the aligned Cα RMSD readout.  Witness coordinates are grading inputs only.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Real

abbrev Mat3 := Fin 3 → Fin 3 → ℝ

def matVec3 (M : Mat3) (v : Coord3) : Coord3 :=
  fun i => (M i 0) * v 0 + (M i 1) * v 1 + (M i 2) * v 2

def matTranspose3 (M : Mat3) : Mat3 := fun i j => M j i

/-- Apply 3×3 rotation to a coordinate. -/
def applyRot3 (R : Mat3) (p : Coord3) : Coord3 := matVec3 R p

/-- Covariance entry ``H_ij = Σ_k mobile_k[i] · target_k[j] / n`` on centered lists. -/
noncomputable def covarianceEntry (mobile target : List Coord3) (i j : Fin 3) : ℝ :=
  if h : mobile.length = target.length ∧ mobile.length > 0 then
    let n := mobile.length
    (List.range n).foldl (fun acc k =>
      match mobile[k]?, target[k]? with
      | some a, some b => acc + a i * b j
      | _, _ => acc) 0 / n
  else 0

noncomputable def covarianceMatrix3 (mobile target : List Coord3) : Mat3 :=
  fun i j => covarianceEntry mobile target i j

noncomputable def powerIterStep3 (M : Mat3) (v : Coord3) : Coord3 :=
  unit3 (matVec3 M v) (fun i => if i = 0 then 1 else 0)

noncomputable def powerIter24 (M : Mat3) : Coord3 :=
  (List.range 24).foldl (fun v _ => powerIterStep3 M v) (fun i => if i = 0 then 1 else 0)

/-- Dominant right singular vector via fixed 24-step power iteration. -/
noncomputable def kabschRightSingularVector (mob tgt : List Coord3) : Coord3 :=
  powerIter24 (covarianceMatrix3 mob tgt)

/-- Build orthonormal rotation columns (Python Kabsch power-iteration path). -/
noncomputable def kabschRotationMatrix (mobile target : List Coord3) : Mat3 :=
  let mob := centerCoords mobile
  let tgt := centerCoords target
  let H := covarianceMatrix3 mob tgt
  let v := kabschRightSingularVector mob tgt
  let u := unit3 (matVec3 (matTranspose3 H) v) (fun i => if i = 1 then 1 else 0)
  let w := unit3 (cross3 u v) (fun i => if i = 2 then 1 else 0)
  let v' := unit3 (cross3 w u) (fun i => if i = 0 then 1 else 0)
  fun i j =>
    match j with
    | 0 => u i
    | 1 => v' i
    | 2 => w i

/-- Align centered ``mobile`` to centered ``target``. -/
noncomputable def kabschAlignCoords (mobile target : List Coord3) : List Coord3 :=
  let mob := centerCoords mobile
  let R := kabschRotationMatrix mobile target
  mob.map (applyRot3 R)

/-- Mean squared error after alignment. -/
noncomputable def alignedCaMeanSqError (mobile target : List Coord3) : ℝ :=
  if h : mobile.length = target.length ∧ mobile.length > 0 then
    let aligned := kabschAlignCoords mobile target
    let tgt := centerCoords target
    let n := mobile.length
    (List.range n).foldl (fun acc k =>
      match aligned[k]?, tgt[k]? with
      | some a, some b => acc + normSq3 (sub3 a b)
      | _, _ => acc) 0 / n
  else 0

/-- Kabsch Cα RMSD [Å] (Python ``kabsch_rmsd``). -/
noncomputable def kabschCaRmsd (mobile target : List Coord3) : ℝ :=
  Real.sqrt (max 0 (alignedCaMeanSqError mobile target))

theorem kabsch_ca_rmsd_nonneg (mobile target : List Coord3) : 0 ≤ kabschCaRmsd mobile target := by
  unfold kabschCaRmsd
  exact Real.sqrt_nonneg _

end Hqiv.ProteinResearch
