import Hqiv.ProteinResearch.ProteinCoord3Ops
import Hqiv.QuantumChemistry.PeptideBackboneGeometry
import Hqiv.ProteinResearch.MiniproteinRamachandran

/-!
# NeRF peptide backbone placement

Python mirror: ``hqiv_lab/miniprotein_backbone.py`` (`_place_atom`, ``place_backbone_atoms``).

Bond-length preservation is proved under ``OrthonormalFrameAssumptions``; the
Python-identical frame builder is ``buildNerfFrameVectors``.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Hqiv.QuantumChemistry
open Real

/-- NeRF local axes (computed; orthogonality checked in parity tests). -/
structure NerfFrameVectors where
  bc : Coord3
  m : Coord3
  n : Coord3

/-- Build NeRF frame from three prior backbone sites (Python ``_place_atom``). -/
noncomputable def buildNerfFrameVectors (origin ref prev : Coord3) : NerfFrameVectors :=
  let bc := unit3 (sub3 prev ref) (fun i => if i = 0 then 1 else 0)
  let ab := unit3 (sub3 ref origin) (fun i => if i = 1 then 1 else 0)
  let perpRaw := cross3 ab bc
  let perp := unit3 perpRaw (fun i => if i = 2 then 1 else 0)
  let mVec := unit3 (cross3 perp bc) (fun i => if i = 1 then 1 else 0)
  let nVec := unit3 (cross3 bc mVec) (fun i => if i = 2 then 1 else 0)
  { bc := bc, m := mVec, n := nVec }

noncomputable def nerfDisplacementFromVectors (frame : NerfFrameVectors) (length angle dihedral : ℝ) :
    Coord3 :=
  nerfDisplacement frame.bc frame.m frame.n length angle dihedral

/-- Internal-coordinate atom placement (NeRF-style). -/
noncomputable def nerfPlaceAtom (origin ref prev : Coord3) (length angle dihedral : ℝ) : Coord3 :=
  add3 prev (nerfDisplacementFromVectors (buildNerfFrameVectors origin ref prev) length angle dihedral)

theorem nerf_place_atom_distance {bc m n : Coord3} (origin ref prev : Coord3)
    (length angle dihedral : ℝ) (hlen : 0 ≤ length)
    (h : OrthonormalFrameAssumptions bc m n) :
    distanceTerm prev (add3 prev (nerfDisplacement bc m n length angle dihedral)) = length :=
  nerf_placement_distance prev length angle dihedral hlen h

/-- First-residue Cα at origin; N along −x; C in xy plane (Python seed). -/
noncomputable def initialCaAtom : Coord3 := zero3

noncomputable def initialNAtom (g : PeptideBondGeometry) : Coord3 :=
  fun i => if i = 0 then -g.n_ca else 0

noncomputable def initialCAtom (g : PeptideBondGeometry) : Coord3 :=
  fun i =>
    match i with
    | 0 => g.ca_c * Real.cos (Real.pi - g.n_ca_c)
    | 1 => g.ca_c * Real.sin (Real.pi - g.n_ca_c)
    | _ => 0

theorem initial_ca_at_origin : initialCaAtom = zero3 := rfl

noncomputable def hqivPeptideBondGeometryWitness : PeptideBondGeometry := hqivPeptideBondGeometry

/-- Place one new residue backbone triplet from prior N, Cα, C and (φ, ψ). -/
noncomputable def placeNextBackboneTriplet
    (nPrev caPrev cPrev : Coord3) (g : PeptideBondGeometry) (phi psi : ℝ) : Coord3 × Coord3 × Coord3 :=
  let nNew := nerfPlaceAtom nPrev caPrev cPrev g.c_n g.ca_c_n psi
  let caNew := nerfPlaceAtom caPrev cPrev nNew g.n_ca g.c_n_ca peptideOmegaRad
  let cNew := nerfPlaceAtom cPrev nNew caNew g.ca_c g.n_ca_c phi
  (nNew, caNew, cNew)

end Hqiv.ProteinResearch
