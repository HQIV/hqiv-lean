import Hqiv.ProteinResearch.ProteinCoord3Ops
import Hqiv.QuantumChemistry.PeptideBackboneGeometry
import Hqiv.ProteinResearch.MiniproteinRamachandran
import Hqiv.Physics.DynamicCentreGeometry

/-!
# NeRF peptide backbone placement

Python mirror: ``hqiv_lab/miniprotein_backbone.py`` (`_place_atom`, ``place_backbone_atoms``).

Bond-length preservation is proved under ``OrthonormalFrameAssumptions``; the
Python-identical frame builder is ``buildNerfFrameVectors``.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Hqiv.QuantumChemistry
open Hqiv.Physics
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

/--
Place one backbone triplet using the bound-system growth geometry at this assembly stage.

The final equilibrated fold uses ``boundCount = nResidues``; assembly-path witnesses may use
``boundCount < nResidues`` to expose the coagulation path explicitly.
-/
noncomputable def placeNextBackboneTripletAtBound
    (nResidues boundCount : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) : Coord3 × Coord3 × Coord3 :=
  placeNextBackboneTriplet nPrev caPrev cPrev
    (dynamicPeptideBondGeometry nResidues boundCount) phi psi

theorem placeNextBackboneTripletAtBound_full
    (nResidues : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) :
    placeNextBackboneTripletAtBound nResidues nResidues nPrev caPrev cPrev phi psi =
      placeNextBackboneTriplet nPrev caPrev cPrev
        (fullBoundPeptideBondGeometry nResidues) phi psi := by
  rfl

/-- Relax an assembly-path backbone triplet toward the full-bound equilibrium triplet. -/
noncomputable def relaxBackboneTriplet
    (relax : ℝ)
    (assembly equilibrium : Coord3 × Coord3 × Coord3) : Coord3 × Coord3 × Coord3 :=
  match assembly, equilibrium with
  | (nA, caA, cA), (nE, caE, cE) =>
      (relaxCoord3 relax nA nE, relaxCoord3 relax caA caE, relaxCoord3 relax cA cE)

theorem relaxBackboneTriplet_zero
    (assembly equilibrium : Coord3 × Coord3 × Coord3) :
    relaxBackboneTriplet 0 assembly equilibrium = assembly := by
  cases assembly with
  | mk nA restA =>
    cases restA with
    | mk caA cA =>
      cases equilibrium with
      | mk nE restE =>
        cases restE with
        | mk caE cE =>
          simp [relaxBackboneTriplet, relaxCoord3_zero]

theorem relaxBackboneTriplet_one
    (assembly equilibrium : Coord3 × Coord3 × Coord3) :
    relaxBackboneTriplet 1 assembly equilibrium = equilibrium := by
  cases assembly with
  | mk nA restA =>
    cases restA with
    | mk caA cA =>
      cases equilibrium with
      | mk nE restE =>
        cases restE with
        | mk caE cE =>
          simp [relaxBackboneTriplet, relaxCoord3_one]

theorem relaxBackboneTriplet_self
    (relax : ℝ) (triplet : Coord3 × Coord3 × Coord3) :
    relaxBackboneTriplet relax triplet triplet = triplet := by
  cases triplet with
  | mk n rest =>
    cases rest with
    | mk ca c =>
      simp [relaxBackboneTriplet, relaxCoord3_self]

/--
Growth-relaxed placement: assemble with partial bound geometry, then relax toward the
full-bound equilibrium triplet.
-/
noncomputable def placeNextBackboneTripletAtBoundRelaxed
    (nResidues boundCount : ℕ) (relax : ℝ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) : Coord3 × Coord3 × Coord3 :=
  relaxBackboneTriplet relax
    (placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi)
    (placeNextBackboneTripletAtBound nResidues nResidues nPrev caPrev cPrev phi psi)

theorem placeNextBackboneTripletAtBoundRelaxed_zero
    (nResidues boundCount : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) :
    placeNextBackboneTripletAtBoundRelaxed nResidues boundCount 0 nPrev caPrev cPrev phi psi =
      placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi := by
  unfold placeNextBackboneTripletAtBoundRelaxed
  rw [relaxBackboneTriplet_zero]

theorem placeNextBackboneTripletAtBoundRelaxed_one
    (nResidues boundCount : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) :
    placeNextBackboneTripletAtBoundRelaxed nResidues boundCount 1 nPrev caPrev cPrev phi psi =
      placeNextBackboneTripletAtBound nResidues nResidues nPrev caPrev cPrev phi psi := by
  unfold placeNextBackboneTripletAtBoundRelaxed
  rw [relaxBackboneTriplet_one]

/-- Carbonyl O placement from prior N, Cα, C (Python ``_place_carbonyl_o``). -/
noncomputable def placeCarbonylO (nPrev caPrev cPrev : Coord3) (c_o : ℝ) : Coord3 :=
  nerfPlaceAtom nPrev caPrev cPrev c_o (Real.pi - dynamicCentreAngleRad 6 3 / 2) Real.pi

theorem placeCarbonylO_eq_nerfPlaceAtom (nPrev caPrev cPrev : Coord3) (c_o : ℝ) :
    placeCarbonylO nPrev caPrev cPrev c_o =
      nerfPlaceAtom nPrev caPrev cPrev c_o (Real.pi - dynamicCentreAngleRad 6 3 / 2) Real.pi := rfl

/-- Full backbone quad for one residue triplet step. -/
noncomputable def placeNextBackboneQuadAtBound
    (nResidues boundCount : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) : Coord3 × Coord3 × Coord3 × Coord3 :=
  let g := dynamicPeptideBondGeometry nResidues boundCount
  let trip := placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi
  match trip with
  | (nNew, caNew, cNew) => (nNew, caNew, cNew, placeCarbonylO nNew caNew cNew g.c_o)

theorem place_next_backbone_quad_uses_dynamic_c_o (nResidues boundCount : ℕ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) :
    (placeNextBackboneQuadAtBound nResidues boundCount nPrev caPrev cPrev phi psi).2.2.2 =
      placeCarbonylO
        (placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi).1
        (placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi).2.1
        (placeNextBackboneTripletAtBound nResidues boundCount nPrev caPrev cPrev phi psi).2.2
        (dynamicPeptideBondGeometry nResidues boundCount).c_o := by
  unfold placeNextBackboneQuadAtBound
  simp [placeNextBackboneTripletAtBound, dynamicPeptideBondGeometry]

theorem placeNextBackboneTripletAtBoundRelaxed_fullBound
    (nResidues : ℕ) (relax : ℝ)
    (nPrev caPrev cPrev : Coord3) (phi psi : ℝ) :
    placeNextBackboneTripletAtBoundRelaxed nResidues nResidues relax nPrev caPrev cPrev phi psi =
      placeNextBackboneTripletAtBound nResidues nResidues nPrev caPrev cPrev phi psi := by
  unfold placeNextBackboneTripletAtBoundRelaxed
  rw [relaxBackboneTriplet_self]

end Hqiv.ProteinResearch
