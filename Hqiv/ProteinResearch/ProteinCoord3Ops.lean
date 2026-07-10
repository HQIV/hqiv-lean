import Hqiv.ProteinResearch.ProteinHKEMinimizer

/-!
# Shared ℝ³ operations for protein geometry modules

Extends `ProteinHKEMinimizer` with vector helpers used by NeRF placement,
Kabsch alignment, and Jacobi closure.
-/

namespace Hqiv.ProteinResearch

open Hqiv.QM
open Real

/-- Zero vector in ℝ³. -/
def zero3 : Coord3 := fun _ => 0

/-- Componentwise subtraction. -/
def sub3 (a b : Coord3) : Coord3 := fun i => a i - b i

/-- Componentwise affine relaxation from an assembly-path point toward equilibrium. -/
def relaxCoord3 (relax : ℝ) (assembly equilibrium : Coord3) : Coord3 :=
  add3 (smul3 (1 - relax) assembly) (smul3 relax equilibrium)

/-- No relaxation keeps the assembly-path coordinate. -/
theorem relaxCoord3_zero (assembly equilibrium : Coord3) :
    relaxCoord3 0 assembly equilibrium = assembly := by
  funext i
  unfold relaxCoord3 add3 smul3
  ring

/-- Unit relaxation recovers the equilibrium coordinate. -/
theorem relaxCoord3_one (assembly equilibrium : Coord3) :
    relaxCoord3 1 assembly equilibrium = equilibrium := by
  funext i
  unfold relaxCoord3 add3 smul3
  ring

/-- Relaxing a coordinate toward itself is a no-op at any relaxation parameter. -/
theorem relaxCoord3_self (relax : ℝ) (p : Coord3) :
    relaxCoord3 relax p p = p := by
  funext i
  unfold relaxCoord3 add3 smul3
  ring

/-- Euclidean norm. -/
noncomputable def norm3 (v : Coord3) : ℝ := Real.sqrt (normSq3 v)

theorem normSq3_nonneg (v : Coord3) : 0 ≤ normSq3 v := by
  unfold normSq3
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem norm3_nonneg (v : Coord3) : 0 ≤ norm3 v := Real.sqrt_nonneg _

/-- Unit vector with fallback when ``‖v‖ = 0``. -/
noncomputable def unit3 (v fallback : Coord3) : Coord3 :=
  if normSq3 v = 0 then fallback
  else smul3 (1 / norm3 v) v

/-- Orthonormal NeRF frame assumptions. -/
def OrthonormalFrameAssumptions (bc m n : Coord3) : Prop :=
  normSq3 bc = 1 ∧ normSq3 m = 1 ∧ normSq3 n = 1 ∧
    dot3 bc m = 0 ∧ dot3 bc n = 0 ∧ dot3 m n = 0

theorem dot3_smul_left (a : ℝ) (u v : Coord3) : dot3 (smul3 a u) v = a * dot3 u v := by
  unfold dot3 smul3
  ring_nf

theorem dot3_smul_right (b : ℝ) (u v : Coord3) : dot3 u (smul3 b v) = b * dot3 u v := by
  unfold dot3 smul3
  ring_nf

theorem dot3_smul_both (a b : ℝ) (u v : Coord3) :
    dot3 (smul3 a u) (smul3 b v) = a * b * dot3 u v := by
  rw [dot3_smul_left, dot3_smul_right]
  ring

theorem dot3_add_left (u v w : Coord3) : dot3 (add3 u v) w = dot3 u w + dot3 v w := by
  unfold dot3 add3
  ring_nf

theorem add3_assoc (u v w : Coord3) : add3 u (add3 v w) = add3 (add3 u v) w := by
  funext i
  unfold add3
  exact (add_assoc (u i) (v i) (w i)).symm

theorem normSq3_add_orthogonal (u v : Coord3) (huv : dot3 u v = 0) (a b : ℝ) :
    normSq3 (add3 (smul3 a u) (smul3 b v)) = a ^ 2 * normSq3 u + b ^ 2 * normSq3 v := by
  have huv' : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by simpa [dot3] using huv
  unfold normSq3 add3 smul3
  have key : 2 * a * b * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) = 0 := by rw [huv']; ring
  ring_nf
  nlinarith [key]

theorem normSq3_add_orthogonal' (u v : Coord3) (huv : dot3 u v = 0) :
    normSq3 (add3 u v) = normSq3 u + normSq3 v := by
  have huv' : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by simpa [dot3] using huv
  unfold normSq3 add3
  have key : 2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) = 0 := by rw [huv']; ring
  ring_nf
  nlinarith [key]

theorem normSq3_smul (u : Coord3) (a : ℝ) :
    normSq3 (smul3 a u) = a ^ 2 * normSq3 u := by
  unfold normSq3 smul3
  ring_nf

/-- NeRF displacement from ``prev`` (not including ``prev`` itself). -/
noncomputable def nerfDisplacement (bc m n : Coord3) (length angle dihedral : ℝ) : Coord3 :=
  let θ := Real.pi - angle
  let φ := dihedral
  add3
    (smul3 (length * Real.cos θ) bc)
    (add3
      (smul3 (length * Real.sin θ * Real.cos φ) m)
      (smul3 (length * Real.sin θ * Real.sin φ) n))

theorem nerf_displacement_length_sq {bc m n : Coord3} (length angle dihedral : ℝ)
    (h : OrthonormalFrameAssumptions bc m n) :
    normSq3 (nerfDisplacement bc m n length angle dihedral) = length ^ 2 := by
  rcases h with ⟨hbc, hm, hn, hbm, hbn, hmn⟩
  set θ := Real.pi - angle
  set φ := dihedral
  set bcP := smul3 (length * Real.cos θ) bc
  set mP := smul3 (length * Real.sin θ * Real.cos φ) m
  set nP := smul3 (length * Real.sin θ * Real.sin φ) n
  unfold nerfDisplacement
  have hbcP : normSq3 bcP = (length * Real.cos θ) ^ 2 := by
    dsimp [bcP]
    rw [normSq3_smul, hbc]
    ring
  have hmP : normSq3 mP = (length * Real.sin θ * Real.cos φ) ^ 2 := by
    dsimp [mP]
    rw [normSq3_smul, hm]
    ring
  have hnP : normSq3 nP = (length * Real.sin θ * Real.sin φ) ^ 2 := by
    dsimp [nP]
    rw [normSq3_smul, hn]
    ring
  have hbm' : dot3 bcP mP = 0 := by
    dsimp [bcP, mP]
    rw [dot3_smul_both, hbm]
    ring
  have hbn' : dot3 bcP nP = 0 := by
    dsimp [bcP, nP]
    rw [dot3_smul_both, hbn]
    ring
  have hmn' : dot3 mP nP = 0 := by
    dsimp [mP, nP]
    rw [dot3_smul_both, hmn]
    ring
  have hsum :
      normSq3 (add3 bcP (add3 mP nP)) =
        (length * Real.cos θ) ^ 2 + (length * Real.sin θ * Real.cos φ) ^ 2 +
          (length * Real.sin θ * Real.sin φ) ^ 2 := by
    have hdot : dot3 (add3 bcP mP) nP = 0 := by
      rw [dot3_add_left, hbn', hmn']
      ring
    have h12 := normSq3_add_orthogonal' bcP mP hbm'
    have h123 := normSq3_add_orthogonal' (add3 bcP mP) nP hdot
    rw [add3_assoc bcP mP nP]
    rw [h123, h12, hbcP, hmP, hnP]
  rw [hsum]
  have hfactor :
      (length * Real.cos θ) ^ 2 + (length * Real.sin θ * Real.cos φ) ^ 2 +
          (length * Real.sin θ * Real.sin φ) ^ 2 =
        length ^ 2 *
          (Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)) := by ring
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) = 1 := by
    calc
      Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)
          = Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq φ]
      _ = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by ring
      _ = 1 := Real.cos_sq_add_sin_sq θ
  rw [hfactor, htrig, mul_one]

theorem nerf_placement_distance {bc m n : Coord3} (prev : Coord3) (length angle dihedral : ℝ)
    (hlen : 0 ≤ length) (h : OrthonormalFrameAssumptions bc m n) :
    distanceTerm prev (add3 prev (nerfDisplacement bc m n length angle dihedral)) = length := by
  set d := nerfDisplacement bc m n length angle dihedral
  have hns := nerf_displacement_length_sq length angle dihedral h
  have hsum : distanceTerm prev (add3 prev d) = Real.sqrt (normSq3 d) := by
    unfold distanceTerm normSq3 add3
    congr 1
    ring_nf
  rw [hsum, hns, Real.sqrt_sq hlen]

/-- List centroid (Python ``center_coordinates`` mean). -/
noncomputable def listCentroid (coords : List Coord3) : Coord3 :=
  match coords with
  | [] => zero3
  | _ :: _ =>
    let n := coords.length
    smul3 (1 / n) (coords.foldl (fun acc p => add3 acc p) zero3)

/-- Center coordinates about their centroid. -/
noncomputable def centerCoords (coords : List Coord3) : List Coord3 :=
  let c := listCentroid coords
  coords.map fun p => sub3 p c

end Hqiv.ProteinResearch
