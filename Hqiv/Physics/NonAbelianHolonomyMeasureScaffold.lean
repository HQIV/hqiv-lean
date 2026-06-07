import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.SO8PlaquetteHolonomy
import Hqiv.Physics.WeakHiggsFromOMaxwellScaffold
import Hqiv.Geometry.SpatialRotationLorentzClosure
import Hqiv.Algebra.WeakInComplexStructure
import Mathlib.Data.Matrix.Mul

/-!
# Non-abelian holonomy + rotated-frame measure (open-frontier scaffold)

The TUFT+SM synthesis paper flags **full non-abelian plaquette holonomy** and **path-integral /
measure choice on rotated frames** as outside the discharged patch bundle
(`TuftSynthesisZetaHolonomyDischarge` proves abelian cyclic flatness, SU(2)/SU(3) commutator charts,
and light-cone SO(8) Lie data — not full Spin(8) Wilson transport).

This module is the Lean roadmap toward closing that gap:

1. **Matrix transport layer** on `DiscretePlaquetteHolonomy` (beyond `linearEnd`) — discharged in
   `SO8PlaquetteHolonomy` (full four-edge Wilson + pinned `(G₀,G₄)` witness).
2. **Witness** that plaquette holonomy is genuinely non-commutative on the weak Pauli chart.
3. **Rotated-frame measure partial discharge** — spatial `O(3)` invariants already proved in
   `SpatialRotationLorentzClosure`; explicit Haar / non-abelian Wilson measure normalization remains open.
-/

namespace Hqiv.Physics

open Hqiv
open Hqiv.Geometry
open Hqiv.Algebra
open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix transport as an endomorphism on `n → K` vectors. -/
def matrixVecEnd (K : Type*) [Field K] (M : Matrix n n K) : Function.End (n → K) :=
  fun v => M.mulVec v

omit [DecidableEq n] in
@[simp]
theorem matrixVecEnd_mul (K : Type*) [Field K] (A B : Matrix n n K) :
    matrixVecEnd K A * matrixVecEnd K B = matrixVecEnd K (A * B) := by
  funext v
  simp [matrixVecEnd, Function.End.mul_def, mulVec_mulVec]

/-!
## Weak Pauli plaquette: non-abelian holonomy ≠ identity
-/

noncomputable section

/-- Complex `2 × 2` transport on the weak doublet (`Fin 2 → ℂ`). -/
def weakMatrixVecEnd (M : Matrix (Fin 2) (Fin 2) ℂ) : Function.End (Fin 2 → ℂ) :=
  matrixVecEnd ℂ M

/-- Standard ladder plaquette: `σ⁺`, `σ⁻`, then identity on the remaining two edges. -/
def weakPauliPlaquetteEdge : PlaquetteEdge (Fin 2 → ℂ) :=
  fun i =>
    match i with
    | 0 => weakMatrixVecEnd weakPauliPlus
    | 1 => weakMatrixVecEnd weakPauliMinus
    | _ => 1

theorem weakPauli_matrix_product_ne_identity :
    weakPauliPlus * weakPauliMinus ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have h11 := congrArg (fun M => M 1 1) h
  simp [weakPauliPlus, weakPauliMinus, Matrix.of_apply] at h11

theorem weakPauliPlaquette_holonomy_apply (v : Fin 2 → ℂ) :
    (discreteSquareHolonomy weakPauliPlaquetteEdge) v =
      (weakPauliPlus * weakPauliMinus).mulVec v := by
  unfold discreteSquareHolonomy weakPauliPlaquetteEdge weakMatrixVecEnd matrixVecEnd
  simp [Function.End.mul_def, mulVec_mulVec]

theorem weakPauliPlaquette_edges_noncommuting :
    weakPauliPlus * weakPauliMinus ≠ weakPauliMinus * weakPauliPlus := by
  intro h
  have hz : weakPauliZ3 ≠ 0 := by
    intro hz0
    have h00 := congrArg (fun M => M 0 0) hz0
    simp [weakPauliZ3, Matrix.of_apply] at h00
  have hc := weakPauli_ladder_comm
  unfold lieBracketMat₂ at hc
  rw [show weakPauliPlus * weakPauliMinus - weakPauliMinus * weakPauliPlus = 0 from by rw [h, sub_self]] at hc
  exact hz hc.symm

/-!
## Rotated frames: partial measure / readout discharge
-/

/-- **Discharged:** orbital vector readouts used in flyby / fluid charts are `O(3)` invariants. -/
structure RotatedFrameReadoutDischarged : Prop where
  angular_momentum_sq :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (_hR : IsOrthogonal3 R) (f : OrbitalVectorFrame),
      orbitalAngularMomentumSq ⟨R.mulVec f.r, R.mulVec f.v⟩ = orbitalAngularMomentumSq f
  equatorial_fraction :
    ∀ (R : Matrix (Fin 3) (Fin 3) ℝ) (_hR : IsOrthogonal3 R) (L axis : Fin 3 → ℝ),
      equatorialFractionFromAxis (R.mulVec L) (R.mulVec axis) =
        equatorialFractionFromAxis L axis
  abelian_cyclic_defect_flat :
    ∀ (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (x : ℝ),
      (pathHolonomy (List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3])) x - x = 0

theorem rotatedFrameReadoutDischarged_holds : RotatedFrameReadoutDischarged where
  angular_momentum_sq := fun R hR f => orbitalAngularMomentumSq_invariant R hR f
  equatorial_fraction := fun R hR L axis => equatorialFractionFromAxis_invariant R hR L axis
  abelian_cyclic_defect_flat := fun A a x => pathHolonomy_cyclic_linearEnd_sub_id_eq_zero A a x

/-- **Open:** Haar / path-integral measure on rotated charts (Wilson–kinetic equivalence discharged in `ActionHolonomyGlue`). -/
def HaarMeasureOnRotatedChartDischarged : Prop := False

theorem haarMeasureOnRotatedChart_not_discharged :
    ¬ HaarMeasureOnRotatedChartDischarged := id

structure FullNonAbelianHolonomyMeasurePending : Prop where
  rotated_readout : RotatedFrameReadoutDischarged
  rotated_frame_haar_measure : ¬ HaarMeasureOnRotatedChartDischarged

def fullNonAbelianHolonomyMeasurePending_default : FullNonAbelianHolonomyMeasurePending where
  rotated_readout := rotatedFrameReadoutDischarged_holds
  rotated_frame_haar_measure := haarMeasureOnRotatedChart_not_discharged

/-- What is already discharged vs what remains for the TUFT+SM holonomy row. -/
structure NonAbelianHolonomyMeasureProgram where
  so8_plaquette : SO8PlaquetteHolonomyDischarged
  rotated_readout : RotatedFrameReadoutDischarged
  wilson_kinetic : WilsonKineticPlaquetteEquivalenceDischarged
  weak_matrix_product_nontrivial : weakPauliPlus * weakPauliMinus ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  weak_edges_noncommuting : weakPauliPlus * weakPauliMinus ≠ weakPauliMinus * weakPauliPlus
  plaquette_holonomy_formula : ∀ v, (discreteSquareHolonomy weakPauliPlaquetteEdge) v =
    (weakPauliPlus * weakPauliMinus).mulVec v
  pending : FullNonAbelianHolonomyMeasurePending

theorem nonAbelianHolonomyMeasureProgram_default : NonAbelianHolonomyMeasureProgram where
  so8_plaquette := so8PlaquetteHolonomyDischarged_holds
  rotated_readout := rotatedFrameReadoutDischarged_holds
  wilson_kinetic := wilsonKineticPlaquetteEquivalence_discharged
  weak_matrix_product_nontrivial := weakPauli_matrix_product_ne_identity
  weak_edges_noncommuting := weakPauliPlaquette_edges_noncommuting
  plaquette_holonomy_formula := weakPauliPlaquette_holonomy_apply
  pending := fullNonAbelianHolonomyMeasurePending_default

end

end Hqiv.Physics
