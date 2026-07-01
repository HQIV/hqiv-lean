import Hqiv.Algebra.OctonionBasics
import Hqiv.Algebra.G2Embedding
import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.HamiltonianToGateMapping
import Hqiv.Story.S3OctonionicAssociatorChannel
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions
import Hqiv.QuantumMechanics.BornMeasurementFinite
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

/-!
# Fano Associator Network — merge pulse sequence and Hamiltonian lift

Certified Tier~II FAN merge-order protocol for the carrier-vs-real-QM experiment
(`papers/carrier_vs_real_quantum/`).

Three Fano ports tagged `e₁`, `e₂`, `e₄` merge into an eight-level product register `R`
by sequential octonion multiplication. Right-append `acc ↦ acc * e_k` and left-prepend
`acc ↦ e_k * acc` implement the two parenthesis topologies; the parenthesis register
`H` records which pair merged first.

Prepend ticks lift to `H_prepend(k) = ω · L(e_k)` with antisymmetric generators from
`G2Embedding.leftMul_matrix_skew`. Monogamy budget at lock-in: `η_φ = 1/30`.

The **near-term quantum-computer experiment** (`fanQc*`) uses three logical qubits,
two primitive merge gates per shot, and Born readout—no composite `L(p)`/`L(q)` gates.
-/

namespace Hqiv.QM.FanoMerge

open Hqiv.Algebra Hqiv.Story Hqiv.QuantumComputing Hqiv.Geometry Hqiv.QM

/-! ## Fano port tags and merge primitives -/

def fanoTagE1 : Fin 8 := 1
def fanoTagE2 : Fin 8 := 2
def fanoTagE4 : Fin 8 := 4

/-- Right-append merge: `acc ↦ acc * e_tag`. -/
def fanMergeAppend (tag : Fin 8) (acc : OctonionVec) : OctonionVec :=
  leftMulVec acc (octonionBasis tag)

/-- Left-prepend merge: `acc ↦ e_tag * acc`. -/
def fanMergePrepend (tag : Fin 8) (acc : OctonionVec) : OctonionVec :=
  leftMulByBasis tag acc

inductive FanMergeOp where
  | append (tag : Fin 8)
  | prepend (tag : Fin 8)
deriving DecidableEq

def fanApplyMergeOp : FanMergeOp → OctonionVec → OctonionVec
  | .append tag, acc => fanMergeAppend tag acc
  | .prepend tag, acc => fanMergePrepend tag acc

def fanRunMergeOps (ops : List FanMergeOp) (acc : OctonionVec) : OctonionVec :=
  ops.foldl (fun v op => fanApplyMergeOp op v) acc

/-! ## Tier~II pulse schedules -/

def fanLeftMergeOps : List FanMergeOp :=
  [.append fanoTagE2, .append fanoTagE4]

def fanRightMergeOps : List FanMergeOp :=
  [.append fanoTagE4, .prepend fanoTagE1]

def fanLeftFinal : OctonionVec :=
  fanRunMergeOps fanLeftMergeOps e1

def fanRightFinal : OctonionVec :=
  fanRunMergeOps fanRightMergeOps e2

def fanEffectiveLeftUnit : OctonionVec := fanLeftFinal
def fanEffectiveRightUnit : OctonionVec := fanRightFinal

theorem fanLeftFinal_eq_neg_e3 : fanLeftFinal = -e3 := by
  unfold fanLeftFinal fanRunMergeOps fanLeftMergeOps fanApplyMergeOp fanMergeAppend
    fanoTagE2 fanoTagE4
  dsimp only [List.foldl, fanoTagE2, fanoTagE4]
  change leftMulVec (leftMulVec e1 e2) e4 = -e3
  rw [e1_mul_e2, e7_mul_e4]

theorem fanRightFinal_eq_e4 : fanRightFinal = e4 := by
  unfold fanRightFinal fanRunMergeOps fanRightMergeOps fanApplyMergeOp fanMergeAppend
    fanMergePrepend fanoTagE4 fanoTagE1
  dsimp only [List.foldl, fanoTagE4, fanoTagE1]
  change leftMulByBasis 1 (leftMulVec e2 e4) = e4
  rw [e2_mul_e4]
  have hneg : leftMulByBasis 1 (-e5) = - leftMulVec e1 e5 := by
    rw [← leftMulVec_octonionBasis 1, leftMulVec_neg_right, e1]
  rw [hneg, e1_mul_e5, neg_neg]

theorem fanLeftRight_difference_eq_associator :
    fanLeftFinal - fanRightFinal = octonionAssociator e1 e2 e4 := by
  rw [fanLeftFinal_eq_neg_e3, fanRightFinal_eq_e4]
  unfold octonionAssociator
  rw [e1_mul_e2, e7_mul_e4, e2_mul_e4, leftMulVec_neg_right, e1_mul_e5, neg_neg]

theorem fanEffectiveUnits_ne : fanEffectiveLeftUnit ≠ fanEffectiveRightUnit := by
  intro h
  have h0 : fanLeftFinal - fanRightFinal = (0 : OctonionVec) := by
    rw [← fanEffectiveLeftUnit, ← fanEffectiveRightUnit, h, sub_self]
  rw [fanLeftRight_difference_eq_associator, octonionAssociator_e1_e2_e4] at h0
  have nz : (-e3 - e4) ≠ 0 := by
    intro hz
    have h3 := congrArg (fun v => v 3) hz
    dsimp at h3
    have lhs : (-e3 - e4) 3 = (-1 : ℝ) := by
      have he3 : (e3) 3 = 1 := by
        unfold e3 octonionBasis
        simp [if_pos (by decide : (3 : Fin 8) = 3)]
      have he4 : (e4) 3 = 0 := by
        unfold e4 octonionBasis
        simp [if_neg (by decide : (3 : Fin 8) ≠ 4)]
      rw [Pi.sub_apply, Pi.neg_apply, he3, he4]
      norm_num
    rw [lhs] at h3
    have rhs : (0 : OctonionVec) 3 = (0 : ℝ) := rfl
    rw [rhs] at h3
    norm_num at h3
  exact nz h0

/-! ## Parenthesis register and pulse metadata -/

abbrev FanParenRegister := Fin 2

inductive FanParenLabel
  | start
  | merged12
  | merged24
deriving DecidableEq

structure FanMergePulseTick where
  op : FanMergeOp
  parenWrite : FanParenLabel
  omega : ℝ
  tau : ℝ

/-- Left topology: merge `(P₁,P₂)` then `P₄`. -/
def fanLeftPulseSchedule : List FanMergePulseTick := [
  { op := .append fanoTagE2, parenWrite := .merged12, omega := 1, tau := 0 },
  { op := .append fanoTagE4, parenWrite := .start, omega := 1, tau := 0 }
]

/-- Right topology: merge `(P₂,P₄)` then prepend `P₁`. -/
def fanRightPulseSchedule : List FanMergePulseTick := [
  { op := .append fanoTagE4, parenWrite := .merged24, omega := 1, tau := 0 },
  { op := .prepend fanoTagE1, parenWrite := .start, omega := 1, tau := 0 }
]

def fanRightAppendOnlyOps : List FanMergeOp :=
  [.append fanoTagE4, .append fanoTagE1]

def fanRightAppendOnlyFinal : OctonionVec :=
  fanRunMergeOps fanRightAppendOnlyOps e2

/-! ## Hamiltonian generators (continuum lift) -/

def fanPrependHamiltonian (omega : ℝ) (tag : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  omega • leftMulMatrix tag

theorem fanPrependGate_eq (tag : Fin 8) (acc : OctonionVec) :
    fanMergePrepend tag acc =
      (fanPrependHamiltonian 1 tag).mulVec acc := by
  show leftMulByBasis tag acc = (1 • leftMulMatrix tag).mulVec acc
  rw [one_smul, leftMulByBasis_eq_mulVec]

theorem fanPrependHamiltonian_skew {tag : Fin 8} (ht : tag ≠ 0) (omega : ℝ) :
    (fanPrependHamiltonian omega tag).transpose = - fanPrependHamiltonian omega tag := by
  unfold fanPrependHamiltonian
  rw [Matrix.transpose_smul]
  have htrans : (leftMulMatrix tag).transpose = - leftMulMatrix tag :=
    (neg_eq_iff_add_eq_zero.mpr (leftMul_matrix_skew tag ht)).symm
  rw [htrans, smul_neg]

/-! ## Monogamy budget at lock-in (referenceM = 4) -/

theorem fanMerge_etaPhi_lockin :
    etaModePhi referenceM = 1 / 30 := by
  rw [etaModePhi_constant referenceM, referenceM_eq_four_lightcone]
  norm_num

/-! ## Tier~I: effective units differ, hence so do the table operators -/

/-- Tier~I uses `L(p)` and `L(q)` with `p ≠ q`; the effective units differ. -/
theorem fanTierOne_effective_units_ne : fanEffectiveLeftUnit ≠ fanEffectiveRightUnit :=
  fanEffectiveUnits_ne

theorem fanAssociator_norm_sq :
    octonionAssociatorNormSq e1 e2 e4 = 2 :=
  octonionAssociatorNormSq_e1_e2_e4

/-! ## Near-term quantum-computer experiment (single-cycle primitive gates) -/

/-- Experimental arms: L topology, R topology, append-only null on tick~2. -/
inductive FanQcArm where
  | leftTopology
  | rightTopology
  | rightAppendOnlyNull
deriving DecidableEq, Repr

def fanQcInitState : FanQcArm → OctonionVec
  | .leftTopology => e1
  | .rightTopology => e2
  | .rightAppendOnlyNull => e2

def fanQcMergeOps : FanQcArm → List FanMergeOp
  | .leftTopology => fanLeftMergeOps
  | .rightTopology => fanRightMergeOps
  | .rightAppendOnlyNull => fanRightAppendOnlyOps

def fanQcFinalState (arm : FanQcArm) : OctonionVec :=
  fanRunMergeOps (fanQcMergeOps arm) (fanQcInitState arm)

theorem fanQcFinalState_left : fanQcFinalState .leftTopology = fanLeftFinal := rfl
theorem fanQcFinalState_right : fanQcFinalState .rightTopology = fanRightFinal := rfl
theorem fanQcFinalState_null : fanQcFinalState .rightAppendOnlyNull = fanRightAppendOnlyFinal := rfl

def fanQcPrimitiveAlphabet : List FanMergeOp := [
  .append fanoTagE1, .append fanoTagE2, .append fanoTagE4,
  .prepend fanoTagE1, .prepend fanoTagE2, .prepend fanoTagE4
]

theorem fanQcMergeGateCount (arm : FanQcArm) : (fanQcMergeOps arm).length = 2 := by
  cases arm <;> rfl

noncomputable def fanOctonionBornProb (ψ : OctonionVec) (a : Fin 8) : ℝ :=
  bornProbN (n := 8) ψ a

private lemma octonionBasis_normSq (a : Fin 8) :
    normSq (n := 8) (octonionBasis a) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single a]
  · simp [octonionBasis]
  · intro b _ hb; simp [octonionBasis, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma normSq_neg (ψ : OctonionVec) : normSq (n := 8) (-ψ) = normSq (n := 8) ψ := by
  unfold normSq
  rw [Finset.sum_congr rfl fun i _ => by show (-ψ i) ^ 2 = (ψ i) ^ 2; ring]

private lemma bornProb_neg_vec (ψ : OctonionVec) (b : Fin 8) :
    fanOctonionBornProb (-ψ) b = fanOctonionBornProb ψ b := by
  unfold fanOctonionBornProb bornProbN bornWeight
  congr 1
  · show (-ψ b) ^ 2 = (ψ b) ^ 2; ring
  · rw [normSq_neg]

theorem fanOctonionBornProb_basis (a b : Fin 8) :
    fanOctonionBornProb (octonionBasis a) b = if a = b then 1 else 0 := by
  unfold fanOctonionBornProb bornProbN bornWeight
  rw [octonionBasis_normSq a, div_one]
  split_ifs with h
  · subst h; simp [octonionBasis]
  · have hb : b ≠ a := Ne.symm h
    have hz : octonionBasis a b = 0 := by simp [octonionBasis, hb]
    simp [hz]

theorem fanOctonionBornProb_neg_e3_at3 : fanOctonionBornProb (-e3) 3 = 1 := by
  rw [show (-e3) = -octonionBasis 3 from by unfold e3; rfl]
  rw [bornProb_neg_vec (octonionBasis 3) 3, fanOctonionBornProb_basis 3 3, if_pos rfl]

theorem fanOctonionBornProb_neg_e3_at4 : fanOctonionBornProb (-e3) 4 = 0 := by
  rw [show (-e3) = -octonionBasis 3 from by unfold e3; rfl]
  rw [bornProb_neg_vec (octonionBasis 3) 4, fanOctonionBornProb_basis 3 4]
  rfl

theorem fanOctonionBornProb_e4_at4 : fanOctonionBornProb e4 4 = 1 := by
  rw [show e4 = octonionBasis 4 from rfl, fanOctonionBornProb_basis 4 4, if_pos rfl]

theorem fanQcLeft_born_peak3 :
    fanOctonionBornProb (fanQcFinalState .leftTopology) 3 = 1 := by
  rw [fanQcFinalState_left, fanLeftFinal_eq_neg_e3, fanOctonionBornProb_neg_e3_at3]

theorem fanQcRight_born_peak4 :
    fanOctonionBornProb (fanQcFinalState .rightTopology) 4 = 1 := by
  rw [fanQcFinalState_right, fanRightFinal_eq_e4, fanOctonionBornProb_e4_at4]

noncomputable def fanQcDeltaP_paren_index (a : Fin 8) : ℝ :=
  |fanOctonionBornProb (fanQcFinalState .leftTopology) a -
    fanOctonionBornProb (fanQcFinalState .rightTopology) a|

theorem fanQcDeltaP_paren_index4_eq_one : fanQcDeltaP_paren_index 4 = 1 := by
  unfold fanQcDeltaP_paren_index
  rw [fanQcFinalState_left, fanQcFinalState_right,
    fanLeftFinal_eq_neg_e3, fanRightFinal_eq_e4,
    fanOctonionBornProb_neg_e3_at4, fanOctonionBornProb_e4_at4]
  norm_num

theorem fanQcDeltaP_paren_pos : 0 < fanQcDeltaP_paren_index 4 := by
  rw [fanQcDeltaP_paren_index4_eq_one]; norm_num

theorem fanRightAppendOnlyFinal_ne_fanRightFinal :
    fanRightAppendOnlyFinal ≠ fanRightFinal := by
  rw [fanRightFinal_eq_e4]
  intro h
  have h4 := congrFun h 4
  unfold fanRightAppendOnlyFinal fanRunMergeOps fanRightAppendOnlyOps
    fanApplyMergeOp fanMergeAppend fanoTagE4 fanoTagE1 at h4
  dsimp only [List.foldl, fanoTagE4, fanoTagE1] at h4
  change leftMulVec (leftMulVec e2 e4) e1 4 = e4 4 at h4
  rw [e2_mul_e4] at h4
  have hneg : leftMulVec (-e5) e1 = -leftMulVec e5 e1 := by
    ext i
    rw [← neg_one_smul ℝ e5, ← neg_one_smul ℝ (leftMulVec e5 e1), leftMulVec_smul_left]
  rw [congrFun hneg 4] at h4
  have h51 := congrFun (leftMulVec_basis_basis 5 1) 4
  have he51 : (leftMulVec e5 e1) 4 = 1 := by
    simpa [e5, e1] using h51
  have he44 : (e4 4 : ℝ) = 1 := by simp [e4, octonionBasis]
  rw [Pi.neg_apply, he51, he44] at h4
  norm_num at h4

theorem fanQcNull_differs_from_right :
    fanQcFinalState .rightAppendOnlyNull ≠ fanQcFinalState .rightTopology := by
  rw [fanQcFinalState_null, fanQcFinalState_right]
  exact fanRightAppendOnlyFinal_ne_fanRightFinal

def fanOctonionBasisCount : ℕ := 8
def fanQcProductRegisterQubits : ℕ := 3

theorem fanQcProductRegister_qubits_eq :
    fanOctonionBasisCount = 2 ^ fanQcProductRegisterQubits := by native_decide

def fanQcMergeCoreLogicalQubits : ℕ := fanQcProductRegisterQubits
def fanQcWithRenouLogicalQubits : ℕ := 28

theorem fanQcWithin64LogicalQubits : fanQcWithRenouLogicalQubits ≤ 64 := by decide

/-- `APPEND(k)` as an 8×8 matrix: `v ↦ v * e_k`. -/
def fanAppendMatrix (tag : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => (leftMulMatrix j) i tag

private lemma leftMulVec_right_basis (tag : Fin 8) (v : OctonionVec) (i : Fin 8) :
    leftMulVec v (octonionBasis tag) i = ∑ k, leftMulMatrix k i tag * v k := by
  simp only [leftMulVec, octonionBasis]
  rw [Finset.sum_eq_single tag]
  · rw [if_pos rfl, mul_one]
  · intro j _ hj; simp [hj]
  · intro ht; exact absurd (Finset.mem_univ tag) ht

theorem fanAppendMatrix_mulVec (tag : Fin 8) (v : OctonionVec) :
    (fanAppendMatrix tag).mulVec v = fanMergeAppend tag v := by
  ext i
  simp only [fanMergeAppend, fanAppendMatrix, Matrix.mulVec, dotProduct]
  exact (leftMulVec_right_basis tag v i).symm

theorem fanPrependMatrix_mulVec (tag : Fin 8) (v : OctonionVec) :
    (leftMulMatrix tag).mulVec v = fanMergePrepend tag v :=
  leftMulByBasis_eq_mulVec tag v

structure FanQcSingleCycleShot where
  arm : FanQcArm
deriving Repr

def fanQcShotFinal (shot : FanQcSingleCycleShot) : OctonionVec :=
  fanQcFinalState shot.arm

end Hqiv.QM.FanoMerge
