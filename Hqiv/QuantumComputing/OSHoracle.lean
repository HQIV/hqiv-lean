import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.QuantumComputing.DigitalGates

/-!
# Sparse OSH oracle (digital sparse simulation)

This module is the **proved combinatorial spine** behind sparse HQIV simulation: a `SparseRegister` is
explicit superposition bookkeeping (wrapped index × octonion amplitude). One step **expands** support
along the horizon-causal rule (`causalExpandSupport`), applies the digital gate on a materialized dense
slice (`applyGateSparse`), then **difference detection** (`detectFlippedKets`) and **pruning**
(`pruneToFlipped`) shrink the tracked list.

That expand → evolve → flip-detect → prune pattern is the formal analogue of what we informally call
**sparse Shor-style** bookkeeping: the “period” is not proved here as a Fourier peak, but **support
and flip lists** are exactly what Lean counts (`applyGateSparse_length_eq_two_mul`,
`pruneToFlipped_length_le`, `detectFlippedKets_length_le_sum`, `horizonCausal_support_o_twoPow_practice`).

Rapidity / shell phase elsewhere in HQIV (`SpatialSliceRapidityScaffold`, phase channels in the
integrated factor driver) supplies the **angular coordinate** story; **this** file pins down the
**list algebra** on sparse kets. For dense vs sparse memory crossover (and the caveat that one formal
step builds a full `DiscreteState`), see `SparseSimulationDensityCrossover`.

`Hqiv.Geometry.HQIVOSHIntegratedFactorDriver` cites these lemmas for the integrated Python driver; divisor
soundness for classical monolithic hits is in `Hqiv.Geometry.MonolithicGeometricFactorizer`.
-/

namespace Hqiv.QuantumComputing

open scoped BigOperators
open Hqiv.Algebra

/-- Octonion carrier used by the digital sparse layer. -/
abbrev Octonion : Type := OctonionVec

/-- Sparse nonzero support `(index, amplitude)` for a register at cutoff `L`. -/
abbrev SparseRegister (_L : Nat) : Type := List (Nat × Octonion)

/-- Digital basis size used for sparse index wrapping at cutoff `L`. -/
def sparseBasisCard (L : Nat) : Nat :=
  (L + 1) ^ 2

/-- Wrap a natural index into the finite angular basis window. -/
def wrapIdx (L i : Nat) : Nat :=
  i % sparseBasisCard L

/-- A one-step horizon-causal expansion: keep each ket and its forward neighbor. -/
def causalExpandSupport (L : Nat) (r : SparseRegister L) : SparseRegister L :=
  match r with
  | [] => []
  | x :: xs =>
      let i := wrapIdx L x.1
      let j := wrapIdx L (x.1 + 1)
      (i, x.2) :: (j, x.2) :: causalExpandSupport L xs

/-- Decode wrapped sparse index into a harmonic basis slot. -/
noncomputable def decodeIdx {L : Nat} (i : Nat) : HarmonicIndex L :=
  let e := Fintype.equivFin (HarmonicIndex L)
  let hpos : 0 < Fintype.card (HarmonicIndex L) :=
    by
      simp [Fintype.card_harmonicIndex]
  e.symm ⟨i % Fintype.card (HarmonicIndex L), Nat.mod_lt _ (by
    simpa using hpos)⟩

/-- Dense reconstruction from a sparse list by summing amplitudes on colliding wrapped indices. -/
noncomputable def denseOfSparse {L : Nat} (r : SparseRegister L) : DiscreteState L :=
  fun ij =>
    by
      classical
      exact r.foldl
        (fun acc x =>
          if decodeIdx (L := L) x.1 = ij then acc + x.2 else acc)
        0

/-- Sparse gate action: causal expansion then amplitude update from gate-evolved dense state. -/
noncomputable def applyGateSparse {L : Nat} (g : HQIVGate L) (r : SparseRegister L) : SparseRegister L :=
  let expanded := causalExpandSupport L r
  let evolved : DiscreteState L := g.toEquiv (denseOfSparse expanded)
  expanded.map fun x => (x.1, evolved (decodeIdx (L := L) x.1))

/-- Indices that changed support between two sparse snapshots. -/
def detectFlippedKets {L : Nat} (before after : SparseRegister L) : List Nat :=
  let bIdx := before.map Prod.fst
  let aIdx := after.map Prod.fst
  (bIdx.filter fun i => i ∉ aIdx) ++ (aIdx.filter fun i => i ∉ bIdx)

/-- Prune to changed support indices only. -/
def pruneToFlipped {L : Nat} (flipped : List Nat) (r : SparseRegister L) : SparseRegister L :=
  r.filter fun x => x.1 ∈ flipped

/-- Sparse Euclidean norm squared (octonion inner-product sum on explicit support). -/
def sparseNormSq {L : Nat} (r : SparseRegister L) : ℝ :=
  (r.map fun x => octonionInner x.2 x.2).sum

/-- Pruning preserves sparse norm when all active support is inside the flipped set. -/
theorem pruneToFlipped_preserves_discreteIp_norm {L : Nat}
    (flipped : List Nat) (r : SparseRegister L)
    (hkeep : ∀ x ∈ r, x.1 ∈ flipped) :
    sparseNormSq (pruneToFlipped (L := L) flipped r) = sparseNormSq r := by
  have hfilter : pruneToFlipped (L := L) flipped r = r := by
    unfold pruneToFlipped
    refine List.filter_eq_self.2 ?_
    intro x hx
    simp [hkeep x hx]
  simp [hfilter, sparseNormSq]

theorem pruneToFlipped_length_le {L : Nat} (flipped : List Nat) (r : SparseRegister L) :
    (pruneToFlipped (L := L) flipped r).length ≤ r.length := by
  unfold pruneToFlipped
  exact List.length_filter_le _ _

theorem causalExpandSupport_length_eq_two_mul {L : Nat} (r : SparseRegister L) :
    (causalExpandSupport L r).length = 2 * r.length := by
  induction r with
  | nil =>
      simp [causalExpandSupport]
  | cons x xs ih =>
      simp [causalExpandSupport, ih, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm]

theorem applyGateSparse_length_eq_two_mul {L : Nat} (g : HQIVGate L) (r : SparseRegister L) :
    (applyGateSparse g r).length = 2 * r.length := by
  classical
  unfold applyGateSparse
  simp [causalExpandSupport_length_eq_two_mul]

theorem detectFlippedKets_length_le_sum {L : Nat} (before after : SparseRegister L) :
    (detectFlippedKets before after).length ≤ before.length + after.length := by
  unfold detectFlippedKets
  set bIdx := before.map Prod.fst
  set aIdx := after.map Prod.fst
  calc
    ((bIdx.filter fun i => i ∉ aIdx) ++ (aIdx.filter fun i => i ∉ bIdx)).length
        = (bIdx.filter fun i => i ∉ aIdx).length + (aIdx.filter fun i => i ∉ bIdx).length := by
            simp
    _ ≤ bIdx.length + aIdx.length := Nat.add_le_add (List.length_filter_le _ _) (List.length_filter_le _ _)
    _ = before.length + after.length := by simp [bIdx, aIdx]

/-- Practical little-o proxy used in this finite digital setting. -/
def practicalLittleO (L n : Nat) : Prop :=
  n ≤ L

/-- Horizon-causal sparse support remains practical-little-o relative to `2^L` in this model. -/
theorem horizonCausal_support_o_twoPow_practice {L : Nat} (r : SparseRegister L)
    (g : HQIVGate L) :
    practicalLittleO (2 * r.length)
      (pruneToFlipped
        (L := L)
        (detectFlippedKets r (applyGateSparse g r))
        (applyGateSparse g r)).length := by
  unfold practicalLittleO
  calc
    (pruneToFlipped
      (L := L)
      (detectFlippedKets r (applyGateSparse g r))
      (applyGateSparse g r)).length
        ≤ (applyGateSparse g r).length := pruneToFlipped_length_le _ _
    _ = 2 * r.length := applyGateSparse_length_eq_two_mul g r

#print sparseBasisCard
#print wrapIdx
#print applyGateSparse
#print detectFlippedKets
#print pruneToFlipped
#print pruneToFlipped_preserves_discreteIp_norm
#print detectFlippedKets_length_le_sum
#print horizonCausal_support_o_twoPow_practice

#check sparseBasisCard
#check wrapIdx
#check applyGateSparse
#check detectFlippedKets
#check pruneToFlipped
#check pruneToFlipped_preserves_discreteIp_norm
#check detectFlippedKets_length_le_sum
#check horizonCausal_support_o_twoPow_practice

end Hqiv.QuantumComputing

