import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Option.Basic

import RhFourierLift.Setup

import Hqiv.Topology.DiscreteNullLatticeComplex
import Hqiv.Topology.DiscretePhaseEvolution
import Hqiv.Topology.SignedShellBudget
import Hqiv.Topology.HopfShellComplex   -- T6/T7/T9 wiring (Hopf shells as discrete complexes + PhaseMap holonomy carriers)
import Hqiv.Algebra.PhaseLiftDelta

/-!
# Shell opening evolution (Phase 2)

Insert one **null-shell vertex** on the smallest active shell with negative budget
(`shellBudgetMismatch < 0`). Vertex-only complexes (`IsVertexOnly`) only; edges and
higher cells stay empty.

**Measure:** `totalNegativeBudget` (full active range) strictly decreases on each `some`
step; `totalEarlyNegativeBudget` decreases when it is positive (smallest negative shell
lies in `m ≤ 2`).
-/

namespace Hqiv.Topology

open Hqiv Hqiv.Geometry RhFourierLift Classical
open Matrix
open scoped BigOperators

/-!
## Insert one vertex (vertex-only)
-/

/-- Insert a null-shell vertex, preserving the vertex-only skeleton. -/
def insertNullShellVertex (M : Discrete3Complex NullShellVertex) (v : NullShellVertex)
    (hv : v ∉ M.vertices) (hV : IsVertexOnly M) : Discrete3Complex NullShellVertex :=
  { vertices := insert v M.vertices
    edges := ∅
    triangles := ∅
    tetrahedra := ∅
    edge_closed := by
      rcases hV with ⟨_, _, _⟩
      simp }

theorem insertNullShellVertex_isVertexOnly (M : Discrete3Complex NullShellVertex)
    (v : NullShellVertex) (hv : v ∉ M.vertices) (hV : IsVertexOnly M) :
    IsVertexOnly (insertNullShellVertex M v hv hV) := by
  dsimp [insertNullShellVertex, IsVertexOnly]
  simp

theorem mem_insertNullShellVertex_vertices {M v hv hV w} :
    w ∈ (insertNullShellVertex M v hv hV).vertices ↔ w = v ∨ w ∈ M.vertices := by
  simp [insertNullShellVertex]

theorem insertNullShellVertex_self_mem (M v hv hV) :
    v ∈ (insertNullShellVertex M v hv hV).vertices :=
  Finset.mem_insert_self _ _

theorem maxVertexShell_insert (M : Discrete3Complex NullShellVertex) (v : NullShellVertex)
    (hv : v ∉ M.vertices) (hV : IsVertexOnly M) :
    maxVertexShell (insertNullShellVertex M v hv hV) =
      max (maxVertexShell M) v.shell := by
  dsimp [insertNullShellVertex, maxVertexShell]
  simp only [Finset.sup_insert, hv, max_comm]

theorem activeShellRange_insert_of_shell_le (M : Discrete3Complex NullShellVertex)
    (v : NullShellVertex) (hv : v ∉ M.vertices) (hV : IsVertexOnly M)
    (hle : v.shell ≤ maxVertexShell M) :
    activeShellRange (insertNullShellVertex M v hv hV) = activeShellRange M := by
  unfold activeShellRange
  rw [maxVertexShell_insert, max_comm, max_eq_right hle]

/-!
## Unused tags on a shell
-/

/-- Tags on shell `m` not yet occupied in `M`. -/
noncomputable def unusedTagsAtShell (M : Discrete3Complex NullShellVertex) (m : ℕ) :
    Finset (Fin (latticeSimplexCount m)) :=
  Finset.univ.filter fun t : Fin (latticeSimplexCount m) =>
    (⟨m, t⟩ : NullShellVertex) ∉ M.vertices

theorem mem_unusedTagsAtShell_iff {M m t} :
    t ∈ unusedTagsAtShell M m ↔ (⟨m, t⟩ : NullShellVertex) ∉ M.vertices := by
  simp [unusedTagsAtShell]

theorem negativeBudget_vertexCount_lt (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) : Discrete3Complex.vertexCountAtShell M m < latticeSimplexCount m := by
  simp only [shellBudgetMismatch, negativeBudget] at h
  exact_mod_cast (show (Discrete3Complex.vertexCountAtShell M m : ℤ) < latticeSimplexCount m from by omega)

theorem exists_unused_tag (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) :
    ∃ t : Fin (latticeSimplexCount m), (⟨m, t⟩ : NullShellVertex) ∉ M.vertices := by
  classical
  by_contra hall
  push_neg at hall
  have hall' : ∀ t, (⟨m, t⟩ : NullShellVertex) ∈ M.vertices := hall
  have hinj : Function.Injective fun t : Fin (latticeSimplexCount m) => (⟨m, t⟩ : NullShellVertex) :=
    fun t₁ t₂ hEq => by cases hEq; rfl
  have hsub :
      (Finset.univ : Finset (Fin (latticeSimplexCount m))).image
          (fun t => (⟨m, t⟩ : NullShellVertex)) ⊆
        M.vertices.filter (fun v : NullShellVertex => v.shell = m) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨t, _, rfl⟩
    exact Finset.mem_filter.mpr ⟨hall' t, rfl⟩
  have hcard_le :
      latticeSimplexCount m ≤
        (M.vertices.filter (fun v : NullShellVertex => v.shell = m)).card := by
    have hcard_image :
        ((Finset.univ : Finset (Fin (latticeSimplexCount m))).image
            (fun t => (⟨m, t⟩ : NullShellVertex))).card =
          latticeSimplexCount m := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    calc
      latticeSimplexCount m =
          ((Finset.univ : Finset (Fin (latticeSimplexCount m))).image
            (fun t => (⟨m, t⟩ : NullShellVertex))).card := hcard_image.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcount := negativeBudget_vertexCount_lt M m h
  unfold Discrete3Complex.vertexCountAtShell at hcount
  omega

theorem unusedTagsAtShell_nonempty (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) :
    (unusedTagsAtShell M m).Nonempty := by
  rcases exists_unused_tag M m h with ⟨t, ht⟩
  exact ⟨t, (mem_unusedTagsAtShell_iff (m := m)).mpr ht⟩

/-- Smallest unused tag on an under-occupied shell. -/
noncomputable def minUnusedTagAtShell (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) : Fin (latticeSimplexCount m) :=
  (unusedTagsAtShell M m).min' (unusedTagsAtShell_nonempty M m h)

theorem minUnusedTagAtShell_mem (M m h) :
    minUnusedTagAtShell M m h ∈ unusedTagsAtShell M m :=
  Finset.min'_mem _ _

theorem minUnusedTag_vertex_not_mem (M m h) :
    (⟨m, minUnusedTagAtShell M m h⟩ : NullShellVertex) ∉ M.vertices :=
  (mem_unusedTagsAtShell_iff (m := m)).mp (minUnusedTagAtShell_mem M m h)

/-!
## Opening shell selection
-/

/-- Active shells with negative budget. -/
noncomputable def negativeActiveShells (M : Discrete3Complex NullShellVertex) : Finset ℕ :=
  Finset.filter (negativeBudget M) (activeShellRange M)

theorem mem_negativeActiveShells {M m} :
    m ∈ negativeActiveShells M ↔ negativeBudget M m ∧ m ∈ activeShellRange M := by
  simp [negativeActiveShells, activeShellRange, and_comm]

/-- Smallest shell index carrying negative budget (deterministic opening). -/
noncomputable def smallestNegativeShell (M : Discrete3Complex NullShellVertex) : Option ℕ :=
  let s := negativeActiveShells M
  if h : s.Nonempty then some (s.min' h) else none

theorem smallestNegativeShell_eq_none_of_not_nonempty (M : Discrete3Complex NullShellVertex)
    (h : ¬ (negativeActiveShells M).Nonempty) : smallestNegativeShell M = none := by
  by_cases hs : (negativeActiveShells M).Nonempty
  · exact False.elim (h hs)
  · simp [smallestNegativeShell, hs]

theorem smallestNegativeShell_eq_none_iff (M : Discrete3Complex NullShellVertex) :
    smallestNegativeShell M = none ↔ negativeActiveShells M = ∅ := by
  constructor
  · intro hnone
    rcases (negativeActiveShells M).eq_empty_or_nonempty with hempty | ⟨m, hm⟩
    · exact hempty
    · have hs : (negativeActiveShells M).Nonempty := ⟨m, hm⟩
      have hsome : smallestNegativeShell M = some ((negativeActiveShells M).min' hs) := by
        simp only [smallestNegativeShell, hs, dite_true]
      rw [hnone] at hsome
      cases hsome
  · intro hempty
    by_cases hs : (negativeActiveShells M).Nonempty
    · rcases hs with ⟨m, hm⟩
      rw [hempty] at hm
      cases hm
    · simp only [smallestNegativeShell, hs, dite_false]

theorem smallestNegativeShell_mem {M m} (h : smallestNegativeShell M = some m) :
    m ∈ negativeActiveShells M := by
  by_cases hs : (negativeActiveShells M).Nonempty
  · simp only [smallestNegativeShell, hs, dite_true] at h
    rcases Option.some.inj h with rfl
    exact Finset.min'_mem _ hs
  · simp only [smallestNegativeShell, hs, dite_false] at h
    cases h

theorem smallestNegativeShell_spec {M m} (h : smallestNegativeShell M = some m) :
    m ∈ negativeActiveShells M ∧ ∀ m', m' ∈ negativeActiveShells M → m ≤ m' := by
  refine ⟨smallestNegativeShell_mem (M := M) (m := m) h, ?_⟩
  intro m' hm'
  by_cases hs : (negativeActiveShells M).Nonempty
  · have heq : (negativeActiveShells M).min' hs = m :=
      Option.some.inj (by simpa [smallestNegativeShell, hs, dite_true] using h)
    exact ((Finset.min'_eq_iff (negativeActiveShells M) hs m).1 heq).2 m' hm'
  · simp only [smallestNegativeShell, hs, dite_false] at h
    cases h

theorem mem_earlyActive_implies_mem_active {M m} (hm : m ∈ earlyActiveShellRange M) :
    m ∈ activeShellRange M := by
  simp only [earlyActiveShellRange, activeShellRange, Finset.mem_filter, Finset.mem_range] at hm ⊢
  exact hm.1

theorem negativeActiveShells_nonempty_of_totalEarly_pos (M : Discrete3Complex NullShellVertex)
    (h : 0 < totalEarlyNegativeBudget M) : (negativeActiveShells M).Nonempty := by
  by_contra hempty
  have hzero :
      ∀ m ∈ earlyActiveShellRange M,
        (if negativeBudget M m then shellBudgetMismatchNatAbs M m else 0) = 0 := by
    intro m hm
    have : ¬ negativeBudget M m := by
      intro hneg
      have hm' : m ∈ negativeActiveShells M :=
        (mem_negativeActiveShells (M := M) (m := m)).mpr
          ⟨hneg, mem_earlyActive_implies_mem_active hm⟩
      exact hempty ⟨m, hm'⟩
    simp [this]
  have hz : totalEarlyNegativeBudget M = 0 := by
    unfold totalEarlyNegativeBudget
    exact Finset.sum_eq_zero hzero
  rw [hz] at h
  exact Nat.lt_irrefl 0 h

theorem exists_early_negative_shell (M : Discrete3Complex NullShellVertex)
    (hpos : 0 < totalEarlyNegativeBudget M) :
    ∃ k, k ∈ earlyActiveShellRange M ∧ negativeBudget M k := by
  by_contra hnot
  push_neg at hnot
  have hzero :
      ∀ k ∈ earlyActiveShellRange M,
        (if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0) = 0 := by
    intro k hk
    have : ¬ negativeBudget M k := fun hneg => hnot k hk hneg
    simp [this]
  have hz : totalEarlyNegativeBudget M = 0 := by
    unfold totalEarlyNegativeBudget
    exact Finset.sum_eq_zero hzero
  rw [hz] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem smallestNegativeShell_le_two_of_early_pos (M : Discrete3Complex NullShellVertex)
    (hpos : 0 < totalEarlyNegativeBudget M) :
    ∃ m, smallestNegativeShell M = some m ∧ m ≤ 2 := by
  have hne := negativeActiveShells_nonempty_of_totalEarly_pos M hpos
  obtain ⟨m, hsm⟩ : ∃ m, smallestNegativeShell M = some m := by
    refine ⟨(negativeActiveShells M).min' hne, ?_⟩
    dsimp [smallestNegativeShell]
    simp [hne]
  rcases smallestNegativeShell_spec hsm with ⟨hm, hmin⟩
  obtain ⟨k, hk_early, hk_neg⟩ := exists_early_negative_shell M hpos
  have hk_act : k ∈ negativeActiveShells M :=
    (mem_negativeActiveShells (M := M) (m := k)).mpr
      ⟨hk_neg, mem_earlyActive_implies_mem_active hk_early⟩
  refine ⟨m, hsm, (hmin k hk_act).trans ?_⟩
  exact (Finset.mem_filter.mp hk_early).2

theorem totalEarly_summand_le {M m}
    (hmem : m ∈ earlyActiveShellRange M) (hneg : negativeBudget M m) :
    shellBudgetMismatchNatAbs M m ≤ totalEarlyNegativeBudget M := by
  rcases Finset.mem_filter.mp hmem with ⟨hm_act, _⟩
  unfold totalEarlyNegativeBudget
  refine le_trans (le_of_eq (by simp [hneg, ite_true])) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)

theorem totalEarlyNegativeBudget_pos_of_neg_shell (M m)
    (hm : m ∈ negativeActiveShells M) (hm2 : m ≤ 2) :
    0 < totalEarlyNegativeBudget M := by
  rcases mem_negativeActiveShells.mp hm with ⟨hneg, hm_active⟩
  exact Nat.lt_of_lt_of_le (negativeBudget_pos_natAbs M m hneg)
    (totalEarly_summand_le (Finset.mem_filter.mpr ⟨hm_active, hm2⟩) hneg)

/-!
## `shellOpeningStep`
-/

/-- Vertex chosen for insertion on shell `m`. -/
noncomputable def openingVertex (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) : NullShellVertex :=
  ⟨m, minUnusedTagAtShell M m h⟩

theorem activeShellRange_insert_opening (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (m : ℕ) (hneg : negativeBudget M m)
    (hm_act : m ∈ activeShellRange M) :
    activeShellRange
        (insertNullShellVertex M (openingVertex M m hneg)
          (minUnusedTag_vertex_not_mem M m hneg) hV) =
      activeShellRange M := by
  set v := openingVertex M m hneg
  set hv := minUnusedTag_vertex_not_mem M m hneg
  have hmax : v.shell ≤ maxVertexShell M := by
    dsimp [v, openingVertex]
    have : m ≤ maxVertexShell M := by
      simp [activeShellRange, Finset.mem_range] at hm_act
      omega
    exact this
  exact activeShellRange_insert_of_shell_le M v hv hV hmax

/-- Add one null-shell vertex on the smallest `m` with `negativeBudget`, if any. -/
noncomputable def shellOpeningStep (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) :
    Option (Discrete3Complex NullShellVertex) :=
  if h : (negativeActiveShells M).Nonempty then
    let m := (negativeActiveShells M).min' h
    have hneg : negativeBudget M m :=
      (mem_negativeActiveShells.mp (Finset.min'_mem _ h)).1
    have hv : openingVertex M m hneg ∉ M.vertices := minUnusedTag_vertex_not_mem M m hneg
    some (insertNullShellVertex M (openingVertex M m hneg) hv hV)
  else none

theorem shellOpeningStep_eq_smallest (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) :
    shellOpeningStep M hV = none ↔ smallestNegativeShell M = none := by
  unfold shellOpeningStep smallestNegativeShell
  rcases (negativeActiveShells M).eq_empty_or_nonempty with hempty | hs
  · simp [hempty]
  · simp [hs, dite_true]

theorem shellOpeningStep_preserves_vertexOnly (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    {M'} (h : shellOpeningStep M hV = some M') : IsVertexOnly M' := by
  rcases (negativeActiveShells M).eq_empty_or_nonempty with hempty | hs
  · simp [shellOpeningStep, hempty] at h
  · have hdef :
        shellOpeningStep M hV =
          some (insertNullShellVertex M (openingVertex M ((negativeActiveShells M).min' hs)
            (mem_negativeActiveShells.mp (Finset.min'_mem _ hs)).1)
            (minUnusedTag_vertex_not_mem M _ _) hV) := by
      unfold shellOpeningStep
      simp [hs]
    exact (Option.some.inj (h.symm.trans hdef)).symm ▸ insertNullShellVertex_isVertexOnly M _ _ hV

theorem shellOpeningStep_some_eq (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (m : ℕ) (hsn : smallestNegativeShell M = some m) :
    ∃ hneg,
      shellOpeningStep M hV =
        some (insertNullShellVertex M (openingVertex M m hneg)
          (minUnusedTag_vertex_not_mem M m hneg) hV) := by
  rcases mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn) with ⟨hneg, hm_rng⟩
  have hs : (negativeActiveShells M).Nonempty :=
    ⟨m, mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩⟩
  have hmin : (negativeActiveShells M).min' hs = m :=
    Option.some.inj (by simpa [smallestNegativeShell, hs, dite_true] using hsn)
  refine ⟨hneg, ?_⟩
  unfold shellOpeningStep
  simp only [hs, dite_true, hmin]

theorem shellOpeningStep_eq_none_iff (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) :
    shellOpeningStep M hV = none ↔ negativeActiveShells M = ∅ := by
  rw [shellOpeningStep_eq_smallest, smallestNegativeShell_eq_none_iff]

theorem shellBudgetMismatch_insert_same_shell (M v hv hV m)
    (hshell : v.shell = m) :
    shellBudgetMismatch (insertNullShellVertex M v hv hV) m =
      shellBudgetMismatch M m + 1 := by
  unfold shellBudgetMismatch
  have hcount :
      Discrete3Complex.vertexCountAtShell (insertNullShellVertex M v hv hV) m =
        Discrete3Complex.vertexCountAtShell M m + 1 := by
    classical
    unfold Discrete3Complex.vertexCountAtShell insertNullShellVertex
    have hEq :
        (insert v M.vertices).filter (fun w : NullShellVertex => w.shell = m) =
          insert v (M.vertices.filter fun w : NullShellVertex => w.shell = m) := by
      ext w
      by_cases hw : w = v <;> by_cases hwm : w.shell = m <;>
        simp [hw, hwm, Finset.mem_filter, Finset.mem_insert, hshell, hv]
    have hv' : v ∉ M.vertices.filter (fun w : NullShellVertex => w.shell = m) := by
      intro hvfil
      exact hv ((Finset.mem_filter.mp hvfil).1)
    rw [hEq, Finset.card_insert_of_notMem hv']
  rw [hcount]
  push_cast
  ring

theorem shellBudgetMismatch_insert_other_shell (M v hv hV m)
    (hshell : v.shell ≠ m) :
    shellBudgetMismatch (insertNullShellVertex M v hv hV) m =
      shellBudgetMismatch M m := by
  unfold shellBudgetMismatch
  have hcount :
      Discrete3Complex.vertexCountAtShell (insertNullShellVertex M v hv hV) m =
        Discrete3Complex.vertexCountAtShell M m := by
    classical
    unfold Discrete3Complex.vertexCountAtShell insertNullShellVertex
    have hEq :
        (insert v M.vertices).filter (fun w : NullShellVertex => w.shell = m) =
          M.vertices.filter (fun w : NullShellVertex => w.shell = m) := by
      ext w
      by_cases hw : w = v <;> simp [hw, hshell, Finset.mem_filter, Finset.mem_insert]
    rw [hEq]
  rw [hcount]

private theorem int_natAbs_add_one_of_neg (z : ℤ) (hz : z < 0) (hz1 : z ≠ -1) :
    Int.natAbs (z + 1) + 1 = Int.natAbs z := by
  grind

theorem shellBudgetMismatchNatAbs_insert_same_shell_neg (M v hv hV m)
    (hshell : v.shell = m) (hneg : negativeBudget M m) :
    shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) m + 1 =
      shellBudgetMismatchNatAbs M m := by
  unfold shellBudgetMismatchNatAbs negativeBudget at *
  rw [shellBudgetMismatch_insert_same_shell M v hv hV m hshell]
  have hz : shellBudgetMismatch M m < 0 := by simpa [negativeBudget] using hneg
  set z := shellBudgetMismatch M m
  by_cases hz1 : z = -1
  · rw [hz1]
    norm_num [Int.natAbs]
  · exact int_natAbs_add_one_of_neg z hz hz1

theorem shellBudgetMismatchNatAbs_insert_other_shell_unchanged (M v hv hV m)
    (hshell : v.shell ≠ m) :
    shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) m =
      shellBudgetMismatchNatAbs M m := by
  unfold shellBudgetMismatchNatAbs
  rw [shellBudgetMismatch_insert_other_shell M v hv hV m hshell]

private theorem natAbs_add_one_lt_natAbs_of_neg {x : ℤ} (hx : x < 0) :
    (x + 1).natAbs < x.natAbs := by omega

theorem lyapunov_le_of_shellOpeningStep_some (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    {M'} (hstep : shellOpeningStep M hV = some M') :
    lyapunovFunctional M' ≤ lyapunovFunctional M := by
  rcases (negativeActiveShells M).eq_empty_or_nonempty with hempty | hs
  · simp [shellOpeningStep, hempty] at hstep
  · have hdef : shellOpeningStep M hV =
        some (insertNullShellVertex M (openingVertex M ((negativeActiveShells M).min' hs)
          (mem_negativeActiveShells.mp (Finset.min'_mem _ hs)).1)
          (minUnusedTag_vertex_not_mem M _ _) hV) := by
      unfold shellOpeningStep
      simp [hs]
    have hEq := (Option.some.inj (hstep.symm.trans hdef)).symm
    have hle : lyapunovFunctional (insertNullShellVertex M (openingVertex M ((negativeActiveShells M).min' hs)
        (mem_negativeActiveShells.mp (Finset.min'_mem _ hs)).1)
        (minUnusedTag_vertex_not_mem M _ _) hV) ≤ lyapunovFunctional M := by
      simp only [lyapunovFunctional_eq_shell0_budget]
      let m := (negativeActiveShells M).min' hs
      let hneg := (mem_negativeActiveShells.mp (Finset.min'_mem _ hs)).1
      let hv' := minUnusedTag_vertex_not_mem M m hneg
      let ins := insertNullShellVertex M (openingVertex M m hneg) hv' hV
      by_cases hm : m = 0
      · have hb := shellBudgetMismatch_insert_same_shell M (openingVertex M m hneg) hv' hV m rfl
        have hlt : (shellBudgetMismatch ins m).natAbs < (shellBudgetMismatch M m).natAbs := by
          rw [hb]
          exact natAbs_add_one_lt_natAbs_of_neg (by simpa [negativeBudget] using hneg)
        have hle : (shellBudgetMismatch ins 0).natAbs ≤ (shellBudgetMismatch M 0).natAbs := by
          rw [← hm]
          exact le_of_lt hlt
        exact_mod_cast hle
      · have hs0 : (openingVertex M m hneg).shell ≠ 0 := by simpa [openingVertex] using hm
        rw [shellBudgetMismatch_insert_other_shell M (openingVertex M m hneg) hv' hV 0 hs0]
    rw [← congrArg lyapunovFunctional hEq]
    exact hle

theorem negativeBudget_insert_other_shell (M v hv hV m) (hshell : v.shell ≠ m) :
    negativeBudget (insertNullShellVertex M v hv hV) m ↔ negativeBudget M m := by
  unfold negativeBudget
  rw [shellBudgetMismatch_insert_other_shell M v hv hV m hshell]

theorem totalEarlyNegativeBudget_insert_opening_late_shell (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (m : ℕ) (hneg : negativeBudget M m) (hm : 2 < m)
    (hm_act : m ∈ activeShellRange M) :
    totalEarlyNegativeBudget
        (insertNullShellVertex M (openingVertex M m hneg) (minUnusedTag_vertex_not_mem M m hneg) hV) =
      totalEarlyNegativeBudget M := by
  classical
  set v := openingVertex M m hneg
  set hv := minUnusedTag_vertex_not_mem M m hneg
  have hmax : v.shell ≤ maxVertexShell M := by
    simp only [activeShellRange, Finset.mem_range] at hm_act
    exact Nat.le_of_lt_succ hm_act
  have hrng := activeShellRange_insert_of_shell_le M v hv hV hmax
  have hrng_early : earlyActiveShellRange (insertNullShellVertex M v hv hV) =
      earlyActiveShellRange M := by
    simp only [earlyActiveShellRange, hrng]
  unfold totalEarlyNegativeBudget
  rw [hrng_early]
  refine Finset.sum_congr rfl fun k hk => ?_
  rcases Finset.mem_filter.mp hk with ⟨_, hk2⟩
  have hshell' : v.shell ≠ k := by
    dsimp [v, openingVertex]
    intro hsk
    omega
  rw [negativeBudget_insert_other_shell M v hv hV k hshell',
    shellBudgetMismatchNatAbs_insert_other_shell_unchanged M v hv hV k hshell']

private theorem budgetTerm_other_shell (M v hv hV k) (hshell : v.shell ≠ k) :
    (if negativeBudget (insertNullShellVertex M v hv hV) k then
        shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) =
      (if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0) := by
  grind [negativeBudget_insert_other_shell, shellBudgetMismatchNatAbs_insert_other_shell_unchanged]

private theorem budgetTerm_same_shell_zneg (M v hv hV m) (hshell : v.shell = m)
    (hneg : negativeBudget M m) (hins : ¬ negativeBudget (insertNullShellVertex M v hv hV) m) :
    (if negativeBudget (insertNullShellVertex M v hv hV) m then
        shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) m else 0) +
      (if m = m then 1 else 0) =
    (if negativeBudget M m then shellBudgetMismatchNatAbs M m else 0) := by
  unfold negativeBudget at hins hneg ⊢
  have hz1 : shellBudgetMismatch M m = -1 := by
    rw [shellBudgetMismatch_insert_same_shell M v hv hV m hshell] at hins
    omega
  have hrs : shellBudgetMismatchNatAbs M m = 1 := by
    unfold shellBudgetMismatchNatAbs
    rw [hz1]
    norm_num [Int.natAbs]
  simp only [hins, hneg, ite_false, ite_true, zero_add, hrs]

theorem totalNegativeBudget_insert_opening_shell (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (m : ℕ) (hneg : negativeBudget M m)
    (hm_act : m ∈ activeShellRange M) :
    totalNegativeBudget
        (insertNullShellVertex M (openingVertex M m hneg)
          (minUnusedTag_vertex_not_mem M m hneg) hV) =
      totalNegativeBudget M - 1 := by
  classical
  set v := openingVertex M m hneg
  set hv := minUnusedTag_vertex_not_mem M m hneg
  have hshell : v.shell = m := by dsimp [openingVertex]; rfl
  have hrng := activeShellRange_insert_opening M hV m hneg hm_act
  have hterm :
      ∀ k ∈ activeShellRange M,
        (if negativeBudget (insertNullShellVertex M v hv hV) k then
            shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
          (if k = m then 1 else 0) =
        (if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0) := by
    intro k hk
    by_cases heq : k = m
    · rw [heq]
      by_cases hins : negativeBudget (insertNullShellVertex M v hv hV) m
      · unfold negativeBudget at hins hneg ⊢
        simp only [hins, hneg, shellBudgetMismatchNatAbs, ite_true]
        exact shellBudgetMismatchNatAbs_insert_same_shell_neg M v hv hV m hshell hneg
      · exact budgetTerm_same_shell_zneg M v hv hV m hshell hneg hins
    · have hne : k ≠ m := heq
      have hshell' : v.shell ≠ k := fun h => hne (hshell ▸ h.symm)
      simpa [if_neg hne, add_zero] using budgetTerm_other_shell M v hv hV k hshell'
  have hsingle : (∑ k ∈ activeShellRange M, if k = m then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single m] <;> simp [*] <;> aesop
  have hsum :
      ∑ k ∈ activeShellRange M,
          ((if negativeBudget (insertNullShellVertex M v hv hV) k then
              shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
            (if k = m then 1 else 0)) =
        ∑ k ∈ activeShellRange M,
          if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0 := by
    refine Finset.sum_congr rfl fun k hk => hterm k hk
  have hadd : totalNegativeBudget (insertNullShellVertex M v hv hV) + 1 = totalNegativeBudget M := by
    unfold totalNegativeBudget
    rw [hrng]
    calc
      (∑ k ∈ activeShellRange M,
          if negativeBudget (insertNullShellVertex M v hv hV) k then
            shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) + 1 =
          (∑ k ∈ activeShellRange M,
              if negativeBudget (insertNullShellVertex M v hv hV) k then
                shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
            (∑ k ∈ activeShellRange M, if k = m then 1 else 0) := by
            simp [hsingle, Finset.sum_add_distrib]
          _ = ∑ k ∈ activeShellRange M,
              if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0 := by
            rw [← Finset.sum_add_distrib, hsum]
  exact Nat.eq_sub_of_add_eq hadd

theorem totalEarlyNegativeBudget_insert_opening_shell (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (m : ℕ) (hneg : negativeBudget M m) (hm2 : m ≤ 2)
    (hm_early : m ∈ earlyActiveShellRange M) :
    totalEarlyNegativeBudget
        (insertNullShellVertex M (openingVertex M m hneg)
          (minUnusedTag_vertex_not_mem M m hneg) hV) =
      totalEarlyNegativeBudget M - 1 := by
  classical
  set v := openingVertex M m hneg
  set hv := minUnusedTag_vertex_not_mem M m hneg
  have hshell : v.shell = m := by dsimp [openingVertex]; rfl
  have hmax : v.shell ≤ maxVertexShell M := by
    have : m ≤ maxVertexShell M := by
      simp [earlyActiveShellRange, activeShellRange, Finset.mem_filter, Finset.mem_range] at hm_early
      omega
    rwa [hshell]
  have hrng := activeShellRange_insert_of_shell_le M v hv hV hmax
  have hrng_early : earlyActiveShellRange (insertNullShellVertex M v hv hV) =
      earlyActiveShellRange M := by
    simp only [earlyActiveShellRange, hrng]
  have hterm :
      ∀ k ∈ earlyActiveShellRange M,
        (if negativeBudget (insertNullShellVertex M v hv hV) k then
            shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
          (if k = m then 1 else 0) =
        (if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0) := by
    intro k hk
    by_cases heq : k = m
    · rw [heq]
      by_cases hins : negativeBudget (insertNullShellVertex M v hv hV) m
      · unfold negativeBudget at hins hneg ⊢
        simp only [hins, hneg, shellBudgetMismatchNatAbs, ite_true]
        exact shellBudgetMismatchNatAbs_insert_same_shell_neg M v hv hV m hshell hneg
      · exact budgetTerm_same_shell_zneg M v hv hV m hshell hneg hins
    · have hne : k ≠ m := heq
      have hshell' : v.shell ≠ k := fun h => hne (hshell ▸ h.symm)
      simpa [if_neg hne, add_zero] using budgetTerm_other_shell M v hv hV k hshell'
  have hsingle : (∑ k ∈ earlyActiveShellRange M, if k = m then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single m] <;> simp [*] <;> aesop
  have hsum :
      ∑ k ∈ earlyActiveShellRange M,
          ((if negativeBudget (insertNullShellVertex M v hv hV) k then
              shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
            (if k = m then 1 else 0)) =
        ∑ k ∈ earlyActiveShellRange M,
          if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0 := by
    refine Finset.sum_congr rfl fun k hk => hterm k hk
  have hadd : totalEarlyNegativeBudget (insertNullShellVertex M v hv hV) + 1 =
      totalEarlyNegativeBudget M := by
    unfold totalEarlyNegativeBudget
    rw [hrng_early]
    calc
      (∑ k ∈ earlyActiveShellRange M,
          if negativeBudget (insertNullShellVertex M v hv hV) k then
            shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) + 1 =
          (∑ k ∈ earlyActiveShellRange M,
              if negativeBudget (insertNullShellVertex M v hv hV) k then
                shellBudgetMismatchNatAbs (insertNullShellVertex M v hv hV) k else 0) +
            (∑ k ∈ earlyActiveShellRange M, if k = m then 1 else 0) := by
            simp [hsingle, Finset.sum_add_distrib]
          _ = ∑ k ∈ earlyActiveShellRange M,
              if negativeBudget M k then shellBudgetMismatchNatAbs M k else 0 := by
            rw [← Finset.sum_add_distrib, hsum]
  exact Nat.eq_sub_of_add_eq hadd

theorem totalNegativeBudget_pos_of_neg_active (M m)
    (hm : m ∈ negativeActiveShells M) : 0 < totalNegativeBudget M := by
  rcases mem_negativeActiveShells.mp hm with ⟨hneg, hm_rng⟩
  unfold totalNegativeBudget
  refine Nat.lt_of_lt_of_le (negativeBudget_pos_natAbs M m hneg) ?_
  exact le_trans (le_of_eq (by simp [hneg, ite_true])) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm_rng)

theorem exists_neg_active_of_totalNeg_pos (M : Discrete3Complex NullShellVertex)
    (hpos : 0 < totalNegativeBudget M) :
    ∃ m, m ∈ negativeActiveShells M := by
  by_contra habs
  push_neg at habs
  have hzero : totalNegativeBudget M = 0 := by
    unfold totalNegativeBudget
    refine Finset.sum_eq_zero fun m hm => ?_
    by_cases hneg : negativeBudget M m
    · exact absurd (mem_negativeActiveShells.mpr ⟨hneg, hm⟩) (habs m)
    · simp [hneg]
  omega

theorem negativeActiveShells_nonempty_of_totalNeg_pos (M : Discrete3Complex NullShellVertex)
    (hpos : 0 < totalNegativeBudget M) : (negativeActiveShells M).Nonempty :=
  let ⟨m, hm⟩ := exists_neg_active_of_totalNeg_pos M hpos
  ⟨m, hm⟩

theorem negativeActiveShells_empty_of_totalNeg_zero (M : Discrete3Complex NullShellVertex)
    (hzero : totalNegativeBudget M = 0) : negativeActiveShells M = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro ⟨m, hm⟩
  rcases mem_negativeActiveShells.mp hm with ⟨hneg, hm_rng⟩
  have hterm : 0 < shellBudgetMismatchNatAbs M m :=
    negativeBudget_pos_natAbs M m hneg
  have hle : shellBudgetMismatchNatAbs M m ≤ totalNegativeBudget M := by
    unfold totalNegativeBudget
    exact le_trans (le_of_eq (by simp [hneg, ite_true])) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm_rng)
  rw [hzero] at hle
  exact Nat.not_lt_of_ge hle hterm

theorem shellOpeningStep_totalNegative_lt_of_some (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) {M'} (hstep : shellOpeningStep M hV = some M')
    (hpos : 0 < totalNegativeBudget M) :
    totalNegativeBudget M' < totalNegativeBudget M := by
  rcases hsn : smallestNegativeShell M with - | m
  · exfalso
    have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hsn
    rw [hstep_none] at hstep
    cases hstep
  · rcases mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn) with ⟨hneg, hm_rng⟩
    have hpos' := totalNegativeBudget_pos_of_neg_active M m
      (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩)
    obtain ⟨hneg', hdef⟩ := shellOpeningStep_some_eq M hV m hsn
    have hM' : insertNullShellVertex M (openingVertex M m hneg')
        (minUnusedTag_vertex_not_mem M m hneg') hV = M' :=
      Option.some.inj (hdef.symm.trans hstep)
    rw [← hM', totalNegativeBudget_insert_opening_shell M hV m hneg' hm_rng]
    exact Nat.sub_lt hpos' (by decide : 0 < 1)

theorem shellOpeningStep_decreases_totalNegative (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (hpos : 0 < totalNegativeBudget M) :
    match shellOpeningStep M hV with
    | some M' => totalNegativeBudget M' < totalNegativeBudget M
    | none => True := by
  rcases hmatch : shellOpeningStep M hV with - | M'
  · exfalso
    have hempty := (shellOpeningStep_eq_none_iff M hV).1 hmatch
    rcases negativeActiveShells_nonempty_of_totalNeg_pos M hpos with ⟨m, hm⟩
    rw [hempty] at hm
    cases hm
  · exact shellOpeningStep_totalNegative_lt_of_some M hV hmatch hpos

theorem shellOpeningStep_earlyNegative_lt_of_some (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) {M'} (hstep : shellOpeningStep M hV = some M')
    (hpos : 0 < totalEarlyNegativeBudget M) :
    totalEarlyNegativeBudget M' < totalEarlyNegativeBudget M := by
  rcases smallestNegativeShell_le_two_of_early_pos M hpos with ⟨m, hsm, hm2⟩
  rcases smallestNegativeShell_spec hsm with ⟨hm_neg, _⟩
  rcases mem_negativeActiveShells.mp hm_neg with ⟨hneg, _⟩
  have hm_early : m ∈ earlyActiveShellRange M :=
    Finset.mem_filter.mpr ⟨(mem_negativeActiveShells.mp hm_neg).2, hm2⟩
  obtain ⟨hneg', hdef⟩ := shellOpeningStep_some_eq M hV m hsm
  have hM' : insertNullShellVertex M (openingVertex M m hneg')
      (minUnusedTag_vertex_not_mem M m hneg') hV = M' :=
    Option.some.inj (hdef.symm.trans hstep)
  rw [← hM', totalEarlyNegativeBudget_insert_opening_shell M hV m hneg' hm2 hm_early]
  exact Nat.sub_lt (Nat.lt_of_lt_of_le (negativeBudget_pos_natAbs M m hneg)
    (totalEarly_summand_le hm_early hneg)) (by decide : 0 < 1)

theorem shellOpeningStep_decreases_early_negative (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (hpos : 0 < totalEarlyNegativeBudget M) :
    match shellOpeningStep M hV with
    | some M' => totalEarlyNegativeBudget M' < totalEarlyNegativeBudget M
    | none => True := by
  rcases hmatch : shellOpeningStep M hV with - | M'
  · exfalso
    have hempty := (shellOpeningStep_eq_none_iff M hV).1 hmatch
    rcases negativeActiveShells_nonempty_of_totalEarly_pos M hpos with ⟨m', hm'⟩
    rw [hempty] at hm'
    cases hm'
  · exact shellOpeningStep_earlyNegative_lt_of_some M hV hmatch hpos

/-!
## Packaged evolution + termination
-/

/-- Opening flow packaged as `DiscreteCurvatureEvolution` (requires `IsVertexOnly` at each state). -/
noncomputable def shellOpeningEvolution (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α) :
    DiscreteCurvatureEvolution where
  α := α
  mStar := mStar
  href := href
  step := fun M =>
    if h : IsVertexOnly M then
      match shellOpeningStep M h with
      | some M' => some M'
      | none => some M
    else none
  lyapunov_nonincreasing := fun M => by
    by_cases hV : IsVertexOnly M
    · rcases hstep : shellOpeningStep M hV with - | M'
      · simp [hV, hstep]
      · simpa [hV, hstep] using lyapunov_le_of_shellOpeningStep_some M hV hstep
    · simp [hV]

theorem shellOpening_not_equilibrium (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (hneg : (negativeActiveShells M).Nonempty) :
    ¬ (shellOpeningEvolution α mStar href).IsEquilibrium M := by
  intro heq
  have hs : (negativeActiveShells M).Nonempty := hneg
  set m0 := (negativeActiveShells M).min' hs
  have hsm : smallestNegativeShell M = some m0 := by
    dsimp [smallestNegativeShell, m0]
    simp [hs]
  obtain ⟨hneg0, hstep⟩ := shellOpeningStep_some_eq M hV m0 hsm
  set hv := minUnusedTag_vertex_not_mem M m0 hneg0
  unfold DiscreteCurvatureEvolution.IsEquilibrium shellOpeningEvolution at heq
  simp only [hV, dite_true, hstep] at heq
  have hM := (Option.some.inj heq).symm
  have hem := insertNullShellVertex_self_mem M (openingVertex M m0 hneg0) hv hV
  rw [← hM] at hem
  exact hv hem

noncomputable def shellOpeningNatLyapunovDescent (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α) :
    NatLyapunovDescent (shellOpeningEvolution α mStar href) where
  μ := totalNegativeBudget
  strict_off_equilibrium := fun M hneq => by
    simp only [shellOpeningEvolution, DiscreteCurvatureEvolution.IsEquilibrium] at hneq ⊢
    by_cases hV : IsVertexOnly M
    · rcases hopen : shellOpeningStep M hV with - | M'
      · exfalso
        exact hneq (by simp [DiscreteCurvatureEvolution.IsEquilibrium, shellOpeningEvolution, hV, hopen])
      · have hsn : smallestNegativeShell M ≠ none := by
          intro hnone
          have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
          rw [hstep_none] at hopen
          cases hopen
        rcases Option.ne_none_iff_exists.mp hsn with ⟨m, hsm⟩
        have hsm' : smallestNegativeShell M = some m := hsm.symm
        have hm_neg := smallestNegativeShell_mem hsm'
        have hpos := totalNegativeBudget_pos_of_neg_active M m hm_neg
        have hlt : totalNegativeBudget M' < totalNegativeBudget M := by
          simpa [hopen] using shellOpeningStep_decreases_totalNegative M hV hpos
        exact Or.inr ⟨M', by simp [shellOpeningEvolution, hV, hopen], hlt⟩
    · exact Or.inl (by simp [shellOpeningEvolution, hV])

theorem shellOpening_flow_terminates (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) :
    FlowTerminatesAt (shellOpeningEvolution α mStar href) M :=
  discrete_flow_terminates_of_descent _ (shellOpeningNatLyapunovDescent α mStar href) M

theorem shellOpening_reaches_zero_totalNegative (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) :
    ∃ n M',
      (shellOpeningEvolution α mStar href).iterate n M = some M' ∧
        totalNegativeBudget M' = 0 := by
  let evo := shellOpeningEvolution α mStar href
  have hrec :
      ∀ k (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M),
        totalNegativeBudget M = k →
          ∃ n M', evo.iterate n M = some M' ∧ totalNegativeBudget M' = 0 := by
    intro k
    refine Nat.strongRecOn k fun k ih => ?_
    intro M hV hEq
    by_cases hz : k = 0
    · subst hEq
      exact ⟨0, M, by simp [evo, DiscreteCurvatureEvolution.iterate_zero], hz⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk => hz hk
      have hEq' : totalNegativeBudget M = k := hEq
      rcases exists_neg_active_of_totalNeg_pos M (hEq' ▸ hkpos) with ⟨m, hm⟩
      rcases hstep : shellOpeningStep M hV with - | M'
      · exfalso
        have hempty := (shellOpeningStep_eq_none_iff M hV).1 hstep
        rw [hempty] at hm
        cases hm
      · have hlt : totalNegativeBudget M' < totalNegativeBudget M := by
          have hpos := hEq' ▸ hkpos
          simpa [hstep] using shellOpeningStep_decreases_totalNegative M hV hpos
        have hV' : IsVertexOnly M' := shellOpeningStep_preserves_vertexOnly M hV hstep
        have hltk : totalNegativeBudget M' < k := hEq' ▸ hlt
        rcases ih (totalNegativeBudget M') hltk M' hV' rfl with ⟨n, M'', hiter, hz'⟩
        refine ⟨n + 1, M'', ?_, hz'⟩
        have hev : evo.step M = some M' := by
          dsimp [evo, shellOpeningEvolution]
          simp only [hV, hstep, dite_true]
        rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo n M M' hev]
        exact hiter
  exact hrec (totalNegativeBudget M) M hV rfl

/-!
## Deficit-only horizon + `S3NullReference` convergence
-/

theorem deficitOnlyOnHorizon_insert_opening (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (n m : ℕ) (hdef : deficitOnlyOnHorizon M n) (hneg : negativeBudget M m)
    (hm : m ≤ n) :
    deficitOnlyOnHorizon
      (insertNullShellVertex M (openingVertex M m hneg) (minUnusedTag_vertex_not_mem M m hneg) hV) n := by
  intro k hk
  by_cases hkm : k = m
  · rw [show k = m from hkm]
    have hb := shellBudgetMismatch_insert_same_shell M (openingVertex M m hneg)
      (minUnusedTag_vertex_not_mem M m hneg) hV m rfl
    rw [hb]
    have hz : shellBudgetMismatch M m < 0 := by simpa [negativeBudget] using hneg
    linarith
  · have hne : m ≠ k := ne_comm.mp hkm
    have hshell : (openingVertex M m hneg).shell ≠ k := by
      dsimp [openingVertex]
      exact hne
    have hbm := shellBudgetMismatch_insert_other_shell M (openingVertex M m hneg)
      (minUnusedTag_vertex_not_mem M m hneg) hV k hshell
    simp only [deficitOnlyOnHorizon, hbm]
    exact hdef k hk

theorem shellOpeningStep_preserves_deficitOnly (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (n : ℕ) (hn : maxVertexShell M = n) (hdef : deficitOnlyOnHorizon M n)
    {M'} (hstep : shellOpeningStep M hV = some M') : deficitOnlyOnHorizon M' n := by
  have hsn : smallestNegativeShell M ≠ none := by
    intro hnone
    have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
    rw [hstep_none] at hstep
    cases hstep
  rcases Option.ne_none_iff_exists.mp hsn with ⟨m, hsm⟩
  have hsn' : smallestNegativeShell M = some m := hsm.symm
  obtain ⟨hneg, hstepDef⟩ := shellOpeningStep_some_eq M hV m hsn'
  have hm_rng := (mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn')).2
  have hm_le : m ≤ n := by
    simp only [activeShellRange, Finset.mem_range] at hm_rng
    exact Nat.le_trans (Nat.le_of_lt_succ hm_rng) (by simpa [hn] using le_rfl)
  have hM' : M' = insertNullShellVertex M (openingVertex M m hneg)
      (minUnusedTag_vertex_not_mem M m hneg) hV :=
    Option.some.inj (hstep.symm.trans hstepDef)
  simpa [hM'] using deficitOnlyOnHorizon_insert_opening M hV n m hdef hneg hm_le

theorem shellOpeningStep_preserves_maxVertexShell (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (n : ℕ) (hn : maxVertexShell M = n)
    {M'} (hstep : shellOpeningStep M hV = some M') : maxVertexShell M' = n := by
  have hsn : smallestNegativeShell M ≠ none := by
    intro hnone
    have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
    rw [hstep_none] at hstep
    cases hstep
  rcases Option.ne_none_iff_exists.mp hsn with ⟨m, hsm⟩
  have hsn' : smallestNegativeShell M = some m := hsm.symm
  obtain ⟨hneg, hstepDef⟩ := shellOpeningStep_some_eq M hV m hsn'
  have hm_rng := (mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn')).2
  have hm_le : m ≤ maxVertexShell M := by
    simp only [activeShellRange, Finset.mem_range] at hm_rng
    exact Nat.le_of_lt_succ hm_rng
  have hM' : M' = insertNullShellVertex M (openingVertex M m hneg)
      (minUnusedTag_vertex_not_mem M m hneg) hV :=
    Option.some.inj (hstep.symm.trans hstepDef)
  rw [hM', maxVertexShell_insert, hn, max_comm, max_eq_right (by simpa [hn] using hm_le)]

theorem shellOpening_not_negative_on_active_of_totalNeg_zero
    (M : Discrete3Complex NullShellVertex) (hzero : totalNegativeBudget M = 0) :
    ∀ m ∈ activeShellRange M, ¬ negativeBudget M m := by
  intro m hm
  intro hneg
  have hpos := totalNegativeBudget_pos_of_neg_active M m
    (mem_negativeActiveShells.mpr ⟨hneg, hm⟩)
  rw [hzero] at hpos
  exact Nat.not_lt_zero _ hpos

theorem shellOpening_equilibrium_iff_totalNegative_zero
    (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) :
    (shellOpeningEvolution α mStar href).IsEquilibrium M ↔ totalNegativeBudget M = 0 := by
  constructor
  · intro heq
    by_contra hz
    have hpos : 0 < totalNegativeBudget M := Nat.pos_iff_ne_zero.mpr hz
    rcases exists_neg_active_of_totalNeg_pos M hpos with ⟨m, hm⟩
    exact shellOpening_not_equilibrium α mStar href M hV
      (negativeActiveShells_nonempty_of_totalNeg_pos M hpos) heq
  · intro hzero
    unfold DiscreteCurvatureEvolution.IsEquilibrium shellOpeningEvolution
    simp only [hV, dite_true]
    rcases hopen : shellOpeningStep M hV with - | M'
    · rfl
    · exfalso
      have hsn : smallestNegativeShell M ≠ none := by
        intro hnone
        have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
        rw [hstep_none] at hopen
        cases hopen
      rcases Option.ne_none_iff_exists.mp hsn with ⟨m, hsm⟩
      have hsm' : smallestNegativeShell M = some m := hsm.symm
      have hpos := totalNegativeBudget_pos_of_neg_active M m (smallestNegativeShell_mem hsm')
      simpa [hzero] using hpos

theorem shellOpeningEvolution_step_some_of_not_equilibrium (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (hneq : ¬ (shellOpeningEvolution α mStar href).IsEquilibrium M) :
    ∃ M', (shellOpeningEvolution α mStar href).step M = some M' := by
  have hpos : 0 < totalNegativeBudget M := by
    by_contra hz
    have hle : totalNegativeBudget M ≤ 0 := Nat.not_lt.mp hz
    exact hneq ((shellOpening_equilibrium_iff_totalNegative_zero α mStar href M hV).mpr
      (Nat.eq_zero_of_le_zero hle))
  rcases exists_neg_active_of_totalNeg_pos M hpos with ⟨m, hm⟩
  have hs : (negativeActiveShells M).Nonempty := ⟨m, hm⟩
  set m0 := (negativeActiveShells M).min' hs
  have hsn : smallestNegativeShell M = some m0 := by
    dsimp only [smallestNegativeShell, m0]
    simp only [hs, dite_true]
  obtain ⟨hneg0, hopen⟩ := shellOpeningStep_some_eq M hV m0 hsn
  refine ⟨insertNullShellVertex M (openingVertex M m0 hneg0) (minUnusedTag_vertex_not_mem M m0 hneg0) hV, ?_⟩
  simp [shellOpeningEvolution, hV, dite_true, hopen]

theorem IsVertexOnly_of_shellOpening_iterate (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α) :
    ∀ k (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
      (M' : Discrete3Complex NullShellVertex),
      (shellOpeningEvolution α mStar href).iterate k M = some M' → IsVertexOnly M' := by
  intro k
  induction k with
  | zero =>
    intro M hV M' hiter
    rcases Option.some.inj hiter with rfl
    exact hV
  | succ k ih =>
    intro M hV M' hiter
    let evo := shellOpeningEvolution α mStar href
    rcases hopen : shellOpeningStep M hV with - | Mmid
    · have hev : evo.step M = some M := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M M hev] at hiter
      exact ih M hV M' hiter
    · have hev : evo.step M = some Mmid := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M Mmid hev] at hiter
      exact ih Mmid (shellOpeningStep_preserves_vertexOnly M hV hopen) M' hiter

theorem maxVertexShell_eq_of_shellOpening_iterate (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (n : ℕ) :
    ∀ k (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
      (hmax : maxVertexShell M = n) (M' : Discrete3Complex NullShellVertex),
      (shellOpeningEvolution α mStar href).iterate k M = some M' → maxVertexShell M' = n := by
  intro k
  induction k with
  | zero =>
    intro M hV hmax M' hiter
    rcases Option.some.inj hiter with rfl
    exact hmax
  | succ k ih =>
    intro M hV hmax M' hiter
    let evo := shellOpeningEvolution α mStar href
    rcases hopen : shellOpeningStep M hV with - | Mmid
    · have hev : evo.step M = some M := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M M hev] at hiter
      exact ih M hV hmax M' hiter
    · have hev : evo.step M = some Mmid := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M Mmid hev] at hiter
      have hmax_mid := shellOpeningStep_preserves_maxVertexShell M hV n hmax hopen
      exact ih Mmid (shellOpeningStep_preserves_vertexOnly M hV hopen) hmax_mid M' hiter

theorem deficitOnlyOnHorizon_of_shellOpening_iterate (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (n : ℕ) :
    ∀ k (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
      (hmax : maxVertexShell M = n) (hdef : deficitOnlyOnHorizon M n)
      (M' : Discrete3Complex NullShellVertex),
      (shellOpeningEvolution α mStar href).iterate k M = some M' → deficitOnlyOnHorizon M' n := by
  intro k
  induction k with
  | zero =>
    intro M hV hmax hdef M' hiter
    rcases Option.some.inj hiter with rfl
    exact hdef
  | succ k ih =>
    intro M hV hmax hdef M' hiter
    let evo := shellOpeningEvolution α mStar href
    rcases hopen : shellOpeningStep M hV with - | Mmid
    · have hev : evo.step M = some M := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M M hev] at hiter
      exact ih M hV hmax hdef M' hiter
    · have hev : evo.step M = some Mmid := by simp [evo, shellOpeningEvolution, hV, hopen]
      rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo k M Mmid hev] at hiter
      have hmax_mid := shellOpeningStep_preserves_maxVertexShell M hV n hmax hopen
      have hdef_mid := shellOpeningStep_preserves_deficitOnly M hV n hmax hdef hopen
      exact ih Mmid (shellOpeningStep_preserves_vertexOnly M hV hopen) hmax_mid hdef_mid M' hiter

theorem shellOpening_iterate_eq_self_at_equilibrium (α : ℝ) (n : ℕ) (href : 0 < K n α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (heq : (shellOpeningEvolution α n href).IsEquilibrium M) :
    ∀ k, (shellOpeningEvolution α n href).iterate k M = some M := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hev : (shellOpeningEvolution α n href).step M = some M := by
      unfold DiscreteCurvatureEvolution.IsEquilibrium at heq
      simpa [shellOpeningEvolution, hV] using heq
    rw [DiscreteCurvatureEvolution.iterate_succ_of_step (shellOpeningEvolution α n href) k M M hev, ih]

theorem shellOpening_iterate_succ_eq_self_at_equilibrium (α : ℝ) (n : ℕ) (href : 0 < K n α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (heq : (shellOpeningEvolution α n href).IsEquilibrium M) (k : ℕ) :
    (shellOpeningEvolution α n href).iterate (k + 1) M = some M := by
  let evo := shellOpeningEvolution α n href
  have hev : evo.step M = some M := by
    unfold DiscreteCurvatureEvolution.IsEquilibrium at heq
    simpa [evo, shellOpeningEvolution, hV] using heq
  induction k with
  | zero =>
    simpa [evo, DiscreteCurvatureEvolution.iterate_one] using hev
  | succ k ih =>
    rw [DiscreteCurvatureEvolution.iterate_succ_of_step evo (k + 1) M M hev, ih]

noncomputable def shellOpeningUsesCurvatureChannel (α : ℝ) (n : ℕ) (href : 0 < K n α) (hα : 0 < α) :
    UsesCurvatureChannel (shellOpeningEvolution α n href) where
  positive_coupling := by simpa [shellOpeningEvolution] using hα
  hqiv_step := { step_eq := rfl }
  phase_readout_eq_omega := fun _ => rfl
  delta_suture_antisymmetric := delta_antisymmetric

theorem shellOpening_reaches_quadratic_on_horizon
    (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (n : ℕ)
    (hmax : maxVertexShell M = n) (hdef : deficitOnlyOnHorizon M n) :
    ∃ M',
      (shellOpeningEvolution α mStar href).IsEquilibrium M' ∧
        QuadraticNullShellGrowthOnHorizon M' n := by
  rcases shellOpening_reaches_zero_totalNegative α mStar href M hV with ⟨k, M', hiter, hz⟩
  have hV' := IsVertexOnly_of_shellOpening_iterate α mStar href k M hV M' hiter
  have heq : (shellOpeningEvolution α mStar href).IsEquilibrium M' :=
    (shellOpening_equilibrium_iff_totalNegative_zero α mStar href M' hV').mpr hz
  have hmax' := maxVertexShell_eq_of_shellOpening_iterate α mStar href n k M hV hmax M' hiter
  have hdef' := deficitOnlyOnHorizon_of_shellOpening_iterate α mStar href n k M hV hmax hdef M' hiter
  refine ⟨M', heq, ?_⟩
  exact deficitOnly_no_negative_budget_imp_quadraticOnHorizon M' n hdef'
    (by simpa [hmax'] using le_rfl)
    (shellOpening_not_negative_on_active_of_totalNeg_zero M' hz)

/-- Opening flow from a deficit-only horizon state reaches the `S3NullReference` template. -/
theorem shellOpeningStep_reaches_S3NullReference
    (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α)
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M) (n : ℕ)
    (hmax : maxVertexShell M = n) (hdef : deficitOnlyOnHorizon M n) :
    ∃ k M',
      (shellOpeningEvolution α mStar href).iterate k M = some M' ∧
        IsS3NullReference M' n := by
  rcases shellOpening_reaches_zero_totalNegative α mStar href M hV with ⟨k, M', hiter, hz⟩
  have hmax' := maxVertexShell_eq_of_shellOpening_iterate α mStar href n k M hV hmax M' hiter
  have hdef' := deficitOnlyOnHorizon_of_shellOpening_iterate α mStar href n k M hV hmax hdef M' hiter
  have hq := deficitOnly_no_negative_budget_imp_quadraticOnHorizon M' n hdef'
    (by simpa [hmax'] using le_rfl) (shellOpening_not_negative_on_active_of_totalNeg_zero M' hz)
  refine ⟨k, M', hiter, ?_⟩
  exact quadraticOnHorizon_is_S3NullReference M' n hq (by simpa [hmax'] using le_rfl)

/-!
## Lexicographic Lyapunov `(totalEarlyNegativeBudget, totalNegativeBudget)`

With `linkDeficit ≡ 0`, the ℝ scaffold `lyapunovFunctional` is shell-0 mismatch only; strict
lex descent for opening is proved on the ℕ pair below and encoded as a single `RealLyapunovDescent`
measure for the parallel-Poincaré certificate.
-/

/-- Lexicographic pair for shell opening (proved strict descent). -/
noncomputable def shellOpeningLexPair (M : Discrete3Complex NullShellVertex) : ℕ × ℕ :=
  (totalEarlyNegativeBudget M, totalNegativeBudget M)

/-- Encode `(early, total)` lex order into one ℕ for `NatLyapunovDescent`. -/
noncomputable def shellOpeningLexEncode (M : Discrete3Complex NullShellVertex) : ℕ :=
  let (e, t) := shellOpeningLexPair M
  e * (t + 1) + t

theorem shellOpeningLexEncode_lt_of_step_some (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) {M'} (hstep : shellOpeningStep M hV = some M') :
    shellOpeningLexEncode M' < shellOpeningLexEncode M := by
  unfold shellOpeningLexEncode shellOpeningLexPair
  have hsn : smallestNegativeShell M ≠ none := by
    intro hnone
    have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
    rw [hstep_none] at hstep
    cases hstep
  rcases Option.ne_none_iff_exists.mp hsn with ⟨m, hsm⟩
  have hsn' : smallestNegativeShell M = some m := hsm.symm
  rcases mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn') with ⟨hneg, hm_rng⟩
  by_cases he : 0 < totalEarlyNegativeBudget M
  · have hE := shellOpeningStep_earlyNegative_lt_of_some M hV hstep he
    have hT := shellOpeningStep_totalNegative_lt_of_some M hV hstep
      (totalNegativeBudget_pos_of_neg_active M m (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩))
    set e := totalEarlyNegativeBudget M
    set e' := totalEarlyNegativeBudget M'
    set t := totalNegativeBudget M
    set t' := totalNegativeBudget M'
    have hE' : e' < e := hE
    have hT' : t' < t := hT
    have hmul : e' * (t' + 1) + t' < e * (t + 1) + t := by
      calc
        e' * (t' + 1) + t' < e * (t' + 1) + t' :=
          Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hE' (Nat.succ_pos t')) _
        _ ≤ e * (t + 1) + t' := by
          have htt : t' + 1 ≤ t + 1 := by omega
          have hmid : e * (t' + 1) ≤ e * (t + 1) := Nat.mul_le_mul_left e htt
          exact Nat.add_le_add_right hmid t'
        _ < e * (t + 1) + t := Nat.add_lt_add_left hT' _
    dsimp [shellOpeningLexEncode, shellOpeningLexPair]
    simpa [e, e', t, t'] using hmul
  · have hpos : 0 < totalNegativeBudget M :=
      totalNegativeBudget_pos_of_neg_active M m (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩)
    have hT := shellOpeningStep_totalNegative_lt_of_some M hV hstep hpos
    have hE0 : totalEarlyNegativeBudget M = 0 := Nat.eq_zero_of_le_zero
      (Nat.le_of_not_lt he)
    obtain ⟨hneg', hstepDef⟩ := shellOpeningStep_some_eq M hV m hsn'
    have hM' : M' = insertNullShellVertex M (openingVertex M m hneg')
        (minUnusedTag_vertex_not_mem M m hneg') hV :=
      Option.some.inj (hstep.symm.trans hstepDef)
    have hm_gt : 2 < m := by
      by_contra hle
      have hpos := totalEarlyNegativeBudget_pos_of_neg_shell M m
        (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩) (by simpa using hle)
      rw [hE0] at hpos
      exact Nat.not_lt_zero _ hpos
    have hE0' : totalEarlyNegativeBudget M' = 0 := by
      rw [hM', totalEarlyNegativeBudget_insert_opening_late_shell M hV m hneg' hm_gt hm_rng, hE0]
    simp only [shellOpeningLexEncode, shellOpeningLexPair, hE0, hE0', zero_mul, zero_add]
    exact hT

theorem smallestNegativeShell_eq_some_zero_of_negative_shell0
    (M : Discrete3Complex NullShellVertex) (hneg0 : negativeBudget M 0) :
    smallestNegativeShell M = some 0 := by
  have hs : (negativeActiveShells M).Nonempty :=
    ⟨0, mem_negativeActiveShells.mpr ⟨hneg0, by simp [activeShellRange]⟩⟩
  have hmem : 0 ∈ negativeActiveShells M :=
    mem_negativeActiveShells.mpr ⟨hneg0, by simp [activeShellRange]⟩
  have hle : (negativeActiveShells M).min' hs ≤ 0 := (negativeActiveShells M).min'_le 0 hmem
  have hmem_min : (negativeActiveShells M).min' hs ∈ negativeActiveShells M :=
    Finset.min'_mem (negativeActiveShells M) hs
  have hge : 0 ≤ (negativeActiveShells M).min' hs := by
    rcases mem_negativeActiveShells.mp hmem_min with ⟨_, hm_act⟩
    simp only [activeShellRange, Finset.mem_range] at hm_act
    omega
  have hm : (negativeActiveShells M).min' hs = 0 := le_antisymm hle hge
  simp only [smallestNegativeShell, hs, dite_true, hm]

theorem shellOpeningLyapunovFunctional_lt_of_shell0_open
    (M : Discrete3Complex NullShellVertex) (hV : IsVertexOnly M)
    (hneg0 : negativeBudget M 0) {M'} (hstep : shellOpeningStep M hV = some M') :
    lyapunovFunctional M' < lyapunovFunctional M := by
  have hsn := smallestNegativeShell_eq_some_zero_of_negative_shell0 M hneg0
  obtain ⟨hneg, hstepDef⟩ := shellOpeningStep_some_eq M hV 0 hsn
  have hM' : M' = insertNullShellVertex M (openingVertex M 0 hneg)
      (minUnusedTag_vertex_not_mem M 0 hneg) hV :=
    Option.some.inj (hstep.symm.trans hstepDef)
  rw [hM', lyapunovFunctional_eq_shell0_budget, lyapunovFunctional_eq_shell0_budget]
  have hb := shellBudgetMismatch_insert_same_shell M (openingVertex M 0 hneg)
    (minUnusedTag_vertex_not_mem M 0 hneg) hV 0 rfl
  have hz : shellBudgetMismatch M 0 < 0 := by simpa [negativeBudget] using hneg0
  rw [hb]
  exact_mod_cast natAbs_add_one_lt_natAbs_of_neg hz

theorem shellOpeningLexPair_lt_of_step_some (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) {M'} (hstep : shellOpeningStep M hV = some M') :
    Prod.Lex (· < ·) (· < ·) (shellOpeningLexPair M') (shellOpeningLexPair M) := by
  unfold shellOpeningLexPair
  have hsn_ne : smallestNegativeShell M ≠ none := by
    intro hnone
    have hstep_none := (shellOpeningStep_eq_smallest M hV).mpr hnone
    rw [hstep_none] at hstep
    cases hstep
  rcases Option.ne_none_iff_exists.mp hsn_ne with ⟨m, hsm⟩
  have hsn : smallestNegativeShell M = some m := hsm.symm
  rcases mem_negativeActiveShells.mp (smallestNegativeShell_mem hsn) with ⟨hneg, hm_rng⟩
  by_cases he : 0 < totalEarlyNegativeBudget M
  · apply Prod.Lex.left
    exact shellOpeningStep_earlyNegative_lt_of_some M hV hstep he
  · have hE0 : totalEarlyNegativeBudget M = 0 := Nat.eq_zero_of_le_zero
      (Nat.le_of_not_lt he)
    have hm_gt : 2 < m := by
      by_contra hle
      have hpos := totalEarlyNegativeBudget_pos_of_neg_shell M m
        (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩) (by simpa using hle)
      rw [hE0] at hpos
      exact Nat.not_lt_zero _ hpos
    obtain ⟨hneg', hstepDef⟩ := shellOpeningStep_some_eq M hV m hsn
    have hM' : M' = insertNullShellVertex M (openingVertex M m hneg')
        (minUnusedTag_vertex_not_mem M m hneg') hV :=
      Option.some.inj (hstep.symm.trans hstepDef)
    have hEunchanged : totalEarlyNegativeBudget M' = totalEarlyNegativeBudget M := by
      simpa [hM'] using
        totalEarlyNegativeBudget_insert_opening_late_shell M hV m hneg' hm_gt hm_rng
    have hT := shellOpeningStep_totalNegative_lt_of_some M hV hstep
      (totalNegativeBudget_pos_of_neg_active M m (mem_negativeActiveShells.mpr ⟨hneg, hm_rng⟩))
    have hlex : Prod.Lex (· < ·) (· < ·) (totalEarlyNegativeBudget M, totalNegativeBudget M')
        (totalEarlyNegativeBudget M, totalNegativeBudget M) :=
      Prod.Lex.right (totalEarlyNegativeBudget M) hT
    simpa [shellOpeningLexPair, hEunchanged] using hlex

noncomputable def shellOpeningLexNatLyapunovDescent (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α) :
    NatLyapunovDescent (shellOpeningEvolution α mStar href) where
  μ := shellOpeningLexEncode
  strict_off_equilibrium := fun M hneq => by
    simp only [shellOpeningEvolution, DiscreteCurvatureEvolution.IsEquilibrium] at hneq ⊢
    by_cases hV : IsVertexOnly M
    · rcases hopen : shellOpeningStep M hV with - | M'
      · exfalso
        exact hneq (by simp [DiscreteCurvatureEvolution.IsEquilibrium, shellOpeningEvolution, hV, hopen])
      · exact Or.inr ⟨M', by simp [shellOpeningEvolution, hV, hopen],
          shellOpeningLexEncode_lt_of_step_some M hV hopen⟩
    · exact Or.inl (by simp [shellOpeningEvolution, hV])

noncomputable def shellOpeningRealLyapunovDescent (α : ℝ) (mStar : ℕ) (href : 0 < K mStar α) :
    RealLyapunovDescent (shellOpeningEvolution α mStar href) where
  toNatLyapunovDescent := shellOpeningLexNatLyapunovDescent α mStar href
  strict_some_off_equilibrium := fun M hV hneq => by
    obtain ⟨M', hstep⟩ :=
      shellOpeningEvolution_step_some_of_not_equilibrium α mStar href M hV hneq
    rcases hopen : shellOpeningStep M hV with - | Mmid
    · have hId : (shellOpeningEvolution α mStar href).step M = some M := by
        simp [shellOpeningEvolution, hV, hopen]
      have hEq : M' = M := Option.some.inj (hstep.symm.trans hId)
      exfalso
      have htot : totalNegativeBudget M = 0 := by
        by_contra hne0
        have hpos : 0 < totalNegativeBudget M := Nat.pos_iff_ne_zero.mpr hne0
        rcases exists_neg_active_of_totalNeg_pos M hpos with ⟨m, hm⟩
        have hempty := (shellOpeningStep_eq_none_iff M hV).1 hopen
        rw [hempty] at hm
        cases hm
      exact hneq ((shellOpening_equilibrium_iff_totalNegative_zero α mStar href M hV).mpr htot)
    · refine ⟨Mmid, ?_, shellOpeningLexEncode_lt_of_step_some M hV hopen⟩
      simpa [shellOpeningEvolution, hV, hopen] using hstep
  functional_nonincreasing_on_mu_descent := fun M M' hstep hμ => by
    have hle := (shellOpeningEvolution α mStar href).lyapunov_nonincreasing M
    simp only [hstep] at hle
    exact hle
  functional_strict_shell0 := fun M M' hstep h0 => by
    by_cases hV : IsVertexOnly M
    · rcases hopen : shellOpeningStep M hV with - | Mmid
      · exfalso
        have hsn := smallestNegativeShell_eq_some_zero_of_negative_shell0 M h0
        rw [shellOpeningStep_eq_smallest M hV, hsn] at hopen
        cases hopen
      · rcases Option.some.inj (by simpa [shellOpeningEvolution, hV, hopen] using hstep) with rfl
        exact shellOpeningLyapunovFunctional_lt_of_shell0_open M hV h0 hopen
    · simp [shellOpeningEvolution, hV] at hstep

/-- Shell-0 mismatch contributes to `totalNegativeBudget` when negative (opening-relevant states). -/
theorem shellOpeningLyapunovFunctional_le_totalNegative_of_shell0_neg
    (M : Discrete3Complex NullShellVertex) (hneg : negativeBudget M 0) :
    lyapunovFunctional M ≤ (totalNegativeBudget M : ℝ) + 1 := by
  rw [lyapunovFunctional_eq_shell0_budget]
  have hm_rng : 0 ∈ activeShellRange M := by
    dsimp [activeShellRange]
    simpa using Nat.zero_lt_succ (maxVertexShell M)
  have hpos := negativeBudget_pos_natAbs M 0 hneg
  have hle : shellBudgetMismatchNatAbs M 0 ≤ totalNegativeBudget M := by
    unfold totalNegativeBudget
    exact le_trans (le_of_eq (by simp [hneg, ite_true])) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm_rng)
  exact_mod_cast Nat.le_trans hle (Nat.le_succ _)

/-! ## T9 wiring example (fiber holonomy via PhaseMap on Hopf shells)

The `HopfShell.HolonomyPhaseCarrier` (defined in `HopfShellComplex`) provides the
typed attachment point for `RhFourierLift.PhaseMap` (curvature-channel phase lifts)
as discrete realisations of TUFT fiber holonomy. This example shows that every
integrable Hopf shell can carry the canonical phase map; downstream work (T9/T11)
will prove agreement with `holonomyRowRhs` and the Beltrami ratios on Fano cycles.
-/

namespace T9WiringExample

open Hqiv.Topology
open RhFourierLift

/-- Every integrable Hopf shell admits a holonomy phase carrier using the
canonical curvature-driven phase map. This is the T9 stub that makes the
dependency between the new Hopf complex, the discrete null-lattice, and the
rh-fourier-lift PhaseMap concrete and buildable. -/
theorem integrableHopfShell_carries_canonicalPhaseMap
    (s : HopfShell) (h : s.integrable) :
    ∃ carrier : HopfShell.HolonomyPhaseCarrier s,
      carrier.phaseMap = canonicalPhaseMap := by
  refine ⟨
    { phaseMap := canonicalPhaseMap
      reproduces_tuft_holonomy := True }, rfl ⟩

/-! ### Interlocking example: full typed HopfShell carrier set (T6/T7/T9/T11)

This small extension demonstrates the current interlocking state of the typed
Hopf-shell substrate after the focused T7/T9 work.

An integrable `HopfShell` now carries, in one place:
- `toDiscrete3Complex_integrable` → `S3NullReference` (T6 mapping to the
  discrete 3-complex substrate)
- `ContactBeltrami` record with spectrum/multiplicity + the improved
  `stable_under_torsion` formal placeholder (T7, with explicit link to curvature
  channel and fibre torsion)
- `HolonomyPhaseCarrier` using `canonicalPhaseMap`, with the shell's own
  `curvatureImprintAlpha` available as the modulation point for the phase lift
  ω (T9, with documented path to Fano holonomy rows)

The same object is the natural carrier for T11 torsion emergence: the
`ContactBeltrami` spectrum on the shell, combined with the phase-lift Δ and
K-channel imprint, supplies the discrete analogue of TUFT fibre-induced torsion
that can be fed into `ParallelPoincareScaffold` or `GRFromMaxwell`.

This is still scaffold level (no full operator or proved agreement lemmas), but
the pieces now visibly interlock and are buildable together. -/

theorem integrableHopfShell_full_carrier_set
    (s : HopfShell) (h : s.integrable) :
    ∃ (c3 : Discrete3Complex NullShellVertex)
      (cb : ContactBeltrami s)
      (carrier : HopfShell.HolonomyPhaseCarrier s),
      c3 = s.toDiscrete3Complex_integrable h ∧
      carrier.phaseMap = canonicalPhaseMap := by
  refine ⟨
    s.toDiscrete3Complex_integrable h,
    mkContactBeltrami s h,
    { phaseMap := canonicalPhaseMap, reproduces_tuft_holonomy := True },
    rfl, rfl ⟩

/-! ### T11 matrix action: phase-lift Δ as a torsion operator (canonical API)

The matrix-level torsion model for T11 now lives in the canonical typed
`HopfShell` API in `HopfShellComplex.lean` (as `torsionMatrixCoefficient`,
`torsionMatrix`, `torsionAction`, plus the skew-adjointness theorem).

The definitions and proofs below are kept only for historical/example purposes
in the wiring namespace.  All production use should go through the canonical
extensions on `HopfShell`.

See `HopfShellComplex.lean` for the authoritative versions and the T11 bridge
work in `HopfShellBeltramiMassBridge.lean`.

-/

-- The concrete matrix torsion operator is now part of the stable
-- `HopfShell` API (see HopfShellComplex).  The original development
-- of the matrix carrier happened here in the T9/T11 wiring example.

end T9WiringExample

end Hqiv.Topology
