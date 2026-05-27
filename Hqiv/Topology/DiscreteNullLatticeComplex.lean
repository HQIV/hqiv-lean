import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Disjoint
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.LatticePointMaxAbsShells

/-!
# Discrete null-lattice 3-complex (scaffold)

Finite closed 3-complexes built from **3+1 null-shell combinatorics** (stars-and-bars tags per shell)
and optional **cubic** spatial tags (`Fin 3 → ℤ`, L∞ shells from `LatticePointMaxAbsShells`).

**Status:** definitions and Tier-1 lemma *targets*; several global lemmas use `sorry` as explicit
obligation markers. Topology is an **output** of the discrete causal + curvature programme, not an
input axiom.

**Not claimed:** identification with a smooth closed 3-manifold, Perelman/Ricci flow, or
\(\mathfrak{so}(8)\) closure forcing \(\pi_1=0\) without `SO8AdmissibleHolonomy` hypotheses.
-/

namespace Hqiv.Topology

open Hqiv Hqiv.Geometry

/-!
## Null-shell vertices (combinatorial substrate)
-/

/-- A vertex on null-shell layer `shell`, tagged by a stars-and-bars mode index. -/
structure NullShellVertex where
  shell : ℕ
  tag : Fin (latticeSimplexCount shell)
  deriving DecidableEq, Repr

namespace NullShellVertex

@[simp] theorem shell_eq (v : NullShellVertex) : v.shell = v.shell := rfl

end NullShellVertex

/-- Optional spatial embedding into the cubic lattice (`ℤ³`, max-|coordinate| shells). -/
structure CubicLatticeVertex where
  coords : Fin 3 → ℤ

/-- Chebyshev shell label for a cubic vertex. -/
def cubicShell (v : CubicLatticeVertex) : ℕ :=
  maxNatAbsCoord v.coords

/-!
## Finite 3-complex (cubical/simplicial bookkeeping)
-/

/-- Undirected edge on the 1-skeleton. -/
structure UndirectedEdge (α : Type) where
  a : α
  b : α
  no_self : a ≠ b

/-- A finite closed 3-complex: 0–3 cells plus closure axioms (partial). -/
structure Discrete3Complex (α : Type) where
  /-- Vertex labels. -/
  vertices : Finset α
  /-- 1-cells (unordered pairs). -/
  edges : Finset (UndirectedEdge α)
  /-- 2-cells: oriented triangles as ordered 3-tuples (convention fixed per instance). -/
  triangles : Finset (α × α × α)
  /-- 3-cells: tetrahedra as 4-tuples. -/
  tetrahedra : Finset (α × α × α × α)
  /-- No boundary: every edge lies in at least one triangle (closedness sketch). -/
  edge_closed : ∀ e ∈ edges, ∃ t ∈ triangles, e.a = t.1 ∧ e.b = t.2.1 ∨ e.a = t.2.1 ∧ e.b = t.1

namespace Discrete3Complex

variable {α : Type}

/-- Count vertices lying on a given null-shell layer (when `α = NullShellVertex`). -/
def vertexCountAtShell (M : Discrete3Complex NullShellVertex) (m : ℕ) : ℕ :=
  (M.vertices.filter fun v => v.shell = m).card

/-- Combinatorial Euler characteristic \(\chi = |V| - |E| + |F| - |T|\) for a 3-dimensional complex. -/
def eulerCharacteristic (M : Discrete3Complex α) : ℤ :=
  (M.vertices.card : ℤ) - (M.edges.card : ℤ) + (M.triangles.card : ℤ) - (M.tetrahedra.card : ℤ)

end Discrete3Complex

/-!
## Discrete fundamental group (placeholder)
-/

/-- Generators for the discrete fundamental group (1-cycles modulo 2-skeleton relations). -/
structure DiscreteFundamentalGroup (α : Type) where
  /-- Generators indexed by a finite set. -/
  generators : Type
  [fin : Fintype generators]
  /-- Triviality: every generator is null-homotopic in the 2-skeleton. -/
  all_trivial : Prop

/-- Simply connected: at most one equivalence class (scaffold). -/
def SimplyConnected {α : Type} (_M : Discrete3Complex α) : Prop :=
  Subsingleton (DiscreteFundamentalGroup α)

/-!
## Shell budget vs quadratic growth law
-/

/-- Signed mismatch between occupied vertices and `latticeSimplexCount m` on shell `m`. -/
def shellBudgetMismatch (M : Discrete3Complex NullShellVertex) (m : ℕ) : ℤ :=
  (Discrete3Complex.vertexCountAtShell M m : ℤ) - (latticeSimplexCount m : ℤ)

/-- Idealized growth on **all** shells `m : ℕ` (continuum / infinite-horizon limit only).
Finite `Discrete3Complex`es cannot satisfy this — see `not_quadratic_null_shell_growth`. -/
structure QuadraticNullShellGrowth (M : Discrete3Complex NullShellVertex) : Prop where
  vertex_count_eq : ∀ m : ℕ, Discrete3Complex.vertexCountAtShell M m = latticeSimplexCount m

/-- **Finite-horizon law (primary).** Quadratic null-shell budget on shells `0 … n` at horizon `n`.
`S3NullReference n` satisfies this; the parallel Poincaré bridge uses this, not global growth. -/
structure QuadraticNullShellGrowthOnHorizon (M : Discrete3Complex NullShellVertex) (n : ℕ) where
  vertex_count_eq : ∀ m ≤ n, Discrete3Complex.vertexCountAtShell M m = latticeSimplexCount m

/-- Alias emphasizing the finite-complex / holonomy-bridge use case. -/
abbrev QuadraticNullShellGrowthFinite (M : Discrete3Complex NullShellVertex) (n : ℕ) :=
  QuadraticNullShellGrowthOnHorizon M n

/-- Maximum null-shell label among vertices (0 if empty). -/
def maxVertexShell (M : Discrete3Complex NullShellVertex) : ℕ :=
  Finset.sup M.vertices fun v => v.shell

theorem vertex_shell_le_maxVertexShell {M : Discrete3Complex NullShellVertex} {v : NullShellVertex}
    (hv : v ∈ M.vertices) : v.shell ≤ maxVertexShell M :=
  Finset.le_sup (f := fun v : NullShellVertex => v.shell) hv

theorem vertexCountAtShell_zero_of_gt_maxVertexShell (M : Discrete3Complex NullShellVertex)
    {m : ℕ} (hm : maxVertexShell M < m) :
    Discrete3Complex.vertexCountAtShell M m = 0 := by
  unfold Discrete3Complex.vertexCountAtShell
  have hnon : ¬ (M.vertices.filter fun v => v.shell = m).Nonempty := by
    rintro ⟨v, hv⟩
    rcases Finset.mem_filter.mp hv with ⟨hv_in, hshell⟩
    have hle : v.shell ≤ maxVertexShell M := vertex_shell_le_maxVertexShell hv_in
    have hgt : maxVertexShell M < v.shell := by simpa [hshell] using hm
    exact not_lt_of_ge hle hgt
  rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.card_empty]

/-- **No finite complex** satisfies global `QuadraticNullShellGrowth`: shells above the top
occupied layer (or shell 0 when empty) violate `latticeSimplexCount m > 0`. -/
theorem not_quadratic_null_shell_growth (M : Discrete3Complex NullShellVertex) :
    ¬ QuadraticNullShellGrowth M := by
  intro h
  by_cases hne : M.vertices.Nonempty
  · have hz :
        Discrete3Complex.vertexCountAtShell M (maxVertexShell M + 1) = 0 :=
      vertexCountAtShell_zero_of_gt_maxVertexShell M (Nat.lt_succ_self _)
    have hp : 0 < latticeSimplexCount (maxVertexShell M + 1) :=
      latticeSimplexCount_pos _
    rw [h.vertex_count_eq (maxVertexShell M + 1)] at hz
    linarith [latticeSimplexCount_pos (maxVertexShell M + 1)]
  · have hz : Discrete3Complex.vertexCountAtShell M 0 = 0 := by
      unfold Discrete3Complex.vertexCountAtShell
      have hnon : ¬ (M.vertices.filter fun v => v.shell = 0).Nonempty := by
        rintro ⟨v, hv⟩
        rcases Finset.mem_filter.mp hv with ⟨hv_in, _⟩
        exact hne ⟨v, hv_in⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.card_empty]
    rw [h.vertex_count_eq 0] at hz
    linarith [latticeSimplexCount_pos 0]

theorem quadraticNullShellGrowth_shell_budget_zero (M : Discrete3Complex NullShellVertex)
    (h : QuadraticNullShellGrowth M) (m : ℕ) :
    shellBudgetMismatch M m = 0 := by
  simp [shellBudgetMismatch, h.vertex_count_eq]

theorem quadraticNullShellGrowthOnHorizon_shell_budget_zero
    (M : Discrete3Complex NullShellVertex) (n : ℕ)
    (h : QuadraticNullShellGrowthOnHorizon M n) {m : ℕ} (hm : m ≤ n) :
    shellBudgetMismatch M m = 0 := by
  simp [shellBudgetMismatch, h.vertex_count_eq m hm]

theorem quadraticNullShellGrowth_iff_forall (M : Discrete3Complex NullShellVertex) :
    QuadraticNullShellGrowth M ↔
      ∀ m, Discrete3Complex.vertexCountAtShell M m = latticeSimplexCount m := by
  constructor
  · intro h m
    exact h.vertex_count_eq m
  · intro h
    exact ⟨h⟩

/-- Local shell defect ↔ failure of quadratic null-shell growth (Tier-1 detection). -/
theorem exists_shell_budget_mismatch_iff_not_quadratic (M : Discrete3Complex NullShellVertex) :
    (∃ m, shellBudgetMismatch M m ≠ 0) ↔ ¬ QuadraticNullShellGrowth M := by
  constructor
  · rintro ⟨m, hm⟩ hq
    dsimp [shellBudgetMismatch] at hm ⊢
    rw [hq.vertex_count_eq] at hm
    simpa using hm
  · intro h
    rw [quadraticNullShellGrowth_iff_forall] at h
    push_neg at h
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_⟩
    simp only [shellBudgetMismatch, sub_ne_zero]
    exact_mod_cast hm

/-- A **fully triangulated** closed 3-manifold has \(\chi = 0\) (e.g. \(\chi(S^3)=0\); \(\chi(S^2)=2\) is 2D). -/
def IsCombinatoriallySpherical {α : Type} (M : Discrete3Complex α) : Prop :=
  M.eulerCharacteristic = 0

/-- Combinatorial equivalence (placeholder: explicit bijection on cells). -/
structure CombinatoriallyEquivalent {α β : Type} (M : Discrete3Complex α) (N : Discrete3Complex β) where
  vertexEquiv : M.vertices ≃ N.vertices

/-!
## Reference discrete 3-sphere template
-/

/-- Vertices on a single null-shell layer: one per stars-and-bars tag at shell `m`. -/
def nullShellVertsAt (m : ℕ) : Finset NullShellVertex :=
  (Finset.univ : Finset (Fin (latticeSimplexCount m))).map
    ⟨fun t => ⟨m, t⟩, fun t₁ t₂ h => by
      cases h
      rfl⟩

theorem nullShellVertsAt_card (m : ℕ) :
    (nullShellVertsAt m).card = latticeSimplexCount m := by
  classical
  dsimp [nullShellVertsAt]
  rw [Finset.card_map]
  simp [latticeSimplexCount]

theorem nullShellVertsAt_pairwiseDisjoint (n : ℕ) :
    (Finset.range (n + 1) : Set ℕ).PairwiseDisjoint nullShellVertsAt := by
  intro m hm m' hm' hne
  refine Finset.disjoint_left.mpr ?_
  intro v hv hm'
  simp only [nullShellVertsAt, Finset.mem_map, Finset.mem_univ, true_and] at hv hm'
  obtain ⟨t, _, rfl⟩ := hv
  obtain ⟨t', _, rfl⟩ := hm'
  exact hne rfl

/-- Reference complex at horizon index `n`: one vertex per stars-and-bars tag on each shell `0…n`. -/
noncomputable def S3NullReference (n : ℕ) : Discrete3Complex NullShellVertex :=
  { vertices := Finset.biUnion (Finset.range (n + 1)) nullShellVertsAt
    edges := ∅
    triangles := ∅
    tetrahedra := ∅
    edge_closed := by
      intro e he
      simp at he }

theorem S3NullReference_vertex_count (n : ℕ) :
    (S3NullReference n).vertices.card =
      ∑ m ∈ Finset.range (n + 1), latticeSimplexCount m := by
  classical
  dsimp [S3NullReference]
  rw [Finset.card_biUnion (nullShellVertsAt_pairwiseDisjoint n)]
  refine Finset.sum_congr rfl ?_
  intro m _
  exact nullShellVertsAt_card m

theorem S3NullReference_filter_shell_eq (n m : ℕ) (hm : m ≤ n) :
    ((S3NullReference n).vertices.filter fun v => v.shell = m) = nullShellVertsAt m := by
  classical
  ext v
  dsimp [S3NullReference]
  constructor
  · intro hv
    simp only [Finset.mem_filter, S3NullReference] at hv
    obtain ⟨hv_in, hshell⟩ := hv
    obtain ⟨m', _, hv'⟩ := Finset.mem_biUnion.mp hv_in
    simp only [nullShellVertsAt, Finset.mem_map, Finset.mem_univ, true_and] at hv'
    obtain ⟨t, _, rfl⟩ := hv'
    have hm_eq : m' = m := by simpa using hshell
    subst hm_eq
    refine Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · intro hv
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), hv⟩
    · simp only [nullShellVertsAt, Finset.mem_map, Finset.mem_univ, true_and] at hv
      obtain ⟨t, _, rfl⟩ := hv
      rfl

/-- On shells inside the horizon, the reference realizes the quadratic null-shell budget exactly. -/
theorem S3NullReference_vertexCountAtShell (n m : ℕ) (hm : m ≤ n) :
    Discrete3Complex.vertexCountAtShell (S3NullReference n) m = latticeSimplexCount m := by
  unfold Discrete3Complex.vertexCountAtShell
  rw [S3NullReference_filter_shell_eq n m hm, nullShellVertsAt_card]

theorem S3NullReference_shell_budget_zero (n m : ℕ) (hm : m ≤ n) :
    shellBudgetMismatch (S3NullReference n) m = 0 := by
  simp [shellBudgetMismatch, S3NullReference_vertexCountAtShell n m hm]

theorem S3NullReference_quadratic_on_horizon (n : ℕ) :
    QuadraticNullShellGrowthOnHorizon (S3NullReference n) n where
  vertex_count_eq m hm := S3NullReference_vertexCountAtShell n m hm

theorem S3NullReference_vertices_card_pos (n : ℕ) :
    0 < (S3NullReference n).vertices.card := by
  rw [S3NullReference_vertex_count]
  have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.succ_pos n)
  exact lt_of_lt_of_le (latticeSimplexCount_pos 0) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)

/-- Matches the null-lattice vertex template at horizon `n` (weaker than \(\chi=0\) until 2/3-cells are populated). -/
def IsS3NullVertexTemplate (M : Discrete3Complex NullShellVertex) (n : ℕ) : Prop :=
  Nonempty (CombinatoriallyEquivalent M (S3NullReference n))

/-!
## Tier-1 targets (local detection of handles / shell defects)
-/

/-- Vertex-only bookkeeping (no 1–3 cells populated yet). -/
def IsVertexOnly (M : Discrete3Complex NullShellVertex) : Prop :=
  M.edges = ∅ ∧ M.triangles = ∅ ∧ M.tetrahedra = ∅

theorem eulerCharacteristic_eq_vertexCard {M : Discrete3Complex NullShellVertex}
    (hV : IsVertexOnly M) :
    M.eulerCharacteristic = (M.vertices.card : ℤ) := by
  rcases hV with ⟨he, ht, htet⟩
  simp [Discrete3Complex.eulerCharacteristic, he, ht, htet]

/-- Vertex-only reference template has \(\chi = |V| > 0\) (not combinatorially spherical). -/
theorem S3NullReference_not_combinatorially_spherical (n : ℕ) :
    ¬ IsCombinatoriallySpherical (S3NullReference n) := by
  unfold IsCombinatoriallySpherical
  have hV : IsVertexOnly (S3NullReference n) := by
    dsimp [IsVertexOnly, S3NullReference]
    simp
  rw [eulerCharacteristic_eq_vertexCard hV]
  have hpos : 0 < (S3NullReference n).vertices.card := S3NullReference_vertices_card_pos n
  linarith

theorem shellBudgetMismatch_pos_imp_vertexCount_pos (M : Discrete3Complex NullShellVertex)
    (m : ℕ) (hpos : 0 < shellBudgetMismatch M m) :
    0 < Discrete3Complex.vertexCountAtShell M m := by
  unfold shellBudgetMismatch at hpos
  have hlt : latticeSimplexCount m < Discrete3Complex.vertexCountAtShell M m := by omega
  exact Nat.lt_trans (latticeSimplexCount_pos m) hlt

theorem shellBudgetMismatch_pos_imp_vertices_nonempty (M : Discrete3Complex NullShellVertex)
    (m : ℕ) (hpos : 0 < shellBudgetMismatch M m) :
    M.vertices.Nonempty := by
  have hcount := shellBudgetMismatch_pos_imp_vertexCount_pos M m hpos
  unfold Discrete3Complex.vertexCountAtShell at hcount
  rcases Finset.card_pos.mp hcount with ⟨v, hv⟩
  exact ⟨v, (Finset.mem_filter.mp hv).1⟩

/-- **Shell budget defect** obstructs quadratic null-shell growth (any sign of mismatch). -/
theorem shell_budget_detects_handle (M : Discrete3Complex NullShellVertex) :
    (∃ m, shellBudgetMismatch M m ≠ 0) → ¬ QuadraticNullShellGrowth M :=
  (exists_shell_budget_mismatch_iff_not_quadratic M).mp

/-- **Positive excess** on a shell (more vertices than the quadratic budget) forces \(\chi \neq 0\)
for vertex-only complexes. Deficit-only mismatch (e.g. the empty complex) does not; full
triangulation layer is still required to link budget defects to \(\chi = 0\) in general. -/
theorem shell_budget_excess_obstructs_chi_zero (M : Discrete3Complex NullShellVertex)
    (hV : IsVertexOnly M) (m : ℕ) (hpos : 0 < shellBudgetMismatch M m) :
    ¬ IsCombinatoriallySpherical M := by
  unfold IsCombinatoriallySpherical
  rw [eulerCharacteristic_eq_vertexCard hV]
  have hpos' : 0 < M.vertices.card :=
    Finset.card_pos.mpr (shellBudgetMismatch_pos_imp_vertices_nonempty M m hpos)
  linarith

/-- Reference vertex template is equivalent to itself. -/
theorem S3NullReference_is_template (n : ℕ) :
    IsS3NullVertexTemplate (S3NullReference n) n := by
  unfold IsS3NullVertexTemplate
  exact ⟨{
    vertexEquiv := Equiv.refl _
  }⟩

end Hqiv.Topology
