import HqivSpine.Topology.NullLatticeComplex
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `HqivSpine.Topology.ShellBudget` — the signed shell ledger

A three-layer separation for the thermodynamic-arrow / parallel-Poincaré programme, built on
`Topology.NullLatticeComplex`:

1. **Signed shell ledger** — `shellBudgetMismatch : ℤ` = occupied vertices minus the
   quadratic budget `latticeSimplexCount m = (m+2)(m+1)`; **negative** values mark closed /
   under-occupied shells, **positive** ones over-filled defects.
2. **Lyapunov fronts** — `totalNegativeBudget` / `totalEarlyNegativeBudget`, the `ℕ`-valued
   deficit sums used for lexicographic descent toward the reference; the reference
   `S3NullReference n` has zero deficit (`S3NullReference_totalNegativeBudget_zero`).
3. **Early-closed regime** — the continuous horizon coordinate `ξ = m+1` with the half-step
   anchor `xiHalfStep = 7/2`, so `isEarlyClosedShell m ↔ m ≤ 2`
   (`isEarlyClosedShell_iff_le_two`).

The deficit-only readout characterises on-horizon quadratic growth
(`deficitOnly_no_negative_budget_imp_quadraticOnHorizon`).

Self-contained on spine definitions; Mathlib + spine only, no legacy `Hqiv.*`, no `sorry`,
no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Topology

open HqivSpine.Physics
open scoped BigOperators Classical

/-! ## Continuous chart and early-closed regime -/

/-- Continuous horizon coordinate `ξ = m + 1`. -/
noncomputable def shellXi (m : ℕ) : ℝ := (m + 1 : ℝ)

@[simp] theorem shellXi_eq (m : ℕ) : shellXi m = (m + 1 : ℝ) := rfl

/-- Half-step horizon anchor `ξ = 7/2` (the EM-normalisation witness value). -/
noncomputable def xiHalfStep : ℝ := 7 / 2

/-- Early closed shells: `ξ ≤ 7/2`. -/
def isEarlyClosedShell (m : ℕ) : Prop :=
  shellXi m ≤ xiHalfStep

theorem isEarlyClosedShell_iff_le_two (m : ℕ) : isEarlyClosedShell m ↔ m ≤ 2 := by
  simp only [isEarlyClosedShell, shellXi, xiHalfStep]
  constructor
  · intro h
    by_contra hm
    push_neg at hm
    have h3 : 3 ≤ m := hm
    have hgt : (7 / 2 : ℝ) < (m + 1 : ℝ) := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
      norm_num
      linarith
    linarith [h]
  · intro hm
    have hle : (m + 1 : ℝ) ≤ 3 := by
      have : m + 1 ≤ 3 := by omega
      exact_mod_cast this
    have hhalf : (3 : ℝ) ≤ (7 / 2 : ℝ) := by norm_num
    exact le_trans hle hhalf

theorem isEarlyClosedShell_zero : isEarlyClosedShell 0 :=
  (isEarlyClosedShell_iff_le_two 0).mpr (Nat.zero_le _)

theorem isEarlyClosedShell_two : isEarlyClosedShell 2 :=
  (isEarlyClosedShell_iff_le_two 2).mpr (by norm_num)

theorem not_isEarlyClosedShell_three : ¬ isEarlyClosedShell 3 :=
  fun h => Nat.not_succ_le_self 2 ((isEarlyClosedShell_iff_le_two 3).mp h)

/-! ## Signed ledger predicates -/

/-- Shell is under-occupied relative to the quadratic null-shell budget. -/
def negativeBudget (M : Discrete3Complex NullShellVertex) (m : ℕ) : Prop :=
  shellBudgetMismatch M m < 0

/-- Shell is open at the quadratic budget (equilibrium on that layer). -/
def shellBudgetOpen (M : Discrete3Complex NullShellVertex) (m : ℕ) : Prop :=
  shellBudgetMismatch M m = 0

/-- Over-filled shell (positive mismatch). -/
def positiveBudget (M : Discrete3Complex NullShellVertex) (m : ℕ) : Prop :=
  0 < shellBudgetMismatch M m

/-- Absolute mismatch (`ℕ` building block for a lexicographic Lyapunov measure). -/
def shellBudgetMismatchNatAbs (M : Discrete3Complex NullShellVertex) (m : ℕ) : ℕ :=
  (shellBudgetMismatch M m).natAbs

theorem negativeBudget_pos_natAbs (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : negativeBudget M m) : 0 < shellBudgetMismatchNatAbs M m := by
  unfold negativeBudget shellBudgetMismatchNatAbs at *
  exact Int.natAbs_pos.mpr (Int.ne_of_lt h)

theorem positiveBudget_pos_natAbs (M : Discrete3Complex NullShellVertex) (m : ℕ)
    (h : positiveBudget M m) : 0 < shellBudgetMismatchNatAbs M m := by
  unfold positiveBudget shellBudgetMismatchNatAbs at *
  exact Int.natAbs_pos.mpr (Int.ne_of_gt h)

/-- Active shells for a complex: `0 … maxVertexShell M`. -/
def activeShellRange (M : Discrete3Complex NullShellVertex) : Finset ℕ :=
  Finset.range (maxVertexShell M + 1)

/-- Early shells within the active range (`m ≤ 2`). -/
def earlyActiveShellRange (M : Discrete3Complex NullShellVertex) : Finset ℕ :=
  Finset.filter (fun m => m ≤ 2) (activeShellRange M)

/-- Total negative budget on active shells (`ℕ` front for lexicographic descent). -/
noncomputable def totalNegativeBudget (M : Discrete3Complex NullShellVertex) : ℕ :=
  ∑ m ∈ activeShellRange M,
    if negativeBudget M m then shellBudgetMismatchNatAbs M m else 0

/-- Negative budget counted only on early closed shells (`m ≤ 2`). -/
noncomputable def totalEarlyNegativeBudget (M : Discrete3Complex NullShellVertex) : ℕ :=
  ∑ m ∈ earlyActiveShellRange M,
    if negativeBudget M m then shellBudgetMismatchNatAbs M m else 0

theorem totalEarlyNegativeBudget_le_totalNegativeBudget (M : Discrete3Complex NullShellVertex) :
    totalEarlyNegativeBudget M ≤ totalNegativeBudget M := by
  unfold totalEarlyNegativeBudget totalNegativeBudget activeShellRange earlyActiveShellRange
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m _ _ => by
    split_ifs <;> exact Nat.zero_le _

/-! ## Reference and growth-law links -/

theorem S3NullReference_not_negativeBudget (n m : ℕ) (hm : m ≤ n) :
    ¬ negativeBudget (S3NullReference n) m := by
  unfold negativeBudget
  intro h
  rw [S3NullReference_shell_budget_zero n m hm] at h
  exact Int.not_lt.mpr le_rfl h

theorem S3NullReference_shellBudgetOpen (n m : ℕ) (hm : m ≤ n) :
    shellBudgetOpen (S3NullReference n) m :=
  S3NullReference_shell_budget_zero n m hm

theorem quadraticOnHorizon_shellBudgetOpen {M : Discrete3Complex NullShellVertex} {n : ℕ}
    (h : QuadraticNullShellGrowthOnHorizon M n) {m : ℕ} (hm : m ≤ n) :
    shellBudgetOpen M m :=
  quadraticNullShellGrowthOnHorizon_shell_budget_zero M n h hm

theorem quadraticOnHorizon_not_negativeBudget {M : Discrete3Complex NullShellVertex} {n : ℕ}
    (h : QuadraticNullShellGrowthOnHorizon M n) {m : ℕ} (hm : m ≤ n) :
    ¬ negativeBudget M m := by
  unfold negativeBudget
  intro hneg
  rw [quadraticOnHorizon_shellBudgetOpen h hm] at hneg
  exact Int.not_lt.mpr le_rfl hneg

theorem S3NullReference_vertex_shell_le (n : ℕ) {v : NullShellVertex}
    (hv : v ∈ (S3NullReference n).vertices) : v.shell ≤ n := by
  classical
  simp only [S3NullReference] at hv
  obtain ⟨m, hm, hv'⟩ := Finset.mem_biUnion.mp hv
  simp only [nullShellVertsAt, Finset.mem_map, Finset.mem_univ, true_and] at hv'
  obtain ⟨t, _, rfl⟩ := hv'
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)

theorem maxVertexShell_S3NullReference_le (n : ℕ) :
    n ≤ maxVertexShell (S3NullReference n) := by
  classical
  have hv :
      (⟨n, ⟨0, latticeSimplexCount_pos n⟩⟩ : NullShellVertex) ∈ (S3NullReference n).vertices := by
    have hfilter :
        (⟨n, ⟨0, latticeSimplexCount_pos n⟩⟩ : NullShellVertex) ∈
          (S3NullReference n).vertices.filter (fun w : NullShellVertex => w.shell = n) := by
      rw [S3NullReference_filter_shell_eq n n (Nat.le_refl n)]
      refine Finset.mem_map.mpr ⟨⟨0, latticeSimplexCount_pos n⟩, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_filter.mp hfilter).1
  have hshell : (⟨n, ⟨0, latticeSimplexCount_pos n⟩⟩ : NullShellVertex).shell = n := rfl
  dsimp [maxVertexShell]
  calc
    n = (⟨n, ⟨0, latticeSimplexCount_pos n⟩⟩ : NullShellVertex).shell := hshell.symm
    _ ≤ _ := Finset.le_sup hv

theorem maxVertexShell_S3NullReference (n : ℕ) :
    maxVertexShell (S3NullReference n) = n := by
  classical
  apply le_antisymm
  · refine Finset.sup_le fun v hv => S3NullReference_vertex_shell_le n hv
  · exact maxVertexShell_S3NullReference_le n

theorem S3NullReference_activeShell_le (n m : ℕ)
    (hm : m ∈ activeShellRange (S3NullReference n)) : m ≤ n := by
  simp only [activeShellRange, Finset.mem_range, maxVertexShell_S3NullReference] at hm
  exact Nat.le_of_lt_succ hm

theorem S3NullReference_totalNegativeBudget_zero (n : ℕ) :
    totalNegativeBudget (S3NullReference n) = 0 := by
  unfold totalNegativeBudget negativeBudget activeShellRange shellBudgetMismatchNatAbs
  refine Finset.sum_eq_zero fun m hm => ?_
  split_ifs with hneg
  · exact absurd hneg (S3NullReference_not_negativeBudget n m (S3NullReference_activeShell_le n m hm))
  · rfl

/-- No shell excess above the quadratic budget on `0 … n` (deficit-only readout). -/
def deficitOnlyOnHorizon (M : Discrete3Complex NullShellVertex) (n : ℕ) : Prop :=
  ∀ m ≤ n, shellBudgetMismatch M m ≤ 0

theorem not_negativeBudget_iff_nonneg (M m) :
    ¬ negativeBudget M m ↔ 0 ≤ shellBudgetMismatch M m := by
  simp [negativeBudget]

theorem deficitOnly_and_not_negative_imp_open (M n m)
    (hdef : deficitOnlyOnHorizon M n) (hm : m ≤ n) (hnn : ¬ negativeBudget M m) :
    shellBudgetOpen M m := by
  unfold shellBudgetOpen
  exact le_antisymm (hdef m hm) ((not_negativeBudget_iff_nonneg M m).mp hnn)

/-- **Deficit-only + no negative budget ⇒ on-horizon quadratic growth.** -/
theorem deficitOnly_no_negative_budget_imp_quadraticOnHorizon
    (M : Discrete3Complex NullShellVertex) (n : ℕ)
    (hdef : deficitOnlyOnHorizon M n) (hmax : maxVertexShell M = n)
    (hno : ∀ m ∈ activeShellRange M, ¬ negativeBudget M m) :
    QuadraticNullShellGrowthOnHorizon M n := by
  refine ⟨fun m hm => ?_⟩
  have hm_act : m ∈ activeShellRange M := by
    simp only [activeShellRange, Finset.mem_range, hmax]
    exact Nat.lt_succ_of_le hm
  have hopen := deficitOnly_and_not_negative_imp_open M n m hdef hm (hno m hm_act)
  unfold shellBudgetOpen shellBudgetMismatch at hopen
  have hEq : (Discrete3Complex.vertexCountAtShell M m : ℤ) = latticeSimplexCount m := by
    omega
  exact_mod_cast hEq

theorem S3NullReference_totalEarlyNegativeBudget_zero (n : ℕ) :
    totalEarlyNegativeBudget (S3NullReference n) = 0 := by
  unfold totalEarlyNegativeBudget negativeBudget earlyActiveShellRange activeShellRange
    shellBudgetMismatchNatAbs
  refine Finset.sum_eq_zero fun m hm => ?_
  simp only [Finset.mem_filter, Finset.mem_range, maxVertexShell_S3NullReference] at hm
  rcases hm with ⟨hm_rng, _⟩
  have hmle : m ≤ n := Nat.le_of_lt_succ hm_rng
  split_ifs with hneg
  · exact absurd hneg (S3NullReference_not_negativeBudget n m hmle)
  · rfl

end HqivSpine.Topology
