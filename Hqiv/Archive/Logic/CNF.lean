/-
General **CNF** and satisfiability, with **uniform k-SAT** (in particular **3-SAT**) as
defined special cases — not a parallel copy of the theory.

This is the Lean spine aligned with `scripts/hqiv_geometric_3sat_demo.py`:

* literals, clauses (lists of any positive length), and conjunctions;
* semantics with the usual convention: the empty clause is false; the empty CNF is true;
* narrative **Ω-encoding weight** (`literalOmegaWeight`, `formulaOmegaEnc`) defined for
  **any** clause length, so the prime-product story extends from 3 literals per clause
  to **n literals per clause** without changing the API shape.

Enumeration of assignments along a patch index (Python `assignment_from_patch_index`) is in
`Hqiv.Archive.Logic.CNFPatchBridge`. No claim is made here about the octonion-shell / moiré score bridge;
see `AGENTS/archive/OCTONION_SAT_PIPELINE.md`.
-/

import Mathlib.Data.List.Basic

namespace Hqiv.Logic

variable {n : ℕ}

/-- Variable = index in `Fin n`; `neg` means the literal is logically negated. -/
structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq, Repr

/-- Assignment of truth values to each variable. -/
abbrev Assignment (n : ℕ) :=
  Fin n → Bool

namespace Literal

/-- A literal is satisfied iff the variable matches the polarity (`¬` when `neg`). -/
def satisfies (a : Assignment n) (l : Literal n) : Bool :=
  a l.var == !l.neg

end Literal

/-- A **clause** is a disjunction of any finite number of literals (including zero). -/
abbrev Clause (n : ℕ) :=
  List (Literal n)

namespace Clause

/-- Semantics: empty clause = `false`; otherwise OR of literal satisfaction. -/
def eval (a : Assignment n) (c : Clause n) : Bool :=
  c.any fun l => l.satisfies a

@[simp] theorem eval_nil (a : Assignment n) : eval a ([] : Clause n) = false := by
  simp [eval]

end Clause

/-- **CNF**: conjunction of clauses. -/
structure CNFFormula (n : ℕ) where
  clauses : List (Clause n)
  deriving Repr

namespace CNFFormula

/-- Semantics: empty CNF = `true`; otherwise AND of clause values. -/
def eval (a : Assignment n) (φ : CNFFormula n) : Bool :=
  φ.clauses.all fun c => c.eval a

@[simp] theorem eval_nil (a : Assignment n) : eval a ⟨[]⟩ = true := by
  simp [eval]

/-- Satisfiability (existential semantics in `Prop`). -/
def Satisfiable (φ : CNFFormula n) : Prop :=
  ∃ a : Assignment n, φ.eval a = true

/-- **Uniform k-SAT**: every clause has exactly `k` literals (`k = 3` is 3-SAT). -/
def IsUniformKSAT (k : ℕ) (φ : CNFFormula n) : Prop :=
  ∀ c ∈ φ.clauses, c.length = k

/-- **3-CNF** as uniform 3-SAT. -/
abbrev IsThreeCNF (φ : CNFFormula n) : Prop :=
  IsUniformKSAT 3 φ

theorem isThreeCNF_iff_uniform3 (φ : CNFFormula n) :
    IsThreeCNF φ ↔ IsUniformKSAT 3 φ :=
  Iff.rfl

end CNFFormula

/-- Bundle a formula with a proof that it is 3-CNF (convenient for downstream refinements). -/
structure ThreeCNF (n : ℕ) where
  formula : CNFFormula n
  hthree : ∀ c ∈ formula.clauses, c.length = 3

namespace ThreeCNF

/-- A bundled 3-CNF is definitionally uniform-3. -/
theorem isUniform (φ : ThreeCNF n) : CNFFormula.IsUniformKSAT 3 φ.formula :=
  φ.hthree

/-- Forget the width witness — **3-SAT instances are CNF instances**. -/
def toCNF (φ : ThreeCNF n) : CNFFormula n :=
  φ.formula

end ThreeCNF

/-! ### Narrative Ω-encoding (extends to arbitrary clause length) -/

namespace Literal

/-- Prime-factor **weight** per literal: positive → 1 factor, negated → 2 (matches Python demo). -/
def omegaWeight (l : Literal n) : ℕ :=
  if l.neg then 2 else 1

end Literal

namespace Clause

/-- Sum of literal weights along a clause (any length). -/
def omegaEnc (c : Clause n) : ℕ :=
  c.foldl (fun acc l => acc + l.omegaWeight) 0

end Clause

namespace CNFFormula

/-- Total Ω-encoding statistic for a whole formula (sum over clauses). -/
def omegaEnc (φ : CNFFormula n) : ℕ :=
  φ.clauses.foldl (fun acc c => acc + c.omegaEnc) 0

private theorem foldl_add_eq_acc_add_sum (cs : List (Clause n)) (acc : ℕ) :
    cs.foldl (fun a c => a + c.omegaEnc) acc = acc + (cs.map Clause.omegaEnc).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp [List.foldl, List.map, List.sum, ih, Nat.add_assoc]

theorem omegaEnc_eq_sum_clause_omega (φ : CNFFormula n) :
    φ.omegaEnc = (φ.clauses.map Clause.omegaEnc).sum := by
  simpa [CNFFormula.omegaEnc, Nat.zero_add] using foldl_add_eq_acc_add_sum φ.clauses 0

/-- For uniform 3-SAT, each clause contributes between 3 and 6 to `omegaEnc`. -/
theorem clause_omegaEnc_three_bounds (c : Clause n) (h : c.length = 3) :
    3 ≤ c.omegaEnc ∧ c.omegaEnc ≤ 6 := by
  rcases List.length_eq_three.mp h with ⟨l₁, l₂, l₃, rfl⟩
  rcases l₁ with ⟨_v₁, n₁⟩
  rcases l₂ with ⟨_v₂, n₂⟩
  rcases l₃ with ⟨_v₃, n₃⟩
  cases n₁ <;> cases n₂ <;> cases n₃ <;>
    simp [Clause.omegaEnc, Literal.omegaWeight, List.foldl]

end CNFFormula

end Hqiv.Logic
