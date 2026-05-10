/-
**SAT ↔ patch index** bridge aligned with `scripts/hqiv_geometric_3sat_demo.py`.

Python `assignment_from_patch_index(j, num_vars)` maps `j` to a tuple in the same order as
`itertools.product((False, True), repeat=n)` — **last variable toggles fastest** (LSB at the last index).

Mathlib’s `finFunctionFinEquiv` encodes `f : Fin n → Fin m` as `∑ i, f i * m^i` (LSB at `i = 0`).
Composing with `Fin.rev` matches the Python bit order (`out[v] =` bit `(n-1-v)` of `j`).

This file proves the **enumeration completeness** statement: satisfiability is equivalent to
some patch index `j < 2^n` evaluating the formula under that decoding — **not** a claim that moiré
scores or thresholds detect satisfiability.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

import Hqiv.Archive.Logic.CNF

namespace Hqiv.Logic

variable {n : ℕ}

/-- `Fin 2` digits for an assignment (`true` ↦ `1`). -/
def assignmentToFin2 (a : Assignment n) : Fin n → Fin 2 :=
  fun v => if a v then 1 else 0

/-- Decode `j` as in `assignment_from_patch_index` / `finFunctionFinEquiv` + bit reversal. -/
def assignmentFromPatchIndex (n : ℕ) (j : Fin (2 ^ n)) : Assignment n :=
  match n with
  | 0 => fun v => v.elim0
  | _ + 1 => fun v =>
      decide
        ((finFunctionFinEquiv.symm j : Fin (Nat.succ _) → Fin 2) (Fin.rev v) = 1)

theorem assignmentFromPatchIndex_finFunctionFinEquiv (a : Assignment n) :
    assignmentFromPatchIndex n (finFunctionFinEquiv (assignmentToFin2 a ∘ Fin.rev)) = a := by
  funext v
  cases n with
  | zero =>
    exact v.elim0
  | succ n' =>
    dsimp [assignmentFromPatchIndex, assignmentToFin2]
    have hsymm :
        (finFunctionFinEquiv.symm (finFunctionFinEquiv (assignmentToFin2 a ∘ Fin.rev))
          : Fin (n' + 1) → Fin 2) =
          assignmentToFin2 a ∘ Fin.rev := by
      simp [Equiv.symm_apply_apply]
    cases ha : a v <;> simp [hsymm, Fin.rev_rev, assignmentToFin2, ha]

/-- **Enumeration bridge:** `φ` is satisfiable iff some `j : Fin (2^n)` passes clause evaluation under
`assignmentFromPatchIndex` (same semantics as Python `eval_sat_at_patch_index` on the first `2^n`
indices, before any modular wrap). -/
theorem CNFFormula.satisfiable_iff_exists_patch_index (φ : CNFFormula n) :
    φ.Satisfiable ↔ ∃ j : Fin (2 ^ n), φ.eval (assignmentFromPatchIndex n j) = true := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨finFunctionFinEquiv (assignmentToFin2 a ∘ Fin.rev), ?_⟩
    simp [assignmentFromPatchIndex_finFunctionFinEquiv a, ha]
  · rintro ⟨j, hj⟩
    exact ⟨assignmentFromPatchIndex n j, hj⟩

end Hqiv.Logic
