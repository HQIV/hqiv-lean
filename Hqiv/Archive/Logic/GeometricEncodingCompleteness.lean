/-
# Geometric **encoding completeness** (paper statement)

This module isolates the **single logical commitment** behind the outer `k`-sweep in the HQIV
geometric SAT demo (`scripts/hqiv_geometric_3sat_demo.py`):

* **`P φ k`** — **null / advance-`k`** pattern at mode index `k` (e.g. BST finds the **same** slope
  diagnostic on **both** sides of the patch — “nothing to see here, try next `k`”).
* **Encoding completeness** — if `φ` is satisfiable, then **some** `k` is **not** null
  (`∃ k, ¬ P φ k`).

Everything here is **pure propositional logic** over an abstract predicate `P`. **Sound** geometry
instantiates `P` from moiré scores; the **encoding completeness** implication is the **paper target**
unless/until it is derived from analytic hypotheses.

**Proved (no `sorry`):** equivalence with the **contrapositive** form used by the procedure:
“`∀ k, P φ k` ⇒ `φ` unsatisfiable”. Under encoding completeness, an outer loop that only **stops**
on non-null `k` **cannot miss** a satisfiable instance — **if** `P` is the right predicate.

**Not proved here:** that a concrete moiré construction instantiates `P` such that encoding
completeness holds for **all** CNFs (that would be a major theorem).
-/

import Hqiv.Archive.Logic.CNF

namespace Hqiv.Logic

open Classical in
variable {n : ℕ}

/-- Predicate: at formula `φ` and mode `k`, the diagnostic is the **null** pattern (e.g. matching
slopes on both patch sides — safe to advance `k`). -/
abbrev MoireNullPattern (n : ℕ) :=
  CNFFormula n → ℕ → Prop

/-- **Encoding completeness** (paper §*target*): satisfiability forces a **non-null** mode. -/
def EncodingCompleteness (P : MoireNullPattern n) : Prop :=
  ∀ φ : CNFFormula n, φ.Satisfiable → ∃ k : ℕ, ¬ P φ k

/-- Finite `k`-range: only `k : Fin K` are scanned (outer loop bound). -/
def EncodingCompletenessFin (K : ℕ) (P : CNFFormula n → Fin K → Prop) : Prop :=
  ∀ φ : CNFFormula n, φ.Satisfiable → ∃ k : Fin K, ¬ P φ k

/-- Contrapositive form: global null pattern ⇒ unsatisfiable. -/
def NullPatternGloballyImpliesUnsat (P : MoireNullPattern n) : Prop :=
  ∀ φ : CNFFormula n, (∀ k : ℕ, P φ k) → ¬ φ.Satisfiable

/-- Same, finite sweep. -/
def NullPatternGloballyImpliesUnsatFin (K : ℕ) (P : CNFFormula n → Fin K → Prop) : Prop :=
  ∀ φ : CNFFormula n, (∀ k : Fin K, P φ k) → ¬ φ.Satisfiable

theorem encodingCompleteness_iff_null_globally_implies_unsat (P : MoireNullPattern n) :
    EncodingCompleteness P ↔ NullPatternGloballyImpliesUnsat P := by
  constructor
  · intro H φ hPk ⟨a, ha⟩
    rcases H φ ⟨a, ha⟩ with ⟨k, hk⟩
    exact hk (hPk k)
  · intro H φ ⟨a, ha⟩
    by_contra hnex
    rw [not_exists] at hnex
    have hPk : ∀ k : ℕ, P φ k := fun k => not_not.mp (hnex k)
    exact H φ hPk ⟨a, ha⟩

theorem encodingCompletenessFin_iff_null_globally_implies_unsat_fin (K : ℕ)
    (P : CNFFormula n → Fin K → Prop) :
    EncodingCompletenessFin K P ↔ NullPatternGloballyImpliesUnsatFin K P := by
  constructor
  · intro H φ hPk ⟨a, ha⟩
    rcases H φ ⟨a, ha⟩ with ⟨k, hk⟩
    exact hk (hPk k)
  · intro H φ ⟨a, ha⟩
    by_contra hnex
    rw [not_exists] at hnex
    have hPk : ∀ k : Fin K, P φ k := fun k => not_not.mp (hnex k)
    exact H φ hPk ⟨a, ha⟩

/-- **Procedure corollary:** under `EncodingCompleteness P`, if every scanned mode is null, the
formula is **unsatisfiable** (sound rejection). -/
theorem unsat_of_forall_k_null (P : MoireNullPattern n)
    (hEnc : EncodingCompleteness P) (φ : CNFFormula n) (hPk : ∀ k : ℕ, P φ k) : ¬ φ.Satisfiable :=
  (encodingCompleteness_iff_null_globally_implies_unsat P).mp hEnc φ hPk

/-- Finite-sweep version. -/
theorem unsat_of_forall_fin_k_null (K : ℕ) (P : CNFFormula n → Fin K → Prop)
    (hEnc : EncodingCompletenessFin K P) (φ : CNFFormula n) (hPk : ∀ k : Fin K, P φ k) :
    ¬ φ.Satisfiable :=
  (encodingCompletenessFin_iff_null_globally_implies_unsat_fin K P).mp hEnc φ hPk

/-- **Witness direction:** under encoding completeness, any satisfiable `φ` admits some non-null `k`. -/
theorem exists_non_null_k_of_sat (P : MoireNullPattern n) (hEnc : EncodingCompleteness P)
    (φ : CNFFormula n) (hsat : φ.Satisfiable) : ∃ k : ℕ, ¬ P φ k :=
  hEnc φ hsat

theorem exists_non_null_k_of_sat_fin (K : ℕ) (P : CNFFormula n → Fin K → Prop)
    (hEnc : EncodingCompletenessFin K P) (φ : CNFFormula n) (hsat : φ.Satisfiable) :
    ∃ k : Fin K, ¬ P φ k :=
  hEnc φ hsat

end Hqiv.Logic
