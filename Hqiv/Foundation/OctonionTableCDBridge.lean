/-
  OctonionTableCDBridge — the explicit Fano table *is* the Cayley–Dickson table
  =============================================================================

  The realism bridge deferred in `OctonionTableRealizability`: we prove that the
  explicit combinatorial table `oct` literally equals the Cayley–Dickson octonion
  structure-constant table `octonionTable` of `OctonionTableIso`, and transport the
  realizability result onto the genuine Cayley–Dickson table.

  The proof is a direct decision over all `8 · 8 · 8` entries: for each `(i, j, k)`
  the left side `coordO (eᵢ · eⱼ) k` is the relevant coordinate of a concrete
  Cayley–Dickson product, and the right side `oct i j k` is its combinatorial value;
  `simp` reduces both to the same real numeral.  (This is a one-time heavy computation,
  isolated in its own module.)

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Foundation.OctonionTableRealizability

namespace Hqiv.Foundation

open Hqiv.Algebra.CayleyDickson

set_option maxHeartbeats 10000000 in
/-- **The realism bridge:** the explicit Fano table equals the Cayley–Dickson table. -/
theorem octonionTable_eq_oct : octonionTable = oct := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [octonionTable, oct, octEntry, coordO, eIdx,
      e0, e1, e2, e3, e4, e5, e6, e7,
      mul_fst, mul_snd, star_fst, star_snd, star_trivial]

/-- Consequently the genuine Cayley–Dickson octonion table is a `StrongTable`. -/
theorem octonionTable_strongTable : StrongTable octonionTable := by
  rw [octonionTable_eq_oct]; exact oct_strongTable

end Hqiv.Foundation
