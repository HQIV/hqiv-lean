/-
  OctonionTableRealizability — the strong octonion spec is *inhabited*
  ===================================================================

  Milestone 2 (realizability) for the Hurwitz-rigidity programme begun in
  `OctonionTableIso`.  We exhibit an explicit structure-constant table `oct` on the
  derived Fano incidence (`SevenImaginaryIncidence`) and prove it satisfies every
  clause of `StrongTable`:

  * `Unital`              — `e₀` is a two-sided identity;
  * `ImaginaryInvolutive` — each imaginary unit squares to `−e₀`;
  * `FanoCompatible`      — distinct imaginary products are supported on the third
                            point of the unique Fano line through their labels;
  * `PureImaginaryProducts` — no scalar leak;
  * `AntisymmetricProducts` — `eᵢeⱼ = −eⱼeᵢ`;
  * `UnitNormProducts`    — each product is a unit vector (`∑ₖ cᵢⱼₖ² = 1`).

  `oct` is defined purely combinatorially from the seven oriented Fano lines, so the
  proofs are decidable case checks (no Cayley–Dickson computation); the build itself
  certifies the table's internal consistency (antisymmetry, Fano-supported products,
  unit norm).  The remaining realism bridge `octonionTable = oct` — that this explicit
  table *is* the Cayley–Dickson octonion table of `OctonionTableIso` — is a separate
  (heavier) computation and is deferred; the present module establishes that the strong
  spec is inhabited, which is all Milestone 2 (realizability) requires.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Foundation.OctonionTableIso

namespace Hqiv.Foundation

/-- `(third point, sign)` of `eᵢ · eⱼ` for distinct imaginary carrier indices `i, j`.
The seven oriented Fano lines (carrier labelling) are
`(1 2 3) (1 4 5) (1 7 6) (2 4 6) (2 5 7) (3 4 7) (3 6 5)`,
each read cyclically `a·b = c, b·c = a, c·a = b` with the reverses negated. -/
def octEntry : Fin 8 → Fin 8 → Fin 8 × ℝ
  | 1, 2 => (3, 1)  | 2, 3 => (1, 1)  | 3, 1 => (2, 1)
  | 2, 1 => (3, -1) | 3, 2 => (1, -1) | 1, 3 => (2, -1)
  | 1, 4 => (5, 1)  | 4, 5 => (1, 1)  | 5, 1 => (4, 1)
  | 4, 1 => (5, -1) | 5, 4 => (1, -1) | 1, 5 => (4, -1)
  | 1, 7 => (6, 1)  | 7, 6 => (1, 1)  | 6, 1 => (7, 1)
  | 7, 1 => (6, -1) | 6, 7 => (1, -1) | 1, 6 => (7, -1)
  | 2, 4 => (6, 1)  | 4, 6 => (2, 1)  | 6, 2 => (4, 1)
  | 4, 2 => (6, -1) | 6, 4 => (2, -1) | 2, 6 => (4, -1)
  | 2, 5 => (7, 1)  | 5, 7 => (2, 1)  | 7, 2 => (5, 1)
  | 5, 2 => (7, -1) | 7, 5 => (2, -1) | 2, 7 => (5, -1)
  | 3, 4 => (7, 1)  | 4, 7 => (3, 1)  | 7, 3 => (4, 1)
  | 4, 3 => (7, -1) | 7, 4 => (3, -1) | 3, 7 => (4, -1)
  | 3, 6 => (5, 1)  | 6, 5 => (3, 1)  | 5, 3 => (6, 1)
  | 6, 3 => (5, -1) | 5, 6 => (3, -1) | 3, 5 => (6, -1)
  | _, _ => (0, 0)

/-- **The explicit octonion structure-constant table** on the Fano incidence. -/
def oct (i j k : Fin 8) : ℝ :=
  if i = 0 then (if j = k then 1 else 0)
  else if j = 0 then (if i = k then 1 else 0)
  else if i = j then (if k = 0 then -1 else 0)
  else if k = (octEntry i j).1 then (octEntry i j).2 else 0

/-! ### `oct` satisfies every clause of `StrongTable` -/

theorem oct_unital : Unital oct := by
  refine ⟨fun j k => ?_, fun i k => ?_⟩
  · simp [oct]
  · by_cases h : i = 0 <;> simp [oct, h]

theorem oct_involutive : ImaginaryInvolutive oct := by
  intro i hi k; simp [oct, hi]

theorem oct_fano : FanoCompatible oct := by
  intro i j k hi hj hij hk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact absurd rfl hij
      | (left; decide)
      | (right; decide)
      | (revert hk; simp [oct, octEntry])

theorem oct_pureImaginary : PureImaginaryProducts oct := by
  intro i j hi hj hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact absurd rfl hij
      | simp [oct, octEntry]

theorem oct_antisymmetric : AntisymmetricProducts oct := by
  intro i j k hi hj hij
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact absurd rfl hij
      | (simp [oct, octEntry])

theorem oct_unitNorm : UnitNormProducts oct := by
  intro i j hi hj hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hi
      | exact absurd rfl hj
      | exact absurd rfl hij
      | (simp [oct, octEntry])

/-- **Realizability** (Milestone 2): the strong octonion spec is inhabited by the
explicit Fano table `oct`. The spec is therefore non-vacuous. -/
theorem oct_strongTable : StrongTable oct :=
  ⟨oct_unital, oct_involutive, oct_fano, oct_pureImaginary, oct_antisymmetric, oct_unitNorm⟩

/-- **Reduction to the realized canonical table.** Uniqueness-up-to-isomorphism follows
from the single rigidity lemma that every strong table is isomorphic to `oct` — and
`oct` is now a *proven* strong table, so the canonical representative is genuinely
inhabited (not merely posited). -/
theorem reduce_to_oct
    (H : ∀ c : CarrierStructure, StrongTable c → TableIso c oct) :
    StrongTableUniqueUpToIso :=
  fun c d hc hd => (H c hc).trans (H d hd).symm

end Hqiv.Foundation
