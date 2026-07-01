/-
  OctonionTableRigidity — sharpening the uniqueness frontier
  ==========================================================

  `Hqiv.Foundation.OctonionForcing` carries the end goal as
  `ThreeDForcesOctonion = ForcedCarrierData ∧ OctonionTableUnique`, with
  `OctonionTableUnique` the sole open hypothesis. Before we can *discharge* that
  hypothesis we must make sure it is actually true.

  It is not — as currently stated. `FanoCompatible` constrains only the *support*
  of a product (`c i j k ≠ 0 → k = 0 ∨ collinear …`), never its values, and in
  particular leaves the scalar slot `c i j 0` of a product of two distinct
  imaginary units completely free. So any compatible table can be padded with a
  spurious scalar component and stay compatible. We prove

      `octonionTableUnique_too_weak : ¬ OctonionTableUnique`

  by exhibiting two unital / involutive / Fano-compatible tables that differ only
  in such a scalar slot.

  The fix is to add the missing **composition-algebra value constraints**. The
  minimal one that kills this family of counterexamples is `PureImaginaryProducts`
  (a product of distinct imaginary units has no scalar part); we prove the
  counterexample violates it. The full rigid specification additionally needs unit
  norms, antisymmetry, and an orientation — see the closing notes.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Foundation.OctonionForcing
import Mathlib.Tactic

namespace Hqiv.Foundation

/-! ### A degenerate compatible table

`degenTable` is unital, has involutive imaginary units, and is (vacuously)
Fano-compatible because every product of two *distinct* imaginary units is `0`. -/

def degenTable : CarrierStructure := fun i j k =>
  if i = 0 then (if j = k then 1 else 0)
  else if j = 0 then (if i = k then 1 else 0)
  else if i = j then (if k = 0 then -1 else 0)
  else 0

theorem degenTable_unital : Unital degenTable := by
  refine ⟨?_, ?_⟩
  · intro j k; simp [degenTable]
  · intro i k
    by_cases hi : i = 0
    · subst hi; simp [degenTable]
    · simp [degenTable, hi]

theorem degenTable_involutive : ImaginaryInvolutive degenTable := by
  intro i hi k; simp [degenTable, hi]

theorem degenTable_fano : FanoCompatible degenTable := by
  intro i j k hi hj hij hk
  exact absurd (by simp [degenTable, hi, hj, hij]) hk

/-! ### The padded table: identical except for a bogus scalar slot -/

def degenTable' : CarrierStructure := fun i j k =>
  if i = 1 ∧ j = 2 ∧ k = 0 then 1 else degenTable i j k

theorem degenTable'_unital : Unital degenTable' := by
  refine ⟨?_, ?_⟩
  · intro j k
    have h : ¬ ((0 : Fin 8) = 1 ∧ j = 2 ∧ k = 0) := by rintro ⟨h, _, _⟩; exact absurd h (by decide)
    rw [degenTable']; rw [if_neg h]; exact (degenTable_unital.1 j k)
  · intro i k
    have h : ¬ (i = 1 ∧ (0 : Fin 8) = 2 ∧ k = 0) := by rintro ⟨_, h, _⟩; exact absurd h (by decide)
    rw [degenTable']; rw [if_neg h]; exact (degenTable_unital.2 i k)

theorem degenTable'_involutive : ImaginaryInvolutive degenTable' := by
  intro i hi k
  have h : ¬ (i = 1 ∧ i = 2 ∧ k = 0) := by
    rintro ⟨h1, h2, _⟩; rw [h1] at h2; exact absurd h2 (by decide)
  rw [degenTable']; rw [if_neg h]; exact (degenTable_involutive i hi k)

theorem degenTable'_fano : FanoCompatible degenTable' := by
  intro i j k hi hj hij hk
  by_cases h : i = 1 ∧ j = 2 ∧ k = 0
  · exact Or.inl h.2.2
  · refine degenTable_fano i j k hi hj hij ?_
    rwa [degenTable', if_neg h] at hk

/-! ### The frontier predicate, as currently stated, is too weak -/

/-- **`OctonionTableUnique` (as currently stated) is false.** Two unital,
involutive, Fano-compatible tables can differ in the (unconstrained) scalar slot
of a distinct-imaginary product, so they are not equal. Discharging the frontier
therefore requires *strengthening* the predicate first. -/
theorem octonionTableUnique_too_weak : ¬ OctonionTableUnique := by
  intro h
  have heq : degenTable = degenTable' :=
    h degenTable degenTable'
      ⟨degenTable_unital, degenTable_involutive, degenTable_fano⟩
      ⟨degenTable'_unital, degenTable'_involutive, degenTable'_fano⟩
  have hval : degenTable 1 2 0 = degenTable' 1 2 0 := by rw [heq]
  have h1 : degenTable 1 2 0 = 0 := by simp [degenTable]
  have h2 : degenTable' 1 2 0 = 1 := by simp [degenTable']
  rw [h1, h2] at hval
  exact absurd hval (by norm_num)

/-! ### The minimal missing constraint -/

/-- A product of two distinct imaginary units has **no scalar component**. This is
one of the composition-algebra value constraints absent from `FanoCompatible`; it
is exactly what rules out the padding counterexample above. -/
def PureImaginaryProducts (c : CarrierStructure) : Prop :=
  ∀ i j : Fin 8, i ≠ 0 → j ≠ 0 → i ≠ j → c i j 0 = 0

/-- The padded counterexample violates `PureImaginaryProducts`, confirming that
adding this constraint excludes that whole family of spurious tables. -/
theorem degenTable'_not_pureImaginary : ¬ PureImaginaryProducts degenTable' := by
  intro h
  have := h 1 2 (by decide) (by decide) (by decide)
  norm_num [degenTable', degenTable] at this

end Hqiv.Foundation
