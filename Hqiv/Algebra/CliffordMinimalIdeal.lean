import Mathlib.Algebra.Field.Equiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Minimal left ideals — definitions and the `Cl(1) ≅ ℂ` certificate

Furey-style arguments use **minimal left ideals** of a Clifford algebra as canonical
one-generator submodules (a “line” inside the spinor / bookkeeping carrier).

This file does two things:

1. **`IsMinimalLeftIdeal`** — a ring-theoretic definition of a **nonzero** minimal
   left ideal, stated uniformly as a submodule of `R` over itself.

2. **A fully proved Clifford instance** — `CliffordAlgebra CliffordAlgebraComplex.Q`
   is (by Mathlib) isomorphic to `ℂ` as an `ℝ`-algebra, hence is a **field**.  A
   field has no nontrivial proper left ideals, so `⊤` is the **unique** nonzero
   left ideal and is therefore **minimal** in the standard sense.

This is the correct *algebraic* pattern behind “pick a minimal ideal to fix a
charge line”: in the division-ring case that line is the whole ring as a
1-dimensional module over itself (here: a **complex** line, i.e. `2` real
dimensions).

The octonionic **8-real** spinor carrier and the **8×8** matrix slot for
`phaseLiftDelta` are handled separately in `Hqiv.Algebra.CliffordHQIVSlotRefinement`
(they are not forced to match the `Cl(1)` model’s linear dimension — that
stronger spinor/matrix bridge is still future `Cl(6)` / representation work).

**Abstract `Cl(0,6)` update:** `Hqiv.Algebra.CliffordCl06SixDimension` now proves
`Module.finrank ℝ CliffordCl06Six = 64` without any matrix lift; `Hqiv.Algebra.CliffordCl06SixIdeal`
and `Hqiv.Algebra.CliffordCl06SixSpinorBridge` package principal left ideals and a
representation-conditional map into `OctonionSpinorCarrier` (see `THEOREMS.md` tag
“Furey claim supported — partial (abstract `Cl(0,6)` ideals)”).
-/

namespace Hqiv.Algebra

variable {R : Type*} [Ring R]

/-- A **left ideal** of `R`: an `R`-submodule of `R` with action `r • x = r * x`. -/
abbrev LeftIdeal (R : Type*) [Ring R] := Submodule R R

/--
A **nonzero** left ideal `I` is **minimal** if every nonzero left ideal contained in
`I` equals `I`.
-/
def IsMinimalLeftIdeal (I : LeftIdeal R) : Prop :=
  I ≠ ⊥ ∧ ∀ J : LeftIdeal R, J ≠ ⊥ → J ≤ I → J = I

theorem IsMinimalLeftIdeal.top_of_isSimpleModule {R : Type*} [Ring R] [IsSimpleModule R R]
    [Nontrivial R] :
    IsMinimalLeftIdeal (⊤ : LeftIdeal R) := by
  refine ⟨Ne.symm bot_ne_top, ?_⟩
  intro J hJ _
  obtain rfl | rfl := eq_bot_or_eq_top (α := Submodule R R) J
  · exact (hJ rfl).elim
  · rfl

/-!
### `Cl(1) ≅ ℂ` via Mathlib’s `CliffordAlgebraComplex`
-/

/-- The standard `Cl(1)` quadratic form used in `CliffordAlgebraComplex`. -/
abbrev cliffordOneDimQ : QuadraticForm ℝ ℝ :=
  CliffordAlgebraComplex.Q

/-- The concrete `Cl(1)` Clifford algebra in this certificate. -/
abbrev CliffordOneDim := CliffordAlgebra cliffordOneDimQ

noncomputable instance instFieldCliffordOneDim : Field CliffordOneDim :=
  (MulEquiv.isField (Field.toIsField ℂ)
      CliffordAlgebraComplex.equiv.toRingEquiv.toMulEquiv).toField

theorem cliffordOneDim_top_isMinimalLeftIdeal :
    IsMinimalLeftIdeal (⊤ : LeftIdeal CliffordOneDim) :=
  IsMinimalLeftIdeal.top_of_isSimpleModule (R := CliffordOneDim)

end Hqiv.Algebra
