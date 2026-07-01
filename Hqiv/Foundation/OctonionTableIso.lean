/-
  OctonionTableIso — uniqueness of the octonion table *up to isomorphism*
  =======================================================================

  `OctonionTableRigidity` showed the original `OctonionTableUnique` (literal table
  equality) is false: the strong-spec family still has the `2⁷` Fano-line sign
  freedom, i.e. tables related by basis sign/relabel changes. The mathematically
  correct statement is therefore **uniqueness up to isomorphism** (the Hurwitz
  rigidity form), which this module sets up.

  This is Milestone 1: the *infrastructure and reduction*, all fully proved.

  * `mulOf c` — the bilinear product on `ℝ⁸` defined by a structure-constant table.
  * `TableIso c d` — an algebra isomorphism: a linear equivalence of `ℝ⁸`
    intertwining the two table products. We prove it is an **equivalence relation**
    (`refl`/`symm`/`trans`).
  * `StrongTable c` — the genuine composition-algebra spec (unital, involutive,
    Fano-compatible, pure-imaginary products, antisymmetric, unit-norm products).
  * `StrongTableUniqueUpToIso` — the end goal, and `reduce_to_canonical`: it follows
    from the single rigidity lemma *every strong table is isomorphic to the octonion
    table*. That lemma and realizability are the next milestones, carried as explicit
    targets — never as axioms.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Foundation.OctonionTableRigidity
import Hqiv.Algebra.OctonionFano
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

namespace Hqiv.Foundation

open Hqiv.Algebra.CayleyDickson

/-! ### Table multiplication on `ℝ⁸` -/

/-- The bilinear product on `ℝ⁸ = Fin 8 → ℝ` defined by a structure-constant table:
`(x · y)_k = Σ_{i,j} c i j k · x_i · y_j`. -/
def mulOf (c : CarrierStructure) (x y : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun k => ∑ i : Fin 8, ∑ j : Fin 8, c i j k * x i * y j

/-! ### Isomorphism of tables (algebra isomorphism of the induced products) -/

/-- `c` and `d` are isomorphic tables when some linear automorphism of `ℝ⁸`
intertwines their products. This is exactly algebra isomorphism of the induced
(generally non-associative) `ℝ`-algebras. -/
def TableIso (c d : CarrierStructure) : Prop :=
  ∃ e : (Fin 8 → ℝ) ≃ₗ[ℝ] (Fin 8 → ℝ),
    ∀ x y, e (mulOf c x y) = mulOf d (e x) (e y)

theorem TableIso.refl (c : CarrierStructure) : TableIso c c :=
  ⟨LinearEquiv.refl ℝ _, fun _ _ => rfl⟩

theorem TableIso.symm {c d : CarrierStructure} : TableIso c d → TableIso d c := by
  rintro ⟨e, he⟩
  refine ⟨e.symm, fun x y => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]

theorem TableIso.trans {c d f : CarrierStructure} :
    TableIso c d → TableIso d f → TableIso c f := by
  rintro ⟨e, he⟩ ⟨e', he'⟩
  refine ⟨e.trans e', fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [he, he']

/-! ### The genuine composition-algebra spec -/

/-- A product of distinct imaginary units is **antisymmetric** in its factors. -/
def AntisymmetricProducts (c : CarrierStructure) : Prop :=
  ∀ i j k : Fin 8, i ≠ 0 → j ≠ 0 → i ≠ j → c i j k = - c j i k

/-- A product of two distinct imaginary units is a **unit vector**: the sum of the
squares of its structure constants is `1`. Together with `FanoCompatible` (support
on the scalar slot or the third Fano point) and `PureImaginaryProducts` (no scalar
part), this pins the product to `±e_k` on the unique third point. -/
def UnitNormProducts (c : CarrierStructure) : Prop :=
  ∀ i j : Fin 8, i ≠ 0 → j ≠ 0 → i ≠ j → ∑ k : Fin 8, (c i j k) ^ 2 = 1

/-- **The strong table spec**: a genuine real composition-algebra structure on the
orthonormal carrier basis. This closes every loophole used by
`octonionTableUnique_too_weak`. -/
def StrongTable (c : CarrierStructure) : Prop :=
  Unital c ∧ ImaginaryInvolutive c ∧ FanoCompatible c ∧
  PureImaginaryProducts c ∧ AntisymmetricProducts c ∧ UnitNormProducts c

/-! ### The canonical octonion table (from the Cayley–Dickson algebra) -/

/-- Coordinates of an octonion in the standard basis `e₀ … e₇`. -/
def coordO (x : 𝕆) : Fin 8 → ℝ
  | 0 => x.fst.fst.fst
  | 1 => x.fst.fst.snd
  | 2 => x.fst.snd.fst
  | 3 => x.fst.snd.snd
  | 4 => x.snd.fst.fst
  | 5 => x.snd.fst.snd
  | 6 => x.snd.snd.fst
  | 7 => x.snd.snd.snd

/-- The standard basis octonions, indexed by `Fin 8`. -/
def eIdx : Fin 8 → 𝕆
  | 0 => e0 | 1 => e1 | 2 => e2 | 3 => e3
  | 4 => e4 | 5 => e5 | 6 => e6 | 7 => e7

/-- **The canonical octonion structure-constant table**: `c i j k` is the `e_k`
coordinate of `eᵢ · eⱼ` in the Cayley–Dickson algebra `𝕆`. -/
def octonionTable : CarrierStructure := fun i j k => coordO (eIdx i * eIdx j) k

/-! ### The end goal and the reduction -/

/-- **Uniqueness up to isomorphism** (the Hurwitz rigidity form, replacing the false
literal-equality `OctonionTableUnique`): any two strong tables are isomorphic. -/
def StrongTableUniqueUpToIso : Prop :=
  ∀ c d : CarrierStructure, StrongTable c → StrongTable d → TableIso c d

/-- **Reduction.** Uniqueness-up-to-isomorphism follows from the single rigidity
lemma that *every* strong table is isomorphic to the canonical octonion table.
This isolates the remaining mathematical content (Hurwitz rigidity) as one explicit
hypothesis — carried in the type, never assumed as an axiom. -/
theorem reduce_to_canonical
    (H : ∀ c : CarrierStructure, StrongTable c → TableIso c octonionTable) :
    StrongTableUniqueUpToIso :=
  fun c d hc hd => (H c hc).trans (H d hd).symm

end Hqiv.Foundation
