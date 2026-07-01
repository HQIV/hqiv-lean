import HqivSpine.Physics.MassLadder
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

/-!
# `HqivSpine.Physics.MixingUnitarity` — the mixing matrix is unitary (derived, not assumed)

Across the three generations (`MassLadder`: the three quark Fano triples / the three `S³` windings),
flavour eigenstates and mass eigenstates are **two orthonormal bases of the same generation space**.
The mixing matrix is their overlap, which in the Standard Model is `V = U_u† · U_d`, where `U_u, U_d`
are the unitary matrices diagonalising the up- and down-type mass operators.

**Unitarity is therefore a theorem, not an input:** a product of unitaries is unitary. The only thing
the dynamics fixes is the *magnitudes* `|V_ij|` (the mixing angles); the unitarity relations
themselves — `V†V = 1`, the unitarity triangles `∑_k V*_{ki}V_{kj} = δ_{ij}`, and the row/column
normalisation `∑_k |V_{ki}|² = 1` (probability conservation in weak decays) — fall straight out of the
orthonormal-basis structure. We make **no** claim about the angles.

* **Unitary.** `mixing Uu Ud ∈ unitary` whenever `Uu, Ud` are (`mixing_unitary`).
* **Unitarity triangles.** `∑_k V*_{ki} V_{kj} = δ_{ij}` (`unitarity_triangle`).
* **Probability conservation.** `∑_k |V_{ki}|² = 1` (`unit_column_norm`).
* **No mixing when aligned.** If up and down diagonalise alike, `V = 1` (`mixing_when_aligned`).
* **Three generations.** `card = conservedTripleCount .quark = 3` (`generations_eq_quark_triples`).

Bundled in `MixingClosure` / `mixing_unitarity_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.MixingUnitarity

open HqivSpine.Physics

/-- The three generations. -/
abbrev Gen := Fin 3

/-- A `3×3` complex mixing matrix. -/
abbrev MixMatrix := Matrix Gen Gen ℂ

/-- **Three generations = the three quark Fano triples** (`conservedTripleCount .quark = 3`). -/
theorem generations_eq_quark_triples : Fintype.card Gen = conservedTripleCount .quark := by
  rw [Fintype.card_fin]; rfl

/-- **The mixing matrix** as the overlap of the two mass-eigenbasis diagonalizers `V = U_u† · U_d`. -/
noncomputable def mixing (Uu Ud : MixMatrix) : MixMatrix := star Uu * Ud

/-- **Unitarity is derived:** a product of unitaries is unitary, so the mixing matrix is unitary
whenever the two diagonalizers are. -/
theorem mixing_unitary {Uu Ud : MixMatrix} (hu : Uu ∈ unitary MixMatrix)
    (hd : Ud ∈ unitary MixMatrix) : mixing Uu Ud ∈ unitary MixMatrix := by
  unfold mixing
  exact mul_mem (Unitary.star_mem hu) hd

/-- The defining unitarity relation `V† · V = 1`. -/
theorem mixing_star_mul_self {Uu Ud : MixMatrix} (hu : Uu ∈ unitary MixMatrix)
    (hd : Ud ∈ unitary MixMatrix) : star (mixing Uu Ud) * mixing Uu Ud = 1 :=
  Unitary.star_mul_self_of_mem (mixing_unitary hu hd)

/-- The dual relation `V · V† = 1`. -/
theorem mixing_mul_star_self {Uu Ud : MixMatrix} (hu : Uu ∈ unitary MixMatrix)
    (hd : Ud ∈ unitary MixMatrix) : mixing Uu Ud * star (mixing Uu Ud) = 1 :=
  Unitary.mul_star_self_of_mem (mixing_unitary hu hd)

/-- **The unitarity triangles:** `∑_k V*_{ki} V_{kj} = δ_{ij}`. -/
theorem unitarity_triangle {Uu Ud : MixMatrix} (hu : Uu ∈ unitary MixMatrix)
    (hd : Ud ∈ unitary MixMatrix) (i j : Gen) :
    ∑ k, star (mixing Uu Ud k i) * mixing Uu Ud k j = if i = j then (1 : ℂ) else 0 := by
  have e := congr_fun (congr_fun (mixing_star_mul_self hu hd) i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at e
  simp only [Matrix.star_apply] at e
  exact e

/-- **Probability conservation:** each column of the mixing matrix has unit norm,
`∑_k |V_{ki}|² = 1`. -/
theorem unit_column_norm {Uu Ud : MixMatrix} (hu : Uu ∈ unitary MixMatrix)
    (hd : Ud ∈ unitary MixMatrix) (i : Gen) :
    ∑ k, Complex.normSq (mixing Uu Ud k i) = 1 := by
  have e := unitarity_triangle hu hd i i
  rw [if_pos rfl] at e
  have key : (((∑ k, Complex.normSq (mixing Uu Ud k i)) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, ← e]
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast key

/-- **No mixing when the bases align:** if up and down diagonalise alike, `V = 1`. -/
theorem mixing_when_aligned {U : MixMatrix} (hU : U ∈ unitary MixMatrix) : mixing U U = 1 :=
  Unitary.star_mul_self_of_mem hU

/-! ## Closure -/

/-- **Mixing-unitarity discharge bundle.** -/
structure MixingClosure : Prop where
  three_generations : Fintype.card Gen = conservedTripleCount .quark
  is_unitary : ∀ (Uu Ud : MixMatrix), Uu ∈ unitary MixMatrix → Ud ∈ unitary MixMatrix →
    mixing Uu Ud ∈ unitary MixMatrix
  unitarity_triangles : ∀ (Uu Ud : MixMatrix), Uu ∈ unitary MixMatrix → Ud ∈ unitary MixMatrix →
    ∀ (i j : Gen), ∑ k, star (mixing Uu Ud k i) * mixing Uu Ud k j = if i = j then (1 : ℂ) else 0
  probability_conservation : ∀ (Uu Ud : MixMatrix), Uu ∈ unitary MixMatrix → Ud ∈ unitary MixMatrix →
    ∀ (i : Gen), ∑ k, Complex.normSq (mixing Uu Ud k i) = 1
  no_mixing_when_aligned : ∀ (U : MixMatrix), U ∈ unitary MixMatrix → mixing U U = 1

/-- **Mixing unitarity is discharged:** the three-generation overlap matrix `V = U_u† U_d` is unitary
by construction, so the unitarity triangles close and each column conserves probability — derived
entirely from the orthonormal-basis structure, with no assumption on the mixing angles. -/
theorem mixing_unitarity_closure : MixingClosure where
  three_generations := generations_eq_quark_triples
  is_unitary := fun _ _ hu hd => mixing_unitary hu hd
  unitarity_triangles := fun _ _ hu hd => unitarity_triangle hu hd
  probability_conservation := fun _ _ hu hd => unit_column_norm hu hd
  no_mixing_when_aligned := fun _ hU => mixing_when_aligned hU

end HqivSpine.Physics.MixingUnitarity
