import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.CCR` — no exact canonical commutation relation in finite dimensions

The Heisenberg relation `[X, P] = iℏ` (normalised to `[A, B] = 1` in units `ℏ = 1`) **cannot
hold** as an identity of `n × n` matrices on a fixed finite space: `Tr([A,B]) = 0` always,
but `Tr(1) = n > 0`. Pure linear algebra (`not_exists_matrix_CCR_one`).

This is the **trace obstruction** invoked in `Physics.Uncertainty`: on the finite carrier
`ℂ²` there is no literal position–momentum pair, so the uncertainty mechanism is carried by
the Robertson/commutator bound for the (traceless) Pauli observables rather than by a CCR.
HQIV observables live on finite causal patches (horizon-limited modes, shell cutoffs), so
the obstruction only rules out the one bad formalisation — "exact CCR as a literal fixed
`Matₙ`" — not the finite-dimensional programme itself.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics

open Matrix

/-- **Trace of a commutator vanishes** (`Tr(AB) = Tr(BA)`). -/
theorem trace_commutator_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : (A * B - B * A).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **No exact CCR on a fixed finite matrix algebra.** For a nonempty index `n`, no pair of
`n × n` complex matrices satisfies the normalised canonical commutation relation
`[A, B] = 1` — the trace would be `0` on the left and `n > 0` on the right. -/
theorem not_exists_matrix_CCR_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    ¬ ∃ A B : Matrix n n ℂ, A * B - B * A = 1 := by
  rintro ⟨A, B, h⟩
  have h0 := congr_arg Matrix.trace h
  rw [trace_commutator_eq_zero, Matrix.trace_one] at h0
  have hcard : Fintype.card n = 0 := (Nat.cast_eq_zero (R := ℂ)).1 h0.symm
  linarith [Fintype.card_pos (α := n), hcard]

/-- **The qubit carrier `ℂ²` has no exact CCR.** This is the trace obstruction behind
`Physics.Uncertainty` using the Robertson bound for the Pauli observables instead of a
literal `[x, p] = iℏ`. -/
theorem not_exists_qubit_CCR_one :
    ¬ ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B - B * A = 1 :=
  not_exists_matrix_CCR_one

end HqivSpine.Physics
