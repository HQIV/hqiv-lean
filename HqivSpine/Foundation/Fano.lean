import HqivSpine.Foundation.Carrier
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Foundation.Fano` — the incidence forced on the 7 imaginary directions

`Carrier` derived exactly `imaginaryDim = 7` imaginary directions. Seven points
admit only one consistent product incidence: the projective plane `PG(2,2)`, the
**Fano plane**. We construct it as seven 3-point lines on `Fin 7` and prove its
defining counts by decision procedure:

* every line has 3 points;
* every point lies on 3 lines;
* every pair of distinct points lies on a **unique** common line.

So the Fano pattern is a *derived* combinatorial object; the concrete octonion
products downstream are just one realization supported on this incidence.
-/

namespace HqivSpine.Foundation

open Finset

/-- An imaginary direction, labelled by `Fin 7` (recall `imaginaryDim = 7`). -/
abbrev ImagPoint := Fin 7

/-- There are exactly `imaginaryDim` imaginary points. -/
theorem card_ImagPoint : Fintype.card ImagPoint = imaginaryDim := by
  rw [imaginaryDim_eq_seven]; rfl

/-- **The seven lines of `PG(2,2)`** on the imaginary directions (standard
labelling). Each line is the triple of imaginary units whose product closes. -/
def fanoLine (i : Fin 7) : Finset ImagPoint :=
  match i with
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {0, 5, 6}
  | 3 => {1, 3, 5}
  | 4 => {1, 4, 6}
  | 5 => {2, 3, 6}
  | 6 => {2, 4, 5}

/-- **Three points per line.** -/
theorem fanoLine_card (i : Fin 7) : (fanoLine i).card = 3 := by
  fin_cases i <;> decide

/-- Standard-line labels incident to a given imaginary point. -/
def linesThrough (v : ImagPoint) : Finset (Fin 7) :=
  Finset.univ.filter fun i => v ∈ fanoLine i

/-- **Three lines per point** (the Fano plane is self-dual: 7 points, 7 lines). -/
theorem linesThrough_card (v : ImagPoint) : (linesThrough v).card = 3 := by
  fin_cases v <;> decide

/-- **Two distinct imaginary directions determine a unique common line.** This is
the incidence axiom pinning the product direction of each pair `e_i · e_j`. -/
theorem unique_common_line (v w : ImagPoint) (hvw : v ≠ w) :
    (Finset.univ.filter fun i => v ∈ fanoLine i ∧ w ∈ fanoLine i).card = 1 := by
  fin_cases v <;> fin_cases w <;> first | (exact absurd rfl hvw) | decide

/-- Collinearity of three imaginary directions: a common Fano line. -/
def collinearImag (a b c : ImagPoint) : Prop :=
  ∃ L : Fin 7, a ∈ fanoLine L ∧ b ∈ fanoLine L ∧ c ∈ fanoLine L

instance (a b c : ImagPoint) : Decidable (collinearImag a b c) := by
  unfold collinearImag; infer_instance

end HqivSpine.Foundation
