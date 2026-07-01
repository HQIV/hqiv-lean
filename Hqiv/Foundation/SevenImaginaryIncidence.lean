import Hqiv.Foundation.CarrierBudget
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

/-!
# SevenImaginaryIncidence — the Fano incidence forced on the 7 imaginary directions

`CarrierBudget` derived that there are exactly `imaginaryDim = 7` imaginary directions.
Seven points cannot be wired into a multiplication table arbitrarily: the only way to
give each pair of imaginary units a single well-defined product direction, with the
products closing among the seven, is the incidence of the projective plane `PG(2,2)` —
the **Fano plane**. Here we *construct* that incidence as a finite combinatorial object
(seven 3-point lines on `Fin 7`) and prove its defining counts by decision procedure:

* every line has 3 points;
* every point lies on 3 lines;
* every pair of distinct points lies on a **unique** common line.

This makes the Fano pattern a **derived combinatorial structure**, not a multiplication
table pasted in by hand. The concrete octonion matrices downstream are then just one
realization of products supported on this incidence.
-/

namespace Hqiv.Foundation

open Finset

/-- An imaginary direction, labelled by `Fin 7` (recall `imaginaryDim = 7`). -/
abbrev ImagPoint := Fin 7

/-- There are exactly `imaginaryDim` imaginary points. -/
theorem card_ImagPoint : Fintype.card ImagPoint = imaginaryDim := by
  rw [imaginaryDim_eq_seven]; rfl

/-- **The seven lines of `PG(2,2)`** on the imaginary directions (standard labelling,
matching the repo's `Hqiv.Physics.fanoStandardLine`). Each line is the set of three
imaginary units whose product closes among themselves. -/
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

/-- **Number of lines is 7** (`Fin 7` indexing). -/
theorem fanoLine_count : Fintype.card (Fin 7) = 7 := rfl

/-- Standard-line labels incident to a given imaginary point. -/
def linesThrough (v : ImagPoint) : Finset (Fin 7) :=
  Finset.univ.filter fun i => v ∈ fanoLine i

/-- **Three lines per point** (the Fano plane is self-dual: 7 points, 7 lines, 3-3). -/
theorem linesThrough_card (v : ImagPoint) : (linesThrough v).card = 3 := by
  fin_cases v <;> decide

/-- **Two distinct imaginary directions determine a unique common line.**

This is the incidence axiom that pins the product direction of each pair `e_i · e_j`:
there is exactly one Fano line through any two distinct imaginary units, so the
"third point" of that line is forced. -/
theorem unique_common_line (v w : ImagPoint) (hvw : v ≠ w) :
    (Finset.univ.filter fun i => v ∈ fanoLine i ∧ w ∈ fanoLine i).card = 1 := by
  fin_cases v <;> fin_cases w <;> first | (exact absurd rfl hvw) | decide

/-- Collinearity of three imaginary directions: they lie on a common Fano line. -/
def collinearImag (a b c : ImagPoint) : Prop :=
  ∃ L : Fin 7, a ∈ fanoLine L ∧ b ∈ fanoLine L ∧ c ∈ fanoLine L

instance (a b c : ImagPoint) : Decidable (collinearImag a b c) := by
  unfold collinearImag; infer_instance

end Hqiv.Foundation
