import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Exact union cardinality (local unit-circle / shell intersections)

This route **does not** use classical kissing numbers `K(d)`. The refined picture
is instance-specific:

- a target shell `C_M` at rapidity radius `M`,
- an annulus `A_M(τ)` controlled by the rapidity threshold `τ` (radial thickening;
  see `SATRapidityAnnulusCircle` for the **analytical arc / ribbon / moiré** story:
  1D arc on the osculating circle, lattice points in an `ε`-ribbon, generically
  **off** the arc while still lying in the annulus when `ε ≤ τ`),
- a finite family `Q` of lattice points in `L ∩ A_M(τ)`,
- for each `q`, a finite set `intersections q` of admissible directions on `C_M`
  (formalizing `C_q ∩ C_M` in the planar osculating model; typical case has at
  most two points).

The **exact** admissible-direction count is the cardinality of the union
`⋃_{q ∈ Q} intersections q` (duplicates removed automatically).

Purely combinatorial fact (proved below): if each `intersections q` has at most
two elements, then

`K_exact := #(⋃_q intersections q)` satisfies `K_exact ≤ 2 * #Q`.

Any polynomial bound on `#Q` from the encoding / collapse layer therefore yields an
**explicit polynomial** bound on `K_exact`, stronger than importing an abstract
asymptotic `K(d)` kissing-number bound. The real-analytic content is packaged in
the hypotheses `∀ q ∈ Q, #(intersections q) ≤ 2` and in whatever lemma supplies
polynomial growth for `#Q`.

**Planar wiring:** `SATRapidityPlaneBridge` specializes the abstract union bound to
`Finset Plane` and `planeLocalShellIntersections` from `SATRapidityAnnulusCircle`.
-/

namespace Hqiv.Geometry

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]

/-- Formal `K_exact`: cardinality of the union of per-point shell intersection sets. -/
def K_exactUnionCard (Q : Finset ι) (intersections : ι → Finset α) : ℕ :=
  (Q.biUnion intersections).card

theorem K_exactUnionCard_le_two_mul (Q : Finset ι) (intersections : ι → Finset α)
    (h : ∀ q ∈ Q, (intersections q).card ≤ 2) :
    K_exactUnionCard Q intersections ≤ 2 * Q.card := by
  classical
  dsimp [K_exactUnionCard]
  refine le_trans card_biUnion_le ?_
  calc
    ∑ q ∈ Q, (intersections q).card ≤ ∑ q ∈ Q, (2 : ℕ) := sum_le_sum (fun q hq => h q hq)
    _ = Q.card * 2 := sum_const_nat (fun _ _ => rfl)
    _ = 2 * Q.card := Nat.mul_comm _ _

theorem K_exactUnionCard_le_two_mul_cast (Q : Finset ι) (intersections : ι → Finset α)
    (h : ∀ q ∈ Q, (intersections q).card ≤ 2) :
    (Nat.cast : ℕ → ℝ) (K_exactUnionCard Q intersections) ≤ (Nat.cast : ℕ → ℝ) (2 * Q.card) :=
  (Nat.cast_le (α := ℝ)).2 (K_exactUnionCard_le_two_mul Q intersections h)

/--
Push `K_exact` through the nonnegative real frontier slot used by
`sphere_code_bound` / `SATRapidityGeometricCollapse`.
-/
def sphereFrontierFromExactCount (K : ℕ → ℕ) (d : ℕ) : ℝ :=
  (Nat.cast : ℕ → ℝ) (K d)

/--
If the residual list is bounded in length by `K_exact` and `K_exact ≤ 2 * #Q`,
then (after casting) the same bound holds with `2 * #Q` on the right — the
polynomial layer can bound `#Q` without any classical `K(d)`.
-/
theorem residualCount_le_two_mul_lattice_of_Kexact {Q : Finset ι}
    (intersections : ι → Finset α) (len : ℕ)
    (hK : len ≤ K_exactUnionCard Q intersections)
    (hCard : ∀ q ∈ Q, (intersections q).card ≤ 2) :
    len ≤ 2 * Q.card :=
  le_trans hK (K_exactUnionCard_le_two_mul Q intersections hCard)

theorem residualLength_real_le_two_mul_lattice_cast {Q : Finset ι}
    (intersections : ι → Finset α) (len : ℕ)
    (hK : len ≤ K_exactUnionCard Q intersections)
    (hCard : ∀ q ∈ Q, (intersections q).card ≤ 2) :
    (Nat.cast : ℕ → ℝ) len ≤ (Nat.cast : ℕ → ℝ) (2 * Q.card) :=
  (Nat.cast_le (α := ℝ)).2 (residualCount_le_two_mul_lattice_of_Kexact intersections len hK hCard)

end Hqiv.Geometry
