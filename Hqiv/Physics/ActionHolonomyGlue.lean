import Hqiv.Physics.Action
import Hqiv.Physics.DiscretePlaquetteHolonomy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# O–Maxwell action ↔ discrete holonomy (same `F` data, different packaging)

`Hqiv.Physics.Action` uses the **same** discrete potential `A : Fin 8 → Fin 4 → ℝ` on all octonion
channels and builds **quadratic** flux `F_from_A` summed into `L_O_kinetic` / `action_O_Maxwell`.
That is the **full** `8 × 4` kinematic DOF at the cutoff: every pair `(a, μ, ν)` enters the kinetic sum.

`Hqiv.Physics.DiscretePlaquetteHolonomy` fixes a **minimal** `Fin 4` cycle and multiplies **four**
transports in `Function.End X` — the natural place for **non-abelian** upgrades (matrix groups
inside `End X`).

This file **slots the two together** in the **abelian ℝ translation** sector: each edge is
`x ↦ x + δ` with `δ` taken from **consecutive ν-differences of one channel** of `A`, i.e. values of
`F_from_A` on the **cyclic** index loop `0 → 1 → 2 → 3 → 0` in `Fin 4`. Then:

* the **plaquette holonomy is trivial** (identity transport): the discrete **Stokes** identity
  `∑_{i : Fin 4} F_from_A A a i (i + 1) = 0` (telescoping);
* the **kinetic** term `-(1/4) F²` is the usual **small-flux** Wilson-style weight on the *same*
  `F` slots — we do **not** reprove the continuum limit here, only align definitions.

**Formal Wilson bridge (real abelian `linearEnd`):** for each edge `U_δ = linearEnd δ`, the pointwise
defect `(U_δ·x - x)` equals `δ` (hence equals the edge `F` when `δ = F_from_A …`). For an **open**
chain, `((∏ U)·x - x)` is the **sum** of edge variables (`pathHolonomy_map_linearEnd_sub_id`). On the
**closed** cyclic plaquette that sum is `0` (`sum_F_cyclicIndex_eq_zero`). The kinetic aggregate
`L_O_kinetic` is bounded by the **sum of squared cyclic edge defects** with coefficient `-1/4`; see
`L_O_kinetic_le_neg_quarter_sum_cyclic_wilson_sq` (equality on each channel iff only cyclic edges carry
flux — `sum_Fsq_eq_two_mul_cyclic_add_opposite`).

So: **one** underlying discrete field `A`; **two** views — global `F²` sum in `Action`, local cyclic
holonomy in `DiscretePlaquetteHolonomy`. Neither view drops octonion indices: the holonomy lemmas
below are **per channel** `a : Fin 8`; summing/averaging over `a` is how you recover the full
`L_O_kinetic` aggregate.
-/

namespace Hqiv.Physics

open BigOperators
open Hqiv

/-- **Abelian ℝ transport:** translation by `δ` (group homomorphism `ℝ → Function.End ℝ`). -/
def linearEnd (δ : ℝ) : Function.End ℝ :=
  fun x => x + δ

@[simp]
theorem linearEnd_zero : linearEnd (0 : ℝ) = (1 : Function.End ℝ) := by
  -- `1` on `Function.End ℝ` is `id` (do not elaborate bare `1` as `ℝ`).
  rw [← show (id : Function.End ℝ) = (1 : Function.End ℝ) from rfl]
  funext x
  simp [linearEnd, add_zero]

theorem linearEnd_mul (d e : ℝ) : linearEnd d * linearEnd e = linearEnd (d + e) := by
  funext x
  simp only [linearEnd, Function.End.mul_def, Function.comp_apply]
  ring

theorem discreteSquareHolonomy_linearEnd_sum (δ : Fin 4 → ℝ) :
    discreteSquareHolonomy (fun i => linearEnd (δ i)) = linearEnd (∑ i : Fin 4, δ i) := by
  unfold discreteSquareHolonomy linearEnd
  rw [Fin.sum_univ_four]
  funext x
  simp only [Function.End.mul_def, Function.comp_apply]
  ring

/-- **Telescoping cyclic flux:** `F` on consecutive `ν` indices around `Fin 4` sums to zero. -/
theorem sum_F_cyclicIndex_eq_zero (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    ∑ i : Fin 4, F_from_A A a i (i + 1) = 0 := by
  simp_rw [F_from_A]
  rw [Fin.sum_univ_four]
  have h0 : ((0 : Fin 4) + 1) = (1 : Fin 4) := rfl
  have h1 : ((1 : Fin 4) + 1) = (2 : Fin 4) := rfl
  have h2 : ((2 : Fin 4) + 1) = (3 : Fin 4) := rfl
  have h3 : ((3 : Fin 4) + 1) = (0 : Fin 4) := rfl
  simp_rw [h0, h1, h2, h3]
  ring

/-- **Bianchi / flatness on the cyclic index plaquette:** holonomy from cyclic `F` edges is `1`. -/
theorem discreteSquareHolonomy_F_cyclic_eq_one (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    discreteSquareHolonomy (fun i => linearEnd (F_from_A A a i (i + 1))) = 1 := by
  rw [discreteSquareHolonomy_linearEnd_sum, sum_F_cyclicIndex_eq_zero, linearEnd_zero]

/-- Same conclusion packaged as `pathHolonomy` on the four cyclic edges. -/
theorem pathHolonomy_F_cyclic_eq_one (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    pathHolonomy (List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3]) = 1 := by
  let e : PlaquetteEdge ℝ := fun i => linearEnd (F_from_A A a i (i + 1))
  have hl :
      List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3] = [e 0, e 1, e 2, e 3] := by
    simp [e]
  rw [hl, ← discreteSquareHolonomy_eq_path e]
  exact discreteSquareHolonomy_F_cyclic_eq_one A a

/-! ## Real abelian `(U - 1)` defect ↔ edge flux, and kinetic vs cyclic Wilson squares

On `ℝ`, `linearEnd δ` is **exactly** translation; there is no separate `ε → 0` expansion: the
first-order Wilson defect `(U·x - x)` already equals the edge variable `δ`. The lemmas below record
the quadratic bookkeeping used to compare the **global** `L_O_kinetic` aggregate to the **cyclic**
sum of squared edge defects (a discrete analogue of “small plaquette / many edges” Wilson weight).
-/

@[simp]
theorem linearEnd_apply (δ x : ℝ) : (linearEnd δ) x = x + δ := rfl

theorem linearEnd_sub_id_apply (δ x : ℝ) : (linearEnd δ) x - x = δ := by
  simp [linearEnd_apply]

theorem linearEnd_wilsonDefect_sq (δ x : ℝ) :
    ((linearEnd δ) x - x) ^ 2 = δ ^ 2 := by
  rw [linearEnd_sub_id_apply]

theorem pathHolonomy_map_linearEnd (ds : List ℝ) :
    pathHolonomy (ds.map linearEnd) = linearEnd ds.sum := by
  induction ds with
  | nil =>
      simp [pathHolonomy, linearEnd_zero]
  | cons d ds ih =>
      rw [List.map_cons, List.sum_cons]
      change linearEnd d * pathHolonomy (List.map linearEnd ds) = linearEnd (d + ds.sum)
      rw [ih, linearEnd_mul]

theorem pathHolonomy_map_linearEnd_sub_id (ds : List ℝ) (x : ℝ) :
    (pathHolonomy (ds.map linearEnd)) x - x = ds.sum := by
  rw [pathHolonomy_map_linearEnd, linearEnd_apply]
  ring

theorem Fin_sum_four_eq_list_sum (d : Fin 4 → ℝ) :
    (∑ i : Fin 4, d i) = ([d 0, d 1, d 2, d 3].sum : ℝ) := by
  simp [Fin.sum_univ_four, List.sum_cons, List.sum_nil, add_assoc, add_comm]

theorem pathHolonomy_cyclic_linearEnd_sub_id (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (x : ℝ) :
    (pathHolonomy (List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3])) x - x =
      ∑ i : Fin 4, F_from_A A a i (i + 1) := by
  let ds : List ℝ := [F_from_A A a 0 (0 + 1), F_from_A A a 1 (1 + 1),
      F_from_A A a 2 (2 + 1), F_from_A A a 3 (3 + 1)]
  have hmap :
      List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3] = ds.map linearEnd := by
    simp [ds]
  rw [hmap, pathHolonomy_map_linearEnd_sub_id]
  change ds.sum = ∑ i : Fin 4, F_from_A A a i (i + 1)
  rw [Fin_sum_four_eq_list_sum]

theorem pathHolonomy_cyclic_linearEnd_sub_id_eq_zero (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (x : ℝ) :
    (pathHolonomy (List.map (fun i => linearEnd (F_from_A A a i (i + 1))) [0, 1, 2, 3])) x - x = 0 := by
  rw [pathHolonomy_cyclic_linearEnd_sub_id, sum_F_cyclicIndex_eq_zero]

/-- **Diagonal split on `Fin 4`:** the ordered `F²` sum is cyclic nearest-neighbor squares (×2) plus
the two “antipodal” `Fin 4` pairs `(0,2)` and `(1,3)` (each also ×2). -/
theorem sum_Fsq_eq_two_mul_cyclic_add_opposite (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 =
      2 * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 +
        2 * ((F_from_A A a 0 2) ^ 2 + (F_from_A A a 1 3) ^ 2) := by
  dsimp [F_from_A]
  simp_rw [Fin.sum_univ_four]
  have h0 : ((0 : Fin 4) + 1) = (1 : Fin 4) := rfl
  have h1 : ((1 : Fin 4) + 1) = (2 : Fin 4) := rfl
  have h2 : ((2 : Fin 4) + 1) = (3 : Fin 4) := rfl
  have h3 : ((3 : Fin 4) + 1) = (0 : Fin 4) := rfl
  simp_rw [h0, h1, h2, h3]
  ring

theorem two_mul_sum_F_cyclic_sq_le_sum_Fsq (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    2 * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 ≤
      ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 := by
  have h := sum_Fsq_eq_two_mul_cyclic_add_opposite A a
  linarith [sq_nonneg (F_from_A A a 0 2), sq_nonneg (F_from_A A a 1 3)]

theorem sum_Fsq_div_two_eq_cyclic_add_opposite (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2) =
      (∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2) +
        ((F_from_A A a 0 2) ^ 2 + (F_from_A A a 1 3) ^ 2) := by
  dsimp [F_from_A]
  simp_rw [Fin.sum_univ_four]
  have h0 : ((0 : Fin 4) + 1) = (1 : Fin 4) := rfl
  have h1 : ((1 : Fin 4) + 1) = (2 : Fin 4) := rfl
  have h2 : ((2 : Fin 4) + 1) = (3 : Fin 4) := rfl
  have h3 : ((3 : Fin 4) + 1) = (0 : Fin 4) := rfl
  simp_rw [h0, h1, h2, h3]
  ring

theorem opposite_edge_sq_le_cyclic_edge_sq (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    ((F_from_A A a 0 2) ^ 2 + (F_from_A A a 1 3) ^ 2) ≤
      ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 := by
  dsimp [F_from_A]
  simp_rw [Fin.sum_univ_four]
  have h0 : ((0 : Fin 4) + 1) = (1 : Fin 4) := rfl
  have h1 : ((1 : Fin 4) + 1) = (2 : Fin 4) := rfl
  have h2 : ((2 : Fin 4) + 1) = (3 : Fin 4) := rfl
  have h3 : ((3 : Fin 4) + 1) = (0 : Fin 4) := rfl
  simp_rw [h0, h1, h2, h3]
  have hsquare :
      0 ≤ (A a 0 - A a 1 + A a 2 - A a 3) ^ 2 := sq_nonneg (A a 0 - A a 1 + A a 2 - A a 3)
  linarith

theorem sum_Fsq_div_two_le_two_mul_cyclic (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) :
    (∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2) ≤
      2 * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 := by
  have hsplit := sum_Fsq_div_two_eq_cyclic_add_opposite A a
  have hopp := opposite_edge_sq_le_cyclic_edge_sq A a
  linarith

theorem L_O_kinetic_le_neg_quarter_sum_cyclic_wilson_sq (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    L_O_kinetic A ≤
      -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 := by
  unfold L_O_kinetic
  have hterm (a : Fin 8) :
      -(1 / 4 : ℝ) * ((∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2) / 2) ≤
        -(1 / 4 : ℝ) * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 := by
    have hsplit := sum_Fsq_eq_two_mul_cyclic_add_opposite A a
    have hdiv :
        (∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2) ≤
          ((∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2) / 2) := by
      linarith [hsplit, sq_nonneg (F_from_A A a 0 2), sq_nonneg (F_from_A A a 1 3)]
    have hneg :
        -(1 / 4 : ℝ) * ((∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2) / 2) ≤
          -(1 / 4 : ℝ) * (∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2) := by
      exact mul_le_mul_of_nonpos_left hdiv (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    exact hneg
  simp_rw [linearEnd_wilsonDefect_sq]
  calc
    -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2
        = ∑ a : Fin 8, (-(1 / 4 : ℝ) * (∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2)) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ a : Fin 8, (-(1 / 4 : ℝ) * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2) :=
          Finset.sum_le_sum (fun a _ => by
            simpa [Finset.sum_div] using hterm a)
    _ = -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 := by
          simp_rw [← Finset.mul_sum]

theorem L_O_kinetic_ge_neg_half_sum_cyclic_wilson_sq (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    -(1 / 2 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 ≤
      L_O_kinetic A := by
  unfold L_O_kinetic
  simp_rw [linearEnd_wilsonDefect_sq]
  have hterm (a : Fin 8) :
      -(1 / 2 : ℝ) * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2 ≤
        -(1 / 4 : ℝ) * (∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2) := by
    have hle := sum_Fsq_div_two_le_two_mul_cyclic A a
    nlinarith
  calc
    -(1 / 2 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2
        = ∑ a : Fin 8, (-(1 / 2 : ℝ) * ∑ i : Fin 4, (F_from_A A a i (i + 1)) ^ 2) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ a : Fin 8, (-(1 / 4 : ℝ) * (∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2)) :=
          Finset.sum_le_sum (fun a _ => hterm a)
    _ = -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν) ^ 2 / 2 := by
          rw [Finset.mul_sum]

theorem L_O_kinetic_two_sided_cyclic_wilson_sq (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    -(1 / 2 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 ≤
      L_O_kinetic A ∧
      L_O_kinetic A ≤
        -(1 / 4 : ℝ) * ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 := by
  exact ⟨L_O_kinetic_ge_neg_half_sum_cyclic_wilson_sq A x,
    L_O_kinetic_le_neg_quarter_sum_cyclic_wilson_sq A x⟩

theorem cyclic_wilson_defect_sum_bounds_from_kinetic (A : Fin 8 → Fin 4 → ℝ) (x : ℝ) :
    (-2 : ℝ) * L_O_kinetic A ≤
      (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ∧
      (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ≤
        (-4 : ℝ) * L_O_kinetic A := by
  rcases L_O_kinetic_two_sided_cyclic_wilson_sq A x with ⟨hlo, hhi⟩
  constructor
  · nlinarith
  · nlinarith

/-- Cyclic plaquette Wilson defects sandwich the global `L_O_kinetic` aggregate. -/
structure WilsonKineticPlaquetteEquivalenceDischarged : Prop where
  two_sided_cyclic_wilson :
    ∀ (A : Fin 8 → Fin 4 → ℝ) (x : ℝ),
      (-(2 : ℝ) * L_O_kinetic A ≤
          ∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2) ∧
        (∑ a : Fin 8, ∑ i : Fin 4, ((linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2 ≤
          -(4 : ℝ) * L_O_kinetic A)

theorem wilsonKineticPlaquetteEquivalence_discharged : WilsonKineticPlaquetteEquivalenceDischarged where
  two_sided_cyclic_wilson := fun A x => cyclic_wilson_defect_sum_bounds_from_kinetic A x

end Hqiv.Physics
