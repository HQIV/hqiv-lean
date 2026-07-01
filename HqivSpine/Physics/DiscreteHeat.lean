import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.DiscreteHeat` — semidiscrete heat dissipation on the 3-cycle

The minimal periodic graph Laplacian on `Fin 3` (the cycle `C₃`) carries the **discrete
integration-by-parts** structure of semidiscrete heat `u' = ν Δ u` on a 1-D periodic mesh:

`⟨u, Δu⟩ = −∑ (uᵢ − u_{i+1})² ≤ 0`  (dissipation sign),

with the exact explicit-Euler energy law `‖u⁺‖² − ‖u‖² = 2(dtν)⟨u,Δu⟩ + (dtν)²‖Δu‖²` and, using the
`C₃` spectral identity `‖Δu‖² = 3‖∇u‖²`, the **CFL Lyapunov step**: when `3·dt·ν ≤ 2` the explicit
step never increases `∑ uᵢ²`.

Honest scope (as in the legacy module): this is the dissipation/stability *sign* of a parabolic
flow on a toy mesh — **not** a continuum PDE-existence or Navier–Stokes claim. Mathlib-only; no
legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.DiscreteHeat

open scoped BigOperators

/-- Cyclic successor on `Fin 3` (edges `0–1–2–0`). -/
def cyclicSucc3 (i : Fin 3) : Fin 3 :=
  match i with
  | ⟨0, _⟩ => (1 : Fin 3)
  | ⟨1, _⟩ => (2 : Fin 3)
  | ⟨2, _⟩ => (0 : Fin 3)

/-- Cyclic predecessor on `Fin 3`. -/
def cyclicPred3 (i : Fin 3) : Fin 3 :=
  match i with
  | ⟨0, _⟩ => (2 : Fin 3)
  | ⟨1, _⟩ => (0 : Fin 3)
  | ⟨2, _⟩ => (1 : Fin 3)

theorem cyclicPred3_cyclicSucc3 (i : Fin 3) : cyclicPred3 (cyclicSucc3 i) = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem cyclicSucc3_cyclicPred3 (i : Fin 3) : cyclicSucc3 (cyclicPred3 i) = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- Graph Laplacian on `C₃`: `(Δ u)_i = u_{i⁺} + u_{i⁻} − 2uᵢ`. -/
def laplacianCycle3 (u : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  u (cyclicSucc3 i) + u (cyclicPred3 i) - 2 * u i

/-- **Discrete `⟨u, Δu⟩`** equals minus the sum of squared edge jumps. -/
theorem sum_u_laplacianCycle3_eq_neg_jump_sq (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, u i * laplacianCycle3 u i) =
      -∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  simp_rw [Fin.sum_univ_three, laplacianCycle3, cyclicSucc3, cyclicPred3]; ring

/-- Hence **`⟨u, Δu⟩ ≤ 0`** (viscous-dissipation sign). -/
theorem sum_u_laplacianCycle3_nonpos (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, u i * laplacianCycle3 u i ≤ 0 := by
  rw [sum_u_laplacianCycle3_eq_neg_jump_sq, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **`C₃` spectral identity** `‖Δu‖² = 3‖∇u‖²` (Laplacian spectrum `{0, −3}`). -/
theorem sum_sq_laplacianCycle3_eq_three_mul_jump_sq (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (laplacianCycle3 u i) ^ 2) =
      3 * ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  simp_rw [Fin.sum_univ_three, laplacianCycle3, cyclicSucc3, cyclicPred3]; ring

/-- One explicit Euler step `u ↦ u + dt ν Δ u`. -/
noncomputable def eulerHeatStep3 (ν dt : ℝ) (u : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  u i + dt * ν * laplacianCycle3 u i

/-- **Discrete energy law** (exact): `‖u⁺‖² − ‖u‖² = 2(dtν)⟨u,Δu⟩ + (dtν)²‖Δu‖²`. -/
theorem eulerHeatStep3_sum_sq_sub_eq (ν dt : ℝ) (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2) - (∑ i : Fin 3, (u i) ^ 2) =
      2 * dt * ν * (∑ i : Fin 3, u i * laplacianCycle3 u i) +
        (dt * ν) ^ 2 * (∑ i : Fin 3, (laplacianCycle3 u i) ^ 2) := by
  simp_rw [Fin.sum_univ_three, eulerHeatStep3]; ring

/-- Same identity in **edge-jump** variables on `C₃`. -/
theorem eulerHeatStep3_sum_sq_sub_eq_jump (ν dt : ℝ) (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2) - (∑ i : Fin 3, (u i) ^ 2) =
      (dt * ν) * (3 * (dt * ν) - 2) *
        ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  rw [eulerHeatStep3_sum_sq_sub_eq, sum_u_laplacianCycle3_eq_neg_jump_sq,
    sum_sq_laplacianCycle3_eq_three_mul_jump_sq]; ring

/-- **CFL / small-`dt` monotonicity** on `C₃`: if `0 ≤ ν`, `0 ≤ dt`, and `3·dt·ν ≤ 2`, the explicit
Euler step does not increase `∑ uᵢ²` — a discrete Lyapunov bound. -/
theorem eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two {ν dt : ℝ}
    (hν : 0 ≤ ν) (hdt : 0 ≤ dt) (hCFL : dt * ν * (3 : ℝ) ≤ 2) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2 ≤ ∑ i : Fin 3, (u i) ^ 2 := by
  have hJ : 0 ≤ ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbracket : 3 * (dt * ν) - 2 ≤ 0 := by nlinarith [hCFL]
  have hmul : (dt * ν) * (3 * (dt * ν) - 2) * ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 ≤ 0 := by
    have hdtν : 0 ≤ dt * ν := mul_nonneg hdt hν
    have hneg := mul_nonpos_of_nonpos_of_nonneg hbracket hJ
    simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hdtν hneg
  have hdiff := eulerHeatStep3_sum_sq_sub_eq_jump ν dt u
  exact le_of_sub_nonpos (by rw [hdiff]; exact hmul)

end HqivSpine.Physics.DiscreteHeat
