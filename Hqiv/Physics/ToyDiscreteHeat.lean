import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic

namespace Hqiv

/-!
# Toy discrete heat on a 3-cycle (NS-shaped dissipation sign)

This is a **minimal** periodic graph Laplacian on `Fin 3` (the cycle `C₃`). For any `u : Fin 3 → ℝ`,

`∑_i u_i (Δ u)_i = -∑_i (u_i - u_{i+1})² ≤ 0`,

the same **discrete integration-by-parts** sign as semidiscrete heat `u' = ν Δ u` on a 1D periodic mesh.

**Not claimed:** 3D Navier–Stokes, continuum PDE existence, or any link to `HQIVFluidClosureScaffold`
beyond motivational wording in the fluid roadmap.

**Euler energy:** `eulerHeatStep3_sum_sq_sub_eq` is the exact `‖u⁺‖²-‖u‖²` identity; on `C₃` one has
`‖Δu‖² = 3‖∇u‖²` (`sum_sq_laplacianCycle3_eq_three_mul_jump_sq`), hence the closed form
`eulerHeatStep3_sum_sq_sub_eq_jump` and the CFL Lyapunov step `eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two`.
-/

open scoped BigOperators

/-- Cyclic successor on `Fin 3` (edges `0–1–2–0`). Uses numeral `Fin` defs so sums simplify cleanly. -/
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

/-- Graph Laplacian on `C₃`: `(Δ u)_i = u_{i^+} + u_{i^-} - 2u_i`. -/
def laplacianCycle3 (u : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  u (cyclicSucc3 i) + u (cyclicPred3 i) - 2 * u i

/-- Discrete **`⟨u, Δu⟩`** equals minus the sum of squared edge jumps. -/
theorem sum_u_laplacianCycle3_eq_neg_jump_sq (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, u i * laplacianCycle3 u i) =
      -∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  simp_rw [Fin.sum_univ_three, laplacianCycle3, cyclicSucc3, cyclicPred3]
  ring

/-- Hence **`⟨u, Δu⟩ ≤ 0`** (viscous-dissipation sign on this toy mesh). -/
theorem sum_u_laplacianCycle3_nonpos (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, u i * laplacianCycle3 u i ≤ 0 := by
  rw [sum_u_laplacianCycle3_eq_neg_jump_sq]
  have hnn : 0 ≤ ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact neg_nonpos.mpr hnn

/-- Squared Laplacian energy equals **three** times the squared-edge (`C₃` spectral identity). -/
theorem sum_sq_laplacianCycle3_eq_three_mul_jump_sq (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (laplacianCycle3 u i) ^ 2) =
      3 * ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  simp_rw [Fin.sum_univ_three, laplacianCycle3, cyclicSucc3, cyclicPred3]
  ring

/-- One explicit Euler step `u ↦ u + dt ν Δ u` (toy; **no** stability proof here). -/
noncomputable def eulerHeatStep3 (ν dt : ℝ) (u : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  u i + dt * ν * laplacianCycle3 u i

/-- **Discrete energy law** (exact): `‖u⁺‖² - ‖u‖² = 2(dtν)⟨u,Δu⟩ + (dtν)²‖Δu‖²`. -/
theorem eulerHeatStep3_sum_sq_sub_eq (ν dt : ℝ) (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2) - (∑ i : Fin 3, (u i) ^ 2) =
      2 * dt * ν * (∑ i : Fin 3, u i * laplacianCycle3 u i) +
        (dt * ν) ^ 2 * (∑ i : Fin 3, (laplacianCycle3 u i) ^ 2) := by
  classical
  have hterm (i : Fin 3) :
      (eulerHeatStep3 ν dt u i) ^ 2 - (u i) ^ 2 =
        2 * dt * ν * (u i * laplacianCycle3 u i) +
          (dt * ν) ^ 2 * (laplacianCycle3 u i) ^ 2 := by
    simp [eulerHeatStep3, add_sq, mul_pow, mul_assoc, mul_left_comm, mul_comm]
    ring
  calc
    (∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2) - (∑ i : Fin 3, (u i) ^ 2)
        = ∑ i : Fin 3, ((eulerHeatStep3 ν dt u i) ^ 2 - (u i) ^ 2) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin 3,
          (2 * dt * ν * (u i * laplacianCycle3 u i) + (dt * ν) ^ 2 * (laplacianCycle3 u i) ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => hterm i
    _ = 2 * dt * ν * (∑ i : Fin 3, u i * laplacianCycle3 u i) +
          (dt * ν) ^ 2 * (∑ i : Fin 3, (laplacianCycle3 u i) ^ 2) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Same identity in **edge-jump** variables on `C₃` (uses `Δ` spectrum `λ ∈ {0, -3}` packaged as `‖Δu‖² = 3‖∇u‖²`). -/
theorem eulerHeatStep3_sum_sq_sub_eq_jump (ν dt : ℝ) (u : Fin 3 → ℝ) :
    (∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2) - (∑ i : Fin 3, (u i) ^ 2) =
      (dt * ν) * (3 * (dt * ν) - 2) *
        ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 := by
  rw [eulerHeatStep3_sum_sq_sub_eq, sum_u_laplacianCycle3_eq_neg_jump_sq,
    sum_sq_laplacianCycle3_eq_three_mul_jump_sq]
  ring

/-- **CFL / small-`dt` monotonicity** on `C₃`: if `0 ≤ ν`, `0 ≤ dt`, and `dt * ν * 3 ≤ 2`, then the explicit Euler step does not increase `∑ u_i²`. -/
theorem eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two {ν dt : ℝ} (hν : 0 ≤ ν) (hdt : 0 ≤ dt)
    (hCFL : dt * ν * (3 : ℝ) ≤ 2) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, (eulerHeatStep3 ν dt u i) ^ 2 ≤ ∑ i : Fin 3, (u i) ^ 2 := by
  have hJ : 0 ≤ ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbracket : 3 * (dt * ν) - 2 ≤ 0 := by
    rw [sub_nonpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hCFL
  have hmul : (dt * ν) * (3 * (dt * ν) - 2) * ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 ≤ 0 := by
    have hdtν : 0 ≤ dt * ν := mul_nonneg hdt hν
    have hneg : (3 * (dt * ν) - 2) * ∑ i : Fin 3, (u i - u (cyclicSucc3 i)) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hbracket hJ
    simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos hdtν hneg
  have hdiff := eulerHeatStep3_sum_sq_sub_eq_jump ν dt u
  exact le_of_sub_nonpos (by rw [hdiff]; exact hmul)

end Hqiv
