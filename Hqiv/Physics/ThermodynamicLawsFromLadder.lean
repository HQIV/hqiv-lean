import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.DivisionAlgebraZetaScaffold
import Hqiv.Physics.ToyDiscreteHeat

namespace Hqiv.Physics

open scoped BigOperators

/-!
# Thermodynamic laws from the HQIV temperature ladder

Concrete law-style packaging from already proved HQIV ingredients:

1. **Zeroth law (equilibrium relation):** equality of ladder temperature is an equivalence relation.
2. **First law (finite-window conservation):** weighted ladder temperature redistributes to the same
   reference value `T_ref`.
3. **Second law (dissipation):** discrete heat dissipation is nonnegative and explicit Euler does not
   increase quadratic energy under the CFL bound on `C₃`.

We also include a discrete **third-law-style cooling statement**: for any `ε > 0`, shells eventually
have temperature below `ε`.
-/

/-- Thermal equilibrium in the ladder readout: same shell-temperature value. -/
def thermalEquilibrium (m n : ℕ) : Prop :=
  Hqiv.T m = Hqiv.T n

theorem zerothLaw_refl (m : ℕ) : thermalEquilibrium m m := rfl

theorem zerothLaw_symm {m n : ℕ} (h : thermalEquilibrium m n) : thermalEquilibrium n m :=
  h.symm

theorem zerothLaw_trans {m n k : ℕ}
    (hmn : thermalEquilibrium m n) (hnk : thermalEquilibrium n k) :
    thermalEquilibrium m k :=
  Eq.trans hmn hnk

/-- First-law style finite-window conservation: weighted ladder sum equals `T_ref`. -/
theorem firstLaw_tempLadder_dimShellWeight (T_ref : ℝ) (p N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight p N m) =
      T_ref :=
  tempLadderConserved_dimShellWeight T_ref p N hN

/-- Dissipation/entropy-production proxy on the `C₃` toy heat graph. -/
noncomputable def entropyProductionCycle3 (u : Fin 3 → ℝ) : ℝ :=
  -∑ i : Fin 3, u i * Hqiv.laplacianCycle3 u i

/-- Second-law style positivity: entropy-production proxy is nonnegative. -/
theorem secondLaw_entropyProduction_nonneg (u : Fin 3 → ℝ) :
    0 ≤ entropyProductionCycle3 u := by
  unfold entropyProductionCycle3
  exact neg_nonneg.mpr (Hqiv.sum_u_laplacianCycle3_nonpos u)

/-- Second-law style monotonicity: explicit Euler heat step decreases quadratic energy under CFL. -/
theorem secondLaw_euler_step_energy_nonincreasing {ν dt : ℝ}
    (hν : 0 ≤ ν) (hdt : 0 ≤ dt) (hCFL : dt * ν * (3 : ℝ) ≤ 2) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, (Hqiv.eulerHeatStep3 ν dt u i) ^ 2 ≤ ∑ i : Fin 3, (u i) ^ 2 :=
  Hqiv.eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two hν hdt hCFL u

/-- Third-law-style ladder cooling: for every `ε > 0`, some shell has `T(m) < ε`. -/
theorem thirdLaw_eventually_below (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, Hqiv.T m < ε := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / ε) < (n : ℝ) := exists_nat_gt (1 / ε)
  refine ⟨n, ?_⟩
  rw [Hqiv.T_eq]
  have hεinv_pos : 0 < (1 / ε : ℝ) := by positivity
  have h_inv_n_lt_eps : (1 : ℝ) / (n : ℝ) < ε := by
    have h := one_div_lt_one_div_of_lt hεinv_pos hn
    simpa [one_div, hε.ne'] using h
  have h_n_pos : 0 < (n : ℝ) := lt_trans hεinv_pos hn
  have h_T_lt_inv_n : (1 : ℝ) / (n + 1 : ℝ) < (1 : ℝ) / (n : ℝ) := by
    exact one_div_lt_one_div_of_lt h_n_pos (by exact_mod_cast Nat.lt_succ_self n)
  exact lt_trans h_T_lt_inv_n h_inv_n_lt_eps

end Hqiv.Physics

