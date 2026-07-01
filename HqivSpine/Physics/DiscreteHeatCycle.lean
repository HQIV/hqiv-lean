import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.DiscreteHeatCycle` — semidiscrete heat on the general cycle `Cₙ`

This is the `Cₙ` generalization of `HqivSpine.Physics.DiscreteHeat` (which mined the legacy
`Hqiv.Physics.ToyDiscreteHeat` `C₃` toy). The periodic mesh is the cyclic group `ZMod n`
(`[NeZero n]`), so the cyclic shift `i ↦ i + 1` is a genuine `Fintype` bijection and the
"integration by parts" reindexing holds for **every** mesh length, not just `n = 3`.

For `u : ZMod n → ℝ` the graph Laplacian of the cycle is `(Δu)_i = u_{i+1} + u_{i-1} − 2uᵢ`,
which factors through the forward difference `(∇u)_i = u_{i+1} − uᵢ` as `(Δu)_i = (∇u)_i − (∇u)_{i-1}`.
The headline structure of the toy model survives verbatim:

* **Dissipation (discrete IBP):** `⟨u, Δu⟩ = −∑ (∇u)_i² ≤ 0` (`sum_u_lap_eq_neg_jumpEnergy`,
  `sum_u_lap_nonpos`) — by cyclic reindexing, valid for all `n`.
* **Spectral bound:** `‖Δu‖² ≤ 4·∑ (∇u)_i²` (`lapEnergy_le_four_mul_jumpEnergy`). The constant `4`
  is the Fourier-symbol ceiling `|2(cos θ − 1)| ≤ 4` of a degree-`2` cycle (`4 = 2·degree`); for
  `n = 3` the sharper identity `‖Δu‖² = 3‖∇u‖²` of `DiscreteHeat` is a special case.
* **Exact explicit-Euler energy law** `‖u⁺‖² − ‖u‖² = 2(dtν)⟨u,Δu⟩ + (dtν)²‖Δu‖²`
  (`eulerStep_energy_sub_eq`).
* **CFL Lyapunov step:** `4·dt·ν ≤ 2 ⇒ ‖u⁺‖² ≤ ‖u‖²` (`eulerStep_energy_le_of_cfl`) — the standard
  cycle stability bound `dt·ν ≤ 1/2`.

Honest scope (inherited from the toy): this is the dissipation/stability *sign* of a parabolic flow
on a 1-D periodic mesh of arbitrary length — **not** a continuum PDE-existence or Navier–Stokes
claim. Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.DiscreteHeatCycle

open scoped BigOperators

variable {n : ℕ} [NeZero n]

/-- Forward difference (oriented edge jump) on the cycle: `(∇u)_i = u_{i+1} − uᵢ`. -/
def fwdDiff (u : ZMod n → ℝ) (i : ZMod n) : ℝ := u (i + 1) - u i

/-- Graph Laplacian on the cycle `Cₙ`: `(Δu)_i = u_{i+1} + u_{i-1} − 2uᵢ`. -/
def lap (u : ZMod n → ℝ) (i : ZMod n) : ℝ := u (i + 1) + u (i - 1) - 2 * u i

/-- Total squared norm `‖u‖² = ∑ uᵢ²`. -/
def energy (u : ZMod n → ℝ) : ℝ := ∑ i, (u i) ^ 2

/-- Dirichlet energy `‖∇u‖² = ∑ (∇u)_i²` (the squared edge jumps). -/
def jumpEnergy (u : ZMod n → ℝ) : ℝ := ∑ i, (fwdDiff u i) ^ 2

/-- Laplacian energy `‖Δu‖² = ∑ (Δu)_i²`. -/
def lapEnergy (u : ZMod n → ℝ) : ℝ := ∑ i, (lap u i) ^ 2

/-! ## Cyclic reindexing (the discrete integration-by-parts engine) -/

/-- Summing over the cycle is invariant under the shift `i ↦ i + 1`. -/
theorem sum_shift_add_one (f : ZMod n → ℝ) : (∑ i, f (i + 1)) = ∑ i, f i := by
  simpa [Equiv.coe_addRight] using Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) f

/-- Summing over the cycle is invariant under the shift `i ↦ i − 1`. -/
theorem sum_shift_sub_one (f : ZMod n → ℝ) : (∑ i, f (i - 1)) = ∑ i, f i := by
  simpa [Equiv.coe_addRight, sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-1 : ZMod n)) f

omit [NeZero n] in
/-- The Laplacian is the (backward) difference of the forward difference:
`(Δu)_i = (∇u)_i − (∇u)_{i-1}`. -/
theorem lap_eq_fwdDiff_sub (u : ZMod n → ℝ) (i : ZMod n) :
    lap u i = fwdDiff u i - fwdDiff u (i - 1) := by
  simp only [lap, fwdDiff]
  have h : (i - 1 + 1 : ZMod n) = i := by ring
  rw [h]; ring

/-! ## Dissipation: `⟨u, Δu⟩ = −‖∇u‖² ≤ 0` -/

/-- **Discrete integration by parts:** `∑ uᵢ (Δu)_i = −∑ (∇u)_i²`, for every cycle length `n`. -/
theorem sum_u_lap_eq_neg_jumpEnergy (u : ZMod n → ℝ) :
    (∑ i, u i * lap u i) = - jumpEnergy u := by
  have reindex : (∑ i, u i * fwdDiff u (i - 1)) = ∑ i, u (i + 1) * fwdDiff u i := by
    rw [← sum_shift_add_one (fun j => u j * fwdDiff u (j - 1))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (i + 1 - 1 : ZMod n) = i := by ring
    rw [h]
  simp only [jumpEnergy]
  calc
    (∑ i, u i * lap u i)
        = ∑ i, (u i * fwdDiff u i - u i * fwdDiff u (i - 1)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lap_eq_fwdDiff_sub]; ring
    _ = (∑ i, u i * fwdDiff u i) - ∑ i, u i * fwdDiff u (i - 1) := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i, u i * fwdDiff u i) - ∑ i, u (i + 1) * fwdDiff u i := by rw [reindex]
    _ = ∑ i, (u i * fwdDiff u i - u (i + 1) * fwdDiff u i) := by rw [← Finset.sum_sub_distrib]
    _ = ∑ i, (-(fwdDiff u i) ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [fwdDiff]; ring
    _ = - ∑ i, (fwdDiff u i) ^ 2 := by rw [← Finset.sum_neg_distrib]

/-- Hence **`⟨u, Δu⟩ ≤ 0`** (viscous-dissipation sign) on every cycle. -/
theorem sum_u_lap_nonpos (u : ZMod n → ℝ) : (∑ i, u i * lap u i) ≤ 0 := by
  rw [sum_u_lap_eq_neg_jumpEnergy, neg_nonpos]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Spectral bound `‖Δu‖² ≤ 4‖∇u‖²` -/

/-- **Cycle Fourier-symbol bound** `‖Δu‖² ≤ 4·‖∇u‖²`: the Laplacian energy is at most four times the
Dirichlet energy (`4 = 2·degree`, the ceiling of `|2(cos θ − 1)|`). The `C₃` identity `= 3‖∇u‖²` is
the sharper special case. -/
theorem lapEnergy_le_four_mul_jumpEnergy (u : ZMod n → ℝ) :
    lapEnergy u ≤ 4 * jumpEnergy u := by
  have hA : (∑ i, (fwdDiff u (i - 1)) ^ 2) = jumpEnergy u := by
    simpa [jumpEnergy] using sum_shift_sub_one (fun i => (fwdDiff u i) ^ 2)
  have hlap : lapEnergy u
      = jumpEnergy u - 2 * (∑ i, fwdDiff u i * fwdDiff u (i - 1)) + jumpEnergy u := by
    simp only [lapEnergy, lap_eq_fwdDiff_sub]
    rw [show (∑ i, (fwdDiff u i - fwdDiff u (i - 1)) ^ 2)
          = ∑ i, ((fwdDiff u i) ^ 2 - 2 * (fwdDiff u i * fwdDiff u (i - 1))
              + (fwdDiff u (i - 1)) ^ 2)
        from Finset.sum_congr rfl fun i _ => by ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hA]
    simp only [jumpEnergy]
  have hexp : (∑ i, (fwdDiff u i + fwdDiff u (i - 1)) ^ 2)
      = jumpEnergy u + 2 * (∑ i, fwdDiff u i * fwdDiff u (i - 1)) + jumpEnergy u := by
    rw [show (∑ i, (fwdDiff u i + fwdDiff u (i - 1)) ^ 2)
          = ∑ i, ((fwdDiff u i) ^ 2 + 2 * (fwdDiff u i * fwdDiff u (i - 1))
              + (fwdDiff u (i - 1)) ^ 2)
        from Finset.sum_congr rfl fun i _ => by ring,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hA]
    simp only [jumpEnergy]
  have hnn : 0 ≤ ∑ i, (fwdDiff u i + fwdDiff u (i - 1)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith [hlap, hexp, hnn]

/-! ## Explicit Euler step and the CFL Lyapunov bound -/

/-- One explicit Euler step `u ↦ u + dt ν Δ u`. -/
noncomputable def eulerStep (ν dt : ℝ) (u : ZMod n → ℝ) (i : ZMod n) : ℝ :=
  u i + dt * ν * lap u i

/-- **Exact discrete energy law:** `‖u⁺‖² − ‖u‖² = 2(dtν)⟨u,Δu⟩ + (dtν)²‖Δu‖²`. -/
theorem eulerStep_energy_sub_eq (ν dt : ℝ) (u : ZMod n → ℝ) :
    energy (eulerStep ν dt u) - energy u
      = 2 * dt * ν * (∑ i, u i * lap u i) + (dt * ν) ^ 2 * lapEnergy u := by
  simp only [energy, eulerStep, lapEnergy]
  rw [← Finset.sum_sub_distrib,
    show (∑ i, ((u i + dt * ν * lap u i) ^ 2 - (u i) ^ 2))
        = ∑ i, (2 * dt * ν * (u i * lap u i) + (dt * ν) ^ 2 * (lap u i) ^ 2)
      from Finset.sum_congr rfl fun i _ => by ring,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **CFL / small-`dt` monotonicity** on `Cₙ`: if `0 ≤ ν`, `0 ≤ dt`, and `4·dt·ν ≤ 2`, the explicit
Euler step does not increase `∑ uᵢ²` — a discrete Lyapunov bound for every mesh length. -/
theorem eulerStep_energy_le_of_cfl {ν dt : ℝ} (hν : 0 ≤ ν) (hdt : 0 ≤ dt)
    (hCFL : dt * ν * 4 ≤ 2) (u : ZMod n → ℝ) :
    energy (eulerStep ν dt u) ≤ energy u := by
  have hdiff := eulerStep_energy_sub_eq ν dt u
  rw [sum_u_lap_eq_neg_jumpEnergy] at hdiff
  have hbound := lapEnergy_le_four_mul_jumpEnergy u
  have hJ : 0 ≤ jumpEnergy u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha : 0 ≤ dt * ν := mul_nonneg hdt hν
  nlinarith [hdiff, mul_nonneg (sq_nonneg (dt * ν)) (sub_nonneg.mpr hbound),
    mul_nonneg (mul_nonneg ha hJ) (sub_nonneg.mpr hCFL)]

end HqivSpine.Physics.DiscreteHeatCycle
