import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `HqivSpine.Physics.PartialWaves` — Legendre angular distributions and forward–backward asymmetry

The angular reading of a decay or scattering: the distribution in `x = cos θ` is a Legendre series
`W(x) = ∑ aℓ Pℓ(x)`. The low partial waves carry the physics, and the **forward–backward asymmetry**
isolates the *odd* partial waves — the angular signature of parity-odd dynamics.

* **Legendre polynomials.** `P₀…P₃` with the three-term recurrence `(ℓ+1)P_{ℓ+1}=(2ℓ+1)xPℓ−ℓP_{ℓ−1}`
  (`legendre_recurrence_2/3`), normalisation `Pℓ(1)=1` (`legendre_one`), and parity
  `Pℓ(−x)=(−1)^ℓ Pℓ(x)` (`legendre_parity_*`).
* **Forward–backward asymmetry.** `W(x) − W(−x) = 2(a₁x + a₃P₃(x))` (`fb_asymmetry`): only the odd
  waves survive, and a parity-even (even-ℓ) distribution is exactly forward–backward symmetric
  (`even_distribution_symmetric`).

Bundled in `PartialWaveClosure` / `partial_wave_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.PartialWaves

/-- Legendre polynomial `P₀(x) = 1`. -/
def P0 (_ : ℝ) : ℝ := 1

/-- Legendre polynomial `P₁(x) = x`. -/
def P1 (x : ℝ) : ℝ := x

/-- Legendre polynomial `P₂(x) = (3x² − 1)/2`. -/
noncomputable def P2 (x : ℝ) : ℝ := (3 * x ^ 2 - 1) / 2

/-- Legendre polynomial `P₃(x) = (5x³ − 3x)/2`. -/
noncomputable def P3 (x : ℝ) : ℝ := (5 * x ^ 3 - 3 * x) / 2

/-! ## Normalisation at `x = 1` -/

theorem legendre_one_0 : P0 1 = 1 := rfl
theorem legendre_one_1 : P1 1 = 1 := rfl
theorem legendre_one_2 : P2 1 = 1 := by unfold P2; norm_num
theorem legendre_one_3 : P3 1 = 1 := by unfold P3; norm_num

/-! ## Parity `Pℓ(−x) = (−1)^ℓ Pℓ(x)` -/

theorem legendre_parity_0 (x : ℝ) : P0 (-x) = P0 x := rfl
theorem legendre_parity_1 (x : ℝ) : P1 (-x) = -P1 x := rfl
theorem legendre_parity_2 (x : ℝ) : P2 (-x) = P2 x := by unfold P2; ring
theorem legendre_parity_3 (x : ℝ) : P3 (-x) = -P3 x := by unfold P3; ring

/-! ## Three-term recurrence `(ℓ+1)P_{ℓ+1} = (2ℓ+1) x Pℓ − ℓ P_{ℓ−1}` -/

/-- Recurrence at `ℓ=1`: `2 P₂ = 3 x P₁ − P₀`. -/
theorem legendre_recurrence_2 (x : ℝ) : 2 * P2 x = 3 * x * P1 x - P0 x := by
  unfold P2 P1 P0; ring

/-- Recurrence at `ℓ=2`: `3 P₃ = 5 x P₂ − 2 P₁`. -/
theorem legendre_recurrence_3 (x : ℝ) : 3 * P3 x = 5 * x * P2 x - 2 * P1 x := by
  unfold P3 P2 P1; ring

/-! ## Angular distribution and forward–backward asymmetry -/

/-- An angular distribution as a low-order Legendre series `W(x) = a₀P₀ + a₁P₁ + a₂P₂ + a₃P₃`. -/
noncomputable def angular (a0 a1 a2 a3 x : ℝ) : ℝ := a0 * P0 x + a1 * P1 x + a2 * P2 x + a3 * P3 x

/-- **Forward–backward asymmetry isolates the odd partial waves:**
`W(x) − W(−x) = 2(a₁x + a₃P₃(x))` — even waves cancel. -/
theorem fb_asymmetry (a0 a1 a2 a3 x : ℝ) :
    angular a0 a1 a2 a3 x - angular a0 a1 a2 a3 (-x) = 2 * (a1 * x + a3 * P3 x) := by
  unfold angular
  rw [legendre_parity_0, legendre_parity_1, legendre_parity_2, legendre_parity_3]
  unfold P1; ring

/-- **A parity-even (even-ℓ) distribution is forward–backward symmetric.** -/
theorem even_distribution_symmetric (a0 a2 x : ℝ) :
    angular a0 0 a2 0 (-x) = angular a0 0 a2 0 x := by
  unfold angular
  rw [legendre_parity_0, legendre_parity_2]; ring

/-! ## Closure -/

/-- **Partial-wave discharge bundle.** -/
structure PartialWaveClosure : Prop where
  normalisation : P0 1 = 1 ∧ P1 1 = 1 ∧ P2 1 = 1 ∧ P3 1 = 1
  recurrence : ∀ x, 2 * P2 x = 3 * x * P1 x - P0 x ∧ 3 * P3 x = 5 * x * P2 x - 2 * P1 x
  parity : ∀ x, P0 (-x) = P0 x ∧ P1 (-x) = -P1 x ∧ P2 (-x) = P2 x ∧ P3 (-x) = -P3 x
  forward_backward : ∀ a0 a1 a2 a3 x,
    angular a0 a1 a2 a3 x - angular a0 a1 a2 a3 (-x) = 2 * (a1 * x + a3 * P3 x)
  even_symmetric : ∀ a0 a2 x, angular a0 0 a2 0 (-x) = angular a0 0 a2 0 x

/-- **The partial-wave story is discharged:** the Legendre series normalises, obeys the three-term
recurrence and definite parity, and the forward–backward asymmetry cleanly extracts the odd waves —
PDG-free. -/
theorem partial_wave_closure : PartialWaveClosure where
  normalisation := ⟨legendre_one_0, legendre_one_1, legendre_one_2, legendre_one_3⟩
  recurrence := fun x => ⟨legendre_recurrence_2 x, legendre_recurrence_3 x⟩
  parity := fun x => ⟨legendre_parity_0 x, legendre_parity_1 x, legendre_parity_2 x, legendre_parity_3 x⟩
  forward_backward := fb_asymmetry
  even_symmetric := even_distribution_symmetric

end HqivSpine.Physics.PartialWaves
