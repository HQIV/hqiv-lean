import HqivSpine.Physics.Monogamy
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.MonogamyWitness` — concrete GHZ / W states realising CKW monogamy

`Physics.Monogamy` states the Coffman–Kundu–Wootters inequality `τ(A:B) + τ(A:C) ≤ τ(A:BC)`
abstractly, with the tangles `τ` as free reals. This module **grounds it in explicit three-qubit
states**, deriving the tangles from first principles rather than asserting them (the legacy
`Hqiv.QuantumMechanics.Monogamy{GHZ,W}Family` modules merely *defined* the tangle values).

A real-amplitude three-qubit state is `ψ : Fin 2 → Fin 2 → Fin 2 → ℝ`. We use two parametric
families:

* the **GHZ family** `ψ = a|000⟩ + b|111⟩` (`ghzVec a b`);
* the **W family** `ψ = x|100⟩ + y|010⟩ + z|001⟩` (`wVec x y z`).

Two genuinely independent quantities are *computed*, not posited:

* the **one-tangle** `τ(A:BC) = 4·det ρ_A`, where `ρ_A` is the single-qubit reduced density
  matrix obtained by tracing out `B,C` (`rhoA`). GHZ → `4a²b²`, W → `4x²(y²+z²)`.
* the **three-tangle** `τ_ABC = 4·|Hdet ψ|`, the residual genuine-tripartite entanglement built
  from the **Cayley `2×2×2` hyperdeterminant** `Hdet` (`hyperdet`). GHZ → `4a²b²`, W → `0`.

The CKW theorem organises these as `τ(A:BC) = τ_AB + τ_AC + τ_ABC`, so the **pairwise tangle budget**
`τ_AB + τ_AC = τ(A:BC) − τ_ABC` (`pairBudget`) is recovered as the residual. Consequences, all
derived:

* CKW monogamy holds for every state — `0 ≤ τ_ABC` forces `pairBudget ≤ oneTangle`
  (`ckw_monogamy`); it feeds the spine's shell-weighted `correctedCkwMonogamy` unchanged.
* **GHZ has no pairwise entanglement** (`ghz_pairBudget_zero`): all of its tangle is genuinely
  tripartite (`τ_ABC = τ(A:BC)`).
* **W saturates CKW** (`w_saturates_ckw`): `τ_ABC = 0`, so `τ_AB + τ_AC = τ(A:BC)` exactly — the
  entanglement lives entirely in the pairs.
* Canonical normalised endpoints: `τ(A:BC)=τ_ABC=1` for GHZ at `a=b=1/√2`; `τ(A:BC)=8/9`,
  `τ_ABC=0` for W at `x=y=z=1/√3`.

Mathlib + spine `Physics.Monogamy` only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`,
no `native_decide`. Honest scope: the individual pairwise concurrences (Wootters' formula) are not
re-derived here — only the one-tangle and three-tangle endpoints and the CKW structure between them.
-/

namespace HqivSpine.Physics.MonogamyWitness

open scoped BigOperators

/-- A real-amplitude three-qubit state. -/
abbrev Q3 : Type := Fin 2 → Fin 2 → Fin 2 → ℝ

/-- GHZ family `ψ = a|000⟩ + b|111⟩`. -/
def ghzVec (a b : ℝ) : Q3 := ![![![a, 0], ![0, 0]], ![![0, 0], ![0, b]]]

/-- W family `ψ = x|100⟩ + y|010⟩ + z|001⟩`. -/
def wVec (x y z : ℝ) : Q3 := ![![![0, z], ![y, 0]], ![![x, 0], ![0, 0]]]

/-! ## Reduced density matrix and the one-tangle -/

/-- Single-qubit reduced density matrix `ρ_A`, tracing out `B,C`:
`(ρ_A)_{i i'} = ∑_{j,k} ψ_{ijk} ψ_{i'jk}`. -/
def rhoA (ψ : Q3) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i i' => ∑ j, ∑ k, ψ i j k * ψ i' j k

/-- **One-tangle** (global `A:BC` entanglement) `τ(A:BC) = 4·det ρ_A`. -/
noncomputable def oneTangle (ψ : Q3) : ℝ := 4 * (rhoA ψ).det

theorem rhoA_ghz (a b : ℝ) : rhoA (ghzVec a b) = !![a * a, 0; 0, b * b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoA, ghzVec, Fin.sum_univ_two, Matrix.of_apply]

theorem rhoA_w (x y z : ℝ) :
    rhoA (wVec x y z) = !![y * y + z * z, 0; 0, x * x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoA, wVec, Fin.sum_univ_two, Matrix.of_apply, add_comm]

/-- **GHZ one-tangle** `τ(A:BC) = 4a²b²`. -/
theorem oneTangle_ghz (a b : ℝ) : oneTangle (ghzVec a b) = 4 * a ^ 2 * b ^ 2 := by
  simp only [oneTangle, rhoA_ghz, Matrix.det_fin_two_of]; ring

/-- **W one-tangle** `τ(A:BC) = 4x²(y²+z²)`. -/
theorem oneTangle_w (x y z : ℝ) :
    oneTangle (wVec x y z) = 4 * x ^ 2 * (y ^ 2 + z ^ 2) := by
  simp only [oneTangle, rhoA_w, Matrix.det_fin_two_of]; ring

/-- The one-tangle is nonnegative (`det ρ_A ≥ 0` for these reduced states). -/
theorem oneTangle_ghz_nonneg (a b : ℝ) : 0 ≤ oneTangle (ghzVec a b) := by
  rw [oneTangle_ghz]; positivity

theorem oneTangle_w_nonneg (x y z : ℝ) : 0 ≤ oneTangle (wVec x y z) := by
  rw [oneTangle_w]; positivity

/-! ## Cayley hyperdeterminant and the three-tangle -/

/-- The **Cayley `2×2×2` hyperdeterminant** of a three-qubit amplitude tensor. Its modulus is the
genuine-tripartite invariant entering the three-tangle. -/
def hyperdet (ψ : Q3) : ℝ :=
  (ψ 0 0 0) ^ 2 * (ψ 1 1 1) ^ 2 + (ψ 0 0 1) ^ 2 * (ψ 1 1 0) ^ 2
    + (ψ 0 1 0) ^ 2 * (ψ 1 0 1) ^ 2 + (ψ 1 0 0) ^ 2 * (ψ 0 1 1) ^ 2
    - 2 * (ψ 0 0 0 * ψ 1 1 1 * ψ 0 0 1 * ψ 1 1 0 + ψ 0 0 0 * ψ 1 1 1 * ψ 0 1 0 * ψ 1 0 1
        + ψ 0 0 0 * ψ 1 1 1 * ψ 1 0 0 * ψ 0 1 1 + ψ 0 0 1 * ψ 1 1 0 * ψ 0 1 0 * ψ 1 0 1
        + ψ 0 0 1 * ψ 1 1 0 * ψ 1 0 0 * ψ 0 1 1 + ψ 0 1 0 * ψ 1 0 1 * ψ 1 0 0 * ψ 0 1 1)
    + 4 * (ψ 0 0 0 * ψ 0 1 1 * ψ 1 0 1 * ψ 1 1 0 + ψ 0 0 1 * ψ 0 1 0 * ψ 1 0 0 * ψ 1 1 1)

/-- **Three-tangle** (genuine tripartite entanglement) `τ_ABC = 4·|Hdet ψ|`. -/
noncomputable def threeTangle (ψ : Q3) : ℝ := 4 * |hyperdet ψ|

theorem threeTangle_nonneg (ψ : Q3) : 0 ≤ threeTangle ψ := by
  unfold threeTangle; positivity

/-- **GHZ hyperdeterminant** `= a²b²`. -/
theorem hyperdet_ghz (a b : ℝ) : hyperdet (ghzVec a b) = a ^ 2 * b ^ 2 := by
  simp only [hyperdet, ghzVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **W hyperdeterminant vanishes**: the W state has no genuine tripartite invariant. -/
theorem hyperdet_w (x y z : ℝ) : hyperdet (wVec x y z) = 0 := by
  simp only [hyperdet, wVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **GHZ three-tangle** `τ_ABC = 4a²b²` — equal to its one-tangle (purely tripartite). -/
theorem threeTangle_ghz (a b : ℝ) : threeTangle (ghzVec a b) = 4 * a ^ 2 * b ^ 2 := by
  unfold threeTangle; rw [hyperdet_ghz, abs_of_nonneg (by positivity)]; ring

/-- **W three-tangle vanishes** `τ_ABC = 0`. -/
theorem threeTangle_w (x y z : ℝ) : threeTangle (wVec x y z) = 0 := by
  unfold threeTangle; rw [hyperdet_w]; simp

/-! ## CKW monogamy, saturation, and the genuine-tripartite split -/

/-- **Pairwise tangle budget** `τ_AB + τ_AC`, recovered from the CKW decomposition
`τ(A:BC) = (τ_AB + τ_AC) + τ_ABC` as the residual `τ(A:BC) − τ_ABC`. -/
noncomputable def pairBudget (ψ : Q3) : ℝ := oneTangle ψ - threeTangle ψ

/-- **CKW monogamy holds for every state:** since the three-tangle is nonnegative, the pairwise
budget never exceeds the one-tangle, i.e. `τ_AB + τ_AC ≤ τ(A:BC)`. Phrased through the spine's
`ckwMonogamy` with the symmetric split `τ_AB = τ_AC = pairBudget/2`. -/
theorem ckw_monogamy (ψ : Q3) :
    HqivSpine.Physics.ckwMonogamy (pairBudget ψ / 2) (pairBudget ψ / 2) (oneTangle ψ) := by
  unfold HqivSpine.Physics.ckwMonogamy pairBudget
  have := threeTangle_nonneg ψ
  linarith

/-- The shell mode-weighted CKW inequality (`Physics.Monogamy`) also holds on every witness. -/
theorem corrected_ckw_monogamy (m : ℕ) (ψ : Q3) :
    HqivSpine.Physics.correctedCkwMonogamy m (pairBudget ψ / 2) (pairBudget ψ / 2)
      (oneTangle ψ) :=
  HqivSpine.Physics.corrected_monogamy_of_ckw m (ckw_monogamy ψ)

/-- **GHZ has no pairwise entanglement:** `τ_AB + τ_AC = 0`; all of its tangle is tripartite. -/
theorem ghz_pairBudget_zero (a b : ℝ) : pairBudget (ghzVec a b) = 0 := by
  unfold pairBudget; rw [oneTangle_ghz, threeTangle_ghz]; ring

/-- **GHZ is genuinely tripartite:** its three-tangle equals its full one-tangle. -/
theorem ghz_genuinely_tripartite (a b : ℝ) :
    threeTangle (ghzVec a b) = oneTangle (ghzVec a b) := by
  rw [threeTangle_ghz, oneTangle_ghz]

/-- **W saturates CKW:** with vanishing three-tangle, `τ_AB + τ_AC = τ(A:BC)` exactly. -/
theorem w_saturates_ckw (x y z : ℝ) : pairBudget (wVec x y z) = oneTangle (wVec x y z) := by
  unfold pairBudget; rw [threeTangle_w]; ring

/-! ## Canonical normalised endpoints -/

private theorem inv_sqrt_sq {n : ℝ} (hn : 0 ≤ n) : ((Real.sqrt n)⁻¹) ^ 2 = n⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hn]

/-- Canonical maximally-entangled GHZ state `a = b = 1/√2`: one-tangle `= 1`. -/
theorem oneTangle_ghz_canonical :
    oneTangle (ghzVec (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹) = 1 := by
  rw [oneTangle_ghz, inv_sqrt_sq (by norm_num)]; norm_num

/-- Canonical GHZ state is fully tripartite: three-tangle `= 1`. -/
theorem threeTangle_ghz_canonical :
    threeTangle (ghzVec (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹) = 1 := by
  rw [threeTangle_ghz, inv_sqrt_sq (by norm_num)]; norm_num

/-- Canonical symmetric W state `x = y = z = 1/√3`: one-tangle `= 8/9`. -/
theorem oneTangle_w_canonical :
    oneTangle (wVec (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹) = 8 / 9 := by
  rw [oneTangle_w, inv_sqrt_sq (by norm_num)]; norm_num

/-- Canonical W state has zero three-tangle, so it **saturates CKW** with pairwise budget `8/9`. -/
theorem pairBudget_w_canonical :
    pairBudget (wVec (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹ (Real.sqrt 3)⁻¹) = 8 / 9 := by
  rw [w_saturates_ckw, oneTangle_w_canonical]

end HqivSpine.Physics.MonogamyWitness
