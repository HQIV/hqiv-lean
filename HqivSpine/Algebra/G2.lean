import HqivSpine.Algebra.So8

/-!
# `HqivSpine.Algebra.G2` — the derivation algebra `𝔤₂` in the rotation chain

The seven imaginary octonion directions carry their own rotation algebra `𝔰𝔬(7)`,
and `𝔤₂ = Der(𝕆)` sits inside it. Using the genuine, determinant-free dimensions
from `So8`, we pin the full chain

`𝔰𝔬(8) ⊃ 𝔰𝔬(7) ⊃ 𝔤₂`,  dimensions  `28 ⊃ 21 ⊃ 14`,

with the exact branchings `21 = 14 + 7` and `28 = 14 + 7 + 7`. The two `7`'s are the
imaginary directions: one coset to fill `𝔰𝔬(7)` from `𝔤₂`, and one phase-lift
(`Δ`) coset to fill `𝔰𝔬(8)` from `𝔰𝔬(7)`.
-/

namespace HqivSpine.Algebra

open HqivSpine.Foundation

/-- **`𝔰𝔬(7)`: the rotation algebra of the seven imaginary directions** has the
genuine dimension `21` (standard skew basis; `decide`, no determinant). -/
theorem finrank_so7 : Module.finrank ℝ (skewMatrices 7) = 21 := by
  rw [finrank_skewMatrices]; decide

/-- **`𝔤₂` dimension** from the foundation: `g2Dim = 2 · imaginaryDim = 14`. -/
theorem g2Dim_eq : g2Dim = 14 := g2Dim_eq_fourteen

/-- **`𝔰𝔬(7)` branches as `21 = 𝔤₂ ⊕ (one imaginary 7)`.** -/
theorem so7_branch_g2 : Module.finrank ℝ (skewMatrices 7) = g2Dim + imaginaryDim := by
  rw [finrank_so7, g2Dim_eq_fourteen, imaginaryDim_eq_seven]

/-- **`𝔰𝔬(8)` branches as `28 = 𝔤₂ ⊕ 7 ⊕ 7`,** the second `7` supplied by the
phase lift `Δ`. -/
theorem so8_branch_g2_genuine :
    Module.finrank ℝ (skewMatrices 8) = g2Dim + imaginaryDim + imaginaryDim := by
  rw [finrank_so8, g2Dim_eq_fourteen, imaginaryDim_eq_seven]

/-- **The full rotation chain, numerically:** `14 ≤ 21 ≤ 28`. -/
theorem g2_so7_so8_chain :
    g2Dim ≤ Module.finrank ℝ (skewMatrices 7) ∧
      Module.finrank ℝ (skewMatrices 7) ≤ Module.finrank ℝ (skewMatrices 8) := by
  rw [finrank_so7, finrank_so8, g2Dim_eq_fourteen]
  exact ⟨by norm_num, by norm_num⟩

/-- **Coset bookkeeping:** the step `𝔰𝔬(7) → 𝔰𝔬(8)` adds exactly `imaginaryDim = 7`
new directions — the phase-lift sector that `Δ` generates. -/
theorem so8_sub_so7_eq_imaginaryDim :
    Module.finrank ℝ (skewMatrices 8) - Module.finrank ℝ (skewMatrices 7) = imaginaryDim := by
  rw [finrank_so7, finrank_so8, imaginaryDim_eq_seven]

end HqivSpine.Algebra
