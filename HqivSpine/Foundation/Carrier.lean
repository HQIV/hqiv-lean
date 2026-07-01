import HqivSpine.Foundation.ThreeGrowth

/-!
# `HqivSpine.Foundation.Carrier` — the 8-channel carrier from 3D growth

The carrier multiplicity `8` (the "octonion factor") is *derived*, not assumed:

* `carrierMultiplicity = 2 ^ transverseDim = 8` — the orientation hypercube over
  the three transverse axes;
* `imaginaryDim = 7` — drop the scalar channel;
* `8` is exactly the `k = 3` rung of the Cayley–Dickson ladder `1, 2, 4, 8`;
* `soDim 8 = 28` and the branching `28 = 14 + 7 + 7`.

Still pure `ℕ` arithmetic: no matrices, no multiplication table.
-/

namespace HqivSpine.Foundation

/-- Two orientations (±) per transverse axis. -/
def signsPerAxis : ℕ := 2

/-- **Carrier multiplicity** = orientation patterns over the three transverse
axes = `2³`. The HQIV octonion factor, derived rather than assumed. -/
def carrierMultiplicity : ℕ := signsPerAxis ^ transverseDim

/-- **The carrier has exactly 8 channels.** Forced by `2 ^ 3`. -/
theorem carrierMultiplicity_eq_eight : carrierMultiplicity = 8 := by
  unfold carrierMultiplicity signsPerAxis transverseDim; norm_num

/-- **Imaginary directions:** carrier minus its scalar channel. -/
def imaginaryDim : ℕ := carrierMultiplicity - 1

/-- **Exactly 7 imaginary directions** (the Fano-plane node count). -/
theorem imaginaryDim_eq_seven : imaginaryDim = 7 := by
  unfold imaginaryDim; rw [carrierMultiplicity_eq_eight]

/-- **Cayley–Dickson / Hurwitz dimension ladder** `1, 2, 4, 8 = 2ᵏ`. -/
def divisionAlgebraDim (k : ℕ) : ℕ := 2 ^ k

/-- **Carrier sits at the top normed-division rung for `d = 3`:** the `2³`
orientation count equals `divisionAlgebraDim 3`, the `k = 3` rung of
`ℝ, ℂ, ℍ, 𝕆`. -/
theorem carrier_is_division_dim :
    carrierMultiplicity = divisionAlgebraDim transverseDim := rfl

theorem divisionAlgebraDim_three : divisionAlgebraDim 3 = 8 := rfl

/-! ## Skew-symmetric algebra dimensions of the carrier -/

/-- **Dimension of `so(n)`:** `n(n−1)/2`. -/
def soDim (n : ℕ) : ℕ := n * (n - 1) / 2

theorem soDim_eight : soDim 8 = 28 := by decide

/-- **The carrier's rotation algebra has dimension 28** = `so(8)`. -/
theorem soDim_carrier : soDim carrierMultiplicity = 28 := by
  rw [carrierMultiplicity_eq_eight]; exact soDim_eight

/-- **Derivation-algebra dimension** `dim 𝔤₂ = 2 · 7 = 14`. -/
def g2Dim : ℕ := 2 * imaginaryDim

theorem g2Dim_eq_fourteen : g2Dim = 14 := by
  unfold g2Dim; rw [imaginaryDim_eq_seven]

/-- **Branching bookkeeping** `so(8) ↓ 𝔤₂ = 14 ⊕ 7 ⊕ 7`: the adjoint `𝔤₂` plus
the two imaginary 7-reps fill the full 28-dimensional rotation algebra. -/
theorem so8_branch_g2 :
    soDim carrierMultiplicity = g2Dim + imaginaryDim + imaginaryDim := by
  rw [soDim_carrier, g2Dim_eq_fourteen, imaginaryDim_eq_seven]

end HqivSpine.Foundation
