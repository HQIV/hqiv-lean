import Hqiv.Foundation.ThreeDGrowth
import Mathlib.Tactic

/-!
# CarrierBudget — deriving the carrier multiplicity `8` from 3D growth

The previous module fixed the single combinatorial input `transverseDim = 3` with no
mention of octonions. Here we **derive** the carrier multiplicity and the count of
imaginary directions, so the number `8` (the "octonion factor") is no longer a
primitive but a theorem:

* `carrierMultiplicity = signsPerAxis ^ transverseDim = 2³ = 8`
  (the orientation hypercube over the three transverse axes);
* `imaginaryDim = carrierMultiplicity − 1 = 7`
  (drop the scalar/identity direction);
* `carrierMultiplicity = divisionAlgebraDim transverseDim`
  (the `2³` orientation count is exactly the `k = 3` rung of the Cayley–Dickson /
  Hurwitz dimension ladder `1, 2, 4, 8`);
* `soDim carrierMultiplicity = 28` and the branching count `28 = 14 + 7 + 7`.

Still **no matrices and no multiplication table**: this is pure `ℕ` arithmetic about
how many channels a 3D-orientation carrier must have, and how the skew-symmetric
algebra of that carrier decomposes.
-/

namespace Hqiv.Foundation

/-- **Two orientations (±) per transverse axis.** -/
def signsPerAxis : ℕ := 2

theorem signsPerAxis_eq : signsPerAxis = 2 := rfl

/-- **Carrier multiplicity** = number of orientation patterns over the three transverse
axes = `2³`. This is the HQIV "octonion factor", here *derived* rather than assumed. -/
def carrierMultiplicity : ℕ := signsPerAxis ^ transverseDim

/-- **The carrier has exactly 8 channels.** Forced by `2 ^ 3`, not chosen. -/
theorem carrierMultiplicity_eq_eight : carrierMultiplicity = 8 := by
  unfold carrierMultiplicity signsPerAxis transverseDim; norm_num

/-- **Imaginary directions:** the carrier minus its scalar (identity) channel. -/
def imaginaryDim : ℕ := carrierMultiplicity - 1

/-- **There are exactly 7 imaginary directions** (the Fano-plane node count). -/
theorem imaginaryDim_eq_seven : imaginaryDim = 7 := by
  unfold imaginaryDim; rw [carrierMultiplicity_eq_eight]

/-- **Cayley–Dickson / Hurwitz dimension ladder:** `1, 2, 4, 8 = 2ᵏ`. -/
def divisionAlgebraDim (k : ℕ) : ℕ := 2 ^ k

theorem divisionAlgebraDim_zero : divisionAlgebraDim 0 = 1 := rfl
theorem divisionAlgebraDim_one : divisionAlgebraDim 1 = 2 := rfl
theorem divisionAlgebraDim_two : divisionAlgebraDim 2 = 4 := rfl
theorem divisionAlgebraDim_three : divisionAlgebraDim 3 = 8 := rfl

/-- **Carrier sits at the top normed-division rung for `d = 3`.**

The `2³` orientation count of the three transverse axes equals `divisionAlgebraDim 3`,
i.e. the fourth (`k = 3`) rung of the doubling ladder `ℝ, ℂ, ℍ, 𝕆`. This is the
number-theoretic coincidence that makes the 3D carrier land exactly on the octonion
dimension. -/
theorem carrier_is_division_dim :
    carrierMultiplicity = divisionAlgebraDim transverseDim := by
  unfold carrierMultiplicity divisionAlgebraDim signsPerAxis; rfl

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

/-- **Branching bookkeeping** `so(8) ↓ 𝔤₂ = 14 ⊕ 7 ⊕ 7`.

The adjoint `𝔤₂` (14) plus the two imaginary 7-dimensional representations fill the
full 28-dimensional rotation algebra. This is the closure-dimension count that the
concrete `G₂ ∪ {Δ} ⇒ 𝔰𝔬(8)` certificate realizes downstream. -/
theorem so8_branch_g2 : soDim carrierMultiplicity = g2Dim + imaginaryDim + imaginaryDim := by
  rw [soDim_carrier, g2Dim_eq_fourteen, imaginaryDim_eq_seven]

end Hqiv.Foundation
