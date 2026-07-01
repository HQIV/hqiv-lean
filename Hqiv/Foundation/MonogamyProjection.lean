import Hqiv.Foundation.ThreeDGrowth
import Mathlib.Tactic

/-!
# MonogamyProjection — the reusable α/γ unit-split readout

`ThreeDGrowth` proved the rational imprint family `(α_d, γ_d) = (d/(2d−1), (d−1)/(2d−1))`
with the unit split `α_d + γ_d = 1`. That file is pure arithmetic; it does not yet package
the split as a *projection object* that downstream geometry and the octonion derivation tree
can both consume.

This module supplies that object. A `MonogamyProjection` is any unit split `imprint + overlap = 1`
on the budget line, with two canonical readouts:

* the **diagonal** readout `imprint + overlap` (always the unit — the conserved total budget);
* the **free / skew** readout `imprint − overlap` (the imprint-vs-overlap imbalance).

The dimension-indexed constructor `ofDim d` feeds the 3D-growth family into this object, and the
**physical** projection `physical := ofDim transverseDim` is the row attached to the HQIV
carrier (`transverseDim = 3`), with `imprint = 3/5`, `overlap = 2/5`, skew `1/5`.

No `sorry`, no new `axiom`, no `native_decide` — everything is `ℚ`-arithmetic over the
already-proved `ThreeDGrowth` identities. The point is to have **one** canonical projection API
so that the story-side rotation geometry (`S3AlphaDimUnitSplitProjection`) and the algebra-side
derivation tree (`G2LadderProjection`) read the same split rather than re-deriving it.
-/

namespace Hqiv.Foundation

/-- **A unit monogamy split.** The imprint fraction `α` and overlap (monogamy) fraction `γ`
fill the unit budget: `imprint + overlap = 1`. -/
structure MonogamyProjection where
  /-- Imprint fraction `α`. -/
  imprint : ℚ
  /-- Overlap (informational-monogamy) fraction `γ`. -/
  overlap : ℚ
  /-- The budget line: imprint and overlap fill the unit. -/
  unit_split : imprint + overlap = 1

namespace MonogamyProjection

/-- **Diagonal readout:** the conserved total budget `imprint + overlap`. -/
def diag (P : MonogamyProjection) : ℚ := P.imprint + P.overlap

/-- **Free / skew readout:** the imprint-vs-overlap imbalance `imprint − overlap`. -/
def free (P : MonogamyProjection) : ℚ := P.imprint - P.overlap

@[simp] theorem diag_eq_one (P : MonogamyProjection) : P.diag = 1 := P.unit_split

/-- The skew readout is the affine image `2·imprint − 1` of the imprint (since `overlap = 1 − imprint`). -/
theorem free_eq (P : MonogamyProjection) : P.free = 2 * P.imprint - 1 := by
  have h := P.unit_split
  unfold MonogamyProjection.free
  linarith

/-- The midpoint of imprint and overlap is always `1/2` (the unit-split equator). -/
theorem midpoint_eq_half (P : MonogamyProjection) :
    (P.imprint + P.overlap) / 2 = (1 / 2 : ℚ) := by
  rw [P.unit_split]

/-! ## Dimension-indexed projection from 3D growth -/

/-- **Dimension-indexed projection.** Feeds the 3D-growth imprint family into the projection
object: `imprint = α_d`, `overlap = γ_d`. -/
def ofDim (d : ℕ) (hd : 1 ≤ d) : MonogamyProjection where
  imprint := alphaRat d
  overlap := gammaRat d
  unit_split := alpha_add_gamma d hd

@[simp] theorem ofDim_imprint (d : ℕ) (hd : 1 ≤ d) :
    (ofDim d hd).imprint = alphaRat d := rfl

@[simp] theorem ofDim_overlap (d : ℕ) (hd : 1 ≤ d) :
    (ofDim d hd).overlap = gammaRat d := rfl

/-- **Skew denominator readout:** the free coordinate of the `d`-row is exactly `1/(2d−1)` —
the same denominator that forces `α_d`. -/
theorem ofDim_free (d : ℕ) (hd : 1 ≤ d) :
    (ofDim d hd).free = 1 / (2 * (d : ℚ) - 1) := by
  have hcast : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hne : (2 * (d : ℚ) - 1) ≠ 0 := by nlinarith
  rw [free_eq, ofDim_imprint]
  unfold alphaRat
  field_simp
  ring

/-! ## The physical projection: the carrier's own row -/

/-- **The physical projection row** attached to the HQIV carrier (`transverseDim = 3`). -/
def physical : MonogamyProjection := ofDim transverseDim (by decide)

/-- The physical imprint is `α = 3/5`. -/
theorem physical_imprint : physical.imprint = 3 / 5 := by
  unfold physical
  rw [ofDim_imprint]
  exact alpha_transverseDim

/-- The physical overlap is `γ = 2/5`. -/
theorem physical_overlap : physical.overlap = 2 / 5 := by
  unfold physical
  rw [ofDim_overlap, transverseDim_eq]
  exact gamma_three

/-- The physical skew is `1/5` (`= 1/(2·3 − 1)`). -/
theorem physical_free : physical.free = 1 / 5 := by
  rw [free_eq, physical_imprint]; norm_num

/-- **Balance ratio** of the physical row: `imprint / overlap = 3/2`. -/
theorem physical_balance_ratio : physical.imprint / physical.overlap = 3 / 2 := by
  rw [physical_imprint, physical_overlap]; norm_num

end MonogamyProjection

end Hqiv.Foundation
