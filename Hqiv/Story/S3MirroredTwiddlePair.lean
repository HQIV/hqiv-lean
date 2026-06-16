import Hqiv.Story.S3RotationRigidity

/-!
# Mirrored twiddle pairs under functional-equation reflection

The functional equation supplies reflection `σ ↔ 1-σ`.  A natural twiddle family
is not a single angle but a **mirrored pair** at angles `θ` and `π/2 - θ`:
the two readouts are mirrors across the 45° line, and their zero loci are
symmetric about `σ = 1/2`.

This module formalizes two complementary parameterizations:

* **Rotation twiddle** (`rotFree` from `S3RotationRigidity`): the paper's
  `(2σ-1)/√2` at `θ = π/4`.  Mirror zero loci satisfy
  `projectionLine (π/2-θ) = 1 - projectionLine θ`; the pair sums to zero
  across the FE reflection `(σ, 1-σ) ↔ (1-σ, σ)`.
* **Affine twiddle** (`affineTwiddle`): the weighted form
  `cos θ·σ + sin θ·(1-σ)` suggested in the mirrored-pair narrative.  Its
  mirror zero loci satisfy the same `1-σ` swap; at `θ = π/4` both angles
  coincide and the zero locus is exactly `σ = 1/2`.

## Proved here

* Mirror-angle trig identities and closed forms for both twiddle families.
* **Symmetric zero loci**: `projectionLine (π/2-θ) = 1 - projectionLine θ`
  (rotation); `affineTwiddleZero (π/2-θ) = 1 - affineTwiddleZero θ` (affine).
* **Coincidence at 45°**: `θ = π/4` is self-mirror for the rotation family
  (`projectionLine (π/4) = 1/2`).  The affine family is **degenerate** there:
  `cos θ = sin θ` so `affineTwiddle (π/4) σ` is the constant `sin (π/4) ≠ 0`.
* **FE orbit cancellation for rotation mirrors**:
  `rotFree θ (σ,1-σ) + rotFree (π/2-θ) (1-σ,σ) = 0`.
* **Critical-line coincidence**: the rotation pair sum
  `rotFree θ + rotFree (π/2-θ)` on `(σ,1-σ)` is `(cos θ+sin θ)(2σ-1)`; the
  difference is `cos θ - sin θ` (constant in `σ`, vanishing only at `θ = π/4`).
* **30° / 60° example**: `π/6` and `π/3` are a mirror pair; their affine zero
  loci are related by `σ' = 1 - σ` (not both near `1/2` — that is the near-45°
  regime).

## Honest scope

Mirrored pairs sharpen the reflection symmetry but do not discharge RH: off the
line each twiddle still has its own vertical zero locus; the critical line is
where the pair **coincides** (rotation sum/difference laws).  Vertical-axis
rigidity from `S3VerticalAxisRigidity` still forces any common strip zero locus
to be `σ = 1/2` when both mirrors are imposed together with FE closure.
-/

namespace Hqiv.Story

noncomputable section

/-! ## Trig for mirror angles -/

private lemma cos_pi_div_two_sub (θ : ℝ) :
    Real.cos (Real.pi / 2 - θ) = Real.sin θ := by
  rw [show Real.pi / 2 - θ = Real.pi / 2 + -θ by ring, Real.cos_add,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg]
  ring

private lemma sin_pi_div_two_sub (θ : ℝ) :
    Real.sin (Real.pi / 2 - θ) = Real.cos θ := by
  rw [show Real.pi / 2 - θ = Real.pi / 2 + -θ by ring, Real.sin_add,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg]
  ring

/-! ## Affine twiddle: cos θ·σ + sin θ·(1-σ) -/

/-- Affine twiddle on the functional-equation pair. -/
noncomputable def affineTwiddle (θ σ : ℝ) : ℝ :=
  Real.cos θ * σ + Real.sin θ * (1 - σ)

theorem affineTwiddle_eq (θ σ : ℝ) :
    affineTwiddle θ σ = σ * (Real.cos θ - Real.sin θ) + Real.sin θ := by
  unfold affineTwiddle
  ring

/-- Mirror angle gives `sin θ·σ + cos θ·(1-σ)`. -/
theorem affineTwiddle_mirror_angle (θ σ : ℝ) :
    affineTwiddle (Real.pi / 2 - θ) σ =
      Real.sin θ * σ + Real.cos θ * (1 - σ) := by
  unfold affineTwiddle
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub]

/-- Zero locus for the affine twiddle when `sin θ ≠ cos θ`. -/
noncomputable def affineTwiddleZero (θ : ℝ) : ℝ :=
  Real.sin θ / (Real.sin θ - Real.cos θ)

theorem affineTwiddle_zero_iff {θ σ : ℝ} (h : Real.sin θ ≠ Real.cos θ) :
    affineTwiddle θ σ = 0 ↔ σ = affineTwiddleZero θ := by
  have hden : Real.cos θ - Real.sin θ ≠ 0 := by
    intro hEq
    apply h
    linarith
  have hden' : Real.sin θ - Real.cos θ ≠ 0 := by
    intro hEq
    apply h
    linarith
  rw [affineTwiddle_eq]
  constructor
  · intro h0
    have hmul : σ * (Real.cos θ - Real.sin θ) = -Real.sin θ := by linarith
    have hσ : σ = -Real.sin θ / (Real.cos θ - Real.sin θ) :=
      (eq_div_iff hden).mpr hmul
    rw [hσ, affineTwiddleZero]
    field_simp [hden, hden']
    ring
  · intro hσ
    rw [hσ, affineTwiddleZero]
    field_simp [hden']
    ring

/-- **Mirror zero loci swap**: the `π/2-θ` zero is `1 - σ₀(θ)`. -/
theorem affineTwiddleZero_mirror {θ : ℝ} (h : Real.sin θ ≠ Real.cos θ) :
    affineTwiddleZero (Real.pi / 2 - θ) = 1 - affineTwiddleZero θ := by
  unfold affineTwiddleZero
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub]
  have hden : Real.cos θ - Real.sin θ ≠ 0 := by
    intro hEq
    apply h
    linarith
  have hden' : Real.sin θ - Real.cos θ ≠ 0 := by
    intro hEq
    apply h
    linarith
  field_simp [hden, hden']
  ring

/-- At `θ = π/4` the affine twiddle is the constant nonzero value `sin (π/4)`. -/
theorem affineTwiddle_pi_div_four (σ : ℝ) :
    affineTwiddle (Real.pi / 4) σ = Real.sin (Real.pi / 4) := by
  rw [affineTwiddle_eq, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring_nf

theorem affineTwiddle_pi_div_four_ne_zero (σ : ℝ) :
    affineTwiddle (Real.pi / 4) σ ≠ 0 := by
  rw [affineTwiddle_pi_div_four]
  have hpos : (0 : ℝ) < Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]
    positivity
  exact hpos.ne'

/-! ## Rotation twiddle mirrors -/

/-- **Mirror zero loci sum to one**: symmetric about `σ = 1/2`. -/
theorem projectionLine_mirror {θ : ℝ} (h : Real.cos θ + Real.sin θ ≠ 0) :
    projectionLine (Real.pi / 2 - θ) = 1 - projectionLine θ := by
  unfold projectionLine
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub,
    show Real.sin θ + Real.cos θ = Real.cos θ + Real.sin θ from add_comm _ _]
  field_simp [h]
  ring

/-- **FE orbit cancellation** for a mirrored rotation pair. -/
theorem rotFree_mirror_pair_sum (θ σ : ℝ) :
    rotFree θ (functionalPair σ) +
      rotFree (Real.pi / 2 - θ) (functionalPair (1 - σ)) = 0 := by
  unfold rotFree functionalPair
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub]
  ring

/-- On a fixed pair `(σ,1-σ)`, the mirrored rotation sum is `(cos θ+sin θ)(2σ-1)`. -/
theorem rotFree_mirror_pair_sum_same_pair (θ σ : ℝ) :
    rotFree θ (functionalPair σ) +
      rotFree (Real.pi / 2 - θ) (functionalPair σ) =
      (Real.cos θ + Real.sin θ) * (2 * σ - 1) := by
  unfold rotFree functionalPair
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub]
  ring

/-- The mirrored rotation **difference** is constant in `σ` and vanishes only at
`θ = π/4` (coincidence locus of the pair). -/
theorem rotFree_mirror_pair_diff (θ σ : ℝ) :
    rotFree θ (functionalPair σ) -
      rotFree (Real.pi / 2 - θ) (functionalPair σ) =
      Real.cos θ - Real.sin θ := by
  unfold rotFree functionalPair
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub]
  ring

theorem rotFree_mirror_pair_diff_zero_iff (θ : ℝ) :
    Real.cos θ - Real.sin θ = 0 ↔ Real.cos θ = Real.sin θ := by
  constructor <;> intro h <;> linarith

/-- **Self-mirror at 45°**: `π/2 - π/4 = π/4`. -/
theorem mirror_angle_pi_div_four :
    Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring

/-! ## 30° / 60° mirror example (affine) -/

theorem sin_pi_div_six_ne_cos_pi_div_six :
    Real.sin (Real.pi / 6) ≠ Real.cos (Real.pi / 6) := by
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
  have hs : (1 : ℝ) < Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [Real.sqrt_nonneg 3]

theorem affineTwiddleZero_pi_six :
    affineTwiddleZero (Real.pi / 6) =
      (1 / 2 : ℝ) / ((1 / 2 : ℝ) - Real.sqrt 3 / 2) := by
  unfold affineTwiddleZero
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six]

theorem affineTwiddleZero_pi_three :
    affineTwiddleZero (Real.pi / 3) =
      Real.sqrt 3 / 2 / (Real.sqrt 3 / 2 - (1 / 2 : ℝ)) := by
  unfold affineTwiddleZero
  rw [Real.sin_pi_div_three, Real.cos_pi_div_three]

theorem affineTwiddle_pi_six_pi_three_mirror :
    Real.pi / 2 - Real.pi / 6 = Real.pi / 3 := by ring

theorem affineTwiddleZero_pi_six_pi_three_mirror :
    affineTwiddleZero (Real.pi / 3) = 1 - affineTwiddleZero (Real.pi / 6) := by
  have hangle : Real.pi / 2 - Real.pi / 6 = Real.pi / 3 := by ring
  simpa [hangle] using
    affineTwiddleZero_mirror (θ := Real.pi / 6) sin_pi_div_six_ne_cos_pi_div_six

end

end Hqiv.Story
