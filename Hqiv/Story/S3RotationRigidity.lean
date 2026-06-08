import Hqiv.Story.S3FortyFiveProjection

/-!
# Rotation-angle rigidity of the critical-line equator

The companion module `S3FortyFiveProjection` proves that the **exact** 45°
rotation sends the functional-equation pair `(σ, 1-σ)` to a free coordinate that
vanishes precisely on `σ = 1/2` (the critical line). This module answers the
sharper question:

> What if we rotate by some other angle `θ` (a deviation `Δ` away from 45°)?

We model a general plane rotation by angle `θ` and read off the **free** (equator)
coordinate

`rotFree θ (x, y) = x · cos θ − y · sin θ`,

so that `rotFree (π/4) = rot45Free`.

The rigidity content:

* `free_vanishes_at_half_iff_cos_eq_sin` — the free coordinate vanishes at the
  critical center `σ = 1/2` **iff** `cos θ = sin θ`, i.e. the rotation is exactly
  45° (mod π). For any other angle, `σ = 1/2` is *not* on the equator.
* `rotFree_perturbed_at_half` — perturbing the angle to `π/4 + δ` gives free
  coordinate `−(√2/2)·sin δ` at the critical center.
* `perturbation_breaks_alignment` — hence for any `δ` with `sin δ ≠ 0` the
  critical-line center fails to cancel: nothing survives on the equator unless we
  hold the rotation at the two 45° angles.

This is a purely geometric/algebraic rigidity statement about the rotation; it
does **not** prove RH. It pins down *why* the construction must use the exact 45°
rotations: any other angle moves the cancellation locus off `Re(s)=1/2`.

**Orbit / twiddle picture.** For fixed functional-equation data, changing the
twiddle angle does not change the underlying pair — it only **relocates the real
σ-line** where the rotated free coordinate vanishes (`projectionLine θ`). Exact 45°
pins that line at `σ = 1/2`; any shift `π/4 + δ` moves it elsewhere.
-/

namespace Hqiv.Story

noncomputable section

/-- The free/equator coordinate after a plane rotation by angle `θ`. -/
noncomputable def rotFree (θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.cos θ - p.2 * Real.sin θ

/-- On the functional-equation pair, the rotated free coordinate is
`σ·(cos θ + sin θ) − sin θ`. -/
theorem rotFree_functionalPair (θ σ : ℝ) :
    rotFree θ (functionalPair σ) =
      σ * (Real.cos θ + Real.sin θ) - Real.sin θ := by
  unfold rotFree functionalPair
  ring

/--
The **line of interest** for twiddle angle `θ`: the real `σ` where the rotated free
coordinate vanishes. Orbits in twiddle space slide this line along the real axis.
-/
noncomputable def projectionLine (θ : ℝ) : ℝ :=
  Real.sin θ / (Real.cos θ + Real.sin θ)

/--
Affine readout in `σ`: vanishing is equivalent to landing on the projection line.
-/
theorem rotFree_vanishes_iff_on_projection_line (θ σ : ℝ)
    (hden : Real.cos θ + Real.sin θ ≠ 0) :
    rotFree θ (functionalPair σ) = 0 ↔ σ = projectionLine θ := by
  rw [rotFree_functionalPair, projectionLine]
  constructor
  · intro h
    have hmul : σ * (Real.cos θ + Real.sin θ) = Real.sin θ := sub_eq_zero.mp h
    exact (eq_div_iff hden).mpr hmul
  · intro h
    subst h
    field_simp [hden]
    ring

/-- Exact 45° pins the projection line at the critical center. -/
theorem projectionLine_pi_div_four :
    projectionLine (Real.pi / 4) = (1 / 2 : ℝ) := by
  unfold projectionLine
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linarith [h2]

/-- At the exact 45° angle the general rotation reduces to `rot45Free`. -/
theorem rotFree_pi_div_four (p : ℝ × ℝ) :
    rotFree (Real.pi / 4) p = rot45Free p := by
  unfold rotFree rot45Free
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
    field_simp
    linarith [h2]
  rw [hs]
  ring

/--
**Rigidity at the critical center.** The free coordinate vanishes at the critical
center `σ = 1/2` exactly when `cos θ = sin θ` — i.e. only for the 45° family of
angles. Any other rotation pushes `σ = 1/2` off the equator.
-/
theorem free_vanishes_at_half_iff_cos_eq_sin (θ : ℝ) :
    rotFree θ (functionalPair (1 / 2)) = 0 ↔ Real.cos θ = Real.sin θ := by
  rw [rotFree_functionalPair]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- The 45° rotation does cancel at the critical center. -/
theorem aligned_at_pi_div_four :
    rotFree (Real.pi / 4) (functionalPair (1 / 2)) = 0 := by
  rw [free_vanishes_at_half_iff_cos_eq_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]

/--
**Perturbation law.** Rotating by `π/4 + δ` (a deviation `Δ = δ` from 45°) sends
the critical center to free coordinate `−(√2/2)·sin δ`.
-/
theorem rotFree_perturbed_at_half (δ : ℝ) :
    rotFree (Real.pi / 4 + δ) (functionalPair (1 / 2)) =
      -(Real.sqrt 2 / 2) * Real.sin δ := by
  unfold rotFree functionalPair
  simp only []
  rw [Real.cos_add, Real.sin_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

/-- The perturbed free coordinate vanishes at the critical center iff `sin δ = 0`. -/
theorem rotFree_perturbed_at_half_eq_zero_iff (δ : ℝ) :
    rotFree (Real.pi / 4 + δ) (functionalPair (1 / 2)) = 0 ↔ Real.sin δ = 0 := by
  rw [rotFree_perturbed_at_half, neg_mul, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exfalso
      have : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
      linarith
    · exact h
  · intro h; right; exact h

/--
**Any nonzero deviation breaks the cancellation.** For a deviation `δ` from 45°
with `sin δ ≠ 0` (in particular any `δ ∈ (0, π)`), the critical-line center no
longer lands on the equator: the projection is nonzero. Nothing survives on
`Re(s)=1/2` unless the rotation is held at exactly 45°.
-/
theorem perturbation_breaks_alignment (δ : ℝ) (hδ : Real.sin δ ≠ 0) :
    rotFree (Real.pi / 4 + δ) (functionalPair (1 / 2)) ≠ 0 := by
  intro h
  exact hδ ((rotFree_perturbed_at_half_eq_zero_iff δ).mp h)

/--
**Twiddle orbit = shift the line of interest.** A nonzero deviation `δ` relocates
the vanishing locus away from `σ = 1/2`: the critical center is no longer on the
shifted equator.
-/
theorem twiddle_shift_avoids_critical_center (δ : ℝ) (hδ : Real.sin δ ≠ 0) :
    ∀ σ : ℝ, rotFree (Real.pi / 4 + δ) (functionalPair σ) = 0 → σ ≠ (1 / 2 : ℝ) := by
  intro σ hzero hhalf
  subst hhalf
  exact perturbation_breaks_alignment δ hδ hzero

/--
When `cos θ + sin θ ≠ 0`, the projection line is `1/2` exactly for the 45° twiddle
family (`cos θ = sin θ`).
-/
theorem projectionLine_eq_half_iff_cos_eq_sin (θ : ℝ) (hden : Real.cos θ + Real.sin θ ≠ 0) :
    projectionLine θ = (1 / 2 : ℝ) ↔ Real.cos θ = Real.sin θ := by
  unfold projectionLine
  constructor
  · intro h
    have hnum : 2 * Real.sin θ = Real.cos θ + Real.sin θ := by
      have := congr_arg (fun x => x * (Real.cos θ + Real.sin θ)) h
      field_simp [hden] at this
      linarith
    linarith
  · intro h
    have htwice : Real.cos θ + Real.sin θ = 2 * Real.sin θ := by rw [h]; ring
    have hsin : Real.sin θ ≠ 0 := by
      intro hzero
      have hcos : Real.cos θ = 0 := h.trans hzero
      exact hden (by rw [hcos, hzero]; norm_num)
    rw [htwice]
    field_simp [hsin]

end

end Hqiv.Story
