import Hqiv.Story.S3SameHeightOrbitCollapse

/-!
# Polar projection collapse: the poles must land on a single point

This module formalizes: *the poles of `S³` must project to a single point on
the complex plane for there to be a zero (on the line) --- and this is what
disallows multiple points per height.*

At height `t`, the mirror symmetry presents two polar lifts whose plane
projections are `s` and `polarPartner s = 1 − conj s` --- the same-height
quadruplet pair.  The provable laws:

* **The polar separation is horizontal and real**:
  `polarPartner s − s = 1 − 2σ` (`polar_separation_eq`).  The two pole
  images never differ in height, only in `Re`.
* **The separation IS the twiddle readout**:
  `polarPartner s − s = −√2 · so4CriticalFactor s`
  (`polar_separation_eq_twiddle`).  The SO(4) equator channel does not
  break off the line --- it *reports the polar separation exactly*.  The
  ``45° twiddle'' is, verbatim, the displacement between the two pole
  projections.
* **Collapse law**: the two pole images coincide iff `Re s = 1/2`
  (`polar_collapse_iff_on_line`), and the separation norm is twice the
  distance to the critical line
  (`polar_separation_eq_twice_deviation`).

## "SO(4) is only applicable if RH" --- the right way around

It is not that the SO(4) machinery silently *presupposes* RH.  The
single-point polar projection on the zero set is a well-formed proposition
(`PolarProjectionCollapsesOnZeros`), and it is RH --- proved as a zero-slack
equivalence (`polar_collapse_iff_RH`), chaining further to "one zero per
height" given the Schwarz identity
(`polar_collapse_iff_unique_height`).  Off the line the geometry stays
perfectly consistent: the projection simply reports a nonzero polar
separation through the surviving twiddle factor, which is exactly the
off-line branch of the resonance-channeling dichotomy.  So the statement is
not sad but sharp: *single-point polar projection at every zero* is the
fourth face of RH in this stack, equal in strength to unimodular tangent,
square-root spectral weights, and one-zero-per-height.
-/

namespace Hqiv.Story

open Complex

noncomputable section

/-- Plane projection of the second pole at the height of `s`: the
same-height mirror image `1 − conj s`. -/
noncomputable def polarPartner (s : ℂ) : ℂ := 1 - schwarzReflect s

/-- The two pole images always share the height. -/
theorem polarPartner_same_height (s : ℂ) : (polarPartner s).im = s.im :=
  one_sub_schwarz_same_height s

/-- **The polar separation is horizontal and real**: `1 − 2σ`.  The pole
images can only disagree along `Re`. -/
theorem polar_separation_eq (s : ℂ) :
    polarPartner s - s = (((1 - 2 * s.re) : ℝ) : ℂ) := by
  unfold polarPartner schwarzReflect
  have h := Complex.add_conj s
  push_cast at h ⊢
  linear_combination -h

/-- **The polar separation IS the twiddle readout** (up to `−√2`): the
equator channel measures exactly the failure of the two poles to project to
a single point.  Off the line SO(4) does not break --- it reports. -/
theorem polar_separation_eq_twiddle (s : ℂ) :
    polarPartner s - s = -(Real.sqrt 2 : ℂ) * so4CriticalFactor s := by
  rw [polar_separation_eq]
  simp only [so4CriticalFactor, exactTwiddleReadout, rot45Free, functionalPair]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  push_cast
  field_simp
  ring

/-- The separation norm is `|1 − 2σ|`. -/
theorem polar_separation_norm (s : ℂ) :
    ‖polarPartner s - s‖ = |1 - 2 * s.re| := by
  rw [polar_separation_eq]
  exact Complex.norm_real _

/-- The separation norm is exactly **twice the distance to the critical
line**. -/
theorem polar_separation_eq_twice_deviation (s : ℂ) :
    ‖polarPartner s - s‖ = 2 * |criticalLineDeviation s| := by
  rw [polar_separation_norm]
  unfold criticalLineDeviation
  rw [show (1 - 2 * s.re) = -2 * (s.re - 1 / 2) by ring, abs_mul]
  norm_num

/-- **Collapse law**: the two pole images coincide iff `s` is on the
critical line. -/
theorem polar_collapse_iff_on_line (s : ℂ) :
    polarPartner s = s ↔ s.re = (1 / 2 : ℝ) :=
  same_height_partner_merges_iff s

/-- Single-point polar projection on the zero set: every nontrivial zero is
a fixed point of the mirror, i.e. its two polar lifts project to one point. -/
def PolarProjectionCollapsesOnZeros : Prop :=
  ∀ ρ : ℂ, IsNontrivialZetaZero ρ → polarPartner ρ = ρ

/-- **Single-point polar projection ⟺ RH** (zero slack, both directions). -/
theorem polar_collapse_iff_RH :
    PolarProjectionCollapsesOnZeros ↔ RiemannHypothesis := by
  constructor
  · intro hP ρ hz hnt h1
    exact (polar_collapse_iff_on_line ρ).mp (hP ρ ⟨hz, hnt, h1⟩)
  · intro hRH ρ hzz
    exact (polar_collapse_iff_on_line ρ).mpr (hRH ρ hzz.1 hzz.2.1 hzz.2.2)

/-- Chaining: single-point polar projection ⟺ one zero per height (given
the Schwarz identity, as in `zeta_zero_quadruplet`).  The polar collapse is
exactly what disallows multiple zeros per height --- and vice versa. -/
theorem polar_collapse_iff_unique_height
    (hconj : ∀ t : ℂ,
      riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    PolarProjectionCollapsesOnZeros ↔
      ∀ ρ₁ ρ₂ : ℂ, IsNontrivialZetaZero ρ₁ → IsNontrivialZetaZero ρ₂ →
        ρ₁.im = ρ₂.im → ρ₁ = ρ₂ :=
  polar_collapse_iff_RH.trans (RH_iff_unique_zero_per_height hconj)

end

end Hqiv.Story
