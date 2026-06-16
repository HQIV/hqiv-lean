import Hqiv.Story.S3SpectralResonanceChanneling
import Hqiv.Story.S3ZeroQuadrupletOrbit

/-!
# Vertical axis rigidity: the orbits cannot wobble

This module formalizes the rigidity intuition: *the orbits can't wobble ---
any curvature (a second symmetry axis, a tilted or bent critical locus)
would force zeros out of the critical strip, off to infinity.*

## The mechanism: two mirrors make a translation

The zero set is unconditionally closed under the FE point-reflection
`s ↦ 1 − s` (`nontrivial_zero_fe_closed` --- no Schwarz hypothesis needed).
Suppose the zero set were *also* closed under the mirror reflection
`verticalReflect σ₀ : s ↦ 2σ₀ − conj s` about some vertical axis
`Re = σ₀`.  Composing the two symmetries twice yields the translation
\[
  s \longmapsto s + (2 - 4\sigma_0),
\]
which is nontrivial unless `σ₀ = 1/2`.  Iterating a nontrivial translation
marches any zero monotonically in `Re` --- straight out of the open strip
`0 < Re < 1`, "out somewhere in infinity" --- contradicting the proved strip
confinement.  Hence (`strip_set_unique_vertical_axis`, abstract; and
`zeta_zero_unique_vertical_axis`, instantiated): **any nonempty
strip-confined FE-closed set admits at most one vertical mirror axis, and it
must be `Re = 1/2`.**

The only hypothesis carried by the zeta instantiation is nonemptiness of the
nontrivial zero set --- classical (Hardy 1914: infinitely many zeros on the
line) but not yet in Mathlib, so it is taken as an explicit hypothesis
rather than smuggled in.

## Supporting rigidity facts (all unconditional)

* `verticalReflect_fixed_iff`: the fixed-point set of the mirror about
  `Re = σ₀` is exactly the vertical line `Re = σ₀`; in particular the
  FE+Schwarz mirror `s ↦ 1 − conj s` fixes exactly the critical line
  (`verticalReflect_half_eq_one_sub_schwarz`).
* `fe_pair_same_vertical_line_iff`: if a point and its FE partner `1 − s`
  lie on a *common* vertical line, that line is `Re = 1/2`.  "Any two
  (symmetry-partner) points on one line force *the* line."
* `sq_weight_locus_is_vertical_line`: the square-root-weight locus
  `{‖n^{−s}‖² = 1/n}` is *globally* the straight vertical line
  `Re = 1/2` --- as a set identity in all of `ℂ`, with zero curvature
  anywhere; `sq_weight_locus_vertical_flow` exhibits the flow invariance
  `s ↦ s + it` explicitly.

## Honest scope

"If any two points are on the line then all points must be on the line" is
not a valid inference classically --- what *is* proved is: (i) any two
symmetry-partner points on a common vertical line pin that line to
`Re = 1/2`; (ii) the candidate locus itself is a perfect straight line, not
a curve; (iii) the zero set cannot support a second mirror axis without
leaking out of the strip.  Promoting "the unique possible axis is `1/2`" to
"every zero lies on it" is exactly RH, already named by
`RH_iff_zero_spectral_weights` and the neighbouring capstones.
-/

namespace Hqiv.Story

open Complex

noncomputable section

/-! ## The mirror and its fixed line -/

/-- Mirror reflection about the vertical line `Re = σ₀`:
`σ + it ↦ (2σ₀ − σ) + it`. -/
def verticalReflect (σ₀ : ℝ) (s : ℂ) : ℂ :=
  2 * (σ₀ : ℂ) - starRingEnd ℂ s

/-- The mirror about `Re = 1/2` is the FE + Schwarz composite `1 − conj s`. -/
theorem verticalReflect_half_eq_one_sub_schwarz (s : ℂ) :
    verticalReflect (1 / 2) s = 1 - schwarzReflect s := by
  unfold verticalReflect schwarzReflect
  push_cast
  ring

/-- The fixed-point set of the mirror about `Re = σ₀` is exactly the
vertical line `Re = σ₀`: vertical mirrors fix straight lines, never curves. -/
theorem verticalReflect_fixed_iff (σ₀ : ℝ) (s : ℂ) :
    verticalReflect σ₀ s = s ↔ s.re = σ₀ := by
  unfold verticalReflect
  constructor
  · intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re, Complex.conj_re] at this
    linarith
  · intro h
    apply Complex.ext
    · simp [Complex.sub_re, Complex.mul_re, Complex.conj_re, h]
      ring
    · simp [Complex.sub_im, Complex.mul_im, Complex.conj_im]

/-- **Two symmetry-partner points on one vertical line force the line.**
If `s` and its FE partner `1 − s` share a real part, that shared vertical
line is `Re = 1/2`. -/
theorem fe_pair_same_vertical_line_iff (s : ℂ) :
    (1 - s).re = s.re ↔ s.re = (1 / 2 : ℝ) := by
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-! ## Abstract rigidity: two mirrors make a translation, translations escape -/

/--
**Unique vertical axis for strip-confined FE-closed sets.**  If a nonempty
set `Z` is confined to the open strip, closed under the FE point-reflection
`z ↦ 1 − z`, and closed under the mirror `verticalReflect σ₀`, then
`σ₀ = 1/2`.  Otherwise the composite of the two symmetries (applied twice)
is the nontrivial translation `z ↦ z + (2 − 4σ₀)`, and iterating it marches
a point of `Z` out of the strip.
-/
theorem strip_set_unique_vertical_axis {Z : Set ℂ}
    (hsub : ∀ z ∈ Z, 0 < z.re ∧ z.re < 1) (hne : Z.Nonempty)
    (hfe : ∀ z ∈ Z, (1 - z) ∈ Z)
    {σ₀ : ℝ} (hax : ∀ z ∈ Z, verticalReflect σ₀ z ∈ Z) :
    σ₀ = (1 / 2 : ℝ) := by
  by_contra hσ
  obtain ⟨z, hz⟩ := hne
  set τ : ℝ := 2 - 4 * σ₀ with hτdef
  have hτ0 : τ ≠ 0 := by
    intro h
    apply hσ
    have : σ₀ = 1 / 2 := by
      rw [hτdef] at h
      linarith
    exact this
  -- one full mirror-FE-mirror-FE cycle is translation by τ
  have hstep : ∀ w ∈ Z, w + (τ : ℂ) ∈ Z := by
    intro w hw
    have h1 := hax w hw
    have h2 := hfe _ h1
    have h3 := hax _ h2
    have h4 := hfe _ h3
    have hcalc : 1 - verticalReflect σ₀ (1 - verticalReflect σ₀ w) = w + (τ : ℂ) := by
      unfold verticalReflect
      rw [hτdef]
      push_cast
      simp only [map_sub, map_mul, map_one, map_ofNat, Complex.conj_ofReal,
        Complex.conj_conj]
      ring
    rwa [hcalc] at h4
  -- iterate the translation
  have hiter : ∀ k : ℕ, z + ((k * τ : ℝ) : ℂ) ∈ Z := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ n ih =>
        have := hstep _ ih
        have hcast : z + ((n * τ : ℝ) : ℂ) + (τ : ℂ) =
            z + (((n + 1 : ℕ) * τ : ℝ) : ℂ) := by
          push_cast
          ring
        rwa [hcast] at this
  have hre : ∀ k : ℕ, (z + ((k * τ : ℝ) : ℂ)).re = z.re + k * τ := by
    intro k
    simp [Complex.add_re, Complex.ofReal_re]
  -- a nontrivial translation exits the strip
  rcases lt_or_gt_of_ne hτ0 with hneg | hpos
  · -- τ < 0 : march out to the left, Re ≤ 0
    obtain ⟨k, hk⟩ := exists_nat_gt (z.re / (-τ))
    have hmem := (hsub _ (hiter k)).1
    rw [hre k] at hmem
    have hkτ : z.re < k * (-τ) := (div_lt_iff₀ (by linarith)).mp hk
    nlinarith
  · -- τ > 0 : march out to the right, Re ≥ 1
    obtain ⟨k, hk⟩ := exists_nat_gt ((1 - z.re) / τ)
    have hmem := (hsub _ (hiter k)).2
    rw [hre k] at hmem
    have hkτ : 1 - z.re < k * τ := (div_lt_iff₀ hpos).mp hk
    nlinarith

/-! ## Zeta instantiation (FE-only; no Schwarz hypothesis) -/

/-- The nontrivial zero set is unconditionally closed under the FE
point-reflection `ρ ↦ 1 − ρ`. -/
theorem nontrivial_zero_fe_closed {ρ : ℂ} (h : IsNontrivialZetaZero ρ) :
    IsNontrivialZetaZero (1 - ρ) := by
  obtain ⟨h0, h1⟩ := nontrivial_zero_open_strip ρ h
  refine ⟨zeta_zero_fe_pair ρ h, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hρ : ρ = (((2 * (n : ℝ) + 3) : ℝ) : ℂ) := by
      push_cast
      linear_combination -hn
    have hre : ρ.re = 2 * (n : ℝ) + 3 := by
      rw [hρ]
      exact Complex.ofReal_re _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro h1eq
    have hρ0 : ρ = 0 := by linear_combination -h1eq
    rw [hρ0] at h0
    simp at h0

/--
**The zero set admits no second vertical mirror axis.**  Given any
nontrivial zero at all (Hardy, classical --- explicit hypothesis), if the
nontrivial zero set is closed under the mirror about `Re = σ₀`, then
`σ₀ = 1/2`.  Any other axis composes with the unconditional FE closure into
a translation that forces zeros out of the strip --- the orbits cannot
wobble.
-/
theorem zeta_zero_unique_vertical_axis
    (hne : ∃ ρ : ℂ, IsNontrivialZetaZero ρ) {σ₀ : ℝ}
    (hax : ∀ ρ : ℂ, IsNontrivialZetaZero ρ →
      IsNontrivialZetaZero (verticalReflect σ₀ ρ)) :
    σ₀ = (1 / 2 : ℝ) := by
  refine strip_set_unique_vertical_axis
    (Z := {s : ℂ | IsNontrivialZetaZero s})
    (fun z hz => nontrivial_zero_open_strip z hz) hne
    (fun z hz => nontrivial_zero_fe_closed hz)
    (fun z hz => hax z hz)

/-! ## The candidate locus is a perfect straight line (no curvature) -/

/-- **No curvature, globally.**  The square-root-weight locus of any
spectral line `n ≥ 2` is, as a subset of all of `ℂ`, exactly the straight
vertical line `Re = 1/2`. -/
theorem sq_weight_locus_is_vertical_line {n : ℕ} (hn : 2 ≤ n) :
    {s : ℂ | ‖so4SpectralLine n s‖ ^ 2 = (n : ℝ)⁻¹} =
      {s : ℂ | s.re = (1 / 2 : ℝ)} :=
  Set.ext fun _ => so4SpectralLine_sq_weight hn

/-- The locus is invariant under the full vertical flow `s ↦ s + it`: it is
a straight line swept by translation, with no transverse drift anywhere. -/
theorem sq_weight_locus_vertical_flow {n : ℕ} (hn : 2 ≤ n) {s : ℂ}
    (hs : ‖so4SpectralLine n s‖ ^ 2 = (n : ℝ)⁻¹) (t : ℝ) :
    ‖so4SpectralLine n (s + Complex.I * t)‖ ^ 2 = (n : ℝ)⁻¹ := by
  rw [so4SpectralLine_sq_weight hn] at hs ⊢
  simp [Complex.add_re, Complex.mul_re, hs]

end

end Hqiv.Story
