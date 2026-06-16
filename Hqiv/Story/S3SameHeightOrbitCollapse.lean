import Hqiv.Story.S3VerticalAxisRigidity

/-!
# Same-height orbit collapse: "one zero per height" is exactly RH

This module makes precise — and honestly scopes — the two-part claim:
*"every zero contains all primes to cancel, and two zeros at the same height
would have opposing orbits in the quadruplet, so that's off the board."*

## Part 1: collectivity does not pin the axis

The cancellation at every zero is provably collective
(`finite_spectral_truncation_ne_zero`), but collectivity alone cannot force
`Re ρ = 1/2`: at *any* point of the strip the all-primes weight family is
the perfectly consistent `‖n^{−s}‖² = n^{−2σ}`
(`spectral_weights_consistent_at_any_sigma`).  Nothing diverges or
contradicts off the line; what distinguishes `σ = 1/2` is solely the
square-root normalization `n^{−1}` — and that normalization is RH itself
(`RH_iff_zero_spectral_weights`).

## Part 2: "one zero per height" — proved equivalent to RH

The quadruplet of an off-line zero `σ + it` contains its same-height partner
`1 − conj ρ = (1−σ) + it`; this partner *merges* with `ρ` exactly on the
critical line (`same_height_partner_merges_iff` — the mirror fixed-point law
again).  Conversely, on the line two same-height zeros are the same point.
Hence "no two zeros share a height" is not an available discharge — it is an
exact reformulation of RH, and we prove the equivalence in two strengths:

* `RH_iff_height_pins_re` (**FE only, fully unconditional statement**):
  RH ⟺ any two nontrivial zeros with the same `|Im|` have the same `Re`.
  The backward direction needs no Schwarz input: the FE partner `1 − ρ`
  already supplies a zero of equal `|Im|` and reflected `Re`.
* `RH_iff_unique_zero_per_height` (with the Schwarz identity carried as the
  explicit hypothesis `hconj`, in the style of `zeta_zero_quadruplet`):
  RH ⟺ each height carries at most one nontrivial zero.

## Honest scope

The orbit picture is right: a quadruplet either straddles the line with two
distinct same-height members or collapses onto it.  But declaring the
straddling case "off the board" *is* RH — now machine-checked as an
equivalence with zero slack, in both directions.
-/

namespace Hqiv.Story

open Complex

noncomputable section

/-! ## Part 1: collectivity is σ-uniform -/

/-- At **any** vertical line, the all-primes weight family is consistent:
`‖n^{−s}‖² = n^{−2σ}` for every `n`.  Collectivity of the cancellation
cannot distinguish `σ = 1/2`; only the square-root normalization does. -/
theorem spectral_weights_consistent_at_any_sigma {n : ℕ} (hn : 0 < n)
    (s : ℂ) :
    ‖so4SpectralLine n s‖ ^ 2 = (n : ℝ) ^ (-(2 * s.re)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [so4SpectralLine_norm hn, pow_two, ← Real.rpow_add hpos]
  ring_nf

/-! ## Part 2: the same-height partner and its merge law -/

/-- The FE + Schwarz orbit member `1 − conj s` sits at the **same height**:
`Im (1 − conj s) = Im s`. -/
theorem one_sub_schwarz_same_height (s : ℂ) :
    (1 - schwarzReflect s).im = s.im := by
  simp [schwarzReflect, Complex.sub_im, Complex.one_im, Complex.conj_im]

/-- **Merge law.**  The same-height orbit partner coincides with `s` exactly
on the critical line: the quadruplet straddles the line with two distinct
same-height members iff `Re s ≠ 1/2`. -/
theorem same_height_partner_merges_iff (s : ℂ) :
    1 - schwarzReflect s = s ↔ s.re = (1 / 2 : ℝ) := by
  rw [← verticalReflect_half_eq_one_sub_schwarz]
  exact verticalReflect_fixed_iff (1 / 2) s

/-! ## "One zero per height" ⟺ RH -/

/--
**RH ⟺ height pins the real part (FE only).**  The Riemann Hypothesis is
equivalent to: any two nontrivial zeros with the same `|Im|` have the same
`Re`.  The backward direction is unconditional — the FE partner `1 − ρ` is
already a zero of equal `|Im|` with reflected real part, so the hypothesis
forces `Re ρ = 1 − Re ρ`.
-/
theorem RH_iff_height_pins_re :
    RiemannHypothesis ↔
      ∀ ρ₁ ρ₂ : ℂ, IsNontrivialZetaZero ρ₁ → IsNontrivialZetaZero ρ₂ →
        |ρ₁.im| = |ρ₂.im| → ρ₁.re = ρ₂.re := by
  constructor
  · intro hRH ρ₁ ρ₂ h1 h2 _
    rw [hRH ρ₁ h1.1 h1.2.1 h1.2.2, hRH ρ₂ h2.1 h2.2.1 h2.2.2]
  · intro hH ρ hz hnt h1
    have hzz : IsNontrivialZetaZero ρ := ⟨hz, hnt, h1⟩
    have hfe : IsNontrivialZetaZero (1 - ρ) := nontrivial_zero_fe_closed hzz
    have him : |(1 - ρ).im| = |ρ.im| := by
      simp [Complex.sub_im, Complex.one_im]
    have hre := hH (1 - ρ) ρ hfe hzz him
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith

/--
**RH ⟺ at most one zero per height** (with the Schwarz identity as the
explicit hypothesis `hconj`, in the style of `zeta_zero_quadruplet`).
Forward: on the line, same height means same point.  Backward: an off-line
zero `ρ` would have the *distinct* same-height quadruplet partner
`1 − conj ρ`, contradicting uniqueness.
-/
theorem RH_iff_unique_zero_per_height
    (hconj : ∀ t : ℂ, riemannZeta (schwarzReflect t) = schwarzReflect (riemannZeta t)) :
    RiemannHypothesis ↔
      ∀ ρ₁ ρ₂ : ℂ, IsNontrivialZetaZero ρ₁ → IsNontrivialZetaZero ρ₂ →
        ρ₁.im = ρ₂.im → ρ₁ = ρ₂ := by
  constructor
  · intro hRH ρ₁ ρ₂ h1 h2 him
    have hre1 := hRH ρ₁ h1.1 h1.2.1 h1.2.2
    have hre2 := hRH ρ₂ h2.1 h2.2.1 h2.2.2
    exact Complex.ext (hre1.trans hre2.symm) him
  · intro hU ρ hz hnt h1
    have hzz : IsNontrivialZetaZero ρ := ⟨hz, hnt, h1⟩
    -- conj ρ is a nontrivial zero (Schwarz)
    have hczero : riemannZeta (schwarzReflect ρ) = 0 := by
      rw [hconj ρ, hz, schwarzReflect_zero]
    have hcnt : ¬ IsTrivialNegativeEvenZeroSlot (schwarzReflect ρ) := by
      rintro ⟨n, hn⟩
      apply hnt
      refine ⟨n, ?_⟩
      have := congrArg (starRingEnd ℂ) hn
      simpa [schwarzReflect, Complex.conj_conj, map_mul, map_add, map_neg,
        map_ofNat, map_one] using this
    have hcone : schwarzReflect ρ ≠ 1 := by
      intro h1'
      apply h1
      have := congrArg (starRingEnd ℂ) h1'
      simpa [schwarzReflect, Complex.conj_conj] using this
    have hcz : IsNontrivialZetaZero (schwarzReflect ρ) := ⟨hczero, hcnt, hcone⟩
    -- its FE partner 1 − conj ρ is the same-height quadruplet member
    have hpartner : IsNontrivialZetaZero (1 - schwarzReflect ρ) :=
      nontrivial_zero_fe_closed hcz
    have hmerge : 1 - schwarzReflect ρ = ρ :=
      hU _ ρ hpartner hzz (one_sub_schwarz_same_height ρ)
    exact (same_height_partner_merges_iff ρ).mp hmerge

end

end Hqiv.Story
