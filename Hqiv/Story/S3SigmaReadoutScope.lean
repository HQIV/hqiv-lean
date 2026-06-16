import Hqiv.Story.S3OrbitVsPointwiseGap
import Hqiv.Story.S3ZetaClosedForm
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# σ-readout scope: what the 45° equator projection can and cannot decide

The exact-45° equator readout factors through `Re s` and is blind to imaginary height.
Proving `construction = ζ` relocates zeros onto the construction, not the equator
vanishing locus onto ζ.  Global identification with the real twiddle readout already
fails at `s = 0` (`not_globally_zeta_eq_real_twiddle_readout`).

The FE + Schwarz quadruplet orbit structure is in `S3ZeroQuadrupletOrbit`.
-/

namespace Hqiv.Story

noncomputable section

open Complex

/-! ## Readout factors through real part -/

/-- A complex readout determined only by `Re s`. -/
def FactorsThroughRealPart (f : ℂ → ℂ) : Prop :=
  ∀ s t : ℂ, s.re = t.re → f s = f t

theorem so4CriticalFactor_factorsThroughRealPart :
    FactorsThroughRealPart so4CriticalFactor := by
  intro s t hre
  simp only [so4CriticalFactor, exactTwiddleReadout, rot45Free_functionalPair, hre]

theorem exactTwiddleReadout_factorsThroughRealPart :
    ∀ s t : ℂ, s.re = t.re → exactTwiddleReadout s = exactTwiddleReadout t := by
  intro s t hre
  simp only [exactTwiddleReadout, rot45Free_functionalPair, hre]

theorem exactTwiddleReadout_eq_of_imag_eq (s t : ℂ) (hre : s.re = t.re) :
    exactTwiddleReadout s = exactTwiddleReadout t :=
  exactTwiddleReadout_factorsThroughRealPart s t hre

theorem sigmaReadout_blind_to_imaginary_height (σ : ℝ) (t₁ t₂ : ℝ) :
    exactTwiddleReadout ⟨σ, t₁⟩ = exactTwiddleReadout ⟨σ, t₂⟩ :=
  exactTwiddleReadout_eq_of_imag_eq ⟨σ, t₁⟩ ⟨σ, t₂⟩ rfl

theorem so4CriticalFactor_eq_of_re_eq (s t : ℂ) (hre : s.re = t.re) :
    so4CriticalFactor s = so4CriticalFactor t :=
  so4CriticalFactor_factorsThroughRealPart s t hre

theorem sigmaReadout_agrees_at_fixed_re (σ : ℝ) (t₁ t₂ : ℝ) :
    so4CriticalFactor ⟨σ, t₁⟩ = so4CriticalFactor ⟨σ, t₂⟩ := by
  simpa using so4CriticalFactor_eq_of_re_eq ⟨σ, t₁⟩ ⟨σ, t₂⟩ rfl

/-! ## Identification transfers zero sets, not σ-constraints -/

theorem eq_imp_zero_iff (f g : ℂ → ℂ) (hfg : ∀ s, f s = g s) (s : ℂ) :
    f s = 0 ↔ g s = 0 := by
  constructor
  · intro hf; simpa [hfg s] using hf
  · intro hg; simpa [hfg s] using hg

theorem zeta_eq_readout_same_zero_set (s : ℂ)
    (hEq : riemannZeta s = (exactTwiddleReadout s : ℂ)) :
    riemannZeta s = 0 ↔ exactTwiddleReadout s = 0 := by
  constructor
  · intro hz; exact Complex.ofReal_eq_zero.mp (hEq ▸ hz)
  · intro hz; rw [hEq]; exact Complex.ofReal_eq_zero.mpr hz

/--
Global identification with the real twiddle readout fails: `ζ(0) = -1/2` but the
readout is `-1/√2`.
-/
theorem not_globally_zeta_eq_real_twiddle_readout :
    ¬ ∀ s : ℂ, riemannZeta s = (exactTwiddleReadout s : ℂ) := by
  intro h
  have hEq := h 0
  rw [riemannZeta_zero] at hEq
  have hread : (exactTwiddleReadout 0 : ℂ) = (-1 / Real.sqrt 2 : ℂ) := by
    unfold exactTwiddleReadout
    simp [rot45Free_functionalPair]
  have hEq' : (-1 / 2 : ℂ) = (-1 / Real.sqrt 2 : ℂ) := hEq.trans hread
  have hre : (-1 / 2 : ℝ) = -1 / Real.sqrt 2 := by
    simpa [Complex.ofReal_div] using congrArg Complex.re hEq'
  have hineq : (-1 / 2 : ℝ) ≠ -1 / Real.sqrt 2 := by
    have hsqrt : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    intro heq
    have hmul : (-1 / 2 : ℝ) * Real.sqrt 2 = (-1 / Real.sqrt 2) * Real.sqrt 2 := by
      rw [heq]
    field_simp [hsqrt] at hmul
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hpos]
  exact hineq hre

theorem so4CriticalFactor_eq_affine_re (z : ℂ) :
    so4CriticalFactor z = ((2 * z.re - 1) / Real.sqrt 2 : ℂ) := by
  simp [so4CriticalFactor, exactTwiddleReadout, rot45Free_functionalPair]

end

end Hqiv.Story
