import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3TwiddleRigidityForcesLine
import Hqiv.Story.S3ComplexResidualModel
import Hqiv.Story.S3FESlotDischarge
import Hqiv.Story.S3DeltaOrbitOffStrip
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Closed-form packaging for `ζ` via SO(4) channels

Classical `ζ` is piecewise closed on the standard regions. On the open critical strip
Mathlib's functional equation is already a **sin/cos–Γ–π** product (`riemannZeta_one_sub`);
the HQIV spine supplies the real **45° SO(4) projection** `(2σ−1)/√2`.

The interior RH capstone is the **factorization**
`ζ(s) = h(s) · (2σ−1)/√2` on `0 < Re s < 1` with `h(s) ≠ 0` off the critical line.
Constructing `h` from the harmonic–Δ–SO(4) even/odd channel split is the analytic target.
-/

namespace Hqiv.Story

noncomputable section

open Complex ArithmeticFunction Real

/-! ## SO(4) 45° critical factor (real projection) -/

/-- Complex lift of the exact-45° equator readout: vanishes iff `Re(s)=1/2`. -/
noncomputable def so4CriticalFactor (s : ℂ) : ℂ :=
  (exactTwiddleReadout s : ℂ)

/-- Legacy blunt interior pin (real-complex lift). -/
def InteriorStripZetaEqExactTwiddleReadout : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = so4CriticalFactor s

theorem so4CriticalFactor_eq_scaled_deviation (s : ℂ) :
    exactTwiddleReadout s = (2 / Real.sqrt 2) * criticalLineDeviation s := by
  have h := criticalLineDeviation_eq_scaled_exactTwiddle s
  field_simp at h ⊢
  linarith

theorem so4CriticalFactor_zero_iff (s : ℂ) :
    so4CriticalFactor s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  simp [so4CriticalFactor, exact_twiddle_zero_iff_on_line]

theorem so4CriticalFactor_ne_zero_off_line {s : ℂ} (h : s.re ≠ (1 / 2 : ℝ)) :
    so4CriticalFactor s ≠ 0 := by
  intro h0
  exact h ((so4CriticalFactor_zero_iff s).mp h0)

/-! ## Open strip: automatic FE slot; sin/cos closed form -/

theorem open_strip_avoids_negative_integers (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (n : ℕ) : s ≠ (-n : ℂ) := by
  intro hn
  have := congrArg Complex.re hn
  simp at this
  linarith

noncomputable def zetaSinCosFactor (s : ℂ) : ℂ :=
  cos (Real.pi * s / 2)

/-- Open-strip closed form: sin/cos–Γ–π assembly times `ζ(1−s)`. -/
theorem riemannZeta_open_strip_fe_closed_form (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s =
      2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Gamma (1 - s) * zetaSinCosFactor (1 - s) *
        riemannZeta (1 - s) := by
  have h0' : 0 < (1 - s).re := by simp [sub_re, one_re]; linarith
  have h1' : (1 - s).re < 1 := by simp [sub_re, one_re]; linarith
  have hs1' : (1 - s) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [sub_re, one_re] at this
    linarith
  simpa [zetaSinCosFactor, sub_sub] using
    riemannZeta_one_sub (open_strip_avoids_negative_integers (1 - s) h0' h1') hs1'

/-- At `σ = 1/2` on the real axis, the sin/cos factor is `cos(π/4)`. -/
theorem zetaSinCosFactor_at_half :
    zetaSinCosFactor (1 / 2 : ℂ) = Complex.cos (Real.pi / 4) := by
  simp only [zetaSinCosFactor]
  have harg : (Real.pi : ℂ) * (1 / 2 : ℂ) / 2 = (Real.pi / 4 : ℂ) := by ring_nf
  rw [harg]

/-! ## Proved closed forms on other regions -/

theorem riemannZeta_dirichlet_closed_form (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  shell_sum_eq_riemannZeta s hs

theorem riemannZeta_bernoulli_neg_closed_form (k : ℕ) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) :=
  riemannZeta_neg_nat_eq_bernoulli' k

theorem riemannZeta_pi_even_closed_form {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) =
      (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1) * (Real.pi : ℂ) ^ (2 * k) * bernoulli (2 * k) /
        Nat.factorial (2 * k) :=
  riemannZeta_two_mul_nat hk

/-! ## Interior factorization pin -/

/-- Assembly nonzero at nontrivial zeros off the critical line (RH uses this). -/
def InteriorAssemblyNonzeroAtNontrivialZerosOffLine (h : ℂ → ℂ) : Prop :=
  ∀ s, IsNontrivialZetaZero s → s.re ≠ (1 / 2 : ℝ) → h s ≠ 0

/--
On the open strip **off** `Re = 1/2`, `ζ` factors through the SO(4) deviation; the
assembly stays nonzero at nontrivial zeros off the line (so zeros come from the
critical factor, not from `h` vanishing).
-/
def InteriorStripZetaCriticalFactorizationOffLine : Prop :=
  ∃ h : ℂ → ℂ,
    (∀ s, 0 < s.re → s.re < 1 → s.re ≠ (1 / 2 : ℝ) →
      riemannZeta s = h s * so4CriticalFactor s) ∧
      InteriorAssemblyNonzeroAtNontrivialZerosOffLine h

/-- Legacy name (off-line formulation). -/
abbrev InteriorStripZetaCriticalFactorization :=
  InteriorStripZetaCriticalFactorizationOffLine

theorem RiemannHypothesis_of_interior_factorization
    (hFac : InteriorStripZetaCriticalFactorizationOffLine) :
    RiemannHypothesis := by
  obtain ⟨h, hEq, hNz⟩ := hFac
  intro s hz hNotTrivial hNotOne
  have hzz : IsNontrivialZetaZero s := ⟨hz, hNotTrivial, hNotOne⟩
  rcases nontrivial_zero_open_strip s hzz with ⟨h0, h1⟩
  by_cases hs : s.re = (1 / 2 : ℝ)
  · exact hs
  · have hfac := hEq s h0 h1 hs
    have hh : h s ≠ 0 := hNz s hzz hs
    have hzero : h s * so4CriticalFactor s = 0 := by rw [← hfac, hz]
    have hcf : so4CriticalFactor s = 0 := by
      rcases mul_eq_zero.mp hzero with hh0 | hcf0
      · exact absurd hh0 hh
      · exact hcf0
    exact (so4CriticalFactor_zero_iff s).mp hcf

def complexResidualModel_of_interior_factorization
    (hFac : InteriorStripZetaCriticalFactorization) :
    S3ComplexResidualModel where
  residual := riemannZeta
  zeta_eq_residual := fun _ => rfl
  nontrivial_zero_locks_re_half := by
    intro s hzz hz
    exact RiemannHypothesis_of_interior_factorization hFac s hz hzz.2.1 hzz.2.2

theorem nonempty_complexResidualModel_of_interior_factorization
    (hFac : InteriorStripZetaCriticalFactorization) :
    Nonempty S3ComplexResidualModel :=
  ⟨complexResidualModel_of_interior_factorization hFac⟩

theorem conditionals_discharged_of_interior_factorization
    (hFac : InteriorStripZetaCriticalFactorization) :
    RiemannHypothesis ∧ Nonempty S3ComplexResidualModel :=
  ⟨RiemannHypothesis_of_interior_factorization hFac,
   nonempty_complexResidualModel_of_interior_factorization hFac⟩

theorem interior_factorization_of_readout_pinning
    (hPin : InteriorStripZetaEqExactTwiddleReadout) :
    InteriorStripZetaCriticalFactorizationOffLine := by
  refine ⟨fun s => riemannZeta s / so4CriticalFactor s, ?_, ?_⟩
  · intro s h0 h1 hσ
    have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
    have hpin := hPin s h0 h1
    field_simp [hpin, hcf]
  · intro s hzz hσ
    have hcf : so4CriticalFactor s ≠ 0 := so4CriticalFactor_ne_zero_off_line hσ
    rcases nontrivial_zero_open_strip s hzz with ⟨h0, h1⟩
    have hpin := hPin s h0 h1
    have hz : riemannZeta s = 0 := hzz.1
    have hcf0 : so4CriticalFactor s = 0 := hpin.symm.trans hz
    exact absurd hcf0 hcf

theorem RiemannHypothesis_of_interior_strip_pinning
    (hPin : InteriorStripZetaEqExactTwiddleReadout) :
    RiemannHypothesis :=
  RiemannHypothesis_of_interior_factorization (interior_factorization_of_readout_pinning hPin)

end

end Hqiv.Story
