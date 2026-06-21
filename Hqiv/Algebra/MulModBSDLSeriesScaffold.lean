import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convergence

import Hqiv.Algebra.MulModBSDCoefficientScaffold

/-!
# Mul-mod BSD coefficients as a Mathlib `LSeries` (analytic hook)

`MulModBSDCoefficientScaffold` freezes the structured mul-mod local residue stream
`mulModBSDLocalCoeff`.  This module proves the same Mathlib analytic consequences as
`Hqiv.Physics.HQIVLSeriesAnalytic` for the HQIV Dirichlet scaffold:

* absolute convergence on `Re s > 1`;
* holomorphy / `AnalyticOnNhd` on that half-plane;
* derivative identity from `LSeries_hasDerivAt`.

**Not here:** modularity, weight-`2` functional equation, or identification with
`L(E,s)` — see `MulModBSDCompletedLFunctionalScaffold` for the named BSD-shaped targets.
-/

namespace Hqiv.Algebra

open Complex Filter
open scoped Topology
open LSeries

noncomputable section

/-- Dirichlet series attached to the mul-mod BSD local coefficient stream. -/
noncomputable def mulModBSDLSeries : ℂ → ℂ :=
  LSeries mulModBSDLocalCoeff

theorem abscissaOfAbsConv_mulModBSDLocalCoeff_lt_re {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv mulModBSDLocalCoeff < s.re :=
  lt_of_le_of_lt abscissaOfAbsConv_mulModBSDLocalCoeff_le_one
    (EReal.coe_lt_coe_iff.mpr hs)

theorem mulModBSDLSeries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable mulModBSDLocalCoeff s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (abscissaOfAbsConv_mulModBSDLocalCoeff_lt_re (s := s) hs)

theorem differentiableOn_mulModBSDLSeries :
    DifferentiableOn ℂ mulModBSDLSeries {s : ℂ | 1 < s.re} := by
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | abscissaOfAbsConv mulModBSDLocalCoeff < s.re} := by
    intro z hz
    exact abscissaOfAbsConv_mulModBSDLocalCoeff_lt_re (s := z) hz
  exact DifferentiableOn.mono (LSeries_differentiableOn mulModBSDLocalCoeff) hsub

theorem analyticOnNhd_mulModBSDLSeries :
    AnalyticOnNhd ℂ mulModBSDLSeries {s : ℂ | 1 < s.re} := by
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | abscissaOfAbsConv mulModBSDLocalCoeff < s.re} := by
    intro z hz
    exact abscissaOfAbsConv_mulModBSDLocalCoeff_lt_re (s := z) hz
  exact AnalyticOnNhd.mono (LSeries_analyticOnNhd mulModBSDLocalCoeff) hsub

theorem mulModBSDLSeries_hasDerivAt {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt mulModBSDLSeries
      (-LSeries (LSeries.logMul mulModBSDLocalCoeff) s) s := by
  exact LSeries_hasDerivAt
    (f := mulModBSDLocalCoeff)
    (abscissaOfAbsConv_mulModBSDLocalCoeff_lt_re (s := s) hs)

/--
Analytic fit bundle: coefficient stream + half-plane holomorphy for the mul-mod BSD channel.
-/
structure MulModBSDLSeriesAnalyticFit where
  coeff : ℕ → ℂ
  coeff_zero : coeff 0 = 0
  coeff_eq_local : ∀ n : ℕ, coeff (n + 1) = mulModBSDLocalCoeff (n + 1)
  abscissa_le_one : abscissaOfAbsConv coeff ≤ (1 : ℝ)
  differentiable_on : DifferentiableOn ℂ (LSeries coeff) {s : ℂ | 1 < s.re}

/-- The mul-mod BSD channel satisfies the analytic `LSeries` fit gate. -/
noncomputable def mulModBSDLSeriesAnalyticFit : MulModBSDLSeriesAnalyticFit where
  coeff := mulModBSDLocalCoeff
  coeff_zero := mulModBSDLocalCoeff_zero
  coeff_eq_local := fun _ => rfl
  abscissa_le_one := abscissaOfAbsConv_mulModBSDLocalCoeff_le_one
  differentiable_on := differentiableOn_mulModBSDLSeries

end

end Hqiv.Algebra
