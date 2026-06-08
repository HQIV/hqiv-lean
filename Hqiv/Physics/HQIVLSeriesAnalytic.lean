import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Hqiv.Physics.HQIVDirichletModularScaffold

/-!
# HQIV Dirichlet series as a complex-analytic L-series (Mathlib `LSeries`)

The informal HQIV sum `hqivDirichletSeries` uses 0-based shell indices with denominators `(n+1)^s`.
Mathlib's `LSeries` uses the standard convention `f n / n^s` with a zero at `n = 0`.

This file introduces `hqivLSeriesCoeff` (a `ℕ → ℂ` coefficient sequence) and proves:

* agreement `hqivDirichletSeries = LSeries hqivLSeriesCoeff` on `Re s > 1`;
* `abscissaOfAbsConv hqivLSeriesCoeff ≤ 1` from `|a_n| ≤ 1`;
* **holomorphy** on `{s : ℂ | 1 < s.re}` by restriction from Mathlib's `LSeries_differentiableOn` /
  `LSeries_analyticOnNhd`;
* the **derivative** identity from `LSeries_hasDerivAt` on that half-plane;
* when **`hqivCoeff ≡ 1`**, identification **`hqivDirichletSeries s = riemannZeta s`** for `1 < re s`
  (`hqivDirichletSeries_eq_riemannZeta_of_hqivCoeff_one`): the same object as Mathlib's **L-series of the
  constant-`1` coefficients** / arithmetic function `ζ` (`LSeries_one_eq_riemannZeta`, `LSeries_zeta_eq_riemannZeta`);
* the same hypothesis identifies **`hqivDirichletSeries` with `DirichletCharacter.LFunction`** for the unique
  character modulo `1` (`hqivDirichletSeries_eq_LFunction_modOne_of_hqivCoeff_one`), i.e. Mathlib’s analytic
  continuation of the trivial Dirichlet series from `DirichletContinuation`;
* the same hypothesis rewrites the HQIV sum as **`completedRiemannZeta s / Gammaℝ s`** (`riemannZeta_def_of_ne_zero`)
  and as **`completedLFunction χ s / gammaFactor χ s`** / **`… / Gammaℝ s`** for `χ : DirichletCharacter ℂ 1`
  (`hqivDirichletSeries_eq_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_one`,
  `hqivDirichletSeries_eq_completedLFunction_div_gammaFactor_of_hqivCoeff_one`,
  `hqivDirichletSeries_eq_completedLFunction_div_Gammaℝ_of_hqivCoeff_one`) — **completed Λ** and
  `Hqiv.Algebra.ThetaCompletedLFunctionalScaffold`;
* **multiplicative** form `completedLFunction χ s = hqivDirichletSeries s · gammaFactor χ s` on `Re s > 1`
  (`completedLFunction_eq_hqivDirichletSeries_mul_gammaFactor_of_hqivCoeff_one`), and constant coefficients
  **`c₀ · (Λ / Γℝ)`** (`hqivDirichletSeries_eq_const_smul_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_const`);
* **functional equation** for the **`LFunction · gammaFactor`** product at modulus `1`
  (`LFunction_mul_gammaFactor_modOne_one_sub`) — same symmetry as `completedRiemannZeta_one_sub`;
* when **`hqivCoeff` is constant** `c : ℝ`, **`hqivDirichletSeries s = (c : ℂ) * riemannZeta s`** on the same
  half-plane (`hqivDirichletSeries_eq_const_smul_riemannZeta_of_hqivCoeff_const`) via `LSeries_smul`.

This reuses Mathlib complex analysis — no new axioms.
-/

namespace Hqiv.Physics

open Complex Filter
open scoped Topology
open LSeries
open DirichletCharacter
open Hqiv.Geometry

noncomputable section

/-- Coefficients aligned with Mathlib `LSeries`: index `0` is unused; shell `n` in the HQIV sum is
index `n + 1` here. -/
noncomputable def hqivLSeriesCoeff (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ) :
    ℕ → ℂ
  | 0 => 0
  | n + 1 => (hqivCoeff φ t ω domains c k n : ℂ)

@[simp]
theorem hqivLSeriesCoeff_zero (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ) :
    hqivLSeriesCoeff φ t ω domains c k 0 = 0 :=
  rfl

theorem norm_hqivLSeriesCoeff_le_one (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ)
    {n : ℕ} (hn : n ≠ 0) : ‖hqivLSeriesCoeff φ t ω domains c k n‖ ≤ 1 := by
  rcases n with _ | m
  · exact False.elim (hn rfl)
  · simpa [hqivLSeriesCoeff, Complex.norm_real, Real.norm_eq_abs] using
      abs_hqivCoeff_le_one φ t ω domains c k m

theorem abscissaOfAbsConv_hqivLSeriesCoeff_le_one (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) :
    abscissaOfAbsConv (hqivLSeriesCoeff φ t ω domains c k) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨1, fun _ hn => norm_hqivLSeriesCoeff_le_one (φ := φ) (t := t) (ω := ω) (domains := domains)
      (c := c) (k := k) hn⟩

theorem abscissaOfAbsConv_hqivLSeriesCoeff_lt_re (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv (hqivLSeriesCoeff φ t ω domains c k) < s.re :=
  lt_of_le_of_lt (abscissaOfAbsConv_hqivLSeriesCoeff_le_one φ t ω domains c k)
    (EReal.coe_lt_coe_iff.mpr hs)

theorem hqivDirichletTerm_eq_LSeries_term_succ (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) (s : ℂ) (n : ℕ) :
    hqivDirichletTerm φ t ω domains c k s n =
      LSeries.term (hqivLSeriesCoeff φ t ω domains c k) s (n + 1) := by
  let f := hqivLSeriesCoeff φ t ω domains c k
  have hf0 : f 0 = 0 := hqivLSeriesCoeff_zero φ t ω domains c k
  rw [LSeries.term_def₀ hf0]
  cases n <;> simp [f, hqivLSeriesCoeff, hqivDirichletTerm]

theorem hqivDirichletSeries_eq_LSeries (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ)
    (s : ℂ) (hs : 1 < s.re) :
    hqivDirichletSeries φ t ω domains c k s = LSeries (hqivLSeriesCoeff φ t ω domains c k) s := by
  let f := hqivLSeriesCoeff φ t ω domains c k
  have hσ : abscissaOfAbsConv f < s.re :=
    abscissaOfAbsConv_hqivLSeriesCoeff_lt_re (φ := φ) (t := t) (ω := ω) (domains := domains) (c := c)
      (k := k) (hs := hs)
  have hL : LSeriesSummable f s := LSeriesSummable_of_abscissaOfAbsConv_lt_re hσ
  dsimp [hqivDirichletSeries, LSeries]
  rw [hL.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  refine tsum_congr fun n => ?_
  dsimp [f]
  exact hqivDirichletTerm_eq_LSeries_term_succ φ t ω domains c k s n

theorem differentiableOn_hqivDirichletSeries (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) :
    DifferentiableOn ℂ (hqivDirichletSeries φ t ω domains c k) {s : ℂ | 1 < s.re} := by
  let f := hqivLSeriesCoeff φ t ω domains c k
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | abscissaOfAbsConv f < s.re} := by
    intro z hz
    dsimp [f] at *
    exact abscissaOfAbsConv_hqivLSeriesCoeff_lt_re (φ := φ) (t := t) (ω := ω) (domains := domains)
      (c := c) (k := k) (s := z) (hs := hz)
  refine DifferentiableOn.congr (DifferentiableOn.mono (LSeries_differentiableOn f) hsub) ?_
  intro z hz
  dsimp [f]
  exact hqivDirichletSeries_eq_LSeries φ t ω domains c k z hz

theorem analyticOnNhd_hqivDirichletSeries (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains)
    (c k : ℕ) :
    AnalyticOnNhd ℂ (hqivDirichletSeries φ t ω domains c k) {s : ℂ | 1 < s.re} := by
  let f := hqivLSeriesCoeff φ t ω domains c k
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | abscissaOfAbsConv f < s.re} := by
    intro z hz
    dsimp [f] at *
    exact abscissaOfAbsConv_hqivLSeriesCoeff_lt_re (φ := φ) (t := t) (ω := ω) (domains := domains)
      (c := c) (k := k) (s := z) (hs := hz)
  refine AnalyticOnNhd.congr hopen (AnalyticOnNhd.mono (LSeries_analyticOnNhd f) hsub) ?_
  intro z hz
  dsimp [f]
  exact Eq.symm (hqivDirichletSeries_eq_LSeries φ t ω domains c k z hz)

theorem hqivDirichletSeries_hasDerivAt (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (hqivDirichletSeries φ t ω domains c k)
      (-LSeries (LSeries.logMul (hqivLSeriesCoeff φ t ω domains c k)) s) s := by
  let f := hqivLSeriesCoeff φ t ω domains c k
  have hσ : abscissaOfAbsConv f < s.re :=
    abscissaOfAbsConv_hqivLSeriesCoeff_lt_re (φ := φ) (t := t) (ω := ω) (domains := domains) (c := c)
      (k := k) (hs := hs)
  have hev : hqivDirichletSeries φ t ω domains c k =ᶠ[𝓝 s] LSeries f := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    dsimp [f]
    exact hqivDirichletSeries_eq_LSeries φ t ω domains c k z hz
  dsimp [f] at hσ ⊢
  exact (LSeries_hasDerivAt (f := hqivLSeriesCoeff φ t ω domains c k) hσ).congr_of_eventuallyEq hev

/-- Coefficients agree with the constant sequence `1` away from `0`, so they define the same
`LSeries` as `riemannZeta` when every `hqivCoeff` is `1`. -/
theorem hqivLSeriesCoeff_eq_one_on_ne_zero_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    ∀ {n : ℕ}, n ≠ 0 → hqivLSeriesCoeff φ t ω domains c k n = (1 : ℕ → ℂ) n := by
  intro n hn
  rcases n with _ | m
  · exact False.elim (hn rfl)
  · simp [hqivLSeriesCoeff, h m]

/-- When every shell coefficient is `1`, the HQIV Dirichlet series is **exactly** the Riemann zeta
function on `re s > 1` — i.e. the standard `LSeries` of the trivial coefficients (`L 1` / `L ↗ζ` in
Mathlib). -/
theorem hqivDirichletSeries_eq_riemannZeta_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re)
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = riemannZeta s := by
  rw [hqivDirichletSeries_eq_LSeries φ t ω domains c k s hs]
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → hqivLSeriesCoeff φ t ω domains c k n = (1 : ℕ → ℂ) n :=
    hqivLSeriesCoeff_eq_one_on_ne_zero_of_hqivCoeff_one φ t ω domains c k h
  rw [LSeries_congr hcongr s]
  exact LSeries_one_eq_riemannZeta hs

/-- On `Re s > 1`, constant coefficients `hqivCoeff ≡ 1` identify the HQIV Dirichlet sum with
Mathlib’s **Dirichlet L-function** for modulus `1` — the same meromorphic object as `riemannZeta`
(`LFunction_modOne_eq`). Links to `completedLFunction` / Λ symmetry via
`Hqiv.Algebra.ThetaCompletedLFunctionalScaffold`. -/
theorem hqivDirichletSeries_eq_LFunction_modOne_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = LFunction χ s := by
  rw [hqivDirichletSeries_eq_riemannZeta_of_hqivCoeff_one φ t ω domains c k s hs h]
  exact (congr_fun LFunction_modOne_eq s).symm

/-- Same hypotheses: agreement with the **naive** `LSeries` of the trivial character (Dirichlet series
convergence range). -/
theorem hqivDirichletSeries_eq_LSeries_trivialCharacter_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = LSeries (χ ·) s := by
  rw [hqivDirichletSeries_eq_LFunction_modOne_of_hqivCoeff_one φ t ω domains c k χ s hs h]
  exact LFunction_eq_LSeries χ hs

lemma even_dirichletCharacter_modOne (χ : DirichletCharacter ℂ 1) : χ.Even := by
  rw [DirichletCharacter.Even]
  rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _]
  simp [MulChar.map_one]

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  intro hs0
  rw [hs0] at hs
  norm_num at hs

/-- Completed Riemann Λ(s) = `Gammaℝ s · ζ(s)` (Mathlib), so **`hqivDirichletSeries = Λ / Gammaℝ`** when
coefficients are `1`. -/
theorem hqivDirichletSeries_eq_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re)
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = completedRiemannZeta s / Gammaℝ s := by
  rw [hqivDirichletSeries_eq_riemannZeta_of_hqivCoeff_one φ t ω domains c k s hs h]
  exact riemannZeta_def_of_ne_zero (ne_zero_of_one_lt_re hs)

/-- Dirichlet **completed L** = `L · gammaFactor`; specialization of the trivial branch. -/
theorem hqivDirichletSeries_eq_completedLFunction_div_gammaFactor_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = completedLFunction χ s / gammaFactor χ s := by
  rw [hqivDirichletSeries_eq_LFunction_modOne_of_hqivCoeff_one φ t ω domains c k χ s hs h]
  exact LFunction_eq_completed_div_gammaFactor χ s (Or.inl (ne_zero_of_one_lt_re hs))

/-- Modulus-`1` characters are **even**, so `gammaFactor χ = Gammaℝ`. -/
theorem hqivDirichletSeries_eq_completedLFunction_div_Gammaℝ_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = completedLFunction χ s / Gammaℝ s := by
  rw [hqivDirichletSeries_eq_completedLFunction_div_gammaFactor_of_hqivCoeff_one φ t ω domains c k χ s hs h,
    Even.gammaFactor_def (even_dirichletCharacter_modOne χ) s]

lemma Gammaℝ_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : Gammaℝ s ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)

/-- On `Re s > 1`, **`completedLFunction χ s = hqivDirichletSeries s · gammaFactor χ s`** when `hqivCoeff ≡ 1`
(`gammaFactor` invertible at `s`). -/
theorem completedLFunction_eq_hqivDirichletSeries_mul_gammaFactor_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) (hγ : gammaFactor χ s ≠ 0) :
    completedLFunction χ s = hqivDirichletSeries φ t ω domains c k s * gammaFactor χ s := by
  have hdiv :=
    hqivDirichletSeries_eq_completedLFunction_div_gammaFactor_of_hqivCoeff_one φ t ω domains c k χ s hs h
  exact (div_eq_iff hγ).mp hdiv.symm

/-- Same with `Gammaℝ` (even character mod `1`). -/
theorem completedLFunction_eq_hqivDirichletSeries_mul_Gammaℝ_of_hqivCoeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hs : 1 < s.re) (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    completedLFunction χ s = hqivDirichletSeries φ t ω domains c k s * Gammaℝ s := by
  have hΓ := Gammaℝ_ne_zero_of_one_lt_re hs
  have hdiv :=
    hqivDirichletSeries_eq_completedLFunction_div_Gammaℝ_of_hqivCoeff_one φ t ω domains c k χ s hs h
  exact (div_eq_iff hΓ).mp hdiv.symm

/-- Algebraic unpack: **`completedLFunction = LFunction · gammaFactor`** when the gamma factor is nonzero. -/
theorem completedLFunction_eq_LFunction_mul_gammaFactor_of_gamma_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (h : s ≠ 0 ∨ N ≠ 1) (hγ : gammaFactor χ s ≠ 0) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hL := LFunction_eq_completed_div_gammaFactor χ s h
  field_simp [hγ] at hL ⊢
  exact hL.symm

/-- Modulus `1`: Λ symmetry as equality of **`LFunction · gammaFactor`** (global meromorphic identity). -/
theorem LFunction_mul_gammaFactor_modOne_one_sub (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hγs : gammaFactor χ s ≠ 0) (hγ1s : gammaFactor χ (1 - s) ≠ 0) :
    LFunction χ (1 - s) * gammaFactor χ (1 - s) = LFunction χ s * gammaFactor χ s := by
  calc
    LFunction χ (1 - s) * gammaFactor χ (1 - s) = completedLFunction χ (1 - s) :=
      (completedLFunction_eq_LFunction_mul_gammaFactor_of_gamma_ne_zero χ (1 - s)
        (Or.inl (sub_ne_zero.mpr hs1.symm)) hγ1s).symm
    _ = completedRiemannZeta (1 - s) := congr_fun completedLFunction_modOne_eq (1 - s)
    _ = completedRiemannZeta s := completedRiemannZeta_one_sub s
    _ = completedLFunction χ s := (congr_fun completedLFunction_modOne_eq s).symm
    _ = LFunction χ s * gammaFactor χ s :=
      completedLFunction_eq_LFunction_mul_gammaFactor_of_gamma_ne_zero χ s (Or.inl hs0) hγs

/-- Coefficients `0` at index `0` and `1` on `ℕ+`; same `LSeries` as the constant-`1` sequence. -/
noncomputable def hqivZetaSliceLSeriesCoeff : ℕ → ℂ :=
  fun n => if n = 0 then 0 else 1

theorem LSeries_hqivZetaSlice_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries hqivZetaSliceLSeriesCoeff s = riemannZeta s := by
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → hqivZetaSliceLSeriesCoeff n = (1 : ℕ → ℂ) n := by
    intro n hn
    simp [hqivZetaSliceLSeriesCoeff, hn]
  rw [LSeries_congr hcongr s]
  exact LSeries_one_eq_riemannZeta hs

theorem hqivLSeriesCoeff_eq_smul_zetaSlice_of_hqivCoeff_const (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) {c₀ : ℝ} (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = c₀) :
    hqivLSeriesCoeff φ t ω domains c k = (c₀ : ℂ) • hqivZetaSliceLSeriesCoeff := by
  funext n
  rcases n with _ | m
  · simp [hqivLSeriesCoeff, hqivZetaSliceLSeriesCoeff]
  · simp [hqivLSeriesCoeff, hqivZetaSliceLSeriesCoeff, h m, Pi.smul_apply]

theorem hqivDirichletSeries_eq_const_smul_riemannZeta_of_hqivCoeff_const (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re) {c₀ : ℝ}
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = c₀) :
    hqivDirichletSeries φ t ω domains c k s = (c₀ : ℂ) * riemannZeta s := by
  rw [hqivDirichletSeries_eq_LSeries φ t ω domains c k s hs,
    hqivLSeriesCoeff_eq_smul_zetaSlice_of_hqivCoeff_const φ t ω domains c k h, LSeries_smul,
    LSeries_hqivZetaSlice_eq_riemannZeta hs]

theorem hqivDirichletSeries_eq_const_smul_completedRiemannZeta_div_Gammaℝ_of_hqivCoeff_const
    (φ t : ℝ) (ω : ℕ → ℝ) (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re) {c₀ : ℝ}
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = c₀) :
    hqivDirichletSeries φ t ω domains c k s =
      (c₀ : ℂ) * (completedRiemannZeta s / Gammaℝ s) := by
  rw [hqivDirichletSeries_eq_const_smul_riemannZeta_of_hqivCoeff_const φ t ω domains c k s hs h]
  congr 1
  exact riemannZeta_def_of_ne_zero (ne_zero_of_one_lt_re hs)

end

end Hqiv.Physics
