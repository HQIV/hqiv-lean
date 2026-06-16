import Hqiv.Story.S3GoldbachPartitionGeneratingFunction
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Perron / contour route: Goldbach generating function → Euler–Maclaurin remainder

Lean outline for proving `ContourGrowthControlsEulerRemainder` from holomorphy and
vertical-line growth of the **pair Dirichlet** generating function.

## Which discrete quantity does Perron recover?

The pipeline has three distinct real readouts — do not conflate them:

| Readout | Role in pipeline |
|---------|------------------|
| `goldbachMidpointGeometricAggregate N` | **Local** geometric-mean weight at midpoint `N` (`midpointGeometricMeanAt N` in the generating chart). |
| `goldbachPerronDiscreteTarget M` | **Cumulative** `∑_{N≤M}` local aggregates — default **Perron discrete target** (unsmoothed). Equals `F_M(0)` in real part when `(2N)^{−0} = 1`. |
| `totalArcHarmonicWeight N` / `rollingHarmonicWeightUpTo N` | Harmonic rolling weight on the **classical** side of `Δ_N`; fed by Goldbach data only after a separate bridge lemma. |
| `weightDifferenceEulerMaclaurinRemainder N` | **Downstream** Euler–Maclaurin tail in `Δ_N = leadingTerm + remainder`; compared to contour tails in step 3, not step 1. |

**Step 1 (this file):** truncated Perron for `goldbachPerronDiscreteTarget M` via
`F_M(s) = goldbachMidpointGeometricGeneratingSumTruncated M s`.

**Step 2:** vertical growth of `F_M` on `σ + it` (proved in
`S3GoldbachPartitionGeneratingFunction`).

**Step 3:** Euler–Maclaurin contour identity comparing harmonic-weight integrals to
the Perron integral + boundary terms, yielding a bound on
`weightDifferenceEulerMaclaurinRemainder N`.

## Finite vs. limiting object

* **Finite `F_M`:** holomorphy on `{Re s > 0}` is proved for each truncation `M`.
* **Limit / regularization:** analytic strength usually comes from `M → ∞` with
  summability on `{Re s > 1}` (named, not proved here).
-/

namespace Hqiv.Story

noncomputable section

open Real Complex Set Filter MeasureTheory Topology
open scoped Interval

/-! ## Limiting-object target (named, not proved) -/

/--
Truncated pair Dirichlet sum `F_M` at complex argument `s`.
-/
noncomputable abbrev goldbachPairDirichletGeneratingTruncated (M : ℕ) (s : ℂ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M s

/--
**Target:** on a right half-plane, truncated sums converge as `M → ∞`.
-/
def GoldbachPairDirichletSummableOnHalfPlane (σ : ℝ) : Prop :=
  ∀ s, σ < s.re →
    ∃ L : ℂ, Tendsto (fun M => goldbachPairDirichletGeneratingTruncated M s) atTop (nhds L)

/--
**Target:** a regularized or limit generating function with global half-plane
holomorphy and vertical-line growth feeding contour integration.
-/
structure GoldbachPairDirichletLimitingObject where
  F_limit : ℂ → ℂ
  domain : Set ℂ
  domain_isOpen : IsOpen domain
  truncates_to_limit :
    ∀ σ, GoldbachPairDirichletSummableOnHalfPlane σ →
      ∀ s, σ < s.re →
        Tendsto (fun M => goldbachPairDirichletGeneratingTruncated M s) atTop (nhds (F_limit s))

/-! ## Vertical-line growth (contour input) -/

structure VerticalLineGrowthBound (σ : ℝ) where
  F : ℂ → ℂ
  bound : ℝ → ℝ
  bound_nonneg : ∀ T, 0 ≤ bound T
  vertical_le :
    ∀ (T : ℝ) (t : ℝ), |t| ≤ T →
      ‖F (σ + t * I)‖ ≤ bound T

structure HolomorphicVerticalGrowth (σ : ℝ) where
  generating : GoldbachPartitionGeneratingFunction
  holomorphic : IsHolomorphicGoldbachPartition generating
  growth : VerticalLineGrowthBound σ
  growth_matches :
    growth.F = generating.F

noncomputable def verticalLineGrowthBound_pairDirichlet_truncated (M : ℕ) (σ : ℝ) :
    VerticalLineGrowthBound σ where
  F := goldbachMidpointGeometricGeneratingSumTruncated M
  bound := fun _ =>
    goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ
  bound_nonneg := fun _ =>
    goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ
  vertical_le := fun _ t _ =>
    goldbach_midpoint_geometric_generating_sum_vertical_bound M σ t

noncomputable def holomorphicVerticalGrowth_pairDirichlet_truncated (M : ℕ) (σ : ℝ) :
    HolomorphicVerticalGrowth σ where
  generating := goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  holomorphic := goldbach_pair_dirichlet_generating_holomorphic M
  growth := verticalLineGrowthBound_pairDirichlet_truncated M σ
  growth_matches := rfl

noncomputable def holomorphicVerticalGrowth_default_truncation (N : ℕ) (σ : ℝ) :
    HolomorphicVerticalGrowth σ where
  generating := goldbachPartitionGeneratingFunctionDefault N
  holomorphic := goldbach_pair_dirichlet_generating_holomorphic N
  growth := verticalLineGrowthBound_pairDirichlet_truncated N σ
  growth_matches := rfl

/-! ## Perron kernel and truncated vertical integral -/

/--
Standard Perron / inverse-Mellin kernel `x^s / s` at scale `x > 0`.
-/
noncomputable def goldbachPerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / s

theorem goldbach_perron_kernel_unit_scale (s : ℂ) (hs : s ≠ 0) :
    goldbachPerronKernel 1 s = 1 / s := by
  dsimp [goldbachPerronKernel]
  simp [hs]

/--
Default even-target scale `2M` for truncated Perron at index `M` (midpoint `N` ↔ even `2N`).
-/
noncomputable def goldbachPerronDefaultScale (M : ℕ) : ℝ :=
  (2 * M : ℝ)

theorem goldbach_perron_default_scale_pos {M : ℕ} (hM : 0 < M) :
    0 < goldbachPerronDefaultScale M := by
  dsimp [goldbachPerronDefaultScale]
  positivity

theorem goldbach_perron_kernel_norm_le_vertical (x : ℝ) (σ t : ℝ) (hσ : 0 < σ) (hx : 0 < x) :
    ‖goldbachPerronKernel x (σ + t * I)‖ ≤ x ^ σ / σ := by
  dsimp [goldbachPerronKernel]
  set s : ℂ := σ + t * I
  have hsne : s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [s] at this
    linarith [hσ]
  have hnorm_pow : ‖(x : ℂ) ^ s‖ = x ^ s.re := by
    rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have hsre : s.re = σ := by simp [s]
  have hnorm_eq : ‖s‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    dsimp [s]
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  have hnorm : ‖s‖ ≥ σ := by
    rw [hnorm_eq]
    have hsq : σ ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith
    calc σ = Real.sqrt (σ ^ 2) := (Real.sqrt_sq (le_of_lt hσ)).symm
      _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Complex.norm_div, hnorm_pow, hsre]
  refine (div_le_div_iff₀ (by positivity) (by linarith [hσ])).mpr ?_
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)

theorem goldbach_perron_kernel_norm_le_on_tail (x : ℝ) (σ T t : ℝ) (hσ : 0 < σ) (hx : 0 < x)
    (hTle : T ≤ |t|) (hT : 1 ≤ T) :
    ‖goldbachPerronKernel x (σ + t * I)‖ ≤ x ^ σ / |t| := by
  dsimp [goldbachPerronKernel]
  set s : ℂ := σ + t * I
  have hsne : s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [s] at this
    linarith [hσ]
  have hnorm_pow : ‖(x : ℂ) ^ s‖ = x ^ s.re := by
    rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have hsre : s.re = σ := by simp [s]
  have hnorm : ‖s‖ = Real.sqrt (σ ^ 2 + t ^ 2) := by
    dsimp [s]
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
  have hsqrt : |t| ≤ ‖s‖ := by
    rw [hnorm]
    have : t ^ 2 ≤ σ ^ 2 + t ^ 2 := by nlinarith
    calc |t| = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) := Real.sqrt_le_sqrt this
  have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one (le_trans hT hTle)
  rw [Complex.norm_div, hnorm_pow, hsre]
  refine (div_le_div_iff₀ (by positivity) ht_pos).mpr ?_
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

theorem goldbach_perron_kernel_norm_le_when_sigma_ge_T (x : ℝ) (σ T t : ℝ) (hσ : 0 < σ)
    (hx : 0 < x) (hT : 0 < T) (hσT : T ≤ σ) :
    ‖goldbachPerronKernel x (σ + t * I)‖ ≤ x ^ σ / T := by
  have hdiv : x ^ σ / σ ≤ x ^ σ / T := by
    rw [div_le_div_iff₀ hσ hT]
    exact mul_le_mul_of_nonneg_left hσT (le_of_lt (Real.rpow_pos_of_pos hx σ))
  exact (goldbach_perron_kernel_norm_le_vertical x σ t hσ hx).trans hdiv

/--
Integrand for the truncated vertical Perron integral:

`F_M(σ + it) · x^s / s` on the line `Re s = σ`.
-/
noncomputable def goldbachTruncatedPerronVerticalIntegrand (M : ℕ) (σ x t : ℝ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I) *
    goldbachPerronKernel x (σ + t * I)

/--
Truncated vertical Perron integral (real part, finite height `T`):

`(1 / 2π) ∫_{-T}^{T} F_M(σ + it) · (x^{σ+it} / (σ + it)) dt`.
-/
noncomputable def goldbachTruncatedPerronVerticalIntegral (M : ℕ) (σ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in (-T)..T, (goldbachTruncatedPerronVerticalIntegrand M σ x t).re)

/--
Tail region `{t : |t| ≥ T}` on the vertical line `Re s = σ`.
-/
noncomputable def goldbachPerronTailGeometricSet (T : ℝ) : Set ℝ :=
  {t | T ≤ |t|}

/--
Bounded two-sided tail proxy used for contour bookkeeping at height `T`:

`[T, 2T] ∪ [-2T, -T]`.  Contributes Lebesgue measure `2T` and matches the usual
pair of tail rays in a rectangle of height `2T`.
-/
noncomputable def goldbachPerronBoundedTailSet (T : ℝ) : Set ℝ :=
  Set.Icc T (2 * T) ∪ Set.Icc (-2 * T) (-T)

theorem mem_goldbachPerronBoundedTailSet_of_ge (T t : ℝ) (hT : 0 < T) (ht : T ≤ |t|)
    (ht' : |t| ≤ 2 * T) : t ∈ goldbachPerronBoundedTailSet T := by
  dsimp [goldbachPerronBoundedTailSet]
  rcases lt_trichotomy 0 t with htpos | ht0 | htneg
  · rw [Set.mem_union, Set.mem_Icc, Set.mem_Icc]
    left
    have htabs : |t| = t := abs_of_pos htpos
    rw [htabs] at ht ht'
    exact ⟨ht, ht'⟩
  · rw [abs_eq_zero.mpr (eq_comm.mp ht0)] at ht
    linarith [hT, ht]
  · rw [Set.mem_union, Set.mem_Icc, Set.mem_Icc]
    right
    have htabs : |t| = -t := abs_of_neg htneg
    rw [htabs] at ht ht'
    exact ⟨by linarith, by linarith⟩

/--
Normalized tail integral on the bounded proxy (same `1 / (2π)` factor as the central
vertical integral):

`(1/2π) · (∫_{T}^{2T} + ∫_{-2T}^{-T}) F_M(σ+it) · x^s/s dt`.
-/
noncomputable def goldbachTruncatedPerronVerticalTailIntegral (M : ℕ) (σ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ((∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) +
      ∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re)

/--
Truncation error from replacing the full vertical line with `[-T, T]` and
any right-edge / residue bookkeeping (named analytic input).
-/
noncomputable def goldbachTruncatedPerronContourError (M : ℕ) (σ T x : ℝ) : ℝ :=
  goldbachPerronDiscreteTarget M -
    goldbachTruncatedPerronVerticalIntegral M σ T x

/-! ## Midpoint-index smoothing (Gaussian / Fejér) -/

/--
Smoothing family on the midpoint index `N` (not on primes `p`).

`scale` is tied to vertical height `T` in default templates (`scale = T`).
-/
inductive GoldbachMidpointSmootherKind
  | gaussian
  | fejer

structure GoldbachMidpointSmoother where
  kind : GoldbachMidpointSmootherKind
  scale : ℝ
  scale_pos : 0 < scale

/--
Gaussian smoother on `N` centred at `center`:

`exp(−(N − center)² / (2 scale²))`.
-/
noncomputable def goldbachMidpointGaussianKernel (scale : ℝ) (center N : ℕ) : ℝ :=
  Real.exp (-((N : ℝ) - center) ^ 2 / (2 * scale ^ 2))

/--
Fejér smoother on `N` centred at `center`:

`max(0, 1 − |N − center| / scale)`.
-/
noncomputable def goldbachMidpointFejerKernel (scale : ℝ) (center N : ℕ) : ℝ :=
  max 0 (1 - |((N : ℝ) - center)| / scale)

noncomputable def GoldbachMidpointSmoother.kernel (S : GoldbachMidpointSmoother) (center N : ℕ) : ℝ :=
  match S.kind with
  | GoldbachMidpointSmootherKind.gaussian => goldbachMidpointGaussianKernel S.scale center N
  | GoldbachMidpointSmootherKind.fejer => goldbachMidpointFejerKernel S.scale center N

theorem goldbach_midpoint_gaussian_kernel_nonneg (scale : ℝ) (center N : ℕ) :
    0 ≤ goldbachMidpointGaussianKernel scale center N :=
  Real.exp_nonneg _

theorem goldbach_midpoint_fejer_kernel_nonneg (scale : ℝ) (center N : ℕ) :
    0 ≤ goldbachMidpointFejerKernel scale center N := by
  dsimp [goldbachMidpointFejerKernel]
  positivity

theorem goldbach_midpoint_smoother_kernel_nonneg (S : GoldbachMidpointSmoother) (center N : ℕ) :
    0 ≤ S.kernel center N := by
  obtain ⟨kind, scale, hscale⟩ := S
  cases kind with
  | gaussian => exact goldbach_midpoint_gaussian_kernel_nonneg scale center N
  | fejer => exact goldbach_midpoint_fejer_kernel_nonneg scale center N

/--
Default Gaussian smoother at vertical height `T` (`scale = T`).
-/
noncomputable def goldbachMidpointGaussianSmoother (T : ℝ) (hT : 0 < T) : GoldbachMidpointSmoother where
  kind := GoldbachMidpointSmootherKind.gaussian
  scale := T
  scale_pos := hT

/--
Default Fejér smoother at vertical height `T` (`scale = T`).
-/
noncomputable def goldbachMidpointFejerSmoother (T : ℝ) (hT : 0 < T) : GoldbachMidpointSmoother where
  kind := GoldbachMidpointSmootherKind.fejer
  scale := T
  scale_pos := hT

/--
Smoothed Perron discrete target:

`∑_{1≤N≤M} K(N; centre=M) · goldbachMidpointGeometricAggregate N`.
-/
noncomputable def goldbachSmoothedPerronDiscreteTarget (M : ℕ) (S : GoldbachMidpointSmoother) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, S.kernel M N * goldbachMidpointGeometricAggregate N

theorem goldbach_smoothed_perron_discrete_target_nonneg (M : ℕ) (S : GoldbachMidpointSmoother) :
    0 ≤ goldbachSmoothedPerronDiscreteTarget M S := by
  dsimp [goldbachSmoothedPerronDiscreteTarget]
  refine Finset.sum_nonneg fun N _ =>
    mul_nonneg (goldbach_midpoint_smoother_kernel_nonneg S M N)
      (goldbach_midpoint_geometric_aggregate_nonneg N)

noncomputable abbrev goldbachGaussianSmoothedPerronDiscreteTarget (M : ℕ) (T : ℝ) (hT : 0 < T) : ℝ :=
  goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T hT)

noncomputable abbrev goldbachFejerSmoothedPerronDiscreteTarget (M : ℕ) (T : ℝ) (hT : 0 < T) : ℝ :=
  goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointFejerSmoother T hT)

private lemma goldbach_gaussian_height_pos_of_one_le (T : ℕ) (hT : 1 ≤ T) : 0 < (T : ℝ) :=
  Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hT)

/--
Aggregate coupling sum: Fejér-smoothed target minus pure kernel mass.

`∑_{1≤N≤M} K_T^{Fejér}(N;M) · (a_N − 1)`.
-/
noncomputable def goldbachFejerSmoothedAggregateCouplingSum (M : ℕ) (T : ℝ) (_hT : 0 < T) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, goldbachMidpointFejerKernel T M N *
    (goldbachMidpointGeometricAggregate N - 1)

noncomputable def goldbachFejerSmoothedAggregateCouplingError (M : ℕ) (T : ℝ) (hT : 0 < T) : ℝ :=
  |goldbachFejerSmoothedAggregateCouplingSum M T hT|

noncomputable def goldbachFejerSmoothedAggregateCouplingErrorNat (M T : ℕ) (hT : 1 ≤ T) : ℝ :=
  goldbachFejerSmoothedAggregateCouplingError M (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)

theorem goldbach_fejer_smoothed_aggregate_coupling_error_nonneg (M : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ goldbachFejerSmoothedAggregateCouplingError M T hT :=
  abs_nonneg _

theorem goldbach_fejer_smoothed_aggregate_coupling_error_nat_nonneg (M T : ℕ) (hT : 1 ≤ T) :
    0 ≤ goldbachFejerSmoothedAggregateCouplingErrorNat M T hT := by
  dsimp [goldbachFejerSmoothedAggregateCouplingErrorNat]
  exact goldbach_fejer_smoothed_aggregate_coupling_error_nonneg M (T : ℝ) _

/--
Aggregate coupling sum: Gaussian-smoothed target minus pure kernel mass.

`∑_{1≤N≤M} K_T(N;M) · (a_N − 1)` with `a_N = goldbachMidpointGeometricAggregate N`.
-/
noncomputable def goldbachGaussianSmoothedAggregateCouplingSum (M : ℕ) (T : ℝ) (_hT : 0 < T) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, goldbachMidpointGaussianKernel T M N *
    (goldbachMidpointGeometricAggregate N - 1)

noncomputable def goldbachGaussianSmoothedAggregateCouplingError (M : ℕ) (T : ℝ) (hT : 0 < T) : ℝ :=
  |goldbachGaussianSmoothedAggregateCouplingSum M T hT|

noncomputable def goldbachGaussianSmoothedAggregateCouplingErrorNat (M T : ℕ) (hT : 1 ≤ T) : ℝ :=
  goldbachGaussianSmoothedAggregateCouplingError M (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)

theorem goldbach_gaussian_smoothed_aggregate_coupling_error_nonneg (M : ℕ) (T : ℝ) (hT : 0 < T) :
    0 ≤ goldbachGaussianSmoothedAggregateCouplingError M T hT :=
  abs_nonneg _

theorem goldbach_gaussian_smoothed_aggregate_coupling_error_nat_nonneg (M T : ℕ) (hT : 1 ≤ T) :
    0 ≤ goldbachGaussianSmoothedAggregateCouplingErrorNat M T hT := by
  dsimp [goldbachGaussianSmoothedAggregateCouplingErrorNat]
  exact goldbach_gaussian_smoothed_aggregate_coupling_error_nonneg M (T : ℝ) _


/-! ## Explicit vertical-tail error template (from vertical growth) -/

/--
Explicit truncated vertical-tail bound exported from proved vertical growth:

`‖F_M(σ+it)‖ ≤ B_{M,σ}` ⇒ tail integrand `|F · x^s/s|` is `O(x^σ / (σ T))` on `|t| ≥ T`
when `σ > 0`.

This is the standard Perron tail rate used to close `|error| ≤ C / T^δ` with `δ = 1`.
-/
noncomputable def goldbachPerronVerticalTailErrorTemplate (M : ℕ) (σ T x : ℝ) : ℝ :=
  x ^ σ * goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ / (σ * max 1 T)

/--
`(B_{M,σ}+1)` tail template from the `‖F_M − 1‖ ≤ B_{M,σ}+1` bound (vs `B_{M,σ}` for `‖F_M‖`).
The proved A₂.1 bookkeeping bound equals `2 ·` this quantity.
-/
noncomputable def goldbachPerronFMPlusOneVerticalTailErrorTemplate (M : ℕ) (σ T x : ℝ) : ℝ :=
  x ^ σ * (goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ + 1) / (σ * max 1 T)

theorem goldbach_perron_fm_plus_one_tail_template_nonneg (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hx : 0 ≤ x) :
    0 ≤ goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ T x := by
  dsimp [goldbachPerronFMPlusOneVerticalTailErrorTemplate]
  refine div_nonneg ?_ ?_
  · exact mul_nonneg (Real.rpow_nonneg hx σ)
      (add_nonneg (goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ)
        zero_le_one)
  · refine mul_nonneg hσ.le ?_
    exact le_max_of_le_left zero_le_one

theorem goldbach_perron_vertical_tail_error_template_nonneg (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hx : 0 ≤ x) :
    0 ≤ goldbachPerronVerticalTailErrorTemplate M σ T x := by
  dsimp [goldbachPerronVerticalTailErrorTemplate]
  refine div_nonneg ?_ ?_
  · exact mul_nonneg (Real.rpow_nonneg hx σ)
      (goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ)
  · refine mul_nonneg hσ.le ?_
    exact le_max_of_le_left zero_le_one

/--
Decay witness: for `T ≥ 1`, template bound is exactly `C / T` with `C = x^σ B_{M,σ} / σ`.
-/
theorem goldbach_perron_vertical_tail_error_template_le_C_div_T (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 ≤ x) :
    goldbachPerronVerticalTailErrorTemplate M σ T x ≤
      (x ^ σ * goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ / σ) / T := by
  dsimp [goldbachPerronVerticalTailErrorTemplate]
  rw [max_eq_right hT]
  apply le_of_eq
  ring

/--
Packaging for `error_bound ≤ C / T^δ` tail decay.
-/
structure PerronVerticalTailDecay where
  δ : ℝ
  δ_pos : 0 < δ
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ℝ → ℝ
  bound_nonneg : ∀ T, 0 ≤ bound T
  bound_le : ∀ T, (1 : ℝ) ≤ T → bound T ≤ C / T ^ δ

/--
Template decay certificate at exponent `δ = 1` from vertical-growth constant `B_{M,σ}`.
-/
noncomputable def goldbachPerronVerticalTailDecay_template (M : ℕ) (σ x : ℝ) (hσ : 0 < σ)
    (hx : 0 ≤ x) : PerronVerticalTailDecay where
  δ := 1
  δ_pos := one_pos
  C := x ^ σ * goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ / σ
  C_nonneg :=
    div_nonneg
      (mul_nonneg (Real.rpow_nonneg hx σ)
        (goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ))
      hσ.le
  bound := fun T => goldbachPerronVerticalTailErrorTemplate M σ T x
  bound_nonneg := fun T =>
    goldbach_perron_vertical_tail_error_template_nonneg M σ T x hσ hx
  bound_le := fun T hT => by
    simpa only [rpow_one] using
      goldbach_perron_vertical_tail_error_template_le_C_div_T M σ T x hσ hT hx

/-! ## Truncated Perron formula (comparison target) -/

/--
Truncated Perron packaging for the **cumulative geometric-mean readout**
`goldbachPerronDiscreteTarget M`.

The vertical integral uses `F_M` from the pair-Dirichlet generating function at
truncation `M`, a vertical abscissa `σ`, Perron scale `x`, and height `T`.

**Not** the Euler–Maclaurin remainder: that comparison is
`euler_maclaurin_contour_holds` (step 3).
-/
structure TruncatedPerronFormula (M : ℕ) (σ : ℝ) where
  /-- Even-target / Mellin scale for the kernel `x^s / s`. -/
  scale : ℝ
  scale_pos : 0 < scale
  /-- Vertical truncation height `T` (`∫_{-T}^T … dt`). -/
  truncationHeight : ℝ
  truncationHeight_nonneg : 0 ≤ truncationHeight
  generating : GoldbachPartitionGeneratingFunction
  generating_eq_truncation :
    generating = goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  /-- Default: cumulative `∑_{N≤M}` geometric-mean aggregate (unsmoothed). -/
  discrete_target : ℝ := goldbachPerronDiscreteTarget M
  discrete_target_is_perron_default :
    discrete_target = goldbachPerronDiscreteTarget M
  kernel : ℂ → ℂ := goldbachPerronKernel scale
  kernel_eq_default : ∀ s, kernel s = goldbachPerronKernel scale s
  vertical_integral : ℝ :=
    goldbachTruncatedPerronVerticalIntegral M σ truncationHeight scale
  vertical_integral_eq_default :
    vertical_integral =
      goldbachTruncatedPerronVerticalIntegral M σ truncationHeight scale
  error_term : ℝ :=
    goldbachTruncatedPerronContourError M σ truncationHeight scale
  error_term_eq_default :
    error_term = goldbachTruncatedPerronContourError M σ truncationHeight scale
  /-- Main Perron identity: cumulative aggregate = truncated vertical integral + tail. -/
  perron_representation_holds :
    discrete_target = vertical_integral + error_term
  /-- Step 3 target: Euler–Maclaurin remainder vs contour / boundary comparison. -/
  euler_maclaurin_contour_holds : Prop

/--
Default truncated Perron data at scale `2M`, height `T`, vertical line `σ`.
Proof fields are Prop until the analytic comparison is available.
-/
noncomputable def truncatedPerronFormula_default (M : ℕ) (σ T : ℝ)
    (hM : 0 < M) (hT : 0 ≤ T) : TruncatedPerronFormula M σ where
  scale := goldbachPerronDefaultScale M
  scale_pos := goldbach_perron_default_scale_pos hM
  truncationHeight := T
  truncationHeight_nonneg := hT
  generating := goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  generating_eq_truncation := rfl
  discrete_target := goldbachPerronDiscreteTarget M
  discrete_target_is_perron_default := rfl
  kernel := goldbachPerronKernel (goldbachPerronDefaultScale M)
  kernel_eq_default := fun _ => rfl
  vertical_integral :=
    goldbachTruncatedPerronVerticalIntegral M σ T (goldbachPerronDefaultScale M)
  vertical_integral_eq_default := rfl
  error_term :=
    goldbachTruncatedPerronContourError M σ T (goldbachPerronDefaultScale M)
  error_term_eq_default := rfl
  perron_representation_holds := by
    dsimp [goldbachTruncatedPerronContourError, goldbachTruncatedPerronVerticalIntegral]
    ring
  euler_maclaurin_contour_holds := True

/-! ## Smoothed truncated Perron (useful error packaging) -/

/--
Strengthened Perron packaging: Gaussian/Fejér smoothing on the midpoint index,
explicit tail bound, and a proved `O(T^{-δ})` decay witness for the bound.

`perron_representation_holds` is the exact book-keeping split.  The analytic
content is `analytic_error_le_bound`: smoothed Perron inversion identifies the
actual error with a quantity controlled by `error_bound`.
-/
structure SmoothedTruncatedPerronFormula (M : ℕ) (σ : ℝ) where
  σ_pos : 0 < σ
  truncationHeight : ℝ
  truncationHeight_pos : 0 < truncationHeight
  smoother : GoldbachMidpointSmoother
  smoother_scale_eq_height :
    smoother.scale = truncationHeight
  scale : ℝ
  scale_pos : 0 < scale
  generating : GoldbachPartitionGeneratingFunction
  generating_eq_truncation :
    generating = goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  smoothed_discrete_target : ℝ :=
    goldbachSmoothedPerronDiscreteTarget M smoother
  smoothed_target_eq_kernel_sum :
    smoothed_discrete_target = goldbachSmoothedPerronDiscreteTarget M smoother
  kernel : ℂ → ℂ := goldbachPerronKernel scale
  kernel_eq_perron : ∀ s, kernel s = goldbachPerronKernel scale s
  vertical_integral : ℝ :=
    goldbachTruncatedPerronVerticalIntegral M σ truncationHeight scale
  vertical_integral_eq_truncated :
    vertical_integral =
      goldbachTruncatedPerronVerticalIntegral M σ truncationHeight scale
  total_error : ℝ :=
    smoothed_discrete_target - vertical_integral
  total_error_eq_difference :
    total_error = smoothed_discrete_target - vertical_integral
  /-- Exact algebraic split (proved for every instance). -/
  perron_representation_holds :
    smoothed_discrete_target = vertical_integral + total_error
  /-- Explicit tail bound (template from vertical growth when `error_bound` is default). -/
  error_bound : ℝ :=
    goldbachPerronVerticalTailErrorTemplate M σ truncationHeight scale
  error_bound_eq_template :
    error_bound = goldbachPerronVerticalTailErrorTemplate M σ truncationHeight scale
  error_bound_nonneg : 0 ≤ error_bound
  /-- Proved decay certificate (`δ`, `C`, and template bounds). -/
  tail_decay : PerronVerticalTailDecay
  /-- At the chart height: `error_bound ≤ tail_decay.bound truncationHeight`. -/
  error_bound_le_tail_at_height :
    error_bound ≤ tail_decay.bound truncationHeight
  /-- When `truncationHeight ≥ 1`: `error_bound ≤ C / truncationHeight^δ`. -/
  error_bound_le_decay :
    (1 : ℝ) ≤ truncationHeight →
      error_bound ≤ tail_decay.C / truncationHeight ^ tail_decay.δ
  /-- **Analytic target:** Perron inversion + smoothing closes the actual error. -/
  analytic_tail_bound_holds : Prop
  /-- Step 3 target: Euler–Maclaurin remainder vs contour / boundary comparison. -/
  euler_maclaurin_contour_holds : Prop

/--
Named analytic target for the Gaussian-smoothed chart: actual error ≤ explicit template.
-/
def GoldbachSmoothedPerronAnalyticTailBound (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |(goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
      goldbachTruncatedPerronVerticalIntegral M σ T x)| ≤
    goldbachPerronVerticalTailErrorTemplate M σ T x

/--
Default Gaussian-smoothed Perron chart: book-keeping split + template tail decay proved;
`analytic_tail_bound_holds` names the classical Perron inversion target.
-/
noncomputable def smoothedTruncatedPerronFormula_gaussian (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : SmoothedTruncatedPerronFormula M σ where
  σ_pos := hσ
  truncationHeight := T
  truncationHeight_pos := by linarith
  smoother := goldbachMidpointGaussianSmoother T (by linarith)
  smoother_scale_eq_height := rfl
  scale := x
  scale_pos := hx
  generating := goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  generating_eq_truncation := rfl
  smoothed_discrete_target := goldbachSmoothedPerronDiscreteTarget M
    (goldbachMidpointGaussianSmoother T (by linarith))
  smoothed_target_eq_kernel_sum := rfl
  kernel := goldbachPerronKernel x
  kernel_eq_perron := fun _ => rfl
  vertical_integral :=
    goldbachTruncatedPerronVerticalIntegral M σ T x
  vertical_integral_eq_truncated := rfl
  total_error :=
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
      goldbachTruncatedPerronVerticalIntegral M σ T x
  total_error_eq_difference := rfl
  perron_representation_holds := by ring
  error_bound := goldbachPerronVerticalTailErrorTemplate M σ T x
  error_bound_eq_template := rfl
  error_bound_nonneg :=
    goldbach_perron_vertical_tail_error_template_nonneg M σ T x hσ hx.le
  tail_decay := goldbachPerronVerticalTailDecay_template M σ x hσ hx.le
  error_bound_le_tail_at_height := le_rfl
  error_bound_le_decay := fun _ =>
    le_trans le_rfl
      ((goldbachPerronVerticalTailDecay_template M σ x hσ hx.le).bound_le T hT)
  analytic_tail_bound_holds :=
    GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx
  euler_maclaurin_contour_holds := True

/--
Default Fejér-smoothed variant (same tail decay certificate; analytic bound still named).
-/
noncomputable def smoothedTruncatedPerronFormula_fejer (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : SmoothedTruncatedPerronFormula M σ where
  σ_pos := hσ
  truncationHeight := T
  truncationHeight_pos := by linarith
  smoother := goldbachMidpointFejerSmoother T (by linarith)
  smoother_scale_eq_height := rfl
  scale := x
  scale_pos := hx
  generating := goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  generating_eq_truncation := rfl
  smoothed_discrete_target := goldbachSmoothedPerronDiscreteTarget M
    (goldbachMidpointFejerSmoother T (by linarith))
  smoothed_target_eq_kernel_sum := rfl
  kernel := goldbachPerronKernel x
  kernel_eq_perron := fun _ => rfl
  vertical_integral := goldbachTruncatedPerronVerticalIntegral M σ T x
  vertical_integral_eq_truncated := rfl
  total_error :=
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointFejerSmoother T (by linarith)) -
      goldbachTruncatedPerronVerticalIntegral M σ T x
  total_error_eq_difference := rfl
  perron_representation_holds := by ring
  error_bound := goldbachPerronVerticalTailErrorTemplate M σ T x
  error_bound_eq_template := rfl
  error_bound_nonneg :=
    goldbach_perron_vertical_tail_error_template_nonneg M σ T x hσ hx.le
  tail_decay := goldbachPerronVerticalTailDecay_template M σ x hσ hx.le
  error_bound_le_tail_at_height := le_rfl
  error_bound_le_decay := fun _ =>
    le_trans le_rfl
      ((goldbachPerronVerticalTailDecay_template M σ x hσ hx.le).bound_le T hT)
  analytic_tail_bound_holds :=
    GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx
  euler_maclaurin_contour_holds := True

theorem smoothed_truncated_perron_gaussian_error_decay (M : ℕ) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) (T : ℝ) (hT : 1 ≤ T) :
    let chart := smoothedTruncatedPerronFormula_gaussian M σ T x hσ hT hx
    chart.error_bound ≤ chart.tail_decay.C / chart.truncationHeight ^ chart.tail_decay.δ := by
  intro chart
  exact chart.error_bound_le_decay hT

/-! ## Analytic tail bound: holomorphy + growth ⇒ usable error -/

/--
Contour input for smoothed Perron inversion: holomorphic `F_M` with explicit vertical
growth constant `B_{M,σ}` on `Re s = σ`.
-/
structure GoldbachSmoothedPerronContourInput (M : ℕ) (σ : ℝ) where
  σ_pos : 0 < σ
  generating : GoldbachPartitionGeneratingFunction :=
    goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  holomorphic : IsHolomorphicGoldbachPartition generating
  vertical_growth : VerticalLineGrowthBound σ
  F_eq_truncated :
    vertical_growth.F = goldbachMidpointGeometricGeneratingSumTruncated M
  /-- Vertical-growth constant `B_{M,σ}` (independent of `t` for finite truncation). -/
  growth_constant : ℝ :=
    goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ
  growth_constant_nonneg : 0 ≤ growth_constant
  growth_constant_eq_value :
    growth_constant = goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ
  growth_constant_eq_vertical_bound :
    ∀ T, vertical_growth.bound T = growth_constant

/--
Proved contour input for the pair-Dirichlet truncation `F_M`.
-/
noncomputable def goldbachSmoothedPerronContourInput_pairDirichlet (M : ℕ) (σ : ℝ)
    (hσ : 0 < σ) : GoldbachSmoothedPerronContourInput M σ where
  σ_pos := hσ
  holomorphic := goldbach_pair_dirichlet_generating_holomorphic M
  vertical_growth := verticalLineGrowthBound_pairDirichlet_truncated M σ
  F_eq_truncated := rfl
  growth_constant_nonneg :=
    goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ
  growth_constant_eq_value := rfl
  growth_constant_eq_vertical_bound := fun _ => rfl

theorem goldbach_smoothed_perron_growth_constant_le_unweighted_mass {M : ℕ} {σ : ℝ}
    (input : GoldbachSmoothedPerronContourInput M σ) (hσ : 0 ≤ σ) :
    input.growth_constant ≤ goldbachMidpointGeometricUnweightedMass M := by
  rw [input.growth_constant_eq_value]
  exact goldbach_midpoint_geometric_generating_sum_vertical_bound_value_le_unweighted M σ hσ

/--
Explicit two-ray tail bookkeeping bound matching `2 · goldbachPerronVerticalTailErrorTemplate`
when `T ≥ 1` and `growth_constant = B_{M,σ}`:

`2 · B_{M,σ} · x^σ / (σ · T)`.
-/
noncomputable def goldbachSmoothedPerronTailContourBookkeepingBound (M : ℕ) (σ T x : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) : ℝ :=
  2 * input.growth_constant * x ^ σ / (σ * T)

/--
Two-ray bookkeeping for the `(F_M − 1) · G_T` heat Mellin tail: the `+ 1` comes from
`‖F_M − 1‖ ≤ ‖F_M‖ + 1 ≤ B_{M,σ} + 1` (cf. `‖F_M‖ ≤ B_{M,σ}` in the unweighted tail).
-/
noncomputable def goldbachPerronFMMinusOneHeatTailContourBookkeepingBound (M : ℕ) (σ T x : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) : ℝ :=
  2 * (input.growth_constant + 1) * x ^ σ / (σ * T)

theorem goldbach_smoothed_perron_tail_contour_bookkeeping_bound_nonneg (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    0 ≤ goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  dsimp [goldbachSmoothedPerronTailContourBookkeepingBound]
  have hnum :
      0 ≤ 2 * input.growth_constant * x ^ σ :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) input.growth_constant_nonneg)
      (Real.rpow_nonneg hx.le σ)
  exact div_nonneg hnum (mul_nonneg hσ.le hTpos.le)

theorem goldbach_smoothed_perron_tail_bookkeeping_bound_eq_two_template (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 ≤ x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input =
      2 * goldbachPerronVerticalTailErrorTemplate M σ T x := by
  dsimp [goldbachSmoothedPerronTailContourBookkeepingBound,
    goldbachPerronVerticalTailErrorTemplate]
  rw [max_eq_right hT, input.growth_constant_eq_value]
  ring

theorem goldbach_smoothed_perron_contour_input_vertical_le (M : ℕ) (σ T : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) (t : ℝ) (hT : |t| ≤ T) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖ ≤ input.growth_constant := by
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖
        = ‖input.vertical_growth.F (σ + t * I)‖ := by rw [← input.F_eq_truncated]
    _ ≤ input.vertical_growth.bound T := input.vertical_growth.vertical_le T t hT
    _ = input.growth_constant := input.growth_constant_eq_vertical_bound T

/--
Uniform vertical growth at arbitrary height: use `T' = max |t| 1` in the proved bound.
-/
theorem goldbach_smoothed_perron_F_norm_le_growth_constant (M : ℕ) (σ : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) (t : ℝ) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖ ≤ input.growth_constant := by
  set T' : ℝ := max |t| 1
  have hT' : |t| ≤ T' := le_max_left |t| 1
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖
        = ‖input.vertical_growth.F (σ + t * I)‖ := by rw [← input.F_eq_truncated]
    _ ≤ input.vertical_growth.bound T' := input.vertical_growth.vertical_le T' t hT'
    _ = input.growth_constant := input.growth_constant_eq_vertical_bound T'

theorem goldbach_perron_integrand_norm_le_vertical_growth (M : ℕ) (σ x t : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) (hx : 0 < x) :
    ‖goldbachTruncatedPerronVerticalIntegrand M σ x t‖ ≤
      input.growth_constant * x ^ σ / σ := by
  have hσ : 0 < σ := input.σ_pos
  dsimp [goldbachTruncatedPerronVerticalIntegrand]
  rw [Complex.norm_mul]
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖ *
        ‖goldbachPerronKernel x (σ + t * I)‖ ≤
        input.growth_constant * (x ^ σ / σ) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) input.growth_constant_nonneg
      · exact goldbach_smoothed_perron_F_norm_le_growth_constant M σ input t
      · exact goldbach_perron_kernel_norm_le_vertical x σ t hσ hx
    _ = input.growth_constant * x ^ σ / σ := by ring

theorem goldbach_perron_integrand_norm_le_tail_from_growth (M : ℕ) (σ T x t : ℝ)
    (input : GoldbachSmoothedPerronContourInput M σ) (hx : 0 < x) (hTle : T ≤ |t|)
    (hT : 1 ≤ T) :
    ‖goldbachTruncatedPerronVerticalIntegrand M σ x t‖ ≤
      input.growth_constant * x ^ σ / T := by
  have hσ : 0 < σ := input.σ_pos
  have hxσ : 0 < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hkernel :=
    goldbach_perron_kernel_norm_le_on_tail x σ T t hσ hx hTle hT
  have hkernel_T : ‖goldbachPerronKernel x (σ + t * I)‖ ≤ x ^ σ / T := by
    have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one (le_trans hT hTle)
    have hdiv : x ^ σ / |t| ≤ x ^ σ / T := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div]
      simpa using
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hTpos hTle) hxσ.le
    exact hkernel.trans hdiv
  dsimp [goldbachTruncatedPerronVerticalIntegrand]
  rw [Complex.norm_mul]
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖ *
        ‖goldbachPerronKernel x (σ + t * I)‖ ≤
        input.growth_constant * (x ^ σ / T) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) input.growth_constant_nonneg
      · exact goldbach_smoothed_perron_F_norm_le_growth_constant M σ input t
      · exact hkernel_T
    _ = input.growth_constant * x ^ σ / T := by ring

theorem goldbach_perron_tail_template_eq_growth_quotient (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 ≤ x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    goldbachPerronVerticalTailErrorTemplate M σ T x =
      x ^ σ * input.growth_constant / (σ * T) := by
  dsimp [goldbachPerronVerticalTailErrorTemplate]
  rw [max_eq_right hT, input.growth_constant_eq_value]

/-! ## Integrand continuity and integrability -/

theorem goldbach_vertical_line_ne_zero (σ t : ℝ) (hσ : 0 < σ) :
    σ + t * I ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  linarith [hσ]

theorem goldbach_vertical_line_continuous (σ : ℝ) :
    Continuous (fun (t : ℝ) => σ + t * I) := by
  simpa using continuous_const.add (continuous_ofReal.mul continuous_const)

theorem goldbach_vertical_line_map_continuousOn (σ : ℝ) (S : Set ℝ) :
    ContinuousOn (fun (t : ℝ) => σ + t * I) S :=
  (goldbach_vertical_line_continuous σ).continuousOn

theorem goldbach_perron_kernel_continuousOn_vertical (x σ : ℝ) (hσ : 0 < σ) (hx : 0 < x)
    (S : Set ℝ) :
    ContinuousOn (fun (t : ℝ) => goldbachPerronKernel x (σ + t * I)) S := by
  dsimp [goldbachPerronKernel]
  set z : ℂ := (x : ℂ)
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hmap := goldbach_vertical_line_map_continuousOn σ S
  have hsne : ∀ t ∈ S, σ + t * I ≠ 0 := fun t _ => goldbach_vertical_line_ne_zero σ t hσ
  have hc := ContinuousOn.const_cpow hmap (Or.inl hz)
  exact ContinuousOn.div hc hmap hsne

theorem goldbach_midpoint_geometric_generating_sum_truncated_continuousOn_vertical
    (M : ℕ) (σ : ℝ) (hσ : 0 < σ) (S : Set ℝ) :
    ContinuousOn (fun (t : ℝ) => goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)) S := by
  refine (goldbach_midpoint_geometric_generating_sum_truncated_continuousOn M).comp
    (goldbach_vertical_line_map_continuousOn σ S) ?_
  intro t ht
  exact mem_goldbachGeneratingHalfPlane_vertical σ t hσ

theorem goldbach_truncated_perron_vertical_integrand_continuousOn (M : ℕ) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun (t : ℝ) => goldbachTruncatedPerronVerticalIntegrand M σ x t) S := by
  dsimp [goldbachTruncatedPerronVerticalIntegrand]
  exact
    (goldbach_midpoint_geometric_generating_sum_truncated_continuousOn_vertical M σ hσ S).mul
      (goldbach_perron_kernel_continuousOn_vertical x σ hσ hx S)

theorem goldbach_truncated_perron_vertical_integrand_re_continuousOn (M : ℕ) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun (t : ℝ) => (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) S :=
  continuous_re.comp_continuousOn
    (goldbach_truncated_perron_vertical_integrand_continuousOn M σ x hσ hx S)

/--
Integrability of the tail integrand on the bounded two-ray proxy.
-/
def GoldbachPerronTailIntegrableAtHeight (M : ℕ) (σ T x : ℝ) (hσ : 0 < σ) (hx : 0 < x) : Prop :=
  IntervalIntegrable (fun t => (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) volume T (2 * T) ∧
    IntervalIntegrable (fun t => (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) volume (-2 * T) (-T)

theorem goldbach_perron_tail_integrable_at_height (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) :
    GoldbachPerronTailIntegrableAtHeight M σ T x hσ hx := by
  constructor
  · exact
      (goldbach_truncated_perron_vertical_integrand_re_continuousOn M σ x hσ hx
        (Set.uIcc T (2 * T))).intervalIntegrable
  · exact
      (goldbach_truncated_perron_vertical_integrand_re_continuousOn M σ x hσ hx
        (Set.uIcc (-2 * T) (-T))).intervalIntegrable

theorem goldbach_perron_central_integrable_at_height (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) :
    IntervalIntegrable (fun t => (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) volume
      (-T) T :=
  (goldbach_truncated_perron_vertical_integrand_re_continuousOn M σ x hσ hx
    (Set.uIcc (-T) T)).intervalIntegrable

theorem goldbach_perron_tail_integrable_at_height_of_contour_input (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) (_input : GoldbachSmoothedPerronContourInput M σ) :
    GoldbachPerronTailIntegrableAtHeight M σ T x hσ hx :=
  goldbach_perron_tail_integrable_at_height M σ T x hσ hx

/-! ## Cauchy rectangle edge integrals -/

/--
Rectangle for smoothed Perron inversion: left vertical `Re s = σ₀`, right vertical `Re s = σ`,
height `2T` (`Im s ∈ [-2T, 2T]`).  The right edge splits into central `[-T, T]` plus the
bounded tail proxy used in tail bounds.
-/
structure GoldbachPerronContourRectangle where
  σ₀ : ℝ
  σ : ℝ
  σ₀_lt_σ : σ₀ < σ
  T : ℝ
  T_pos : 0 < T
  x : ℝ
  x_pos : 0 < x

noncomputable def goldbachPerronContourRectangle_default (σ₀ σ T x : ℝ)
    (hσ₀σ : σ₀ < σ) (hT : 0 < T) (hx : 0 < x) : GoldbachPerronContourRectangle where
  σ₀ := σ₀
  σ := σ
  σ₀_lt_σ := hσ₀σ
  T := T
  T_pos := hT
  x := x
  x_pos := hx

/--
Right vertical edge at `Re s = σ`, integrated over `t ∈ [-2T, 2T]` (normalized by `1/2π`).
-/
noncomputable def goldbachPerronRightVerticalEdgeIntegral (M : ℕ) (σ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re)

/--
Left vertical edge at `Re s = σ₀`, same height and normalization.
-/
noncomputable def goldbachPerronLeftVerticalEdgeIntegral (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ₀ x t).re)

/--
Integrand along a horizontal edge at fixed `Im s = γ`, parametrized by `Re s`.
-/
noncomputable def goldbachPerronHorizontalEdgeIntegrand (M : ℕ) (x γ : ℝ) (s_re : ℝ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M (s_re + γ * I) *
    goldbachPerronKernel x (s_re + γ * I)

/--
Top horizontal edge `Im s = 2T`, integrated over `Re s ∈ [σ₀, σ]`.
-/
noncomputable def goldbachPerronTopHorizontalEdgeIntegral (M : ℕ) (σ₀ σ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ s_re in σ₀..σ, (goldbachPerronHorizontalEdgeIntegrand M x (2 * T) s_re).re)

/--
Bottom horizontal edge `Im s = -2T`, integrated over `Re s ∈ [σ₀, σ]`.
-/
noncomputable def goldbachPerronBottomHorizontalEdgeIntegral (M : ℕ) (σ₀ σ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ s_re in σ₀..σ, (goldbachPerronHorizontalEdgeIntegrand M x (-2 * T) s_re).re)

/--
Normalized boundary bookkeeping for the rectangle (counterclockwise orientation):

`left + top − right − bottom`.
-/
noncomputable def goldbachPerronCauchyRectangleBoundaryIntegral (M : ℕ) (σ₀ σ T x : ℝ) : ℝ :=
  goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x +
    goldbachPerronTopHorizontalEdgeIntegral M σ₀ σ T x -
    goldbachPerronRightVerticalEdgeIntegral M σ T x -
    goldbachPerronBottomHorizontalEdgeIntegral M σ₀ σ T x

theorem goldbach_perron_right_vertical_edge_eq_central_plus_tail (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 0 < T) (hx : 0 < x) :
    goldbachPerronRightVerticalEdgeIntegral M σ T x =
      goldbachTruncatedPerronVerticalIntegral M σ T x +
        goldbachTruncatedPerronVerticalTailIntegral M σ T x := by
  set f : ℝ → ℝ := fun t => (goldbachTruncatedPerronVerticalIntegrand M σ x t).re
  rcases goldbach_perron_tail_integrable_at_height M σ T x hσ hx with
    ⟨hint_pos_tail, hint_neg_tail⟩
  have hint_central :=
    goldbach_perron_central_integrable_at_height M σ T x hσ hx
  have hint_neg_to_pos := hint_neg_tail.trans hint_central
  have hsplit₁ :
      (∫ t in (-2 * T)..(-T), f t) + (∫ t in (-T)..T, f t) =
        ∫ t in (-2 * T)..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals hint_neg_tail hint_central
  have hsplit₂ :
      (∫ t in (-2 * T)..T, f t) + (∫ t in T..(2 * T), f t) =
        ∫ t in (-2 * T)..(2 * T), f t :=
    intervalIntegral.integral_add_adjacent_intervals hint_neg_to_pos hint_pos_tail
  have hcore :
      (∫ t in (-2 * T)..(2 * T), f t) =
        (∫ t in (-T)..T, f t) +
          ((∫ t in T..(2 * T), f t) + (∫ t in (-2 * T)..(-T), f t)) := by
    rw [hsplit₂.symm, ← hsplit₁]
    ring
  dsimp only [goldbachPerronRightVerticalEdgeIntegral, goldbachTruncatedPerronVerticalIntegral,
    goldbachTruncatedPerronVerticalTailIntegral]
  simp only [← mul_add, f, hcore]

/-! ### Mathlib-aligned complex contour (Cauchy–Goursat) -/

/--
Closed rectangle `σ₀ ≤ Re s ≤ σ`, `-2T ≤ Im s ≤ 2T`.
-/
noncomputable def goldbachPerronContourRectangleClosed (σ₀ σ T : ℝ) : Set ℂ :=
  [[σ₀, σ]] ×ℂ [[-2 * T, 2 * T]]

/--
Open rectangle interior (product of open intervals).
-/
noncomputable def goldbachPerronContourRectangleInterior (σ₀ σ T : ℝ) : Set ℂ :=
  Ioo (min σ₀ σ) (max σ₀ σ) ×ℂ Ioo (-2 * T) (2 * T)

noncomputable def goldbachPerronContourRectangleCorner₀ (σ₀ T : ℝ) : ℂ :=
  (σ₀ : ℂ) + (-2 * T) * I

noncomputable def goldbachPerronContourRectangleCorner₁ (σ T : ℝ) : ℂ :=
  (σ : ℂ) + (2 * T) * I

/--
Full Perron contour integrand `F_M(s) · x^s / s` on the rectangle.
-/
noncomputable def goldbachPerronContourIntegrand (M : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M s * goldbachPerronKernel x s

theorem ne_zero_of_mem_goldbachGeneratingHalfPlane_zero (s : ℂ)
    (hs : s ∈ goldbachGeneratingHalfPlane (0 : ℝ)) : s ≠ 0 := by
  intro h0
  have hlt : (0 : ℝ) < s.re := by
    simpa [goldbachGeneratingHalfPlane, Set.mem_setOf_eq] using hs
  rw [h0, Complex.zero_re] at hlt
  exact lt_irrefl 0 hlt

theorem mem_goldbachPerronContourRectangleClosed_of_pos_re (σ₀ σ T : ℝ) (hσ₀ : 0 < σ₀)
    (hσ₀σ : σ₀ ≤ σ) (s : ℂ) (hs : s ∈ goldbachPerronContourRectangleClosed σ₀ σ T) :
    s ∈ goldbachGeneratingHalfPlane 0 := by
  rcases hs with ⟨hsre, _⟩
  rcases hsre with ⟨hle, _⟩
  have hσ₀le : σ₀ ≤ s.re := by
    rw [min_eq_left hσ₀σ] at hle
    exact hle
  exact mem_goldbachGeneratingHalfPlane_of_pos_re s (lt_of_lt_of_le hσ₀ hσ₀le)

theorem ne_zero_of_mem_goldbachPerronContourRectangleClosed (σ₀ σ T : ℝ) (hσ₀ : 0 < σ₀)
    (hσ₀σ : σ₀ ≤ σ) (s : ℂ) (hs : s ∈ goldbachPerronContourRectangleClosed σ₀ σ T) : s ≠ 0 :=
  ne_zero_of_mem_goldbachGeneratingHalfPlane_zero s
    (mem_goldbachPerronContourRectangleClosed_of_pos_re σ₀ σ T hσ₀ hσ₀σ s hs)

theorem goldbach_perron_kernel_differentiableOn (x : ℝ) (hx : 0 < x) (S : Set ℂ)
    (hS : ∀ s ∈ S, s ∈ goldbachGeneratingHalfPlane 0) :
    DifferentiableOn ℂ (goldbachPerronKernel x) S := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s) S := by
    refine Differentiable.differentiableOn ?_
    intro s
    exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hx')).differentiableAt
  have hid : DifferentiableOn ℂ id S := differentiableOn_id
  refine DifferentiableOn.div hpow hid ?_
  intro s hs
  exact ne_zero_of_mem_goldbachGeneratingHalfPlane_zero s (hS s hs)

theorem goldbach_perron_contour_integrand_differentiableOn (M : ℕ) (x : ℝ) (σ₀ σ T : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₀σ : σ₀ ≤ σ) (hx : 0 < x) :
    DifferentiableOn ℂ (goldbachPerronContourIntegrand M x)
      (goldbachPerronContourRectangleClosed σ₀ σ T) := by
  have hsub : ∀ s ∈ goldbachPerronContourRectangleClosed σ₀ σ T,
      s ∈ goldbachGeneratingHalfPlane 0 :=
    fun s hs => mem_goldbachPerronContourRectangleClosed_of_pos_re σ₀ σ T hσ₀ hσ₀σ s hs
  have hF :=
    (goldbach_midpoint_geometric_generating_sum_truncated_differentiableOn M).mono hsub
  have hk := goldbach_perron_kernel_differentiableOn x hx
    (goldbachPerronContourRectangleClosed σ₀ σ T) hsub
  exact DifferentiableOn.mul hF hk

/--
Mathlib-oriented boundary integral for `f` on corners `σ₀ - 2Ti` and `σ + 2Ti`
(counterclockwise, matching `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).
-/
noncomputable def goldbachPerronComplexRectangleBoundary (f : ℂ → ℂ) (σ₀ σ T : ℝ) : ℂ :=
  let z := goldbachPerronContourRectangleCorner₀ σ₀ T
  let w := goldbachPerronContourRectangleCorner₁ σ T
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable def goldbachPerronTopHorizontalEdgeComplexIntegral (M : ℕ) (x σ₀ σ T : ℝ) : ℂ :=
  ∫ s_re in σ₀..σ, goldbachPerronContourIntegrand M x (s_re + (2 * T) * I)

noncomputable def goldbachPerronBottomHorizontalEdgeComplexIntegral (M : ℕ) (x σ₀ σ T : ℝ) : ℂ :=
  ∫ s_re in σ₀..σ, goldbachPerronContourIntegrand M x (s_re + (-2 * T) * I)

noncomputable def goldbachPerronRightVerticalEdgeComplexIntegral (M : ℕ) (σ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T), goldbachPerronContourIntegrand M x (σ + t * I)

noncomputable def goldbachPerronLeftVerticalEdgeComplexIntegral (M : ℕ) (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T), goldbachPerronContourIntegrand M x (σ₀ + t * I)

theorem goldbach_intervalIntegral_re (f : ℝ → ℂ) (a b : ℝ)
    (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
  rw [← Complex.reCLM_apply]
  exact ((Complex.reCLM : ℂ →L[ℝ] ℝ).intervalIntegral_comp_comm hf).symm

theorem goldbach_perron_complex_vertical_point (σ t : ℝ) :
    (σ : ℂ) + t * I = Complex.I * t + σ := by push_cast; ring_nf

theorem goldbach_perron_complex_horizontal_top_point (T s_re : ℝ) :
    (s_re : ℂ) + (2 * T) * I = Complex.I * (2 * T) + s_re := by push_cast; ring_nf

theorem goldbach_perron_complex_horizontal_bottom_point (T s_re : ℝ) :
    (s_re : ℂ) + (-2 * T) * I = -(Complex.I * (2 * T)) + s_re := by push_cast; ring_nf

theorem goldbach_perron_contour_corner₀_re (σ₀ T : ℝ) :
    (goldbachPerronContourRectangleCorner₀ σ₀ T).re = σ₀ := by
  simp [goldbachPerronContourRectangleCorner₀]

theorem goldbach_perron_contour_corner₀_im (σ₀ T : ℝ) :
    (goldbachPerronContourRectangleCorner₀ σ₀ T).im = -2 * T := by
  simp [goldbachPerronContourRectangleCorner₀]

theorem goldbach_perron_contour_corner₁_re (σ T : ℝ) :
    (goldbachPerronContourRectangleCorner₁ σ T).re = σ := by
  simp [goldbachPerronContourRectangleCorner₁]

theorem goldbach_perron_contour_corner₁_im (σ T : ℝ) :
    (goldbachPerronContourRectangleCorner₁ σ T).im = 2 * T := by
  simp [goldbachPerronContourRectangleCorner₁]

theorem goldbach_perron_mathlib_horizontal_bottom_integrand (σ₀ T x₁ : ℝ) :
    x₁ + (goldbachPerronContourRectangleCorner₀ σ₀ T).im * I =
      (x₁ : ℂ) + (-2 * T) * I := by
  rw [goldbach_perron_contour_corner₀_im]
  push_cast
  ring_nf

theorem goldbach_perron_mathlib_horizontal_top_integrand (σ T x₁ : ℝ) :
    x₁ + (goldbachPerronContourRectangleCorner₁ σ T).im * I =
      (x₁ : ℂ) + (2 * T) * I := by
  rw [goldbach_perron_contour_corner₁_im]
  push_cast
  ring_nf

theorem goldbach_perron_mathlib_vertical_integrand_at_re (s_re y : ℝ) :
    s_re + y * I = (s_re : ℂ) + y * I := by
  push_cast
  rfl

noncomputable def goldbachPerronMathlibComplexRectangleBoundary (M : ℕ) (x σ₀ σ T : ℝ) : ℂ :=
  goldbachPerronComplexRectangleBoundary (goldbachPerronContourIntegrand M x) σ₀ σ T

/-- Bookkeeping-oriented complex boundary (edge-sum form used in the reduction). -/
noncomputable def goldbachPerronContourComplexRectangleBoundary (M : ℕ) (x σ₀ σ T : ℝ) : ℂ :=
  goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T -
    goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T +
    Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x -
    Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x

theorem goldbach_perron_complex_rectangle_boundary_eq_edge_sum (M : ℕ) (x σ₀ σ T : ℝ) :
    goldbachPerronContourComplexRectangleBoundary M x σ₀ σ T =
      goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T -
        goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T +
        Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x -
        Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x :=
  rfl

theorem goldbach_perron_mathlib_complex_rectangle_boundary_eq_edge_sum (M : ℕ) (x σ₀ σ T : ℝ)
    (hσ₀σ : σ₀ ≤ σ) :
    goldbachPerronMathlibComplexRectangleBoundary M x σ₀ σ T =
      goldbachPerronContourComplexRectangleBoundary M x σ₀ σ T := by
  dsimp only [goldbachPerronMathlibComplexRectangleBoundary,
    goldbachPerronContourComplexRectangleBoundary, goldbachPerronComplexRectangleBoundary]
  let z := goldbachPerronContourRectangleCorner₀ σ₀ T
  let w := goldbachPerronContourRectangleCorner₁ σ T
  have hzre := goldbach_perron_contour_corner₀_re σ₀ T
  have hwre := goldbach_perron_contour_corner₁_re σ T
  have hzim := goldbach_perron_contour_corner₀_im σ₀ T
  have hwim := goldbach_perron_contour_corner₁_im σ T
  have hbot :
      (∫ x₁ in z.re..w.re,
          goldbachPerronContourIntegrand M x (x₁ + z.im * I)) =
        goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T := by
    rw [hzre, hwre]
    dsimp [goldbachPerronBottomHorizontalEdgeComplexIntegral, goldbachPerronContourIntegrand]
    refine intervalIntegral.integral_congr fun x₁ hx₁ => ?_
    dsimp [goldbachPerronContourIntegrand]
    have hpt : x₁ + z.im * I = (x₁ : ℂ) + (-2 * T) * I := by
      dsimp only [z]
      simpa using goldbach_perron_mathlib_horizontal_bottom_integrand σ₀ T x₁
    rw [hpt]
  have htop :
      (∫ x₁ in z.re..w.re,
          goldbachPerronContourIntegrand M x (x₁ + w.im * I)) =
        goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T := by
    rw [hzre, hwre]
    dsimp [goldbachPerronTopHorizontalEdgeComplexIntegral, goldbachPerronContourIntegrand]
    refine intervalIntegral.integral_congr fun x₁ hx₁ => ?_
    dsimp [goldbachPerronContourIntegrand]
    have hpt : x₁ + w.im * I = (x₁ : ℂ) + (2 * T) * I := by
      dsimp only [w]
      simpa using goldbach_perron_mathlib_horizontal_top_integrand σ T x₁
    rw [hpt]
  have hright :
      (∫ y in z.im..w.im, goldbachPerronContourIntegrand M x (w.re + y * I)) =
        goldbachPerronRightVerticalEdgeComplexIntegral M σ T x := by
    rw [hzim, hwim]
    dsimp [goldbachPerronRightVerticalEdgeComplexIntegral, goldbachPerronContourIntegrand]
    refine intervalIntegral.integral_congr fun y hy => ?_
    dsimp [goldbachPerronContourIntegrand]
    dsimp only [w]
    rw [hwre, goldbach_perron_mathlib_vertical_integrand_at_re σ y]
  have hleft :
      (∫ y in z.im..w.im, goldbachPerronContourIntegrand M x (z.re + y * I)) =
        goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x := by
    rw [hzim, hwim]
    dsimp [goldbachPerronLeftVerticalEdgeComplexIntegral, goldbachPerronContourIntegrand]
    refine intervalIntegral.integral_congr fun y hy => ?_
    dsimp [goldbachPerronContourIntegrand]
    dsimp only [z]
    rw [hzre, goldbach_perron_mathlib_vertical_integrand_at_re σ₀ y]
  rw [hbot, htop, hright, hleft]

/--
**Cauchy–Goursat (formal):** holomorphic `F_M · x^s/s` on the closed rectangle with `σ₀ > 0`
has zero Mathlib-oriented boundary integral.
-/
theorem goldbach_perron_contour_rectangle_closed_eq_mathlib (σ₀ σ T : ℝ) :
    goldbachPerronContourRectangleClosed σ₀ σ T =
      [[(goldbachPerronContourRectangleCorner₀ σ₀ T).re,
          (goldbachPerronContourRectangleCorner₁ σ T).re]] ×ℂ
        [[(goldbachPerronContourRectangleCorner₀ σ₀ T).im,
          (goldbachPerronContourRectangleCorner₁ σ T).im]] := by
  simp [goldbachPerronContourRectangleClosed, goldbachPerronContourRectangleCorner₀,
    goldbachPerronContourRectangleCorner₁]

theorem goldbach_perron_mathlib_complex_rectangle_boundary_eq_zero (M : ℕ) (x σ₀ σ T : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₀σ : σ₀ ≤ σ) (hx : 0 < x) :
    goldbachPerronMathlibComplexRectangleBoundary M x σ₀ σ T = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (goldbachPerronContourIntegrand M x)
    (goldbachPerronContourRectangleCorner₀ σ₀ T)
    (goldbachPerronContourRectangleCorner₁ σ T)
    (by
      rw [← goldbach_perron_contour_rectangle_closed_eq_mathlib σ₀ σ T]
      exact goldbach_perron_contour_integrand_differentiableOn M x σ₀ σ T hσ₀ hσ₀σ hx)

theorem goldbach_perron_contour_complex_rectangle_boundary_eq_zero (M : ℕ) (x σ₀ σ T : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₀σ : σ₀ ≤ σ) (hx : 0 < x) :
    goldbachPerronContourComplexRectangleBoundary M x σ₀ σ T = 0 :=
  goldbach_perron_mathlib_complex_rectangle_boundary_eq_edge_sum M x σ₀ σ T hσ₀σ ▸
    goldbach_perron_mathlib_complex_rectangle_boundary_eq_zero M x σ₀ σ T hσ₀ hσ₀σ hx

/--
Complex horizontal edges vanish (stronger than real-part bookkeeping).
-/
def GoldbachSmoothedPerronHorizontalComplexEdgesVanish (M : ℕ) (σ₀ σ T x : ℝ) : Prop :=
  goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T = 0 ∧
    goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T = 0

/--
Horizontal edges vanish in the Gaussian smoothing limit (named analytic input).
-/
def GoldbachSmoothedPerronHorizontalEdgesVanish (M : ℕ) (σ₀ σ T x : ℝ) : Prop :=
  goldbachPerronTopHorizontalEdgeIntegral M σ₀ σ T x = 0 ∧
    goldbachPerronBottomHorizontalEdgeIntegral M σ₀ σ T x = 0

/--
Cauchy residue bookkeeping: oriented real-part boundary sum vanishes once complex horizontal
edges vanish and `σ₀ > 0` (Cauchy–Goursat on the rectangle interior).
-/
def GoldbachSmoothedPerronCauchyBoundaryVanishes (M : ℕ) (σ₀ σ T x : ℝ) : Prop :=
  goldbachPerronCauchyRectangleBoundaryIntegral M σ₀ σ T x = 0

/-! ### Horizontal growth (edge bounds from `B_{M,σ}`) -/

/--
Uniform bound on `‖F_M‖` along horizontal lines `Im s = γ` with `|γ| ≥ T`, from vertical
growth at height `|γ|`.
-/
theorem goldbach_perron_F_norm_le_vertical_bound_at_re_ge (M : ℕ) (σ₀ s_re γ : ℝ)
    (hσ₀ : 0 < σ₀) (hs : σ₀ ≤ s_re) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (s_re + γ * I)‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ :=
  goldbach_midpoint_geometric_generating_sum_truncated_norm_le_vertical_bound_at_re_ge M σ₀ s_re γ
    hσ₀ hs

theorem goldbach_perron_kernel_norm_le_on_horizontal_line (x σ₀ s_re γ : ℝ) (hσ₀ : 0 < σ₀)
    (hx : 0 < x) (hσ₀le : σ₀ ≤ s_re) :
    ‖goldbachPerronKernel x (s_re + γ * I)‖ ≤ x ^ s_re / s_re := by
  have hsre : (s_re + γ * I).re = s_re := by simp
  have hσre : 0 < s_re := lt_of_lt_of_le hσ₀ hσ₀le
  dsimp [goldbachPerronKernel]
  set s : ℂ := s_re + γ * I
  have hsne : s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [s] at this
    linarith [hσre]
  have hnorm_pow : ‖(x : ℂ) ^ s‖ = x ^ s.re := by
    rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hx s
  have hnorm : ‖s‖ ≥ s_re := by
    dsimp [s]
    rw [Complex.norm_def, Complex.normSq_add_mul_I]
    have : s_re ^ 2 ≤ s_re ^ 2 + γ ^ 2 := by nlinarith
    calc s_re = Real.sqrt (s_re ^ 2) := (Real.sqrt_sq hσre.le).symm
      _ ≤ Real.sqrt (s_re ^ 2 + γ ^ 2) := Real.sqrt_le_sqrt this
  rw [Complex.norm_div, hnorm_pow, hsre]
  refine (div_le_div_iff₀ (by positivity) hσre).mpr ?_
  exact mul_le_mul_of_nonneg_left hnorm (by positivity)

theorem goldbach_perron_horizontal_integrand_norm_le (M : ℕ) (x σ₀ σ γ : ℝ)
    (hx : 0 < x) (hσ₀ : 0 < σ₀) (s_re : ℝ) (hs₀ : σ₀ ≤ s_re) (_hsσ : s_re ≤ σ) :
    ‖goldbachPerronHorizontalEdgeIntegrand M x γ s_re‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ * (x ^ s_re / σ₀) := by
  dsimp [goldbachPerronHorizontalEdgeIntegrand]
  rw [Complex.norm_mul]
  have hσre : 0 < s_re := lt_of_lt_of_le hσ₀ hs₀
  calc
    _ ≤ goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ * (x ^ s_re / s_re) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
      · exact goldbach_perron_F_norm_le_vertical_bound_at_re_ge M σ₀ s_re γ hσ₀ hs₀
      · exact goldbach_perron_kernel_norm_le_on_horizontal_line x σ₀ s_re γ hσ₀ hx hs₀
      · exact goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ₀
    _ ≤ goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ * (x ^ s_re / σ₀) := by
      refine mul_le_mul_of_nonneg_left ?_ (goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ₀)
      rw [div_le_div_iff₀ hσre hσ₀]
      nlinarith [hs₀, Real.rpow_pos_of_pos hx s_re]

/--
Pointwise horizontal edge bound at `Im s = ±2T` from `‖F_M‖ ≤ B_{M,σ}` on the rectangle.
-/
theorem goldbach_perron_horizontal_edge_integrand_le_template (M : ℕ) (σ₀ σ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hx : 0 < x) (s_re : ℝ) (hs₀ : σ₀ ≤ s_re) (hsσ : s_re ≤ σ) :
    ‖goldbachPerronHorizontalEdgeIntegrand M x (2 * T) s_re‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ * (x ^ s_re / σ₀) ∧
      ‖goldbachPerronHorizontalEdgeIntegrand M x (-2 * T) s_re‖ ≤
        goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ * (x ^ s_re / σ₀) := by
  constructor
  · exact goldbach_perron_horizontal_integrand_norm_le M x σ₀ σ (2 * T) hx hσ₀ s_re hs₀ hsσ
  · exact goldbach_perron_horizontal_integrand_norm_le M x σ₀ σ (-2 * T) hx hσ₀ s_re hs₀ hsσ

/--
Horizontal complex edges vanish from uniform `B_{M,σ}` growth when the horizontal integrand is
identically zero on both edges (named analytic input for Gaussian-deformed contours).
-/
def GoldbachPerronHorizontalIntegrandVanishesOnEdges (M : ℕ) (σ₀ σ T x : ℝ) : Prop :=
  ∀ s_re ∈ Set.uIcc σ₀ σ,
    goldbachPerronContourIntegrand M x (s_re + (2 * T) * I) = 0 ∧
      goldbachPerronContourIntegrand M x (s_re + (-2 * T) * I) = 0

theorem goldbach_smoothed_perron_horizontal_complex_edges_vanish_of_edge_integrand_zero
    (M : ℕ) (σ₀ σ T x : ℝ) (hσ₀σ : σ₀ ≤ σ)
    (h : GoldbachPerronHorizontalIntegrandVanishesOnEdges M σ₀ σ T x) :
    GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ T x := by
  dsimp [GoldbachSmoothedPerronHorizontalComplexEdgesVanish,
    goldbachPerronTopHorizontalEdgeComplexIntegral,
    goldbachPerronBottomHorizontalEdgeComplexIntegral]
  constructor
  · rw [intervalIntegral.integral_congr (fun s_re hs => (h s_re hs).1)]
    simp
  · rw [intervalIntegral.integral_congr (fun s_re hs => (h s_re hs).2)]
    simp

/-! ### Subgoal A: Gaussian Mellin inversion (foundational) -/

/-!
## Classical target (Subgoal A)

Gaussian smoother on midpoint index `N` (centre `M`, scale `T`):

`K_T(N;M) = exp(−(N−M)² / (2T²))`.

Smoothed discrete readout (truncation `M`):

`∑_{1≤N≤M} K_T(N;M) · a_N`.

At unit Perron scale `x = 1` the kernel is `1/s`; on the vertical line `s = σ₀ + it`:

`(1/2π) ∫ F_M(σ₀+it) / (σ₀+it) · G_T(t) dt`

with vertical heat profile `G_T` tied to the same Gaussian (`exp(−t²/(2T²))` after
Fourier–Mellin bookkeeping).

**Target identity (finite height `|t| ≤ 2T`, truncation `M`):**

`∑_{1≤N≤M} K_T(N;M) · a_N
  = (1/2π) ∫_{-2T}^{2T} F_M(σ₀+it) / (σ₀+it) · G_T(t) dt + ε_M(σ₀,T)`

where `ε_M` collects (i) finite-index truncation, (ii) vertical tails `|t| > 2T` (Subgoal C),
and (iii) discrete ↔ continuous Gaussian bookkeeping.

**Proof roadmap**

1. **Fourier:** `K_T` is a heat kernel on `ℤ`; `𝓕[K_T](ξ) = T√(2π) · exp(−T²ξ²/2)`.
2. **Poisson / discrete–continuous:** `∑_N K(N−M) f(N)` as convolution on the ladder.
3. **Mellin bridge:** Perron line `s = σ₀+it` links Mellin inversion with Fourier mode `e^{itξ}`.
4. **Contour shift:** extend to `∫ F_M(s) x^s/s` with `x = 1`; holomorphy of `F_M` on `Re s > 0`.
5. **Truncation:** finite `M` and finite height produce explicit `ε_M`; tail to right edge.

Lean packages the `x = 1`, finite-height version as
`GoldbachMidpointGaussianKernelMellinInversionHypothesis`; pure-kernel lemmas (no `F_M`)
are split below for modular proof.
-/

/--
Continuous vertical heat kernel `exp(−t² / (2T²))` (same scale as `goldbachMidpointGaussianSmoother`).
-/
noncomputable def goldbachGaussianVerticalHeatKernel (T t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / (2 * T ^ 2))

/--
ℕ prefix of the centred Gaussian smoother at height `T`:

`∑_{0 ≤ n < M} exp(−n² / (2T²))`.
-/
noncomputable def goldbachMidpointGaussianNatPrefixSum (M : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, Real.exp (-((n : ℝ) ^ 2) / (2 * T ^ 2))

/--
Centred truncated Gaussian weight sum on the midpoint ladder:

`∑_{1≤N≤M} K_T(N;M)`.
-/
noncomputable def goldbachMidpointGaussianCenteredTruncatedSum (M : ℕ) (T : ℝ) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, goldbachMidpointGaussianKernel T M N

/--
Truncated discrete Gaussian weight sum on the midpoint ladder.

Definitional alias of the centred sum `∑_{1≤N≤M} K_T(N;M)`; equals the ℕ prefix
`goldbachMidpointGaussianNatPrefixSum M T` by reindex `n = M - N`.
-/
noncomputable def goldbachMidpointGaussianKernelTruncatedSum (M : ℕ) (T : ℝ) : ℝ :=
  goldbachMidpointGaussianCenteredTruncatedSum M T

private lemma goldbach_midpoint_gaussian_icc_one_eq_ico_succ (M : ℕ) :
    Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]

theorem goldbach_midpoint_gaussian_centered_truncated_sum_eq_nat_prefix (M T : ℕ) :
    goldbachMidpointGaussianCenteredTruncatedSum M (T : ℝ) =
      goldbachMidpointGaussianNatPrefixSum M (T : ℝ) := by
  dsimp [goldbachMidpointGaussianCenteredTruncatedSum, goldbachMidpointGaussianNatPrefixSum,
    goldbachMidpointGaussianKernel]
  rcases M with _ | M
  · simp
  · refine Finset.sum_nbij' (fun N => M + 1 - N) (fun n => M + 1 - n) ?_ ?_ ?_ ?_ ?_
    · intro N hN
      simp only [Finset.mem_Icc, Finset.mem_range] at hN ⊢
      omega
    · intro n hn
      simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
      omega
    · intro N hN
      simp only [Finset.mem_Icc] at hN
      exact Nat.sub_sub_self hN.2
    · intro n hn
      simp only [Finset.mem_range] at hn
      exact Nat.sub_sub_self (Nat.le_of_lt hn)
    · intro N hN
      simp only [Finset.mem_Icc] at hN
      rw [Nat.cast_sub hN.2]
      ring_nf

theorem goldbach_midpoint_gaussian_kernel_truncated_sum_eq_nat_prefix (M T : ℕ) :
    goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) =
      goldbachMidpointGaussianNatPrefixSum M (T : ℝ) := by
  dsimp [goldbachMidpointGaussianKernelTruncatedSum]
  exact goldbach_midpoint_gaussian_centered_truncated_sum_eq_nat_prefix M T

theorem goldbach_midpoint_gaussian_kernel_truncated_sum_eq_centered (M T : ℕ) :
    goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) =
      goldbachMidpointGaussianCenteredTruncatedSum M (T : ℝ) := rfl

/--
Centred truncated Fejér weight sum on the midpoint ladder: `∑_{1≤N≤M} K_T^{Fejér}(N;M)`.
-/
noncomputable def goldbachMidpointFejerKernelTruncatedSum (M : ℕ) (T : ℝ) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, goldbachMidpointFejerKernel T M N

theorem goldbach_midpoint_fejer_kernel_le_one (scale : ℝ) (center N : ℕ) (hscale : 0 < scale) :
    goldbachMidpointFejerKernel scale center N ≤ 1 := by
  dsimp [goldbachMidpointFejerKernel]
  rw [max_le_iff]
  constructor
  · norm_num
  · have habs : 0 ≤ |((N : ℝ) - center)| / scale :=
      div_nonneg (abs_nonneg _) hscale.le
    linarith

theorem goldbach_midpoint_fejer_kernel_truncated_sum_ge_one (M : ℕ) (T : ℝ) (hM : 0 < M) :
    (1 : ℝ) ≤ goldbachMidpointFejerKernelTruncatedSum M T := by
  dsimp [goldbachMidpointFejerKernelTruncatedSum]
  have hMmem : M ∈ Finset.Icc 1 M := by
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_of_lt hM, le_rfl⟩
  calc (1 : ℝ)
      = goldbachMidpointFejerKernel T M M := by
        dsimp [goldbachMidpointFejerKernel]
        simp
    _ ≤ ∑ N ∈ Finset.Icc 1 M, goldbachMidpointFejerKernel T M N :=
      Finset.single_le_sum (fun N _ => goldbach_midpoint_fejer_kernel_nonneg T M N) hMmem

/--
Smoothed Fejér target minus pure kernel mass equals Fejér aggregate coupling.
-/
theorem goldbach_fejer_smoothed_perron_discrete_target_kernel_gap_eq (M : ℕ) (T : ℝ) (hT : 0 < T) :
    goldbachFejerSmoothedPerronDiscreteTarget M T hT -
        goldbachMidpointFejerKernelTruncatedSum M T =
      goldbachFejerSmoothedAggregateCouplingSum M T hT := by
  dsimp [goldbachFejerSmoothedPerronDiscreteTarget, goldbachSmoothedPerronDiscreteTarget,
    goldbachMidpointFejerSmoother, goldbachMidpointFejerKernelTruncatedSum,
    goldbachFejerSmoothedAggregateCouplingSum, GoldbachMidpointSmoother.kernel]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun N _ => by ring_nf

/--
Smoothed target minus pure kernel mass equals aggregate coupling
`∑_{1≤N≤M} K_T(N;M) · (a_N − 1)`.
-/
theorem goldbach_smoothed_perron_discrete_target_kernel_gap_eq (M : ℕ) (T : ℝ) (hT : 0 < T) :
    goldbachGaussianSmoothedPerronDiscreteTarget M T hT -
        goldbachMidpointGaussianKernelTruncatedSum M T =
      goldbachGaussianSmoothedAggregateCouplingSum M T hT := by
  dsimp [goldbachGaussianSmoothedPerronDiscreteTarget, goldbachSmoothedPerronDiscreteTarget,
    goldbachMidpointGaussianSmoother, goldbachMidpointGaussianKernelTruncatedSum,
    goldbachMidpointGaussianCenteredTruncatedSum, goldbachGaussianSmoothedAggregateCouplingSum,
    GoldbachMidpointSmoother.kernel]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun N _ => by ring_nf

/-! ## Aggregate coupling bounds (structural Goldbach mass vs Mellin slack) -/

/--
Explicit coupling bound template:

`B_{M,0} + ∑_{N≤M} K_T(N;M)` — separates unweighted Goldbach mass from kernel mass.
The decay-weighted `B_{M,σ₀}` from vertical growth is **not** a valid upper bound on
coupling (coupling scales with raw `a_N`, not `(2N)^{−σ} a_N`).
-/
noncomputable def goldbachGaussianSmoothedAggregateCouplingBound (M : ℕ) (T : ℝ) : ℝ :=
  goldbachMidpointGeometricUnweightedMass M +
    goldbachMidpointGaussianKernelTruncatedSum M T

theorem goldbach_gaussian_smoothed_aggregate_coupling_bound_nonneg (M : ℕ) (T : ℝ) :
    0 ≤ goldbachGaussianSmoothedAggregateCouplingBound M T := by
  dsimp [goldbachGaussianSmoothedAggregateCouplingBound]
  apply add_nonneg
  · exact goldbach_midpoint_geometric_unweighted_mass_nonneg M
  · dsimp [goldbachMidpointGaussianKernelTruncatedSum, goldbachMidpointGaussianCenteredTruncatedSum]
    refine Finset.sum_nonneg fun N _ =>
      goldbach_midpoint_gaussian_kernel_nonneg T M N

noncomputable def goldbachGaussianSmoothedAggregateCouplingBoundNat (M T : ℕ) (_hT : 1 ≤ T) : ℝ :=
  goldbachGaussianSmoothedAggregateCouplingBound M (T : ℝ)

/--
Centered coupling bound: at `N = M` the kernel equals `1`, so off-center mass is
`(∑ K − 1) · (B_{M,0} + 1)` plus the on-center term `|a_M − 1| ≤ a_M + 1`.
Tighter when `T` is small and the kernel concentrates at the truncation point.
-/
noncomputable def goldbachGaussianSmoothedAggregateCouplingCenteredBound (M : ℕ) (T : ℝ) : ℝ :=
  goldbachMidpointGeometricAggregate M + 1 +
    (goldbachMidpointGeometricUnweightedMass M + 1) *
      max 0 (goldbachMidpointGaussianKernelTruncatedSum M T - 1)

theorem goldbach_gaussian_smoothed_aggregate_coupling_centered_bound_nonneg (M : ℕ) (T : ℝ) :
    0 ≤ goldbachGaussianSmoothedAggregateCouplingCenteredBound M T := by
  dsimp [goldbachGaussianSmoothedAggregateCouplingCenteredBound]
  apply add_nonneg
  · exact add_nonneg (goldbach_midpoint_geometric_aggregate_nonneg M) zero_le_one
  · apply mul_nonneg
    · exact add_nonneg (goldbach_midpoint_geometric_unweighted_mass_nonneg M) zero_le_one
    · exact le_max_left _ _

theorem goldbach_midpoint_gaussian_kernel_le_one (scale : ℝ) (center N : ℕ) :
    goldbachMidpointGaussianKernel scale center N ≤ 1 := by
  dsimp [goldbachMidpointGaussianKernel]
  have hnonpos : -((N : ℝ) - center) ^ 2 / (2 * scale ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    exact mul_nonneg (by norm_num) (sq_nonneg scale)
  exact (Real.exp_le_one_iff).mpr hnonpos

private theorem goldbach_midpoint_geometric_aggregate_minus_one_abs_le (N : ℕ) :
    |goldbachMidpointGeometricAggregate N - 1| ≤ goldbachMidpointGeometricAggregate N + 1 := by
  have hnonneg := goldbach_midpoint_geometric_aggregate_nonneg N
  rcases le_total (goldbachMidpointGeometricAggregate N) 1 with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith

theorem goldbach_midpoint_gaussian_kernel_truncated_sum_ge_one (M : ℕ) (T : ℝ) (hM : 0 < M) :
    (1 : ℝ) ≤ goldbachMidpointGaussianKernelTruncatedSum M T := by
  dsimp [goldbachMidpointGaussianKernelTruncatedSum, goldbachMidpointGaussianCenteredTruncatedSum]
  have hMmem : M ∈ Finset.Icc 1 M := by
    simp only [Finset.mem_Icc]
    exact ⟨Nat.one_le_of_lt hM, le_rfl⟩
  calc (1 : ℝ)
      = goldbachMidpointGaussianKernel T M M := by
        dsimp [goldbachMidpointGaussianKernel]
        simp
    _ ≤ ∑ N ∈ Finset.Icc 1 M, goldbachMidpointGaussianKernel T M N :=
      Finset.single_le_sum (fun N _ => goldbach_midpoint_gaussian_kernel_nonneg T M N) hMmem

theorem goldbach_gaussian_smoothed_aggregate_coupling_sum_abs_le (M : ℕ) (T : ℝ) (hT : 0 < T) :
    |goldbachGaussianSmoothedAggregateCouplingSum M T hT| ≤
      goldbachGaussianSmoothedAggregateCouplingBound M T := by
  set B₀ := goldbachMidpointGeometricUnweightedMass M
  set mass := goldbachMidpointGaussianKernelTruncatedSum M T
  have hterm :
      ∀ N ∈ Finset.Icc 1 M,
        |goldbachMidpointGeometricAggregate N - 1| ≤ goldbachMidpointGeometricAggregate N + 1 :=
    fun N _ => goldbach_midpoint_geometric_aggregate_minus_one_abs_le N
  have hkernel :
      ∀ N ∈ Finset.Icc 1 M, goldbachMidpointGaussianKernel T M N ≤ 1 :=
    fun N _ => goldbach_midpoint_gaussian_kernel_le_one T M N
  have hweighted :
      ∑ N ∈ Finset.Icc 1 M,
          goldbachMidpointGaussianKernel T M N * goldbachMidpointGeometricAggregate N ≤ B₀ := by
    dsimp [B₀, goldbachMidpointGeometricUnweightedMass, goldbachMidpointGeometricCoefficientSum]
    refine Finset.sum_le_sum fun N hN => ?_
    exact
      mul_le_of_le_one_left (goldbach_midpoint_geometric_aggregate_nonneg N) (hkernel N hN)
  calc
    |goldbachGaussianSmoothedAggregateCouplingSum M T hT|
        = |∑ N ∈ Finset.Icc 1 M,
            goldbachMidpointGaussianKernel T M N *
              (goldbachMidpointGeometricAggregate N - 1)| := by
          dsimp [goldbachGaussianSmoothedAggregateCouplingSum]
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
          |goldbachMidpointGaussianKernel T M N *
            (goldbachMidpointGeometricAggregate N - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
          goldbachMidpointGaussianKernel T M N *
            (goldbachMidpointGeometricAggregate N + 1) := by
      refine Finset.sum_le_sum fun N hN => ?_
      have hK := goldbach_midpoint_gaussian_kernel_nonneg T M N
      calc
        |goldbachMidpointGaussianKernel T M N *
            (goldbachMidpointGeometricAggregate N - 1)| =
            goldbachMidpointGaussianKernel T M N *
              |goldbachMidpointGeometricAggregate N - 1| := by
              rw [abs_mul, abs_of_nonneg hK]
        _ ≤ goldbachMidpointGaussianKernel T M N *
              (goldbachMidpointGeometricAggregate N + 1) :=
              mul_le_mul_of_nonneg_left (hterm N hN) hK
    _ = (∑ N ∈ Finset.Icc 1 M,
            goldbachMidpointGaussianKernel T M N * goldbachMidpointGeometricAggregate N) +
          (∑ N ∈ Finset.Icc 1 M, goldbachMidpointGaussianKernel T M N) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun N _ => ?_
      ring
    _ ≤ B₀ + mass := by
      dsimp [mass, goldbachMidpointGaussianKernelTruncatedSum,
        goldbachMidpointGaussianCenteredTruncatedSum]
      linarith [hweighted]

theorem goldbach_gaussian_smoothed_aggregate_coupling_error_le_bound (M : ℕ) (T : ℝ) (hT : 0 < T) :
    goldbachGaussianSmoothedAggregateCouplingError M T hT ≤
      goldbachGaussianSmoothedAggregateCouplingBound M T :=
  goldbach_gaussian_smoothed_aggregate_coupling_sum_abs_le M T hT

theorem goldbach_gaussian_smoothed_aggregate_coupling_error_nat_le_bound (M T : ℕ) (hT : 1 ≤ T) :
    goldbachGaussianSmoothedAggregateCouplingErrorNat M T hT ≤
      goldbachGaussianSmoothedAggregateCouplingBoundNat M T hT := by
  dsimp [goldbachGaussianSmoothedAggregateCouplingErrorNat,
    goldbachGaussianSmoothedAggregateCouplingBoundNat,
    goldbachGaussianSmoothedAggregateCouplingError, goldbachGaussianSmoothedAggregateCouplingBound]
  exact goldbach_gaussian_smoothed_aggregate_coupling_error_le_bound M (T : ℝ)
    (goldbach_gaussian_height_pos_of_one_le T hT)

/-- User-facing alias for the proved coupling bound. -/
theorem goldbach_gaussian_smoothed_aggregate_coupling_bound (M : ℕ) (T : ℝ) (hT : 0 < T) :
    |goldbachGaussianSmoothedAggregateCouplingSum M T hT| ≤
      goldbachGaussianSmoothedAggregateCouplingBound M T :=
  goldbach_gaussian_smoothed_aggregate_coupling_sum_abs_le M T hT

/-! ## Fejér aggregate coupling bounds (same triangle template as Gaussian) -/

noncomputable def goldbachFejerSmoothedAggregateCouplingBound (M : ℕ) (T : ℝ) : ℝ :=
  goldbachMidpointGeometricUnweightedMass M + goldbachMidpointFejerKernelTruncatedSum M T

theorem goldbach_fejer_smoothed_aggregate_coupling_bound_nonneg (M : ℕ) (T : ℝ) :
    0 ≤ goldbachFejerSmoothedAggregateCouplingBound M T := by
  dsimp [goldbachFejerSmoothedAggregateCouplingBound]
  apply add_nonneg
  · exact goldbach_midpoint_geometric_unweighted_mass_nonneg M
  · dsimp [goldbachMidpointFejerKernelTruncatedSum]
    refine Finset.sum_nonneg fun N _ => goldbach_midpoint_fejer_kernel_nonneg T M N

noncomputable def goldbachFejerSmoothedAggregateCouplingBoundNat (M T : ℕ) (_hT : 1 ≤ T) : ℝ :=
  goldbachFejerSmoothedAggregateCouplingBound M (T : ℝ)

theorem goldbach_fejer_smoothed_aggregate_coupling_sum_abs_le (M : ℕ) (T : ℝ) (hT : 0 < T) :
    |goldbachFejerSmoothedAggregateCouplingSum M T hT| ≤
      goldbachFejerSmoothedAggregateCouplingBound M T := by
  set B₀ := goldbachMidpointGeometricUnweightedMass M
  set mass := goldbachMidpointFejerKernelTruncatedSum M T
  have hterm :
      ∀ N ∈ Finset.Icc 1 M,
        |goldbachMidpointGeometricAggregate N - 1| ≤ goldbachMidpointGeometricAggregate N + 1 :=
    fun N _ => goldbach_midpoint_geometric_aggregate_minus_one_abs_le N
  have hkernel :
      ∀ N ∈ Finset.Icc 1 M, goldbachMidpointFejerKernel T M N ≤ 1 :=
    fun N _ => goldbach_midpoint_fejer_kernel_le_one T M N hT
  have hweighted :
      ∑ N ∈ Finset.Icc 1 M,
          goldbachMidpointFejerKernel T M N * goldbachMidpointGeometricAggregate N ≤ B₀ := by
    dsimp [B₀, goldbachMidpointGeometricUnweightedMass, goldbachMidpointGeometricCoefficientSum]
    refine Finset.sum_le_sum fun N hN => ?_
    exact
      mul_le_of_le_one_left (goldbach_midpoint_geometric_aggregate_nonneg N) (hkernel N hN)
  calc
    |goldbachFejerSmoothedAggregateCouplingSum M T hT|
        = |∑ N ∈ Finset.Icc 1 M,
            goldbachMidpointFejerKernel T M N *
              (goldbachMidpointGeometricAggregate N - 1)| := by
          dsimp [goldbachFejerSmoothedAggregateCouplingSum]
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
          |goldbachMidpointFejerKernel T M N *
            (goldbachMidpointGeometricAggregate N - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
          goldbachMidpointFejerKernel T M N *
            (goldbachMidpointGeometricAggregate N + 1) := by
      refine Finset.sum_le_sum fun N hN => ?_
      have hK := goldbach_midpoint_fejer_kernel_nonneg T M N
      calc
        |goldbachMidpointFejerKernel T M N *
            (goldbachMidpointGeometricAggregate N - 1)| =
            goldbachMidpointFejerKernel T M N *
              |goldbachMidpointGeometricAggregate N - 1| := by
              rw [abs_mul, abs_of_nonneg hK]
        _ ≤ goldbachMidpointFejerKernel T M N *
              (goldbachMidpointGeometricAggregate N + 1) :=
              mul_le_mul_of_nonneg_left (hterm N hN) hK
    _ = (∑ N ∈ Finset.Icc 1 M,
            goldbachMidpointFejerKernel T M N * goldbachMidpointGeometricAggregate N) +
          (∑ N ∈ Finset.Icc 1 M, goldbachMidpointFejerKernel T M N) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun N _ => ?_
      ring
    _ ≤ B₀ + mass := by
      dsimp [mass, goldbachMidpointFejerKernelTruncatedSum]
      linarith [hweighted]

theorem goldbach_fejer_smoothed_aggregate_coupling_error_le_bound (M : ℕ) (T : ℝ) (hT : 0 < T) :
    goldbachFejerSmoothedAggregateCouplingError M T hT ≤
      goldbachFejerSmoothedAggregateCouplingBound M T :=
  goldbach_fejer_smoothed_aggregate_coupling_sum_abs_le M T hT

theorem goldbach_fejer_smoothed_aggregate_coupling_error_nat_le_bound (M T : ℕ) (hT : 1 ≤ T) :
    goldbachFejerSmoothedAggregateCouplingErrorNat M T hT ≤
      goldbachFejerSmoothedAggregateCouplingBoundNat M T hT := by
  dsimp [goldbachFejerSmoothedAggregateCouplingErrorNat, goldbachFejerSmoothedAggregateCouplingBoundNat,
    goldbachFejerSmoothedAggregateCouplingError, goldbachFejerSmoothedAggregateCouplingBound]
  exact goldbach_fejer_smoothed_aggregate_coupling_error_le_bound M (T : ℝ)
    (goldbach_gaussian_height_pos_of_one_le T hT)

theorem goldbach_fejer_smoothed_aggregate_coupling_bound (M : ℕ) (T : ℝ) (hT : 0 < T) :
    |goldbachFejerSmoothedAggregateCouplingSum M T hT| ≤
      goldbachFejerSmoothedAggregateCouplingBound M T :=
  goldbach_fejer_smoothed_aggregate_coupling_sum_abs_le M T hT

/--
Gaussian heat-kernel decay parameter `b = 1/(2T²)` for Mathlib's `integral_gaussian`.
-/
noncomputable def goldbachGaussianHeatKernelB (T : ℝ) : ℝ :=
  1 / (2 * T ^ 2)

/--
Classical full-line heat-kernel normalisation `∫_{ℝ} exp(−t²/(2T²)) dt = T√(2π)`.
Named value used in the Fourier–Mellin normalisation step.
-/
noncomputable def goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) : ℝ :=
  T * Real.sqrt (2 * Real.pi)

/--
Finite-height heat-kernel integral on the Perron proxy `|t| ≤ 2T`.
-/
noncomputable def goldbachGaussianHeatKernelVerticalIntegral (T : ℝ) : ℝ :=
  ∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t

/--
Positive tail `∫_{t > 2T} exp(−t²/(2T²)) dt` (one-sided; full tail is twice this).
-/
noncomputable def goldbachGaussianHeatKernelPositiveTailIntegral (T : ℝ) : ℝ :=
  ∫ t in Set.Ioi (2 * T), goldbachGaussianVerticalHeatKernel T t

/--
Full-line minus finite-height proxy: `∫_ℝ G − ∫_{|t|≤2T} G = 2 · ∫_{t>2T} G`.
-/
noncomputable def goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) : ℝ :=
  goldbachGaussianHeatKernelFullLineIntegral T - goldbachGaussianHeatKernelVerticalIntegral T

/--
Half-line heat-kernel mass `∫_{t > 0} exp(−t²/(2T²)) dt = (T√(2π))/2`.
-/
noncomputable def goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ) : ℝ :=
  goldbachGaussianHeatKernelFullLineIntegral T / 2

/--
ℤ Gaussian lattice sum `∑'_{n ∈ ℤ} exp(−n²/(2T²))` (Poisson summation target).
-/
noncomputable def goldbachMidpointGaussianZSum (T : ℕ) : ℝ :=
  ∑' n : ℤ, Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2))

/--
Poisson scale `a = 1/(2πT²)` matching `Real.tsum_exp_neg_mul_int_sq`.
-/
noncomputable def goldbachGaussianPoissonScale (T : ℕ) : ℝ :=
  1 / (2 * Real.pi * (T : ℝ) ^ 2)

/--
Dual ℤ lattice factor from Poisson summation:

`∑'_{n∈ℤ} exp(−π n² / a)` with `a = 1/(2πT²)`.
-/
noncomputable def goldbachGaussianPoissonDualZSum (T : ℕ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (n : ℝ) ^ 2)

/--
ℕ tail beyond the truncation index `M` (shifted form `∑'_{n≥0} exp(−(n+M)²/(2T²))`).
-/
noncomputable def goldbachGaussianZSumNatTailBeyond (M T : ℕ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(((n + M) : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2))

/--
Mirror gap `∑_{0≤n<M} K − 1` (missing negative ℤ indices in the centred prefix).
-/
noncomputable def goldbachGaussianZSumNatMirrorGap (M T : ℕ) : ℝ :=
  goldbachMidpointGaussianNatPrefixSum M T - 1

/--
Poisson dual excess `∑'_{ℤ} exp(−2π²T²n²) − 1` (exponentially small for `T ≥ 1`).
-/
noncomputable def goldbachGaussianPoissonDualExcess (T : ℕ) : ℝ :=
  goldbachGaussianPoissonDualZSum T - 1

/--
Poisson-sharpened A₁ error: mirror gap + doubled ℕ tail + full-line × dual excess.
-/
noncomputable def goldbachGaussianA1PoissonFourierInversionError (M T : ℕ) : ℝ :=
  goldbachGaussianZSumNatMirrorGap M T +
    2 * goldbachGaussianZSumNatTailBeyond M T +
    goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) * goldbachGaussianPoissonDualExcess T

/--
Explicit discrete lattice error: endpoint sum–integral gap (`1`) plus the full-line heat mass.
Provable from antitone sum–integral comparison on `[0,M]`; when `1 ≤ T`, Poisson summation
sharpens the tail via Poisson summation on `goldbachMidpointGaussianZSum`.
-/
noncomputable def goldbachGaussianA0DiscreteLatticeError (M T : ℕ) : ℝ :=
  1 + goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)

/--
Explicit Subgoal A₀ error: vertical tail (beyond `|t| > 2T`) plus discrete lattice term.
-/
noncomputable def goldbachGaussianA0NormalizationError (M T : ℕ) : ℝ :=
  goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) + goldbachGaussianA0DiscreteLatticeError M T

theorem goldbach_gaussian_vertical_heat_kernel_even (T t : ℝ) :
    goldbachGaussianVerticalHeatKernel T (-t) = goldbachGaussianVerticalHeatKernel T t := by
  dsimp [goldbachGaussianVerticalHeatKernel]
  ring_nf

theorem goldbach_gaussian_heat_kernel_b_pos (T : ℝ) (hT : 0 < T) :
    0 < goldbachGaussianHeatKernelB T := by
  dsimp [goldbachGaussianHeatKernelB]
  positivity

theorem goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ goldbachGaussianHeatKernelFullLineIntegral T := by
  dsimp [goldbachGaussianHeatKernelFullLineIntegral]
  positivity

theorem goldbach_gaussian_heat_kernel_vertical_integral_nonneg_nat (T : ℕ) :
    0 ≤ goldbachGaussianHeatKernelVerticalIntegral (T : ℝ) := by
  dsimp [goldbachGaussianHeatKernelVerticalIntegral]
  have hTnonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  refine intervalIntegral.integral_nonneg (by linarith [hTnonneg]) ?_
  intro t ht
  simp only [Set.mem_Icc] at ht
  exact Real.exp_nonneg _

theorem goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq (T t : ℝ) :
    goldbachGaussianVerticalHeatKernel T t =
      Real.exp (-goldbachGaussianHeatKernelB T * t ^ 2) := by
  dsimp [goldbachGaussianVerticalHeatKernel, goldbachGaussianHeatKernelB]
  ring_nf

theorem goldbach_gaussian_heat_kernel_full_line_integral_eq (T : ℝ) (hT : 0 < T) :
    ∫ t : ℝ, goldbachGaussianVerticalHeatKernel T t = goldbachGaussianHeatKernelFullLineIntegral T := by
  have hform :
      (fun t : ℝ => goldbachGaussianVerticalHeatKernel T t) =
        fun t : ℝ => Real.exp (-goldbachGaussianHeatKernelB T * t ^ 2) := by
    funext t
    exact goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq T t
  rw [hform, integral_gaussian (goldbachGaussianHeatKernelB T)]
  dsimp [goldbachGaussianHeatKernelFullLineIntegral, goldbachGaussianHeatKernelB]
  have hden : (1 / (2 * T ^ 2)) ≠ 0 := by positivity
  have hsqrt_div :
      Real.sqrt (Real.pi / (1 / (2 * T ^ 2))) = Real.sqrt (Real.pi * (2 * T ^ 2)) := by
    congr 1
    field_simp [hden]
  rw [hsqrt_div, Real.sqrt_mul Real.pi_pos.le (2 * T ^ 2)]
  rw [Real.sqrt_mul' (2) (sq_nonneg T), Real.sqrt_sq (le_of_lt hT)]
  conv_rhs => rw [show (2 : ℝ) * Real.pi = Real.pi * 2 by ring, Real.sqrt_mul Real.pi_pos.le (2 : ℝ)]
  ring_nf

theorem goldbach_gaussian_vertical_heat_kernel_antitone_on_Icc (T M : ℕ) :
    AntitoneOn (goldbachGaussianVerticalHeatKernel (T : ℝ)) (Set.Icc 0 (M : ℝ)) := by
  intro x hx y hy hxy
  dsimp [goldbachGaussianVerticalHeatKernel]
  have hdiv :
      -(y ^ 2) / (2 * (T : ℝ) ^ 2) ≤ -(x ^ 2) / (2 * (T : ℝ) ^ 2) := by
    gcongr
    nlinarith [hx.1, hxy, hy.2]
  exact (Real.exp_le_exp).mpr hdiv

theorem goldbach_gaussian_heat_kernel_half_line_integral_eq (T : ℝ) (hT : 0 < T) :
    ∫ x in Set.Ioi (0 : ℝ), goldbachGaussianVerticalHeatKernel T x =
      goldbachGaussianHeatKernelHalfLineIntegral T := by
  have hform :
      (fun x : ℝ => goldbachGaussianVerticalHeatKernel T x) =
        fun x : ℝ => Real.exp (-goldbachGaussianHeatKernelB T * x ^ 2) := by
    funext x
    exact goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq T x
  rw [hform, integral_gaussian_Ioi (goldbachGaussianHeatKernelB T)]
  dsimp [goldbachGaussianHeatKernelHalfLineIntegral, goldbachGaussianHeatKernelFullLineIntegral,
    goldbachGaussianHeatKernelB]
  have hden : (1 / (2 * T ^ 2)) ≠ 0 := by positivity
  have hsqrt_div :
      Real.sqrt (Real.pi / (1 / (2 * T ^ 2))) = Real.sqrt (Real.pi * (2 * T ^ 2)) := by
    congr 1
    field_simp [hden]
  rw [hsqrt_div, Real.sqrt_mul Real.pi_pos.le (2 * T ^ 2)]
  rw [Real.sqrt_mul' (2) (sq_nonneg T), Real.sqrt_sq (le_of_lt hT)]
  conv_rhs => rw [show (2 : ℝ) * Real.pi = Real.pi * 2 by ring, Real.sqrt_mul Real.pi_pos.le (2 : ℝ)]
  ring_nf

theorem goldbach_gaussian_heat_kernel_interval_le_half_line (T M : ℕ) (hT : 0 < T) :
    (∫ x in (0 : ℝ)..(M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x) ≤
      goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ) := by
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hf_int : Integrable (goldbachGaussianVerticalHeatKernel (T : ℝ)) volume := by
    have hform : goldbachGaussianVerticalHeatKernel (T : ℝ) =
        fun x => Real.exp (-goldbachGaussianHeatKernelB (T : ℝ) * x ^ 2) := by
      funext x
      exact goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq (T : ℝ) x
    rw [hform]
    exact integrable_exp_neg_mul_sq (goldbach_gaussian_heat_kernel_b_pos (T : ℝ) (Nat.cast_pos.mpr hT))
  have hsubset : Set.Ioc (0 : ℝ) (M : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    simp only [Set.mem_Ioc, Set.mem_Ioi] at hx ⊢
    exact hx.1
  have hint :
      IntegrableOn (goldbachGaussianVerticalHeatKernel (T : ℝ)) (Set.Ioi (0 : ℝ)) volume :=
    hf_int.integrableOn
  have hle :
      (∫ x in Set.Ioc (0 : ℝ) (M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x) ≤
        ∫ x in Set.Ioi (0 : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ => Real.exp_nonneg _)
      (HasSubset.Subset.eventuallyLE hsubset)
  have hinterval :
      (∫ x in (0 : ℝ)..(M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x) =
        ∫ x in Set.Ioc (0 : ℝ) (M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x := by
    rw [intervalIntegral.integral_of_le hMnonneg]
  rw [hinterval]
  exact hle.trans (le_of_eq (goldbach_gaussian_heat_kernel_half_line_integral_eq (T : ℝ) (Nat.cast_pos.mpr hT)))

/--
Positive tail `∫_{x > M} exp(−x²/(2T²)) dx` (ℕ truncation parameter `M`).
-/
noncomputable def goldbachGaussianHeatKernelNatTailIntegral (T M : ℕ) : ℝ :=
  ∫ x in Set.Ioi (M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x

theorem goldbach_gaussian_heat_kernel_nat_tail_integral_nonneg (T M : ℕ) :
    0 ≤ goldbachGaussianHeatKernelNatTailIntegral T M := by
  dsimp [goldbachGaussianHeatKernelNatTailIntegral]
  refine setIntegral_nonneg measurableSet_Ioi (fun _ _ => Real.exp_nonneg _)

theorem goldbach_gaussian_heat_kernel_nat_tail_integral_le_half_line (T M : ℕ) (hT : 0 < T) :
    goldbachGaussianHeatKernelNatTailIntegral T M ≤
      goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ) := by
  let t : ℝ := (T : ℝ)
  have ht : 0 < t := Nat.cast_pos.mpr hT
  have hf_int : Integrable (goldbachGaussianVerticalHeatKernel t) volume := by
    have hform : goldbachGaussianVerticalHeatKernel t =
        fun x => Real.exp (-goldbachGaussianHeatKernelB t * x ^ 2) := by
      funext x
      exact goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq t x
    rw [hform]
    exact integrable_exp_neg_mul_sq (goldbach_gaussian_heat_kernel_b_pos t ht)
  have hsubset : Set.Ioi (M : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith [hx, hMnonneg]
  have hint :
      IntegrableOn (goldbachGaussianVerticalHeatKernel t) (Set.Ioi (0 : ℝ)) volume :=
    hf_int.integrableOn
  have hle :
      (∫ x in Set.Ioi (M : ℝ), goldbachGaussianVerticalHeatKernel t x) ≤
        ∫ x in Set.Ioi (0 : ℝ), goldbachGaussianVerticalHeatKernel t x :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ => Real.exp_nonneg _)
      (HasSubset.Subset.eventuallyLE hsubset)
  dsimp [goldbachGaussianHeatKernelNatTailIntegral, goldbachGaussianHeatKernelHalfLineIntegral]
  calc
    goldbachGaussianHeatKernelNatTailIntegral T M ≤
        ∫ x in Set.Ioi (0 : ℝ), goldbachGaussianVerticalHeatKernel t x := hle
    _ = goldbachGaussianHeatKernelHalfLineIntegral t :=
      goldbach_gaussian_heat_kernel_half_line_integral_eq t ht

theorem goldbach_midpoint_gaussian_nat_prefix_sum_nonneg (M T : ℕ) :
    0 ≤ goldbachMidpointGaussianNatPrefixSum M T := by
  dsimp [goldbachMidpointGaussianNatPrefixSum]
  apply Finset.sum_nonneg
  intro n _
  exact Real.exp_nonneg _

private lemma goldbach_gaussian_nat_prefix_sum_range_shift (f : ℝ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, f ((i + 1 : ℕ) : ℝ)) =
      (∑ i ∈ Finset.range m, f (i : ℝ)) + f (m : ℝ) - f 0 := by
  induction m with
  | zero => simp
  | succ k ih => {
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [Nat.cast_add]
    ring
  }

private lemma goldbach_gaussian_nat_prefix_sum_succ_shift (f : ℝ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), f ((i + 1 : ℕ) : ℝ)) =
      (∑ n ∈ Finset.range (N + 1), f (n : ℝ)) + f ((N + 1 : ℕ) : ℝ) - f 0 := by
  rw [Finset.sum_range_succ (fun n => f (n : ℝ)),
    Finset.sum_range_succ (fun n => f ((n + 1 : ℕ) : ℝ)),
    goldbach_gaussian_nat_prefix_sum_range_shift f N]
  ring

theorem goldbach_midpoint_gaussian_nat_prefix_le_interval_plus_one (T M : ℕ) (hT : 0 < T) :
    goldbachMidpointGaussianNatPrefixSum M T ≤
      (∫ x in (0 : ℝ)..(M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x) + 1 := by
  set f : ℝ → ℝ := goldbachGaussianVerticalHeatKernel (T : ℝ) with hf
  have hanti' : AntitoneOn f (Set.Icc (0 : ℝ) (0 + (M : ℝ))) := by
    simpa [add_zero, hf] using goldbach_gaussian_vertical_heat_kernel_antitone_on_Icc T M
  dsimp [goldbachMidpointGaussianNatPrefixSum, hf]
  have h0 : f 0 = 1 := by
    dsimp [f, goldbachGaussianVerticalHeatKernel]
    simp
  match M with
  | 0 => simp [h0]
  | N + 1 => {
    have hsumle :=
      @AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := N + 1) (f := f) hanti'
    have hsumle' :
        (∑ i ∈ Finset.range (N + 1), f ((i + 1 : ℕ) : ℝ)) ≤
          ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), f x := by
      simpa [zero_add, Nat.cast_add, Nat.cast_one] using hsumle
    have hfN : 0 ≤ f ((N + 1 : ℕ) : ℝ) := Real.exp_nonneg _
    have hsum_shift := goldbach_gaussian_nat_prefix_sum_succ_shift f N
    have hstep :
        (∑ n ∈ Finset.range (N + 1), f (n : ℝ)) ≤
          (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), f x) - f ((N + 1 : ℕ) : ℝ) + f 0 := by
      linarith [hsum_shift, hsumle']
    calc (∑ n ∈ Finset.range (N + 1), f (n : ℝ))
        ≤ (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), f x) - f ((N + 1 : ℕ) : ℝ) + f 0 := hstep
      _ ≤ (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), f x) + 1 := by linarith [hfN, h0]
  }

theorem goldbach_midpoint_gaussian_nat_prefix_ge_interval (T M : ℕ) (hT : 0 < T) :
    goldbachMidpointGaussianNatPrefixSum M T ≥
      ∫ x in (0 : ℝ)..(M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x := by
  have hanti' : AntitoneOn (goldbachGaussianVerticalHeatKernel (T : ℝ)) (Set.Icc (0 : ℝ) (0 + (M : ℝ))) := by
    simpa [add_zero] using goldbach_gaussian_vertical_heat_kernel_antitone_on_Icc T M
  have hle :=
    @AntitoneOn.integral_le_sum (x₀ := (0 : ℝ)) (a := M)
      (f := goldbachGaussianVerticalHeatKernel (T : ℝ)) hanti'
  dsimp [goldbachMidpointGaussianNatPrefixSum, goldbachGaussianVerticalHeatKernel] at hle ⊢
  simp only [zero_add] at hle
  exact hle

theorem goldbach_midpoint_gaussian_nat_prefix_near_half_line (T M : ℕ) (hT : 0 < T) :
    |goldbachMidpointGaussianNatPrefixSum M T -
        goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ)| ≤
      1 + goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ) := by
  have hinterval_le := goldbach_gaussian_heat_kernel_interval_le_half_line T M hT
  have hlower := goldbach_midpoint_gaussian_nat_prefix_ge_interval T M hT
  have hupper := goldbach_midpoint_gaussian_nat_prefix_le_interval_plus_one T M hT
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hint_nonneg :
      0 ≤ ∫ x in (0 : ℝ)..(M : ℝ), goldbachGaussianVerticalHeatKernel (T : ℝ) x := by
    refine intervalIntegral.integral_nonneg (by linarith [hMnonneg]) ?_
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact Real.exp_nonneg _
  have hhalf_nonneg :
      0 ≤ goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ) := by
    dsimp [goldbachGaussianHeatKernelHalfLineIntegral]
    linarith [goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
      (Nat.cast_nonneg T)]
  rcases le_total (goldbachMidpointGaussianNatPrefixSum M T)
      (goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ)) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hinterval_le, hlower, hint_nonneg, hhalf_nonneg]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hupper, hinterval_le, hhalf_nonneg]

theorem goldbach_midpoint_gaussian_nat_prefix_near_full_line (T M : ℕ) (hT : 0 < T) :
    |goldbachMidpointGaussianNatPrefixSum M T -
        goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| ≤
      goldbachGaussianA0DiscreteLatticeError M T := by
  dsimp [goldbachGaussianA0DiscreteLatticeError]
  set half := goldbachGaussianHeatKernelHalfLineIntegral (T : ℝ)
  set full := goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)
  have hhalf_def : half = full / 2 := by
    dsimp [half, goldbachGaussianHeatKernelHalfLineIntegral]
  have hhalf := goldbach_midpoint_gaussian_nat_prefix_near_half_line T M hT
  have hsplit :=
    abs_sub_le (goldbachMidpointGaussianNatPrefixSum M T) half full
  have hfull_nonneg :
      0 ≤ full := goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
      (Nat.cast_nonneg T)
  have hhalfdist : |half - full| = half := by
    have habs : |full / 2 - full| = full / 2 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hfull_nonneg])]
      ring
    simpa [hhalf_def] using habs
  calc
    |goldbachMidpointGaussianNatPrefixSum M T - full| ≤
        |goldbachMidpointGaussianNatPrefixSum M T - half| + |half - full| := hsplit
    _ ≤ (1 + half) + half := by gcongr <;> linarith [hhalf, hhalfdist]
    _ = 1 + full := by rw [hhalf_def]; ring

theorem goldbach_midpoint_gaussian_kernel_truncated_sum_le_full_line_plus_a0 (M T : ℕ)
    (hT : 0 < T) :
    goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) ≤
      goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
        goldbachGaussianA0DiscreteLatticeError M T := by
  have h := goldbach_midpoint_gaussian_nat_prefix_near_full_line T M hT
  have heq : goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) =
      goldbachMidpointGaussianNatPrefixSum M T := by
    dsimp [goldbachMidpointGaussianKernelTruncatedSum]
    exact goldbach_midpoint_gaussian_kernel_truncated_sum_eq_nat_prefix M T
  rw [heq]
  linarith [abs_le.mp h]

theorem goldbach_gaussian_poisson_a_pos (T : ℕ) (hT : 0 < T) :
    0 < 1 / (2 * Real.pi * (T : ℝ) ^ 2) := by
  positivity

theorem goldbach_gaussian_poisson_scale_eq (T : ℕ) :
    goldbachGaussianPoissonScale T = 1 / (2 * Real.pi * (T : ℝ) ^ 2) := rfl

private lemma goldbach_gaussian_pi_mul_poisson_scale (T : ℕ) :
    Real.pi * goldbachGaussianPoissonScale T = 1 / (2 * (T : ℝ) ^ 2) := by
  dsimp [goldbachGaussianPoissonScale]
  field_simp [Real.pi_ne_zero]

private lemma goldbach_gaussian_full_line_eq_inv_sqrt_poisson_scale (T : ℕ) (hT : 0 < T) :
    goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) =
      (1 : ℝ) / goldbachGaussianPoissonScale T ^ (1 / 2 : ℝ) := by
  dsimp [goldbachGaussianHeatKernelFullLineIntegral, goldbachGaussianPoissonScale]
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hden : 0 < (2 * Real.pi * (T : ℝ) ^ 2) := by positivity
  have hsqrt_rpow : (1 / (2 * Real.pi * (T : ℝ) ^ 2)) ^ (1 / 2 : ℝ) =
      (Real.sqrt (2 * Real.pi * (T : ℝ) ^ 2))⁻¹ := by
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
  rw [hsqrt_rpow, one_div, inv_inv]
  rw [Real.sqrt_mul' (2 * Real.pi) (sq_nonneg (T : ℝ)), Real.sqrt_sq (le_of_lt ht)]
  field_simp [hden.ne', Real.pi_ne_zero, pow_ne_zero (T : ℝ) (Nat.cast_ne_zero.mpr hT.ne')]

private lemma goldbach_gaussian_int_exp_neg_sq_summable {T : ℕ} (hT : 0 < T) :
    Summable fun n : ℤ => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) := by
  apply Summable.congr (summable_pow_mul_jacobiTheta₂_term_bound 0
    (goldbach_gaussian_poisson_a_pos T hT) 0)
  intro n
  dsimp [goldbachGaussianPoissonScale]
  field_simp [Real.pi_ne_zero, pow_ne_zero (T : ℝ) (Nat.cast_ne_zero.mpr hT.ne')]
  ring

private lemma goldbach_gaussian_poisson_dual_zsum_summable {T : ℕ} (hT : 0 < T) :
    Summable fun n : ℤ => Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (n : ℝ) ^ 2) := by
  set a := goldbachGaussianPoissonScale T
  have ha : 0 < a := goldbach_gaussian_poisson_a_pos T hT
  have hinv : 0 < (1 / a) := one_div_pos.mpr ha
  apply Summable.congr (summable_pow_mul_jacobiTheta₂_term_bound 0 hinv 0)
  intro n
  dsimp [a, goldbachGaussianPoissonScale]
  field_simp [Real.pi_ne_zero, pow_ne_zero (T : ℝ) (Nat.cast_ne_zero.mpr hT.ne')]
  ring

theorem goldbach_midpoint_gaussian_zsum_poisson_factor (T : ℕ) (hT : 0 < T) :
    goldbachMidpointGaussianZSum T =
      goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) * goldbachGaussianPoissonDualZSum T := by
  set a := goldbachGaussianPoissonScale T
  have ha : 0 < a := by dsimp [a]; exact goldbach_gaussian_poisson_a_pos T hT
  have hsum_eq :
      (∑' n : ℤ, Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2))) =
        ∑' n : ℤ, Real.exp (-Real.pi * a * (n : ℝ) ^ 2) := by
    refine tsum_congr fun n => ?_
    simp only [a, goldbachGaussianPoissonScale]
    congr 1
    field_simp [Real.pi_ne_zero, pow_ne_zero (T : ℝ) (Nat.cast_ne_zero.mpr hT.ne')]
  dsimp [goldbachMidpointGaussianZSum, goldbachGaussianPoissonDualZSum, a]
  rw [hsum_eq, @Real.tsum_exp_neg_mul_int_sq a ha,
    ← goldbach_gaussian_full_line_eq_inv_sqrt_poisson_scale T hT]

theorem goldbach_gaussian_poisson_dual_zsum_ge_one {T : ℕ} (hT : 0 < T) :
    (1 : ℝ) ≤ goldbachGaussianPoissonDualZSum T := by
  dsimp [goldbachGaussianPoissonDualZSum]
  have hsummable := goldbach_gaussian_poisson_dual_zsum_summable hT
  have hterm :
      (1 : ℝ) =
        Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (0 : ℝ) ^ 2) := by
    simp
  calc
    (1 : ℝ) = Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (0 : ℝ) ^ 2) := hterm
    _ = ∑ n ∈ ({0} : Finset ℤ),
        Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (n : ℝ) ^ 2) := by simp
    _ ≤ ∑' n : ℤ, Real.exp (-Real.pi / goldbachGaussianPoissonScale T * (n : ℝ) ^ 2) :=
      Summable.sum_le_tsum ({0} : Finset ℤ) (fun _ _ => Real.exp_nonneg _) hsummable

theorem goldbach_gaussian_poisson_dual_excess_nonneg {T : ℕ} (hT : 0 < T) :
    0 ≤ goldbachGaussianPoissonDualExcess T := by
  dsimp [goldbachGaussianPoissonDualExcess]
  linarith [goldbach_gaussian_poisson_dual_zsum_ge_one hT]

theorem goldbach_gaussian_a1_poisson_fourier_inversion_error_nonneg {M T : ℕ} (hM : 0 < M) (hT : 0 < T) :
    0 ≤ goldbachGaussianA1PoissonFourierInversionError M T := by
  dsimp [goldbachGaussianA1PoissonFourierInversionError, goldbachGaussianZSumNatMirrorGap,
    goldbachGaussianZSumNatTailBeyond, goldbachGaussianPoissonDualExcess]
  apply add_nonneg
  · apply add_nonneg
    · dsimp [goldbachGaussianZSumNatMirrorGap]
      have hge1 : (1 : ℝ) ≤ goldbachMidpointGaussianNatPrefixSum M T := by
        calc
          (1 : ℝ) = Real.exp (-((0 : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) := by simp
          _ ≤ goldbachMidpointGaussianNatPrefixSum M T := by
            dsimp [goldbachMidpointGaussianNatPrefixSum]
            simpa only [Nat.cast_zero] using
              Finset.single_le_sum
                (f := fun n : ℕ => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)))
                (fun n _ => Real.exp_nonneg _) (Finset.mem_range.mpr hM)
      linarith
    · apply mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      refine tsum_nonneg fun n => Real.exp_nonneg _
  · apply mul_nonneg (goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
      (Nat.cast_nonneg T))
    exact goldbach_gaussian_poisson_dual_excess_nonneg hT

private lemma goldbach_gaussian_nat_exp_neg_sq_summable {T : ℕ} (hT : 0 < T) :
    Summable fun n : ℕ => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) := by
  simpa using (goldbach_gaussian_int_exp_neg_sq_summable hT).comp_injective Nat.cast_injective

private lemma goldbach_gaussian_zsum_eq_one_add_twice_nat_tail {T : ℕ} (hT : 0 < T) :
    goldbachMidpointGaussianZSum T =
      1 + 2 * ∑' n : ℕ, Real.exp (-(((n + 1) : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) := by
  set f : ℤ → ℝ := fun n => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2))
  have hEven : Function.Even f := by
    intro n
    dsimp [f]
    push_cast
    ring_nf
  have hf : Summable f := goldbach_gaussian_int_exp_neg_sq_summable hT
  have hf1 : Summable fun n : ℕ => f (n + 1) := by
    have h :=
      (goldbach_gaussian_nat_exp_neg_sq_summable hT).comp_injective Nat.succ_injective
    refine Summable.congr h ?_
    intro n
    simp [f, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hneg_eq : ∀ n : ℕ, f (-(n + 1)) = f (n + 1) := fun n => hEven (n + 1)
  have hf2 : Summable fun n : ℕ => f (-(n + 1)) := hf1.congr fun n => (hneg_eq n).symm
  have hf0 : f 0 = 1 := by dsimp [f]; simp
  have hneg_tail : ∑' n : ℕ, f (-(n + 1)) = ∑' n : ℕ, f (n + 1) := by
    refine tsum_congr fun n => hneg_eq n
  have hz :
      ∑' n : ℤ, f n = 1 + 2 * ∑' n : ℕ, f (n + 1) := by
    calc
      ∑' n : ℤ, f n
          = (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
        tsum_of_add_one_of_neg_add_one hf1 hf2
      _ = 1 + 2 * ∑' n : ℕ, f (n + 1) := by
        rw [hf0, hneg_tail]
        ring_nf
  simpa [goldbachMidpointGaussianZSum, f] using hz

private lemma goldbach_gaussian_zsum_nat_prefix_gap_eq {M T : ℕ} (hM : 0 < M) (hT : 0 < T) :
    goldbachMidpointGaussianZSum T - goldbachMidpointGaussianNatPrefixSum M T =
      goldbachGaussianZSumNatMirrorGap M T + 2 * goldbachGaussianZSumNatTailBeyond M T := by
  set g : ℕ → ℝ := fun n => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2))
  have hg : Summable g := goldbach_gaussian_nat_exp_neg_sq_summable hT
  have hg0 : g 0 = 1 := by simp [g]
  have hsplit :
      (∑ n ∈ Finset.range M, g n) + ∑' n : ℕ, g (n + M) = ∑' n : ℕ, g n :=
    hg.sum_add_tsum_nat_add M
  have hpos1 : ∑' n : ℕ, g (n + 1) = (∑' n : ℕ, g n) - 1 := by
    linarith [hg.tsum_eq_zero_add, hg0]
  have hz := goldbach_gaussian_zsum_eq_one_add_twice_nat_tail hT
  have htail_eq :
      ∑' n : ℕ, Real.exp (-(((n + M) : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) =
        ∑' n : ℕ, g (n + M) := by
    congr 1; funext n; simp [g]
  have hpos_eq :
      ∑' n : ℕ, Real.exp (-(((n + 1) : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) =
        ∑' n : ℕ, g (n + 1) := by
    congr 1; funext n; simp [g]
  dsimp [goldbachMidpointGaussianNatPrefixSum, goldbachGaussianZSumNatMirrorGap,
    goldbachGaussianZSumNatTailBeyond, g] at hz ⊢
  rw [hz, hpos_eq, hpos1, htail_eq]
  linarith [hsplit]

theorem goldbach_midpoint_gaussian_nat_prefix_fourier_gap_le_poisson_error
    (M T : ℕ) (hM : 0 < M) (hT : 0 < T) :
    |goldbachMidpointGaussianNatPrefixSum M T -
        goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| ≤
      goldbachGaussianA1PoissonFourierInversionError M T := by
  set full := goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)
  set latticeZ := goldbachMidpointGaussianZSum T
  set natPrefix := goldbachMidpointGaussianNatPrefixSum M T
  have hsplit := abs_sub_le natPrefix latticeZ full
  have hZfull :
      |latticeZ - full| = full * goldbachGaussianPoissonDualExcess T := by
    have hpoisson := goldbach_midpoint_gaussian_zsum_poisson_factor T hT
    have hdual := goldbach_gaussian_poisson_dual_zsum_ge_one hT
    have hfull_nonneg :=
      goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ) (Nat.cast_nonneg T)
    dsimp only [goldbachGaussianPoissonDualExcess, latticeZ, full]
    calc
      |goldbachMidpointGaussianZSum T - goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)|
          = |goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) * goldbachGaussianPoissonDualZSum T -
              goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| := by rw [← hpoisson]
      _ = |goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) *
            (goldbachGaussianPoissonDualZSum T - 1)| := by
            congr 1
            ring_nf
      _ = goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) *
            (goldbachGaussianPoissonDualZSum T - 1) := by
            rw [abs_mul, abs_of_nonneg hfull_nonneg, abs_of_nonneg (sub_nonneg.mpr hdual)]
  have hprefixZ :
      |latticeZ - natPrefix| =
        goldbachGaussianZSumNatMirrorGap M T + 2 * goldbachGaussianZSumNatTailBeyond M T := by
    have hgap := goldbach_gaussian_zsum_nat_prefix_gap_eq hM hT
    have hnonneg_tail : 0 ≤ goldbachGaussianZSumNatTailBeyond M T := by
      refine tsum_nonneg fun n => Real.exp_nonneg _
    have hnonneg_gap : 0 ≤ goldbachGaussianZSumNatMirrorGap M T := by
      dsimp [goldbachGaussianZSumNatMirrorGap]
      have hge1 : (1 : ℝ) ≤ goldbachMidpointGaussianNatPrefixSum M T := by
        calc
          (1 : ℝ) = Real.exp (-((0 : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)) := by simp
          _ ≤ goldbachMidpointGaussianNatPrefixSum M T := by
            dsimp [goldbachMidpointGaussianNatPrefixSum]
            simpa only [Nat.cast_zero] using
              Finset.single_le_sum
                (f := fun n : ℕ => Real.exp (-((n : ℝ) ^ 2) / (2 * (T : ℝ) ^ 2)))
                (fun n _ => Real.exp_nonneg _) (Finset.mem_range.mpr hM)
      linarith
    have hZ_ge : natPrefix ≤ latticeZ := by
      dsimp [natPrefix, latticeZ] at hgap ⊢
      linarith [hgap, hnonneg_gap, hnonneg_tail]
    rw [abs_of_nonneg (sub_nonneg.mpr hZ_ge)]
    dsimp [natPrefix, latticeZ]
    linarith [hgap]
  calc
    |natPrefix - full| ≤ |natPrefix - latticeZ| + |latticeZ - full| := hsplit
    _ = goldbachGaussianZSumNatMirrorGap M T + 2 * goldbachGaussianZSumNatTailBeyond M T +
          full * goldbachGaussianPoissonDualExcess T := by
      rw [← abs_sub_comm latticeZ natPrefix, hprefixZ, hZfull]
    _ = goldbachGaussianA1PoissonFourierInversionError M T := by
      dsimp [goldbachGaussianA1PoissonFourierInversionError]

theorem goldbach_gaussian_heat_kernel_vertical_le_full_line_nat (T : ℕ) (hT : 0 < T) :
    goldbachGaussianHeatKernelVerticalIntegral (T : ℝ) ≤
      goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) := by
  let t : ℝ := (T : ℝ)
  have ht : 0 < t := Nat.cast_pos.mpr hT
  have hhab : -2 * t ≤ 2 * t := by linarith
  have hf_int : Integrable (goldbachGaussianVerticalHeatKernel t) volume := by
    have hform : goldbachGaussianVerticalHeatKernel t =
        fun x => Real.exp (-goldbachGaussianHeatKernelB t * x ^ 2) := by
      funext x
      exact goldbach_gaussian_vertical_heat_kernel_eq_exp_mul_sq t x
    rw [hform]
    exact integrable_exp_neg_mul_sq (goldbach_gaussian_heat_kernel_b_pos t ht)
  have hle_Ioc :
      (∫ x in Set.Ioc (-2 * t) (2 * t), goldbachGaussianVerticalHeatKernel t x) ≤
        ∫ x, goldbachGaussianVerticalHeatKernel t x :=
    integral_mono_measure volume.restrict_le_self
      (Eventually.of_forall fun _ => Real.exp_nonneg _) hf_int
  dsimp [goldbachGaussianHeatKernelVerticalIntegral, goldbachGaussianHeatKernelFullLineIntegral]
  calc
    ∫ t_1 in (-2 * t)..(2 * t), goldbachGaussianVerticalHeatKernel t t_1 ≤
        ∫ x, goldbachGaussianVerticalHeatKernel t x := by
      rw [intervalIntegral.integral_of_le hhab]
      exact hle_Ioc
    _ = goldbachGaussianHeatKernelFullLineIntegral t :=
      goldbach_gaussian_heat_kernel_full_line_integral_eq t ht

theorem goldbach_gaussian_a0_normalization_error_nonneg (M T : ℕ) :
    0 ≤ goldbachGaussianA0NormalizationError M T := by
  dsimp [goldbachGaussianA0NormalizationError, goldbachGaussianHeatKernelVerticalTailBound,
    goldbachGaussianA0DiscreteLatticeError]
  apply add_nonneg
  · match T with
    | 0 =>
      simp [goldbachGaussianHeatKernelVerticalIntegral, goldbachGaussianHeatKernelFullLineIntegral]
    | n + 1 =>
      exact sub_nonneg.mpr (goldbach_gaussian_heat_kernel_vertical_le_full_line_nat (n + 1) (Nat.succ_pos n))
  · apply add_nonneg (by norm_num : 0 ≤ (1 : ℝ))
    exact goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ) (Nat.cast_nonneg T)

theorem goldbach_gaussian_heat_kernel_vertical_tail_bound_nonneg_nat (T : ℕ) (hT : 0 < T) :
    0 ≤ goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) := by
  dsimp [goldbachGaussianHeatKernelVerticalTailBound]
  have hvert := goldbach_gaussian_heat_kernel_vertical_integral_nonneg_nat T
  linarith [goldbach_gaussian_heat_kernel_vertical_le_full_line_nat T hT, hvert]

/--
Even heat kernel: full-line integral equals finite-height proxy plus twice the positive tail.
-/
def GoldbachMidpointGaussianKernelVerticalTailDecompositionHypothesis (T : ℕ) : Prop :=
  0 < T ∧
    goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) =
      2 * goldbachGaussianHeatKernelPositiveTailIntegral (T : ℝ)

/--
**Subgoal A₀ (pure Gaussian, no `F_M`):** truncated discrete kernel mass is within explicit
error of the finite-height continuous heat integral on `|t| ≤ 2T`.
-/
def GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis (M T : ℕ) : Prop :=
  |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
      goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)| ≤
    goldbachGaussianA0NormalizationError M T

/--
Vertical tail beyond `|t| > 2T` is bounded by the explicit tail template (from full-line value).
-/
def GoldbachMidpointGaussianKernelVerticalTailHypothesis (T : ℕ) : Prop :=
  0 < T ∧
    goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) ≤
      goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)

theorem goldbach_midpoint_gaussian_kernel_vertical_tail_hypothesis (T : ℕ) (hT : 0 < T) :
    GoldbachMidpointGaussianKernelVerticalTailHypothesis T := by
  refine ⟨hT, ?_⟩
  dsimp [goldbachGaussianHeatKernelVerticalTailBound]
  linarith [goldbach_gaussian_heat_kernel_vertical_integral_nonneg_nat T,
    goldbach_gaussian_heat_kernel_vertical_le_full_line_nat T hT]

/--
Discrete lattice truncation error (centred Gaussian sum vs full-line heat integral).
Requires `1 ≤ T` so the heat scale is positive and antitone sum–integral comparison applies.
-/
def GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis (M T : ℕ) : Prop :=
  0 < M ∧ 1 ≤ T ∧
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| ≤
      goldbachGaussianA0DiscreteLatticeError M T

theorem goldbach_midpoint_gaussian_kernel_discrete_lattice_hypothesis (M T : ℕ)
    (hM : 0 < M) (hT : 1 ≤ T) :
    GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis M T := by
  refine ⟨hM, hT, ?_⟩
  dsimp [GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis]
  rw [goldbach_midpoint_gaussian_kernel_truncated_sum_eq_nat_prefix]
  exact goldbach_midpoint_gaussian_nat_prefix_near_full_line T M (Nat.succ_le_iff.mpr hT)

theorem goldbach_midpoint_gaussian_kernel_discrete_normalization_of_components
    (M T : ℕ) (htail : GoldbachMidpointGaussianKernelVerticalTailHypothesis T)
    (hlattice : GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis M T) :
    GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis M T := by
  dsimp [GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis,
    GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis,
    GoldbachMidpointGaussianKernelVerticalTailHypothesis,
    goldbachGaussianA0NormalizationError, goldbachGaussianA0DiscreteLatticeError,
    goldbachGaussianHeatKernelVerticalTailBound] at htail hlattice ⊢
  rcases hlattice with ⟨_, _, hlattice⟩
  rcases htail with ⟨hT, _⟩
  calc
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)| ≤
        |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
            goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| +
          |goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) -
            goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ goldbachGaussianA0DiscreteLatticeError M T +
        goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) := by
      gcongr
      · exact hlattice
      · dsimp [goldbachGaussianHeatKernelVerticalTailBound]
        rw [abs_of_nonneg (sub_nonneg.mpr (goldbach_gaussian_heat_kernel_vertical_le_full_line_nat T hT))]
    _ = goldbachGaussianA0NormalizationError M T := by
      dsimp [goldbachGaussianA0NormalizationError, goldbachGaussianA0DiscreteLatticeError]
      rw [add_comm]

theorem goldbach_midpoint_gaussian_kernel_discrete_normalization (M T : ℕ) (hM : 0 < M)
    (hT : 1 ≤ T) :
    GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis M T :=
  goldbach_midpoint_gaussian_kernel_discrete_normalization_of_components M T
    (goldbach_midpoint_gaussian_kernel_vertical_tail_hypothesis T (Nat.succ_le_iff.mpr hT))
    (goldbach_midpoint_gaussian_kernel_discrete_lattice_hypothesis M T hM hT)

/--
Fourier-side reconstruction target for the discrete Gaussian kernel mass.

Provably equals `goldbachMidpointGaussianZSum T` by Poisson summation; packaged here as the
full-line heat integral `T√(2π)` (the `ξ = 0` mode of `𝓕[K_T]`). The truncation index `M`
enters only through the explicit A₁ error budget below.
-/
noncomputable def goldbachMidpointGaussianFourierReconstruction (M T : ℕ) : ℝ :=
  goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)

/--
Explicit error term for Subgoal A₁ (compatible with Subgoal A₀'s `O(1)` lattice budget).
-/
noncomputable def goldbachGaussianA1FourierInversionError (M T : ℕ) : ℝ :=
  2 + goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) / max M 1

theorem goldbach_gaussian_a1_fourier_inversion_error_nonneg (M T : ℕ) :
    0 ≤ goldbachGaussianA1FourierInversionError M T := by
  dsimp [goldbachGaussianA1FourierInversionError]
  apply add_nonneg (by norm_num : 0 ≤ (2 : ℝ))
  apply div_nonneg (goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
    (Nat.cast_nonneg T))
  exact Nat.cast_nonneg (max M 1)

/--
Fourier inversion of the discrete Gaussian kernel on the midpoint index.

The truncated discrete mass `∑_{N=1}^M K_T(N; M)` (packaged as
`goldbachMidpointGaussianKernelTruncatedSum`) matches its Fourier-side reconstruction with an
explicit error compatible with the `O(1)` budget already established in Subgoal A₀.

This is the discrete Fourier inversion step (A₁) before coupling to `F_M` via Mellin.
-/
def GoldbachMidpointGaussianFourierInversionHypothesis (M T : ℕ) : Prop :=
  |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
      goldbachMidpointGaussianFourierReconstruction M T| ≤
    goldbachGaussianA1FourierInversionError M T

theorem goldbach_midpoint_gaussian_fourier_reconstruction_eq_full_line (M T : ℕ) :
    goldbachMidpointGaussianFourierReconstruction M T =
      goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) := by
  dsimp [goldbachMidpointGaussianFourierReconstruction]

/--
Poisson-sharpened Subgoal A₁: truncated discrete mass vs full-line Fourier target,
with explicit mirror + tail + dual-excess budget.
-/
def GoldbachMidpointGaussianFourierInversionPoissonHypothesis (M T : ℕ) : Prop :=
  |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
      goldbachMidpointGaussianFourierReconstruction M T| ≤
    goldbachGaussianA1PoissonFourierInversionError M T

theorem goldbach_midpoint_gaussian_fourier_inversion_poisson (M T : ℕ) (hM : 0 < M) (hT : 0 < T) :
    GoldbachMidpointGaussianFourierInversionPoissonHypothesis M T := by
  dsimp only [GoldbachMidpointGaussianFourierInversionPoissonHypothesis]
  rw [goldbach_midpoint_gaussian_kernel_truncated_sum_eq_nat_prefix,
    goldbach_midpoint_gaussian_fourier_reconstruction_eq_full_line]
  exact goldbach_midpoint_gaussian_nat_prefix_fourier_gap_le_poisson_error M T hM hT

theorem goldbach_midpoint_gaussian_fourier_inversion_of_lattice_error_le
    (M T : ℕ) (hlattice : GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis M T)
    (herr :
      goldbachGaussianA0DiscreteLatticeError M T ≤ goldbachGaussianA1FourierInversionError M T) :
    GoldbachMidpointGaussianFourierInversionHypothesis M T := by
  dsimp [GoldbachMidpointGaussianFourierInversionHypothesis,
    GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis,
    goldbachMidpointGaussianFourierReconstruction, goldbachGaussianA0DiscreteLatticeError] at hlattice herr ⊢
  rcases hlattice with ⟨_, _, hlattice⟩
  exact hlattice.trans herr

theorem goldbach_midpoint_gaussian_fourier_inversion_one (T : ℕ) (hT : 1 ≤ T) :
    GoldbachMidpointGaussianFourierInversionHypothesis 1 T := by
  refine goldbach_midpoint_gaussian_fourier_inversion_of_lattice_error_le 1 T
    (goldbach_midpoint_gaussian_kernel_discrete_lattice_hypothesis 1 T (Nat.one_pos) hT) ?_
  dsimp [goldbachGaussianA0DiscreteLatticeError, goldbachGaussianA1FourierInversionError]
  simp only [show max 1 1 = (1 : ℕ) from max_eq_left (Nat.zero_lt_one), Nat.cast_one,
    div_self (show (1 : ℝ) ≠ 0 from by norm_num)]
  nlinarith [goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
    (Nat.cast_nonneg T)]

/--
Midpoint Gaussian kernel against the truncated generating function on the left vertical line
(complex, unnormalized).
-/
noncomputable def goldbachPerronGaussianLeftVerticalKernelIntegral (M : ℕ) (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T),
    goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) *
      goldbachPerronKernel x (σ₀ + t * I)

/--
Heat-weighted Mellin–Perron integrand on `Re s = σ₀` (Subgoal A₂ analytic core):

`F_M(σ₀+it) · G_T(t) · x^{σ₀+it} / (σ₀+it)` with `G_T(t) = exp(−t²/(2T²))`.
-/
noncomputable def goldbachPerronGaussianHeatWeightedMellinIntegrand (M : ℕ) (σ₀ T x t : ℝ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) *
    goldbachGaussianVerticalHeatKernel T t *
    goldbachPerronKernel x (σ₀ + t * I)

/--
`(F_M − 1)` heat-weighted Mellin integrand (Subgoal A₂.1 analytic core):

`(F_M(σ₀+it) − 1) · G_T(t) · x^{σ₀+it} / (σ₀+it)` on `Re s = σ₀`.
-/
noncomputable def goldbachPerronGaussianFMMinusOneHeatMellinIntegrand (M : ℕ) (σ₀ T x t : ℝ) : ℂ :=
  (goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1) *
    goldbachGaussianVerticalHeatKernel T t *
    goldbachPerronKernel x (σ₀ + t * I)

noncomputable def goldbachPerronGaussianFMMinusOneHeatMellinIntegral (M : ℕ) (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T), goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t

noncomputable def goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachPerronGaussianFMMinusOneHeatMellinIntegral M σ₀ T x).re

/--
Central (`|t| ≤ T`) part of the A₂.1 `(F_M − 1)` heat Mellin integral (normalized real part).
-/
noncomputable def goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ t in (-T)..T, (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re)

/--
Two-ray tail (`T ≤ |t| ≤ 2T` on the finite proxy) of the A₂.1 integrand (normalized).
-/
noncomputable def goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ((∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re) +
      ∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re)

/--
Normalized heat-weighted Mellin pairing on the finite-height proxy `|t| ≤ 2T`:

`(1/2π) ∫_{-2T}^{2T} F_M(σ₀+it) · G_T(t) · x^{σ₀+it} / (σ₀+it) dt` (real part, normalized).
-/
noncomputable def goldbachPerronGaussianMellinPairingAtScale (M : ℕ) (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T), goldbachPerronGaussianHeatWeightedMellinIntegrand M σ₀ T x t

noncomputable def goldbachPerronGaussianMellinPairingAtScaleNormalized (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachPerronGaussianMellinPairingAtScale M σ₀ T x).re

/--
Unit-scale heat-weighted pairing (`x = 1`).
-/
noncomputable def goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernel (M : ℕ) (σ₀ T : ℝ) : ℂ :=
  goldbachPerronGaussianMellinPairingAtScale M σ₀ T 1

noncomputable def goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized
    (M : ℕ) (σ₀ T : ℝ) : ℝ :=
  goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ T 1

/--
Pure-kernel Mellin anchor (no `F_M`): heat profile against the Perron kernel only.
Used to connect A₁ (kernel mass) with the vertical Mellin normalization.
-/
noncomputable def goldbachGaussianHeatKernelMellinAnchor (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T),
    goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel x (σ₀ + t * I)

noncomputable def goldbachGaussianHeatKernelMellinAnchorNormalized (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachGaussianHeatKernelMellinAnchor σ₀ T x).re

/--
Unit-scale (`x = 1`) Perron Mellin anchor on `Re s = σ₀`.
-/
noncomputable def goldbachGaussianHeatKernelMellinAnchorAtUnitScale (σ₀ T : ℝ) : ℝ :=
  goldbachGaussianHeatKernelMellinAnchorNormalized σ₀ T 1

/--
Finite-height heat mass normalized by `1/(2π)` — the immediate Fourier-side proxy on `|t| ≤ 2T`
before the `1/s` Perron weight is applied.
-/
noncomputable def goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * goldbachGaussianHeatKernelVerticalIntegral T

theorem goldbach_gaussian_heat_kernel_vertical_anchor_normalized_nonneg (T : ℕ) :
    0 ≤ goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ) := by
  dsimp [goldbachGaussianHeatKernelVerticalAnchorNormalized]
  exact mul_nonneg (by positivity)
    (goldbach_gaussian_heat_kernel_vertical_integral_nonneg_nat T)

/--
Explicit A₂.0 error budget: Poisson A₁ on the discrete kernel mass plus the vertical heat tail
`|∫_ℝ G − ∫_{|t|≤2T} G|`.
-/
noncomputable def goldbachGaussianA20HeatKernelMellinLinkError (M T : ℕ) : ℝ :=
  goldbachGaussianA1PoissonFourierInversionError M T +
    goldbachGaussianHeatKernelVerticalTailBound (T : ℝ)

theorem goldbach_gaussian_a20_heat_kernel_mellin_link_error_nonneg (M T : ℕ) (hM : 0 < M) (hT : 0 < T) :
    0 ≤ goldbachGaussianA20HeatKernelMellinLinkError M T := by
  dsimp [goldbachGaussianA20HeatKernelMellinLinkError]
  apply add_nonneg
  · exact goldbach_gaussian_a1_poisson_fourier_inversion_error_nonneg hM hT
  · exact goldbach_gaussian_heat_kernel_vertical_tail_bound_nonneg_nat T hT

/--
Gap between the finite-height heat proxy and the `1/s`-weighted Perron Mellin anchor
(Fourier → Mellin translation on the pure Gaussian side).
-/
noncomputable def goldbachGaussianHeatKernelVerticalMellinAnchorGap (σ₀ T : ℝ) : ℝ :=
  |goldbachGaussianHeatKernelVerticalAnchorNormalized T -
      goldbachGaussianHeatKernelMellinAnchorAtUnitScale σ₀ T|

/--
Poisson complement integrand `G_T(t) · |σ₀²+t²−σ₀|/(σ₀²+t²)` on the finite-height proxy.

Since `Re(1/(σ₀+it)) = σ₀/(σ₀²+t²)`, the vertical→Mellin anchor gap equals
`(1/2π) ∫_{|t|≤2T} G_T · |σ₀²+t²−σ₀|/(σ₀²+t²) dt` (Poisson complement mass).
When `1 ≤ σ₀` the complement factor is `≤ 1` pointwise, hence the gap is `≤` the vertical anchor.
-/
noncomputable def goldbachGaussianHeatKernelPoissonWeightIntegrand (σ₀ T t : ℝ) : ℝ :=
  goldbachGaussianVerticalHeatKernel T t * (|σ₀ ^ 2 + t ^ 2 - σ₀| / (σ₀ ^ 2 + t ^ 2))

noncomputable def goldbachGaussianHeatKernelPoissonSignedIntegrand (σ₀ T t : ℝ) : ℝ :=
  goldbachGaussianVerticalHeatKernel T t * ((σ₀ ^ 2 + t ^ 2 - σ₀) / (σ₀ ^ 2 + t ^ 2))

noncomputable def goldbachGaussianHeatKernelPoissonWeightIntegral (σ₀ T : ℝ) : ℝ :=
  ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t

/--
Explicit A₂.0b bridge budget: normalized Poisson-weight mass on `|t| ≤ 2T`.
-/
noncomputable def goldbachGaussianHeatKernelVerticalPoissonBridgeBound (σ₀ T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * goldbachGaussianHeatKernelPoissonWeightIntegral σ₀ T

private theorem goldbach_poisson_den_pos (σ₀ t : ℝ) (hσ₀ : 0 < σ₀) : 0 < σ₀ ^ 2 + t ^ 2 := by
  nlinarith [sq_pos_of_pos hσ₀, sq_nonneg t]

private theorem goldbach_poisson_den_ne_zero (σ₀ t : ℝ) (hσ₀ : 0 < σ₀) : σ₀ ^ 2 + t ^ 2 ≠ 0 :=
  ne_of_gt (goldbach_poisson_den_pos σ₀ t hσ₀)

theorem goldbach_perron_kernel_inv_re (σ t : ℝ) (hσ : 0 < σ) :
    ((1 : ℂ) / ((σ : ℂ) + t * Complex.I)).re = σ / (σ ^ 2 + t ^ 2) := by
  rw [Complex.div_re, Complex.one_re, Complex.one_im, zero_mul]
  simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  field_simp

theorem goldbach_gaussian_heat_kernel_poisson_weight_nonneg (σ₀ T t : ℝ) :
    0 ≤ goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t := by
  dsimp [goldbachGaussianHeatKernelPoissonWeightIntegrand]
  apply mul_nonneg (Real.exp_nonneg _)
  apply div_nonneg (abs_nonneg _) (add_nonneg (sq_nonneg σ₀) (sq_nonneg t))

private theorem goldbach_gaussian_heat_kernel_poisson_complement_le_one (σ₀ t : ℝ) (hσ₁ : 1 ≤ σ₀) :
    |σ₀ ^ 2 + t ^ 2 - σ₀| / (σ₀ ^ 2 + t ^ 2) ≤ 1 := by
  have hden : 0 < σ₀ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ₀, sq_nonneg t]
  have hnum_nonneg : 0 ≤ σ₀ ^ 2 + t ^ 2 - σ₀ := by
    nlinarith [hσ₁, sq_nonneg t, sq_nonneg (σ₀ - 1)]
  rw [abs_of_nonneg hnum_nonneg, div_le_iff₀ hden]
  linarith

private theorem goldbach_gaussian_heat_kernel_continuousOn (T : ℝ) (S : Set ℝ) :
    ContinuousOn (goldbachGaussianVerticalHeatKernel T) S := by
  unfold goldbachGaussianVerticalHeatKernel
  fun_prop

private theorem goldbach_gaussian_heat_kernel_poisson_factor_continuous (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    Continuous (fun t => |σ₀ ^ 2 + t ^ 2 - σ₀| / (σ₀ ^ 2 + t ^ 2)) := by
  have hden : Continuous fun t => σ₀ ^ 2 + t ^ 2 := by continuity
  have hnum : Continuous fun t => |σ₀ ^ 2 + t ^ 2 - σ₀| :=
    continuous_abs.comp (hden.sub continuous_const)
  exact hnum.div hden fun t => goldbach_poisson_den_ne_zero σ₀ t hσ₀

private theorem goldbach_gaussian_heat_kernel_poisson_reciprocal_continuous (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    Continuous (fun t => σ₀ / (σ₀ ^ 2 + t ^ 2)) := by
  have hden : Continuous fun t => σ₀ ^ 2 + t ^ 2 := by continuity
  exact continuous_const.div hden fun t => goldbach_poisson_den_ne_zero σ₀ t hσ₀

private theorem goldbach_gaussian_heat_kernel_poisson_factor_continuousOn (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (S : Set ℝ) :
    ContinuousOn (fun t => |σ₀ ^ 2 + t ^ 2 - σ₀| / (σ₀ ^ 2 + t ^ 2)) S :=
  (goldbach_gaussian_heat_kernel_poisson_factor_continuous σ₀ hσ₀).continuousOn

private theorem goldbach_gaussian_heat_kernel_poisson_signed_factor_continuous (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    Continuous (fun t => (σ₀ ^ 2 + t ^ 2 - σ₀) / (σ₀ ^ 2 + t ^ 2)) := by
  have hden : Continuous fun t => σ₀ ^ 2 + t ^ 2 := by continuity
  exact (hden.sub continuous_const).div hden fun t => goldbach_poisson_den_ne_zero σ₀ t hσ₀

private theorem goldbach_gaussian_heat_kernel_poisson_signed_factor_continuousOn (σ₀ : ℝ) (hσ₀ : 0 < σ₀)
    (S : Set ℝ) :
    ContinuousOn (fun t => (σ₀ ^ 2 + t ^ 2 - σ₀) / (σ₀ ^ 2 + t ^ 2)) S :=
  (goldbach_gaussian_heat_kernel_poisson_signed_factor_continuous σ₀ hσ₀).continuousOn

private theorem goldbach_gaussian_heat_kernel_poisson_weight_continuousOn (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (S : Set ℝ) :
    ContinuousOn (goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T) S := by
  unfold goldbachGaussianHeatKernelPoissonWeightIntegrand
  exact (goldbach_gaussian_heat_kernel_continuousOn T S).mul
    (goldbach_gaussian_heat_kernel_poisson_factor_continuousOn σ₀ hσ₀ S)

private theorem goldbach_gaussian_heat_kernel_poisson_signed_continuousOn (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (S : Set ℝ) :
    ContinuousOn (goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T) S := by
  unfold goldbachGaussianHeatKernelPoissonSignedIntegrand
  exact (goldbach_gaussian_heat_kernel_continuousOn T S).mul
    (goldbach_gaussian_heat_kernel_poisson_signed_factor_continuousOn σ₀ hσ₀ S)

private theorem goldbach_gaussian_heat_kernel_interval_integrable (T : ℝ) :
    IntervalIntegrable (goldbachGaussianVerticalHeatKernel T) volume (-2 * T) (2 * T) :=
  (goldbach_gaussian_heat_kernel_continuousOn T (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_poisson_weight_interval_integrable (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) :
    IntervalIntegrable (goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T) volume
      (-2 * T) (2 * T) :=
  (goldbach_gaussian_heat_kernel_poisson_weight_continuousOn σ₀ T hσ₀
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_poisson_signed_interval_integrable (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) :
    IntervalIntegrable (goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T) volume
      (-2 * T) (2 * T) :=
  (goldbach_gaussian_heat_kernel_poisson_signed_continuousOn σ₀ T hσ₀
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_mellin_integrand_continuousOn (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (S : Set ℝ) :
    ContinuousOn
      (fun t => goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel 1 (σ₀ + t * I)) S :=
  continuous_ofReal.comp_continuousOn (goldbach_gaussian_heat_kernel_continuousOn T S) |>.mul
    (goldbach_perron_kernel_continuousOn_vertical 1 σ₀ hσ₀ (by norm_num) S)

private theorem goldbach_gaussian_heat_kernel_mellin_integrand_interval_integrable
    (σ₀ T : ℝ) (hσ₀ : 0 < σ₀) :
    IntervalIntegrable
      (fun t => goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel 1 (σ₀ + t * I)) volume
      (-2 * T) (2 * T) :=
  (goldbach_gaussian_heat_kernel_mellin_integrand_continuousOn σ₀ T hσ₀
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_scaled_interval_integrable (σ₀ T : ℝ) (hσ₀ : 0 < σ₀) :
    IntervalIntegrable
      (fun t => goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2))) volume
      (-2 * T) (2 * T) := by
  have hscaled :
      ContinuousOn (fun t => σ₀ / (σ₀ ^ 2 + t ^ 2)) (Set.uIcc (-2 * T) (2 * T)) :=
    (goldbach_gaussian_heat_kernel_poisson_reciprocal_continuous σ₀ hσ₀).continuousOn
  exact
    (goldbach_gaussian_heat_kernel_continuousOn T (Set.uIcc (-2 * T) (2 * T))).mul
      hscaled |>.intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_mellin_integrand_re (σ₀ T t : ℝ) (hσ₀ : 0 < σ₀) :
    (goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel 1 (σ₀ + t * I)).re =
      goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2)) := by
  have hs : σ₀ + t * I ≠ 0 := goldbach_vertical_line_ne_zero σ₀ t hσ₀
  calc
    (goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel 1 (σ₀ + t * I)).re
        = goldbachGaussianVerticalHeatKernel T t *
            (goldbachPerronKernel 1 (σ₀ + t * I)).re := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2)) := by
          rw [goldbach_perron_kernel_unit_scale _ hs, goldbach_perron_kernel_inv_re σ₀ t hσ₀]

private theorem goldbach_gaussian_heat_kernel_poisson_signed_eq_weight (σ₀ T t : ℝ) (hσ₁ : 1 ≤ σ₀) :
    goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t =
      goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t := by
  dsimp [goldbachGaussianHeatKernelPoissonSignedIntegrand,
    goldbachGaussianHeatKernelPoissonWeightIntegrand]
  congr 1
  have hnum : 0 ≤ σ₀ ^ 2 + t ^ 2 - σ₀ := by nlinarith [hσ₁, sq_nonneg t, sq_nonneg (σ₀ - 1)]
  rw [abs_of_nonneg hnum]

theorem goldbach_abs_mul_sub_mul (c A B : ℝ) (hc : 0 < c) :
    |c * A - c * B| = c * |A - B| := by
  rw [show c * A - c * B = c * (A - B) from by ring]
  rw [abs_mul, abs_of_pos hc]

theorem goldbach_gaussian_heat_kernel_mellin_anchor_re_eq_poisson (σ₀ T : ℝ) (hσ₀ : 0 < σ₀) :
    (goldbachGaussianHeatKernelMellinAnchor σ₀ T 1).re =
      ∫ t in (-2 * T)..(2 * T),
        goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2)) := by
  have hf := goldbach_gaussian_heat_kernel_mellin_integrand_interval_integrable σ₀ T hσ₀
  rw [goldbachGaussianHeatKernelMellinAnchor]
  rw [goldbach_intervalIntegral_re (fun t =>
      goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel 1 (σ₀ + t * I)) (-2 * T)
    (2 * T) hf]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact goldbach_gaussian_heat_kernel_mellin_integrand_re σ₀ T t hσ₀

theorem goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_eq_poisson (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) :
    goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ T =
      goldbachGaussianHeatKernelVerticalPoissonBridgeBound σ₀ T := by
  have hG' := goldbach_gaussian_heat_kernel_interval_integrable T
  have hscaled := goldbach_gaussian_heat_kernel_scaled_interval_integrable σ₀ T hσ₀
  have hre := goldbach_gaussian_heat_kernel_mellin_anchor_re_eq_poisson σ₀ T hσ₀
  have hhab : -2 * T ≤ 2 * T := by linarith [hT]
  have hsub :
      (∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t) -
          ∫ t in (-2 * T)..(2 * T),
            goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2)) =
        ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t := by
    calc
      (∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t) -
          ∫ t in (-2 * T)..(2 * T),
            goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2)) =
          ∫ t in (-2 * T)..(2 * T),
            (goldbachGaussianVerticalHeatKernel T t -
              goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2))) :=
        (intervalIntegral.integral_sub hG' hscaled).symm
      _ = ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        dsimp [goldbachGaussianHeatKernelPoissonSignedIntegrand]
        field_simp [goldbach_poisson_den_ne_zero σ₀ t hσ₀]
  have hsigned_nonneg :
      0 ≤ ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t := by
    refine intervalIntegral.integral_nonneg hhab fun t ht => ?_
    simp only [Set.mem_Icc] at ht
    dsimp [goldbachGaussianHeatKernelPoissonSignedIntegrand]
    apply mul_nonneg (Real.exp_nonneg _)
    apply div_nonneg (by nlinarith [hσ₁, sq_nonneg t, sq_nonneg (σ₀ - 1)])
      (add_nonneg (sq_nonneg σ₀) (sq_nonneg t))
  have hweight :
      ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t =
        ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact goldbach_gaussian_heat_kernel_poisson_signed_eq_weight σ₀ T t hσ₁
  have habs :
      |goldbachGaussianHeatKernelVerticalIntegral T -
          ∫ t in (-2 * T)..(2 * T),
            goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2))| =
        ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t := by
    rw [show goldbachGaussianHeatKernelVerticalIntegral T =
        ∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t from rfl]
    calc
      |(∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t) -
          ∫ t in (-2 * T)..(2 * T),
            goldbachGaussianVerticalHeatKernel T t * (σ₀ / (σ₀ ^ 2 + t ^ 2))| =
          |∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t| :=
        congrArg abs hsub
      _ = ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonSignedIntegrand σ₀ T t :=
        abs_of_nonneg hsigned_nonneg
      _ = ∫ t in (-2 * T)..(2 * T), goldbachGaussianHeatKernelPoissonWeightIntegrand σ₀ T t := hweight
  calc
    goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ T
        = |goldbachGaussianHeatKernelVerticalAnchorNormalized T -
            goldbachGaussianHeatKernelMellinAnchorAtUnitScale σ₀ T| := rfl
    _ = |(1 / (2 * Real.pi)) * goldbachGaussianHeatKernelVerticalIntegral T -
          (1 / (2 * Real.pi)) * (goldbachGaussianHeatKernelMellinAnchor σ₀ T 1).re| := by
          dsimp [goldbachGaussianHeatKernelVerticalAnchorNormalized,
            goldbachGaussianHeatKernelMellinAnchorAtUnitScale,
            goldbachGaussianHeatKernelMellinAnchorNormalized]
    _ = (1 / (2 * Real.pi)) * |goldbachGaussianHeatKernelVerticalIntegral T -
          (goldbachGaussianHeatKernelMellinAnchor σ₀ T 1).re| :=
          goldbach_abs_mul_sub_mul (1 / (2 * Real.pi)) _ _ (by positivity)
    _ = goldbachGaussianHeatKernelVerticalPoissonBridgeBound σ₀ T := by
          dsimp [goldbachGaussianHeatKernelVerticalPoissonBridgeBound,
            goldbachGaussianHeatKernelPoissonWeightIntegral]
          rw [hre, show goldbachGaussianHeatKernelVerticalIntegral T =
              ∫ t in (-2 * T)..(2 * T), goldbachGaussianVerticalHeatKernel T t from rfl]
          exact congrArg (fun x => (1 / (2 * Real.pi)) * x) habs

theorem goldbach_gaussian_heat_kernel_poisson_weight_integral_le_vertical (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) :
    goldbachGaussianHeatKernelPoissonWeightIntegral σ₀ T ≤
      goldbachGaussianHeatKernelVerticalIntegral T := by
  dsimp [goldbachGaussianHeatKernelPoissonWeightIntegral]
  have hab : -2 * T ≤ 2 * T := by linarith [hT]
  have hG := goldbach_gaussian_heat_kernel_poisson_weight_interval_integrable σ₀ T hσ₀
  have hG' := goldbach_gaussian_heat_kernel_interval_integrable T
  refine (intervalIntegral.integral_mono_on (a := -2 * T) (b := 2 * T) hab hG hG' ?_).trans ?_
  · intro t ht
    have hle := goldbach_gaussian_heat_kernel_poisson_complement_le_one σ₀ t hσ₁
    have hexp := Real.exp_nonneg (- t ^ 2 / (2 * T ^ 2))
    dsimp [goldbachGaussianHeatKernelPoissonWeightIntegrand, goldbachGaussianVerticalHeatKernel]
    nlinarith [hexp, hle]
  · rfl

theorem goldbach_gaussian_heat_kernel_poisson_weight_gap_le_vertical (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) :
    goldbachGaussianHeatKernelVerticalPoissonBridgeBound σ₀ T ≤
      goldbachGaussianHeatKernelVerticalAnchorNormalized T := by
  dsimp [goldbachGaussianHeatKernelVerticalPoissonBridgeBound,
    goldbachGaussianHeatKernelVerticalAnchorNormalized]
  refine mul_le_mul_of_nonneg_left
    (goldbach_gaussian_heat_kernel_poisson_weight_integral_le_vertical σ₀ T hσ₀ hσ₁ hT) ?_
  positivity

theorem goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_le_vertical (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) :
    goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ T ≤
      goldbachGaussianHeatKernelVerticalAnchorNormalized T := by
  rw [goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_eq_poisson σ₀ T hσ₀ hσ₁ hT]
  exact goldbach_gaussian_heat_kernel_poisson_weight_gap_le_vertical σ₀ T hσ₀ hσ₁ hT

/--
**A₂.0b (proved):** vertical heat proxy vs Perron Mellin anchor on `|t| ≤ 2T`.

The gap equals the explicit Poisson complement integral and is bounded by the vertical heat
proxy `(1/2π)∫_{|t|≤2T} G_T` when `1 ≤ σ₀`, since `|σ₀²+t²−σ₀|/(σ₀²+t²) ≤ 1` then.  This is the
correct scale for the `1/(σ₀+it)` translation; the exponentially smaller
`goldbachGaussianHeatKernelVerticalTailBound` controls the **full-line vs finite-height** step
(already in A₂.0 core).
-/
def GoldbachMidpointGaussianHeatKernelVerticalMellinAnchorBridgeHypothesis (σ₀ : ℝ) (T : ℕ)
    (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) : Prop :=
  goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ (T : ℝ) ≤
    goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ)

theorem goldbach_midpoint_gaussian_heat_kernel_vertical_mellin_anchor_bridge (σ₀ : ℝ) (T : ℕ)
    (hσ₁ : 1 ≤ σ₀) (hT : 0 < T) :
    GoldbachMidpointGaussianHeatKernelVerticalMellinAnchorBridgeHypothesis σ₀ T hσ₁ hT := by
  dsimp [GoldbachMidpointGaussianHeatKernelVerticalMellinAnchorBridgeHypothesis]
  exact goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_le_vertical σ₀ (T : ℝ)
    (by linarith [hσ₁]) hσ₁ (by exact_mod_cast hT)

theorem goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_le_tail_of_poisson_le_tail
    {σ₀ T : ℝ} (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 0 < T)
    (h :
      goldbachGaussianHeatKernelVerticalPoissonBridgeBound σ₀ T ≤
        goldbachGaussianHeatKernelVerticalTailBound T) :
    goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ T ≤
      goldbachGaussianHeatKernelVerticalTailBound T := by
  rw [goldbach_gaussian_heat_kernel_vertical_mellin_anchor_gap_eq_poisson σ₀ T hσ₀ hσ₁ hT]
  exact h

/-! ### Subgoal A₂.0: Poisson kernel mass → heat / Mellin anchor -/

theorem goldbach_gaussian_heat_kernel_full_line_sub_vertical_eq_tail (T : ℝ) :
    goldbachGaussianHeatKernelFullLineIntegral T - goldbachGaussianHeatKernelVerticalIntegral T =
      goldbachGaussianHeatKernelVerticalTailBound T := rfl

theorem goldbach_gaussian_heat_kernel_full_line_vertical_tail_abs (T : ℕ) (hT : 0 < T) :
    |goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) -
        goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)| =
      goldbachGaussianHeatKernelVerticalTailBound (T : ℝ) := by
  rw [goldbach_gaussian_heat_kernel_full_line_sub_vertical_eq_tail]
  exact abs_of_nonneg (goldbach_gaussian_heat_kernel_vertical_tail_bound_nonneg_nat T hT)

theorem goldbach_midpoint_gaussian_kernel_near_full_line_poisson (M T : ℕ) (hM : 0 < M)
    (hT : 0 < T) :
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)| ≤
      goldbachGaussianA1PoissonFourierInversionError M T := by
  have h := goldbach_midpoint_gaussian_fourier_inversion_poisson M T hM hT
  dsimp [GoldbachMidpointGaussianFourierInversionPoissonHypothesis,
    goldbachMidpointGaussianFourierReconstruction] at h
  exact h

/--
**A₂.0 core (proved):** Poisson A₁ plus vertical tail controls the kernel vs the finite-height
heat integral on `|t| ≤ 2T`.
-/
theorem goldbach_midpoint_gaussian_kernel_near_vertical_heat_integral (M T : ℕ) (hM : 0 < M)
    (hT : 0 < T) :
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)| ≤
      goldbachGaussianA20HeatKernelMellinLinkError M T := by
  have hpoisson := goldbach_midpoint_gaussian_kernel_near_full_line_poisson M T hM hT
  have htail := goldbach_gaussian_heat_kernel_full_line_vertical_tail_abs T hT
  exact
    (abs_sub_le (goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ))
        (goldbachGaussianHeatKernelFullLineIntegral (T : ℝ))
        (goldbachGaussianHeatKernelVerticalIntegral (T : ℝ))).trans
      (add_le_add hpoisson (le_of_eq htail))

theorem goldbach_midpoint_gaussian_kernel_near_vertical_heat_proxy (M T : ℕ) (hM : 0 < M)
    (hT : 0 < T) :
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ)| ≤
      goldbachGaussianA20HeatKernelMellinLinkError M T +
        (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) := by
  have hvert := goldbach_midpoint_gaussian_kernel_near_vertical_heat_integral M T hM hT
  set vert := goldbachGaussianHeatKernelVerticalIntegral (T : ℝ)
  set proxy := goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ)
  set full := goldbachGaussianHeatKernelFullLineIntegral (T : ℝ)
  have hvert_nonneg : 0 ≤ vert := goldbach_gaussian_heat_kernel_vertical_integral_nonneg_nat T
  have hsub : vert - proxy = (1 - 1 / (2 * Real.pi)) * vert := by
    dsimp [proxy, goldbachGaussianHeatKernelVerticalAnchorNormalized]
    ring
  have hfactor_nonneg : 0 ≤ 1 - 1 / (2 * Real.pi) := by
    have h2pi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hrecip : 1 / (2 * Real.pi) ≤ 1 := by
      have hrecip' : 1 / (2 * Real.pi) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (show 0 < (1 : ℝ) by norm_num) h2pi_ge_one
      simpa using hrecip'
    linarith
  have hscale : |vert - proxy| = (1 - 1 / (2 * Real.pi)) * vert := by
    rw [hsub, abs_of_nonneg (mul_nonneg hfactor_nonneg hvert_nonneg)]
  have hscale_le :
      (1 - 1 / (2 * Real.pi)) * vert ≤ (1 - 1 / (2 * Real.pi)) * full :=
    mul_le_mul_of_nonneg_left (goldbach_gaussian_heat_kernel_vertical_le_full_line_nat T hT)
      hfactor_nonneg
  exact
    (abs_sub_le (goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ)) vert proxy).trans
      (add_le_add hvert (by rw [hscale]; exact hscale_le))

/--
**A₂.0 Mellin anchor link:** Poisson A₁ + vertical tail + the vertical→Mellin anchor gap.
When `GoldbachMidpointGaussianHeatKernelVerticalMellinAnchorBridgeHypothesis` holds, the gap
is absorbed into the tail budget.
-/
theorem goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hT : 0 < T) (_hσ₀ : 0 < σ₀) :
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelMellinAnchorAtUnitScale σ₀ (T : ℝ)| ≤
      goldbachGaussianA20HeatKernelMellinLinkError M T +
        (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
          goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ (T : ℝ) := by
  have hproxy := goldbach_midpoint_gaussian_kernel_near_vertical_heat_proxy M T hM hT
  set kernel := goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ)
  set proxy := goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ)
  set anchor := goldbachGaussianHeatKernelMellinAnchorAtUnitScale σ₀ (T : ℝ)
  set gap := goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ (T : ℝ)
  have hsplit := abs_sub_le kernel proxy anchor
  have hgap :
      |proxy - anchor| ≤ goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ (T : ℝ) := by
    subst proxy anchor gap
    exact le_rfl
  exact hsplit.trans (add_le_add hproxy hgap)

theorem goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link_of_bridge
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hT : 0 < T) (hσ₁ : 1 ≤ σ₀)
    (_hBridge : GoldbachMidpointGaussianHeatKernelVerticalMellinAnchorBridgeHypothesis σ₀ T hσ₁ hT) :
    |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
        goldbachGaussianHeatKernelMellinAnchorAtUnitScale σ₀ (T : ℝ)| ≤
      goldbachGaussianA20HeatKernelMellinLinkError M T +
        (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
          goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ) := by
  have hmain := goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link M T σ₀ hM hT
    (by linarith [hσ₁])
  have hstep :
      goldbachGaussianA20HeatKernelMellinLinkError M T +
          (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
            goldbachGaussianHeatKernelVerticalMellinAnchorGap σ₀ (T : ℝ) ≤
        goldbachGaussianA20HeatKernelMellinLinkError M T +
          (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
            goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ) := by
    gcongr
    exact _hBridge
  exact hmain.trans hstep

/--
`F_M`-weighted heat Mellin pairing minus the pure-kernel anchor (Subgoal A₂.1 residual).

Formally `∫ (F_M − 1) · G_T · x^s / s` on the finite-height proxy; packaged as the
normalized real difference of the two completed integrals.
-/
noncomputable def goldbachPerronGaussianMellinMinusAnchorNormalized (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ T x -
    goldbachGaussianHeatKernelMellinAnchorNormalized σ₀ T x

/-! ### Subgoal A₂.1: `(F_M − 1)` heat Mellin bridge -/

theorem goldbach_gaussian_vertical_heat_kernel_le_one (T t : ℝ) :
    goldbachGaussianVerticalHeatKernel T t ≤ 1 := by
  dsimp [goldbachGaussianVerticalHeatKernel]
  by_cases hT : T = 0
  · simp [hT, le_refl]
  · exact (Real.exp_le_one_iff).2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t))
      (by nlinarith [sq_pos_of_ne_zero hT]))

private theorem goldbach_perron_gaussian_heat_kernel_factor_continuousOn (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀)
    (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn
      (fun t => (goldbachGaussianVerticalHeatKernel T t : ℂ) * goldbachPerronKernel x (σ₀ + t * I)) S :=
  continuous_ofReal.comp_continuousOn (goldbach_gaussian_heat_kernel_continuousOn T S) |>.mul
    (goldbach_perron_kernel_continuousOn_vertical x σ₀ hσ₀ hx S)

private theorem goldbach_perron_gaussian_heat_weighted_mellin_integrand_continuousOn
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun t => goldbachPerronGaussianHeatWeightedMellinIntegrand M σ₀ T x t) S := by
  have hF :=
    goldbach_midpoint_geometric_generating_sum_truncated_continuousOn_vertical M σ₀ hσ₀ S
  have hGk := goldbach_perron_gaussian_heat_kernel_factor_continuousOn σ₀ T x hσ₀ hx S
  exact (hF.mul hGk).congr fun _ _ => by
    simp [goldbachPerronGaussianHeatWeightedMellinIntegrand]
    ring_nf

private theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_continuousOn
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun t => goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t) S := by
  have hF :=
    goldbach_midpoint_geometric_generating_sum_truncated_continuousOn_vertical M σ₀ hσ₀ S
  have hGk := goldbach_perron_gaussian_heat_kernel_factor_continuousOn σ₀ T x hσ₀ hx S
  exact
    ((hF.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) S)).mul hGk).congr fun _ _ => by
      simp [goldbachPerronGaussianFMMinusOneHeatMellinIntegrand]
      ring_nf

private theorem goldbach_gaussian_heat_kernel_mellin_anchor_integrand_continuousOn
    (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn
      (fun t => goldbachGaussianVerticalHeatKernel T t * goldbachPerronKernel x (σ₀ + t * I)) S :=
  continuous_ofReal.comp_continuousOn (goldbach_gaussian_heat_kernel_continuousOn T S) |>.mul
    (goldbach_perron_kernel_continuousOn_vertical x σ₀ hσ₀ hx S)

private theorem goldbach_perron_gaussian_heat_weighted_mellin_integrand_interval_integrable
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    IntervalIntegrable (fun t => goldbachPerronGaussianHeatWeightedMellinIntegrand M σ₀ T x t)
      volume (-2 * T) (2 * T) :=
  (goldbach_perron_gaussian_heat_weighted_mellin_integrand_continuousOn M σ₀ T x hσ₀ hx
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_interval_integrable
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    IntervalIntegrable (fun t => goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t)
      volume (-2 * T) (2 * T) :=
  (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_continuousOn M σ₀ T x hσ₀ hx
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

private theorem goldbach_gaussian_heat_kernel_mellin_anchor_integrand_interval_integrable
    (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    IntervalIntegrable
      (fun t => (goldbachGaussianVerticalHeatKernel T t : ℂ) * goldbachPerronKernel x (σ₀ + t * I)) volume
      (-2 * T) (2 * T) :=
  (continuous_ofReal.comp_continuousOn
      (goldbach_gaussian_heat_kernel_continuousOn T (Set.uIcc (-2 * T) (2 * T))) |>.mul
    (goldbach_perron_kernel_continuousOn_vertical x σ₀ hσ₀ hx (Set.uIcc (-2 * T) (2 * T)))).intervalIntegrable

theorem goldbach_perron_gaussian_mellin_minus_anchor_eq_fm_integral (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ T x =
      goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized M σ₀ T x := by
  have hf := goldbach_perron_gaussian_heat_weighted_mellin_integrand_interval_integrable M σ₀ T x hσ₀ hx
  have hg := goldbach_gaussian_heat_kernel_mellin_anchor_integrand_interval_integrable σ₀ T x hσ₀ hx
  have hfm := goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_interval_integrable M σ₀ T x hσ₀ hx
  have hdiff :
      goldbachPerronGaussianMellinPairingAtScale M σ₀ T x -
          goldbachGaussianHeatKernelMellinAnchor σ₀ T x =
        goldbachPerronGaussianFMMinusOneHeatMellinIntegral M σ₀ T x := by
    dsimp [goldbachPerronGaussianMellinPairingAtScale, goldbachGaussianHeatKernelMellinAnchor,
      goldbachPerronGaussianFMMinusOneHeatMellinIntegral]
    rw [← intervalIntegral.integral_sub hf hg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [goldbachPerronGaussianHeatWeightedMellinIntegrand,
      goldbachPerronGaussianFMMinusOneHeatMellinIntegrand]
    push_cast
    ring_nf
  have hre :
      (goldbachPerronGaussianMellinPairingAtScale M σ₀ T x).re -
          (goldbachGaussianHeatKernelMellinAnchor σ₀ T x).re =
        (goldbachPerronGaussianFMMinusOneHeatMellinIntegral M σ₀ T x).re := by
    rw [← Complex.sub_re, hdiff]
  dsimp [goldbachPerronGaussianMellinMinusAnchorNormalized,
    goldbachPerronGaussianMellinPairingAtScaleNormalized,
    goldbachGaussianHeatKernelMellinAnchorNormalized,
    goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized]
  calc (1 / (2 * Real.pi)) * (goldbachPerronGaussianMellinPairingAtScale M σ₀ T x).re -
        (1 / (2 * Real.pi)) * (goldbachGaussianHeatKernelMellinAnchor σ₀ T x).re
      = (1 / (2 * Real.pi)) *
          ((goldbachPerronGaussianMellinPairingAtScale M σ₀ T x).re -
            (goldbachGaussianHeatKernelMellinAnchor σ₀ T x).re) := by ring
    _ = (1 / (2 * Real.pi)) * (goldbachPerronGaussianFMMinusOneHeatMellinIntegral M σ₀ T x).re := by
          rw [hre]

theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_le_norm
    (M : ℕ) (σ₀ T x t : ℝ) :
    |(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re| ≤
      ‖goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t‖ :=
  Complex.abs_re_le_norm _

theorem goldbach_perron_gaussian_fm_minus_one_heat_integrand_norm_le_tail_from_growth
    (M : ℕ) (σ₀ T x t : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (hTle : T ≤ |t|) (hT : 1 ≤ T)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    ‖goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t‖ ≤
      (input.growth_constant + 1) * x ^ σ₀ / T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hG := goldbach_gaussian_vertical_heat_kernel_le_one T t
  have hGle : ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ ≤ 1 := by
    have hG0 : 0 ≤ goldbachGaussianVerticalHeatKernel T t := Real.exp_nonneg _
    rw [Complex.norm_def, Complex.normSq_ofReal]
    exact Real.sqrt_le_one.mpr (by nlinarith [hG, hG0])
  have hkernel := goldbach_perron_kernel_norm_le_on_tail x σ₀ T t hσ₀ hx hTle hT
  have hkernelT : ‖goldbachPerronKernel x (σ₀ + t * I)‖ ≤ x ^ σ₀ / T := by
    have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one (le_trans hT hTle)
    refine hkernel.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hTle (Real.rpow_nonneg hx.le σ₀)
  dsimp [goldbachPerronGaussianFMMinusOneHeatMellinIntegrand]
  rw [Complex.norm_mul, Complex.norm_mul]
  have hFminus :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ ≤
        input.growth_constant + 1 := by
    calc
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ ≤
          ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ input.growth_constant + 1 := by
        gcongr
        · exact goldbach_smoothed_perron_F_norm_le_growth_constant M σ₀ input t
        · norm_num
  have hmid :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ *
          ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ ≤
        input.growth_constant + 1 := by
    simpa [mul_one] using
      mul_le_mul hFminus hGle (norm_nonneg _) (add_nonneg input.growth_constant_nonneg zero_le_one)
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ *
        ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ *
        ‖goldbachPerronKernel x (σ₀ + t * I)‖ ≤
        (input.growth_constant + 1) * (x ^ σ₀ / T) := by
      exact mul_le_mul hmid hkernelT (norm_nonneg _)
        (add_nonneg input.growth_constant_nonneg zero_le_one)
    _ = (input.growth_constant + 1) * x ^ σ₀ / T := by ring

theorem goldbach_perron_gaussian_fm_minus_one_heat_integrand_norm_le_from_growth_on_finite_proxy
    (M : ℕ) (σ₀ T x t : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    ‖goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t‖ ≤
      (input.growth_constant + 1) * x ^ σ₀ / T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hG := goldbach_gaussian_vertical_heat_kernel_le_one T t
  have hGle : ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ ≤ 1 := by
    have hG0 : 0 ≤ goldbachGaussianVerticalHeatKernel T t := Real.exp_nonneg _
    rw [Complex.norm_def, Complex.normSq_ofReal]
    exact Real.sqrt_le_one.mpr (by nlinarith [hG, hG0])
  have hkernelT : ‖goldbachPerronKernel x (σ₀ + t * I)‖ ≤ x ^ σ₀ / T :=
    goldbach_perron_kernel_norm_le_when_sigma_ge_T x σ₀ T t hσ₀ hx hTpos hσT
  have hFminus :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ ≤
        input.growth_constant + 1 := by
    calc
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ ≤
          ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ input.growth_constant + 1 := by
        gcongr
        · exact goldbach_smoothed_perron_F_norm_le_growth_constant M σ₀ input t
        · norm_num
  have hmid :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) - 1‖ *
          ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ ≤
        input.growth_constant + 1 := by
    simpa [mul_one] using
      mul_le_mul hFminus hGle (norm_nonneg _) (add_nonneg input.growth_constant_nonneg zero_le_one)
  dsimp [goldbachPerronGaussianFMMinusOneHeatMellinIntegrand]
  rw [Complex.norm_mul, Complex.norm_mul]
  calc
    _ ≤ (input.growth_constant + 1) * (x ^ σ₀ / T) := by
      exact mul_le_mul hmid hkernelT (norm_nonneg _)
        (add_nonneg input.growth_constant_nonneg zero_le_one)
    _ = (input.growth_constant + 1) * x ^ σ₀ / T := by ring

/--
Integrand for the pure-kernel vs heat-weighted Mellin gap on `Re s = σ₀`:

`F_M · (1 − G_T) · x^s / s`.
-/
noncomputable def goldbachPerronGaussianFMOneMinusHeatGapIntegrand (M : ℕ) (σ₀ T x t : ℝ) : ℂ :=
  goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) *
    ((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ)) *
    goldbachPerronKernel x (σ₀ + t * I)

noncomputable def goldbachPerronGaussianFMOneMinusHeatGapIntegral (M : ℕ) (σ₀ T x : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T), goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ T x t

noncomputable def goldbachPerronGaussianFMOneMinusHeatGapIntegralNormalized (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachPerronGaussianFMOneMinusHeatGapIntegral M σ₀ T x).re

private theorem goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_continuousOn
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun t => goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ T x t) S :=
  (goldbach_truncated_perron_vertical_integrand_continuousOn M σ₀ x hσ₀ hx S).sub
    (goldbach_perron_gaussian_heat_weighted_mellin_integrand_continuousOn M σ₀ T x hσ₀ hx S) |>.congr
      fun _ _ => by
        simp [goldbachPerronGaussianFMOneMinusHeatGapIntegrand,
          goldbachTruncatedPerronVerticalIntegrand, goldbachPerronGaussianHeatWeightedMellinIntegrand]
        ring_nf

private theorem goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_interval_integrable
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    IntervalIntegrable (fun t => goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ T x t)
      volume (-2 * T) (2 * T) :=
  (goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_continuousOn M σ₀ T x hσ₀ hx
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

theorem goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_norm_le_from_growth_on_finite_proxy
    (M : ℕ) (σ₀ T x t : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    ‖goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ T x t‖ ≤
      2 * (input.growth_constant + 1) * x ^ σ₀ / T := by
  have hG := goldbach_gaussian_vertical_heat_kernel_le_one T t
  have hF' :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)‖ ≤
        input.growth_constant + 1 :=
    le_trans (goldbach_smoothed_perron_F_norm_le_growth_constant M σ₀ input t)
      (le_add_of_nonneg_right zero_le_one)
  have hkernelT : ‖goldbachPerronKernel x (σ₀ + t * I)‖ ≤ x ^ σ₀ / T :=
    goldbach_perron_kernel_norm_le_when_sigma_ge_T x σ₀ T t hσ₀ hx
      (lt_of_lt_of_le zero_lt_one hT) hσT
  have hGle : ‖(goldbachGaussianVerticalHeatKernel T t : ℂ)‖ ≤ 1 := by
    have hG0 : 0 ≤ goldbachGaussianVerticalHeatKernel T t := Real.exp_nonneg _
    rw [Complex.norm_def, Complex.normSq_ofReal]
    exact Real.sqrt_le_one.mpr (by nlinarith [hG, hG0])
  have h1G : ‖((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ))‖ ≤ 2 := by
    have hnorm1 : ‖(1 : ℂ)‖ = 1 := by norm_cast
    linarith [norm_sub_le (1 : ℂ) (goldbachGaussianVerticalHeatKernel T t : ℂ), hnorm1, hGle]
  have hmid :
      ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)‖ *
          ‖((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ))‖ ≤
        (input.growth_constant + 1) * 2 := by
    nlinarith [norm_nonneg (goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)),
      norm_nonneg ((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ)), hF', h1G,
      input.growth_constant_nonneg]
  dsimp [goldbachPerronGaussianFMOneMinusHeatGapIntegrand]
  rw [Complex.norm_mul, Complex.norm_mul]
  calc
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)‖ *
        ‖((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ))‖ *
        ‖goldbachPerronKernel x (σ₀ + t * I)‖ ≤
        (input.growth_constant + 1) * 2 * (x ^ σ₀ / T) := by
      nlinarith [norm_nonneg (goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I)),
        norm_nonneg ((1 : ℂ) - (goldbachGaussianVerticalHeatKernel T t : ℂ)),
        norm_nonneg (goldbachPerronKernel x (σ₀ + t * I)), hF', h1G, hmid, hkernelT,
        input.growth_constant_nonneg, Real.rpow_nonneg hx.le σ₀,
        div_nonneg (Real.rpow_nonneg hx.le σ₀) (le_of_lt (lt_of_lt_of_le zero_lt_one hT))]
    _ = 2 * (input.growth_constant + 1) * x ^ σ₀ / T := by ring

theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integral_normalized_le_bookkeeping
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) (hσT : (T : ℝ) ≤ σ₀)
    (hσTpi : σ₀ * T ≤ 2 * Real.pi) (input : GoldbachSmoothedPerronContourInput M σ₀) :
    |goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized M σ₀ T x| ≤
      2 * goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hC : ∀ t ∈ Set.uIcc (-2 * T) (2 * T),
      |(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re| ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht
    exact (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_le_norm M σ₀ T x t).trans
      (goldbach_perron_gaussian_fm_minus_one_heat_integrand_norm_le_from_growth_on_finite_proxy
        M σ₀ T x t hσ₀ hx hT hσT input)
  have hCnorm : ∀ t ∈ Set.uIcc (-2 * T) (2 * T),
      ‖(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht; rw [Real.norm_eq_abs]; exact hC t ht
  have hle : -2 * T ≤ 2 * T := by linarith
  have hint :
      ‖∫ t in (-2 * T)..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T * |2 * T - (-2 * T)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : -2 * T < t := by
      have hmin : min (-2 * T) (2 * T) = -2 * T := min_eq_left hle
      rwa [hmin] at htl
    have htr' : t ≤ 2 * T := by
      have hmax : max (-2 * T) (2 * T) = 2 * T := max_eq_right hle
      exact hmax ▸ htr
    exact hCnorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have hre :
      (goldbachPerronGaussianFMMinusOneHeatMellinIntegral M σ₀ T x).re =
        ∫ t in (-2 * T)..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re :=
    goldbach_intervalIntegral_re _ _ _
      (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_interval_integrable M σ₀ T x hσ₀ hx)
  dsimp [goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized,
    goldbachPerronFMMinusOneHeatTailContourBookkeepingBound]
  rw [abs_mul, abs_div, abs_of_pos (by positivity), abs_of_pos (by positivity), hre]
  have hbound :
      (1 / (2 * Real.pi)) *
          |∫ t in (-2 * T)..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re|
        ≤ 4 * (input.growth_constant + 1) * x ^ σ₀ / (σ₀ * T) := by
    calc
      (1 / (2 * Real.pi)) *
          |∫ t in (-2 * T)..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re|
        ≤ (1 / (2 * Real.pi)) *
            ((input.growth_constant + 1) * x ^ σ₀ / T * |2 * T - (-2 * T)|) := by
          gcongr; exact hint
      _ = (1 / (2 * Real.pi)) * (input.growth_constant + 1) * x ^ σ₀ / T * (4 * T) := by
          have hlen : |2 * T - (-2 * T)| = 4 * T := by
            have : 2 * T - (-2 * T) = 4 * T := by ring
            rw [this, abs_of_pos (by linarith [hTpos])]
          calc
            (1 / (2 * Real.pi)) *
                ((input.growth_constant + 1) * x ^ σ₀ / T * |2 * T - (-2 * T)|)
              = (1 / (2 * Real.pi)) * ((input.growth_constant + 1) * x ^ σ₀ / T * (4 * T)) := by
                  rw [hlen]
              _ = (1 / (2 * Real.pi)) * (input.growth_constant + 1) * x ^ σ₀ / T * (4 * T) := by ring
      _ = 2 * (input.growth_constant + 1) * x ^ σ₀ / Real.pi := by
          field_simp
          ring
      _ ≤ 4 * (input.growth_constant + 1) * x ^ σ₀ / (σ₀ * T) := by
          refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
          calc 2 * (input.growth_constant + 1) * x ^ σ₀ * (σ₀ * T)
              ≤ 2 * (input.growth_constant + 1) * x ^ σ₀ * (2 * Real.pi) := by
                have hpos₁ : 0 ≤ input.growth_constant + 1 := by linarith [input.growth_constant_nonneg]
                have hpos₂ : 0 ≤ x ^ σ₀ := Real.rpow_nonneg hx.le σ₀
                have hcoef : 0 ≤ 2 * (input.growth_constant + 1) * x ^ σ₀ :=
                  mul_nonneg (mul_nonneg zero_le_two hpos₁) hpos₂
                exact mul_le_mul_of_nonneg_left hσTpi hcoef
            _ = 4 * (input.growth_constant + 1) * x ^ σ₀ * Real.pi := by ring
  have hbound' :
      (1 / (2 * Real.pi)) *
          |∫ t in (-2 * T)..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re|
        ≤ 2 * goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input := by
    calc
      _ ≤ 4 * (input.growth_constant + 1) * x ^ σ₀ / (σ₀ * T) := hbound
      _ = 2 * goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input := by
          dsimp [goldbachPerronFMMinusOneHeatTailContourBookkeepingBound]
          ring
  exact hbound'

theorem goldbach_perron_fm_bookkeeping_le_two_times_B_plus_one_template (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input =
      2 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ T x := by
  dsimp [goldbachPerronFMMinusOneHeatTailContourBookkeepingBound,
    goldbachPerronFMPlusOneVerticalTailErrorTemplate]
  rw [max_eq_right hT, input.growth_constant_eq_value]
  ring

theorem goldbach_perron_fm_plus_one_template_le_two_b_templates (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ₀) (hBgrowth : 1 ≤ input.growth_constant) :
    goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ T x ≤
      2 * goldbachPerronVerticalTailErrorTemplate M σ₀ T x := by
  have hB :
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ = input.growth_constant :=
    input.growth_constant_eq_value.symm
  dsimp [goldbachPerronFMPlusOneVerticalTailErrorTemplate, goldbachPerronVerticalTailErrorTemplate]
  rw [max_eq_right hT, hB]
  have hden : 0 < σ₀ * T := mul_pos hσ₀ (lt_of_lt_of_le zero_lt_one hT)
  have hle : input.growth_constant + 1 ≤ 2 * input.growth_constant := by nlinarith [hBgrowth]
  calc x ^ σ₀ * (input.growth_constant + 1) / (σ₀ * T)
      ≤ x ^ σ₀ * (2 * input.growth_constant) / (σ₀ * T) := by gcongr
    _ = 2 * (x ^ σ₀ * input.growth_constant / (σ₀ * T)) := by ring

private theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_continuousOn
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) (S : Set ℝ) :
    ContinuousOn (fun t => (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re) S :=
  continuous_re.comp_continuousOn
    (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_continuousOn M σ₀ T x hσ₀ hx S)

theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_integral_eq_central_plus_tail
    (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀) (hT : 0 < T) (hx : 0 < x) :
    goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized M σ₀ T x =
      goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral M σ₀ T x +
        goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral M σ₀ T x := by
  set f : ℝ → ℝ := fun t =>
    (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re
  have hint_pos_tail :
      IntervalIntegrable f volume T (2 * T) :=
    (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_continuousOn M σ₀ T x hσ₀ hx
      (Set.uIcc T (2 * T))).intervalIntegrable
  have hint_neg_tail :
      IntervalIntegrable f volume (-2 * T) (-T) :=
    (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_continuousOn M σ₀ T x hσ₀ hx
      (Set.uIcc (-2 * T) (-T))).intervalIntegrable
  have hint_central :
      IntervalIntegrable f volume (-T) T :=
    (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_continuousOn M σ₀ T x hσ₀ hx
      (Set.uIcc (-T) T)).intervalIntegrable
  have hint_neg_to_pos := hint_neg_tail.trans hint_central
  have hsplit₁ :
      (∫ t in (-2 * T)..(-T), f t) + (∫ t in (-T)..T, f t) =
        ∫ t in (-2 * T)..T, f t :=
    intervalIntegral.integral_add_adjacent_intervals hint_neg_tail hint_central
  have hsplit₂ :
      (∫ t in (-2 * T)..T, f t) + (∫ t in T..(2 * T), f t) =
        ∫ t in (-2 * T)..(2 * T), f t :=
    intervalIntegral.integral_add_adjacent_intervals hint_neg_to_pos hint_pos_tail
  have hcore :
      (∫ t in (-2 * T)..(2 * T), f t) =
        (∫ t in (-T)..T, f t) +
          ((∫ t in T..(2 * T), f t) + (∫ t in (-2 * T)..(-T), f t)) := by
    rw [hsplit₂.symm, ← hsplit₁]
    ring
  dsimp [goldbachPerronGaussianFMMinusOneHeatMellinIntegralNormalized,
    goldbachPerronGaussianFMMinusOneHeatMellinIntegral,
    goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral,
    goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral]
  rw [goldbach_intervalIntegral_re _ _ _
    (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_interval_integrable M σ₀ T x hσ₀ hx)]
  simp only [← mul_add, f, hcore]

theorem goldbach_perron_gaussian_fm_minus_one_heat_mellin_tail_le_bookkeeping_bound (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ₀ * T ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    |goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral M σ₀ T x| ≤
      goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hC : ∀ t, T ≤ |t| →
      ‖goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T :=
    fun t ht =>
      goldbach_perron_gaussian_fm_minus_one_heat_integrand_norm_le_tail_from_growth M σ₀ T x t hσ₀ hx
        ht hT input
  have hC' : ∀ t ∈ Set.uIcc T (2 * T),
      |(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re| ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht
    exact (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_le_norm M σ₀ T x t).trans
      (hC t (by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨htl, _⟩ | ⟨_, htr⟩
        · have htpos : 0 < t := lt_of_lt_of_le hTpos htl
          rw [abs_of_pos htpos]; exact htl
        · linarith [hTpos, htr]))
  have hCneg : ∀ t ∈ Set.uIcc (-2 * T) (-T),
      |(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re| ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨htl, htr⟩ | ⟨htl, htr⟩
    · have htneg : t < 0 := lt_of_le_of_lt htr (neg_neg_of_pos hTpos)
      have hTle : T ≤ |t| := by rw [abs_of_neg htneg]; linarith [htr]
      exact (goldbach_perron_gaussian_fm_minus_one_heat_mellin_integrand_re_le_norm M σ₀ T x t).trans
        (hC t hTle)
    · linarith [hTpos, htr]
  dsimp [goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral]
  rw [abs_mul, abs_div, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hle : T ≤ 2 * T := by linarith
  have hle' : -2 * T ≤ -T := by linarith
  have hCnorm : ∀ t ∈ Set.uIcc T (2 * T),
      ‖(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht; rw [Real.norm_eq_abs]; exact hC' t ht
  have hCnegNorm : ∀ t ∈ Set.uIcc (-2 * T) (-T),
      ‖(goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T := by
    intro t ht; rw [Real.norm_eq_abs]; exact hCneg t ht
  have htail1 :
      ‖∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T * |2 * T - T| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : T < t := by
      have hmin : min T (2 * T) = T := min_eq_left hle
      rwa [hmin] at htl
    have htr' : t ≤ 2 * T := by
      have hmax : max T (2 * T) = 2 * T := max_eq_right hle
      exact hmax ▸ htr
    exact hCnorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have htail2 :
      ‖∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ ≤
        (input.growth_constant + 1) * x ^ σ₀ / T * |(-T) - (-2 * T)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : -2 * T < t := by
      have hmin : min (-2 * T) (-T) = -2 * T := min_eq_left hle'
      rwa [hmin] at htl
    have htr' : t ≤ -T := by
      have hmax : max (-2 * T) (-T) = -T := max_eq_right hle'
      exact hmax ▸ htr
    exact hCnegNorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have habs_sum :
      ‖(∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re) +
          (∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re)‖ ≤
        ‖∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ +
          ‖∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ :=
    norm_add_le _ _
  calc (1 / (2 * Real.pi)) *
        |(∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re) +
            (∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re)|
      ≤ (1 / (2 * Real.pi)) *
          (‖∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖ +
            ‖∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖) := by
        gcongr
        rw [← Real.norm_eq_abs]
        exact habs_sum
    _ ≤ (1 / (2 * Real.pi)) *
          ((input.growth_constant + 1) * x ^ σ₀ / T * T +
            (input.growth_constant + 1) * x ^ σ₀ / T * T) := by
      gcongr
      · calc
          ‖∫ t in T..(2 * T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖
              ≤ (input.growth_constant + 1) * x ^ σ₀ / T * |2 * T - T| := htail1
          _ = (input.growth_constant + 1) * x ^ σ₀ / T * T := by
            have : 2 * T - T = T := by ring
            rw [this, abs_of_pos hTpos]
      · calc
          ‖∫ t in (-2 * T)..(-T), (goldbachPerronGaussianFMMinusOneHeatMellinIntegrand M σ₀ T x t).re‖
              ≤ (input.growth_constant + 1) * x ^ σ₀ / T * |(-T) - (-2 * T)| := htail2
          _ = (input.growth_constant + 1) * x ^ σ₀ / T * T := by
            have : (-T) - (-2 * T) = T := by ring
            rw [this, abs_of_pos hTpos]
    _ = (input.growth_constant + 1) * x ^ σ₀ / Real.pi := by
      field_simp
      ring
    _ ≤ 2 * (input.growth_constant + 1) * x ^ σ₀ / (σ₀ * T) := by
        refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
        simpa [mul_comm, mul_left_comm, mul_assoc, two_mul] using
          mul_le_mul_of_nonneg_left hσT
            (mul_nonneg (add_nonneg input.growth_constant_nonneg zero_le_one)
              (Real.rpow_nonneg hx.le σ₀))
    _ = goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ T x input := by
        dsimp [goldbachPerronFMMinusOneHeatTailContourBookkeepingBound]

/--
**Subgoal A₂.1 (relaxed):** `F_M`-weighted heat Mellin pairing vs pure-kernel anchor on `Re s = σ₀`.

Analytic content: `(1/2π)|∫_{|t|≤2T} (F_M(σ₀+it)−1) · G_T(t) · x^{σ₀+it}/(σ₀+it) dt|`
(`goldbachPerronGaussianMellinMinusAnchorNormalized`) bounded by **four times**
`goldbachPerronFMPlusOneVerticalTailErrorTemplate` — the honest full-proxy `(B_{M,σ}+1)` scale from
coarse vertical growth on `|t| ≤ 2T` (twice the tail bookkeeping bound `2 · (B+1)`-template).
This is `≤ 8 · goldbachPerronVerticalTailErrorTemplate` when `B_{M,σ} ≥ 1`.
The sharp single-`B` target is
`GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_sharp` (Path 2).

See `GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_explicit` for the equivalent
`4 · (B_{M,σ}+1) · x^σ / (σ T)` form when `T ≥ 1`.
-/
def GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ (T : ℝ) x| ≤
    4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x

/--
Single-template A₂.1 target (Path 2 / sharp closure).
-/
def GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_sharp (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ (T : ℝ) x| ≤
    goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x

/--
Explicit relaxed A₂.1 bridge using vertical growth from `GoldbachSmoothedPerronContourInput`.
When `T ≥ 1`, this matches `2 · goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ T x`.
-/
def GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_explicit (M T : ℕ) (σ₀ x : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ₀) : Prop :=
  |goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ (T : ℝ) x| ≤
    4 * x ^ σ₀ * (input.growth_constant + 1) / (σ₀ * (T : ℝ))

theorem goldbach_midpoint_gaussian_f_mellin_anchor_bridge_iff_explicit (M T : ℕ) (σ₀ x : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ₀) :
    GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis M T σ₀ x hM hσ₀ hT hx ↔
      GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_explicit M T σ₀ x hM hσ₀ hT hx input := by
  dsimp [GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis,
    GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_explicit,
    goldbachPerronFMPlusOneVerticalTailErrorTemplate]
  rw [max_eq_right (by exact_mod_cast hT), input.growth_constant_eq_value]
  ring_nf

theorem goldbach_midpoint_gaussian_f_mellin_anchor_bridge (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) (hσT : (T : ℝ) ≤ σ₀) (_hσTpi : σ₀ * T ≤ 2 * Real.pi) :
    GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis M T σ₀ x hM hσ₀ hT hx := by
  dsimp [GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis]
  rw [goldbach_perron_gaussian_mellin_minus_anchor_eq_fm_integral M σ₀ (T : ℝ) x hσ₀ hx]
  have hinput := goldbachSmoothedPerronContourInput_pairDirichlet M σ₀ hσ₀
  have hle := goldbach_perron_gaussian_fm_minus_one_heat_mellin_integral_normalized_le_bookkeeping M σ₀
    (T : ℝ) x hσ₀ (by exact_mod_cast hT) hx hσT _hσTpi hinput
  have hscale :
      2 * goldbachPerronFMMinusOneHeatTailContourBookkeepingBound M σ₀ (T : ℝ) x hinput =
        4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
    rw [goldbach_perron_fm_bookkeeping_le_two_times_B_plus_one_template M σ₀ (T : ℝ) x hσ₀
      (by exact_mod_cast hT) hx hinput]
    ring
  exact hle.trans (le_of_eq hscale)

theorem goldbach_midpoint_gaussian_f_mellin_anchor_bridge_le_eight_b_templates (M T : ℕ) (σ₀ x : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ₀) (hBgrowth : 1 ≤ input.growth_constant)
    (hBridge : GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis M T σ₀ x hM hσ₀ hT hx) :
    |goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ (T : ℝ) x| ≤
      8 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
  dsimp [GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis] at hBridge
  calc
    _ ≤ 4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x := hBridge
    _ ≤ 8 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
      calc
        (4 : ℝ) * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x ≤
            4 * (2 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x) := by
          gcongr
          exact goldbach_perron_fm_plus_one_template_le_two_b_templates M σ₀ (T : ℝ) x hσ₀
            (by exact_mod_cast hT) hx input hBgrowth
        _ = 8 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by ring

/--
Central (`|t| ≤ T`) part of the A₂.1 `(F_M − 1)` integral; Mellin inversion of `F_M` against
`G_T` on the bulk of the heat mass.
-/
def GoldbachMidpointGaussianFMellinCentralAnchorHypothesis (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral M σ₀ (T : ℝ) x| ≤
    goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x

/--
Partial A₂.1 closure: central + tail each bounded by the template ⇒ total gap ≤ `2 · template`.
Sharp single-template closure is `GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_sharp` (Path 2).
The proved relaxed bridge is `GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis`.
-/
theorem goldbach_perron_gaussian_mellin_minus_anchor_le_double_template_of_central_and_tail
    (M T : ℕ) (σ₀ x : ℝ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (hCentral :
      |goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral M σ₀ (T : ℝ) x| ≤
        goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x)
    (hTail :
      |goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral M σ₀ (T : ℝ) x| ≤
        goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x) :
    |goldbachPerronGaussianMellinMinusAnchorNormalized M σ₀ (T : ℝ) x| ≤
      2 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hT
  rw [goldbach_perron_gaussian_mellin_minus_anchor_eq_fm_integral M σ₀ (T : ℝ) x hσ₀ hx]
  rw [goldbach_perron_gaussian_fm_minus_one_heat_mellin_integral_eq_central_plus_tail M σ₀ (T : ℝ) x
    hσ₀ hTpos hx]
  calc
    |goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral M σ₀ (T : ℝ) x +
        goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral M σ₀ (T : ℝ) x|
        ≤ |goldbachPerronGaussianFMMinusOneHeatMellinCentralIntegral M σ₀ (T : ℝ) x| +
            |goldbachPerronGaussianFMMinusOneHeatMellinTailIntegral M σ₀ (T : ℝ) x| :=
      abs_add_le _ _
    _ ≤ goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x +
          goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
      gcongr
    _ = 2 * goldbachPerronVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by ring

/--
Explicit A₂ error budget: A₂.0 heat→Mellin anchor link plus the relaxed `(B+1)` A₂.1 bridge.
-/
noncomputable def goldbachGaussianA2HeatKernelMellinAnchorLinkError (M T : ℕ) (σ₀ : ℝ) : ℝ :=
  goldbachGaussianA20HeatKernelMellinLinkError M T +
    (1 - 1 / (2 * Real.pi)) * goldbachGaussianHeatKernelFullLineIntegral (T : ℝ) +
      goldbachGaussianHeatKernelVerticalAnchorNormalized (T : ℝ)

theorem goldbach_gaussian_a2_heat_kernel_mellin_anchor_link_error_nonneg (M T : ℕ) (hM : 0 < M)
    (hT : 0 < T) (σ₀ : ℝ) :
    0 ≤ goldbachGaussianA2HeatKernelMellinAnchorLinkError M T σ₀ := by
  dsimp [goldbachGaussianA2HeatKernelMellinAnchorLinkError]
  apply add_nonneg
  · apply add_nonneg
    · exact goldbach_gaussian_a20_heat_kernel_mellin_link_error_nonneg M T hM hT
    · apply mul_nonneg
      · have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        have hrecip : 1 / (2 * Real.pi) ≤ 1 := by
          refine (one_div_le_one_div_of_le (by positivity) h2pi).trans ?_
          simp
        linarith
      · exact goldbach_gaussian_heat_kernel_full_line_integral_nonneg_of_nonneg (T : ℝ)
          (Nat.cast_nonneg T)
  · exact goldbach_gaussian_heat_kernel_vertical_anchor_normalized_nonneg T

/--
Explicit A₂ error budget: A₂.0 anchor link plus relaxed A₂.1 `(B+1)` bridge at scale `x`.
-/
noncomputable def goldbachGaussianA2MellinKernelPairingError (M T : ℕ) (σ₀ x : ℝ) : ℝ :=
  goldbachGaussianA2HeatKernelMellinAnchorLinkError M T σ₀ +
    4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x

theorem goldbach_gaussian_a2_mellin_kernel_pairing_error_nonneg (M T : ℕ) (hM : 0 < M) (hT : 0 < T)
    (σ₀ x : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    0 ≤ goldbachGaussianA2MellinKernelPairingError M T σ₀ x := by
  dsimp [goldbachGaussianA2MellinKernelPairingError]
  apply add_nonneg
  · exact goldbach_gaussian_a2_heat_kernel_mellin_anchor_link_error_nonneg M T hM hT σ₀
  · exact mul_nonneg (by norm_num)
      (goldbach_perron_fm_plus_one_tail_template_nonneg M σ₀ (T : ℝ) x hσ₀ hx.le)

/--
Residual in the smoothed-target Mellin factorization at unit scale `x = 1`.
-/
noncomputable def goldbachGaussianSmoothedMellinFactorizationResidual (M : ℕ) (σ₀ T : ℝ)
    (hT : 0 < T) : ℝ :=
  goldbachGaussianSmoothedPerronDiscreteTarget M T hT -
    goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ T

/--
Full A₂ smoothed error: aggregate coupling plus kernel–Mellin pairing budget.
-/
noncomputable def goldbachGaussianA2SmoothedMellinPairingError (M T : ℕ) (σ₀ : ℝ) (hT : 1 ≤ T) : ℝ :=
  goldbachGaussianSmoothedAggregateCouplingErrorNat M T hT +
    goldbachGaussianA2MellinKernelPairingError M T σ₀ 1

theorem goldbach_gaussian_a2_smoothed_mellin_pairing_error_nonneg (M T : ℕ) (hM : 0 < M) (hT : 1 ≤ T)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    0 ≤ goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT := by
  dsimp [goldbachGaussianA2SmoothedMellinPairingError]
  apply add_nonneg
  · exact goldbach_gaussian_smoothed_aggregate_coupling_error_nat_nonneg M T hT
  · exact goldbach_gaussian_a2_mellin_kernel_pairing_error_nonneg M T hM (lt_of_lt_of_le Nat.zero_lt_one hT)
      σ₀ 1 hσ₀ (by norm_num)

theorem goldbach_gaussian_a2_smoothed_mellin_pairing_error_le_coupling_bound_plus_kernel
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hT : 1 ≤ T) :
    goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT ≤
      goldbachGaussianSmoothedAggregateCouplingBoundNat M T hT +
        goldbachGaussianA2MellinKernelPairingError M T σ₀ 1 := by
  dsimp [goldbachGaussianA2SmoothedMellinPairingError]
  gcongr
  exact goldbach_gaussian_smoothed_aggregate_coupling_error_nat_le_bound M T hT

/--
Exact Mellin factorization: smoothed target = heat-weighted pairing + residual.
-/
theorem goldbach_smoothed_perron_discrete_target_factorization (M : ℕ) (σ₀ T : ℝ) (hT : 0 < T) :
    goldbachGaussianSmoothedPerronDiscreteTarget M T hT =
      goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ T +
        goldbachGaussianSmoothedMellinFactorizationResidual M σ₀ T hT := by
  dsimp [goldbachGaussianSmoothedMellinFactorizationResidual]
  ring

/--
Residual splits into aggregate coupling plus the kernel–Mellin gap (hypothesis (2) input).
-/
theorem goldbach_smoothed_perron_discrete_target_mellin_factorization (M : ℕ) (σ₀ T : ℝ)
    (hT : 0 < T) :
    goldbachGaussianSmoothedMellinFactorizationResidual M σ₀ T hT =
      goldbachMidpointGaussianKernelTruncatedSum M T -
        goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ T +
        goldbachGaussianSmoothedAggregateCouplingSum M T hT := by
  dsimp [goldbachGaussianSmoothedMellinFactorizationResidual]
  linarith [goldbach_smoothed_perron_discrete_target_kernel_gap_eq M T hT]

/--
Legacy Mellin pairing without explicit heat weight (`G_T ≡ 1` on the integrand).
Kept for the proved `x = 1` kernel identification below; the A₂ target uses
`goldbachPerronGaussianMellinPairingAtScale` with `G_T`.
-/
noncomputable def goldbachPerronGaussianMellinPairingAtUnitScale (M : ℕ) (σ₀ T : ℝ) : ℂ :=
  ∫ t in (-2 * T)..(2 * T),
    goldbachMidpointGeometricGeneratingSumTruncated M (σ₀ + t * I) / (σ₀ + t * I)

theorem goldbach_perron_gaussian_mellin_pairing_eq_kernel_integral (M : ℕ) (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) :
    goldbachPerronGaussianMellinPairingAtUnitScale M σ₀ T =
      goldbachPerronGaussianLeftVerticalKernelIntegral M σ₀ T 1 := by
  dsimp [goldbachPerronGaussianMellinPairingAtUnitScale, goldbachPerronGaussianLeftVerticalKernelIntegral]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hs : (σ₀ + t * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith [hσ₀]
  rw [goldbach_perron_kernel_unit_scale (σ₀ + t * I) hs, div_eq_mul_inv, inv_eq_one_div]

/--
Normalized left vertical kernel integral (matches `goldbachPerronLeftVerticalEdgeIntegral`
normalization).
-/
noncomputable def goldbachPerronGaussianLeftVerticalKernelIntegralNormalized (M : ℕ) (σ₀ T x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachPerronGaussianLeftVerticalKernelIntegral M σ₀ T x).re

noncomputable def goldbachPerronGaussianMellinPairingAtUnitScaleNormalized (M : ℕ) (σ₀ T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (goldbachPerronGaussianMellinPairingAtUnitScale M σ₀ T).re

theorem goldbach_perron_gaussian_mellin_pairing_normalized_eq_kernel (M : ℕ) (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) :
    goldbachPerronGaussianMellinPairingAtUnitScaleNormalized M σ₀ T =
      goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T 1 := by
  dsimp [goldbachPerronGaussianMellinPairingAtUnitScaleNormalized,
    goldbachPerronGaussianLeftVerticalKernelIntegralNormalized]
  congr 1
  exact congrArg Complex.re (goldbach_perron_gaussian_mellin_pairing_eq_kernel_integral M σ₀ T hσ₀)

private theorem goldbach_truncated_perron_vertical_integrand_interval_integrable
    (M : ℕ) (σ₀ x T : ℝ) (hσ₀ : 0 < σ₀) (hx : 0 < x) :
    IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t) volume (-2 * T)
      (2 * T) :=
  (goldbach_truncated_perron_vertical_integrand_continuousOn M σ₀ x hσ₀ hx
    (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable

theorem goldbach_perron_gaussian_kernel_minus_heat_mellin_normalized_le_eight_fm_plus_one
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    |goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ (T : ℝ) 1 -
        goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ (T : ℝ)| ≤
      8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 := by
  have hx : 0 < (1 : ℝ) := one_pos
  have hTpos : 0 < (T : ℝ) := goldbach_gaussian_height_pos_of_one_le T hT
  have hf := goldbach_perron_gaussian_heat_weighted_mellin_integrand_interval_integrable M σ₀
    (T : ℝ) 1 hσ₀ hx
  have hkernel :=
    goldbach_truncated_perron_vertical_integrand_interval_integrable M σ₀ 1 (T : ℝ) hσ₀ hx
  have hdiff :
      goldbachPerronGaussianLeftVerticalKernelIntegral M σ₀ (T : ℝ) 1 -
          goldbachPerronGaussianMellinPairingAtScale M σ₀ (T : ℝ) 1 =
        goldbachPerronGaussianFMOneMinusHeatGapIntegral M σ₀ (T : ℝ) 1 := by
    have hkernelInt :
        goldbachPerronGaussianLeftVerticalKernelIntegral M σ₀ (T : ℝ) 1 =
          ∫ t in (-2 * (T : ℝ))..(2 * (T : ℝ)), goldbachTruncatedPerronVerticalIntegrand M σ₀ 1 t := by
      dsimp [goldbachPerronGaussianLeftVerticalKernelIntegral, goldbachTruncatedPerronVerticalIntegrand]
    rw [hkernelInt, goldbachPerronGaussianMellinPairingAtScale, goldbachPerronGaussianFMOneMinusHeatGapIntegral]
    rw [← intervalIntegral.integral_sub hkernel hf]
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp [goldbachTruncatedPerronVerticalIntegrand, goldbachPerronGaussianHeatWeightedMellinIntegrand,
      goldbachPerronGaussianFMOneMinusHeatGapIntegrand]
    ring_nf
  have hre :
      goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ (T : ℝ) 1 -
          goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ (T : ℝ) 1 =
        goldbachPerronGaussianFMOneMinusHeatGapIntegralNormalized M σ₀ (T : ℝ) 1 := by
    dsimp [goldbachPerronGaussianLeftVerticalKernelIntegralNormalized,
      goldbachPerronGaussianMellinPairingAtScaleNormalized,
      goldbachPerronGaussianFMOneMinusHeatGapIntegralNormalized]
    rw [← mul_sub, ← Complex.sub_re, hdiff]
  rw [goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized, hre]
  have hinput := goldbachSmoothedPerronContourInput_pairDirichlet M σ₀ hσ₀
  have hC : ∀ t ∈ Set.uIcc (-2 * (T : ℝ)) (2 * (T : ℝ)),
      |(goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re| ≤
        2 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (T : ℝ) := by
    intro t ht
    exact (Complex.abs_re_le_norm _).trans
      (goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_norm_le_from_growth_on_finite_proxy
        M σ₀ (T : ℝ) 1 t hσ₀ hx (by exact_mod_cast hT) hσT hinput)
  have hCnorm : ∀ t ∈ Set.uIcc (-2 * (T : ℝ)) (2 * (T : ℝ)),
      ‖(goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re‖ ≤
        2 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (T : ℝ) := by
    intro t ht; rw [Real.norm_eq_abs]; exact hC t ht
  have hle : -2 * (T : ℝ) ≤ 2 * (T : ℝ) := by linarith
  have hint :
      ‖∫ t in (-2 * (T : ℝ))..(2 * (T : ℝ)),
          (goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re‖ ≤
        2 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (T : ℝ) * |2 * (T : ℝ) - (-2 * (T : ℝ))| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : -2 * (T : ℝ) < t := by
      have hmin : min (-2 * (T : ℝ)) (2 * (T : ℝ)) = -2 * (T : ℝ) := min_eq_left hle
      rwa [hmin] at htl
    have htr' : t ≤ 2 * (T : ℝ) := by
      have hmax : max (-2 * (T : ℝ)) (2 * (T : ℝ)) = 2 * (T : ℝ) := max_eq_right hle
      exact hmax ▸ htr
    exact hCnorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have hre' :
      (goldbachPerronGaussianFMOneMinusHeatGapIntegral M σ₀ (T : ℝ) 1).re =
        ∫ t in (-2 * (T : ℝ))..(2 * (T : ℝ)),
          (goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re :=
    goldbach_intervalIntegral_re _ _ _
      (goldbach_perron_gaussian_fm_one_minus_heat_gap_integrand_interval_integrable M σ₀ (T : ℝ) 1 hσ₀ hx)
  dsimp [goldbachPerronGaussianFMOneMinusHeatGapIntegralNormalized,
    goldbachPerronFMPlusOneVerticalTailErrorTemplate]
  rw [abs_mul, abs_div, abs_of_pos (by positivity), abs_of_pos (by positivity), hre']
  have hbound :
      (1 / (2 * Real.pi)) *
          |∫ t in (-2 * (T : ℝ))..(2 * (T : ℝ)),
              (goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re|
        ≤ 8 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (σ₀ * (T : ℝ)) := by
    calc
      _ ≤ (1 / (2 * Real.pi)) *
            (2 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (T : ℝ) * |2 * (T : ℝ) - (-2 * (T : ℝ))|) := by
        gcongr; exact hint
      _ = 4 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / Real.pi := by
          have hlen : |2 * (T : ℝ) - (-2 * (T : ℝ))| = 4 * (T : ℝ) := by
            have : 2 * (T : ℝ) - (-2 * (T : ℝ)) = 4 * (T : ℝ) := by ring
            rw [this, abs_of_pos (by linarith [hTpos])]
          rw [hlen]
          field_simp
      _ ≤ 8 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (σ₀ * (T : ℝ)) := by
          refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
          calc 4 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ * (σ₀ * (T : ℝ))
              ≤ 4 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ * (2 * Real.pi) := by
                have hpos₁ : 0 ≤ hinput.growth_constant + 1 := by linarith [hinput.growth_constant_nonneg]
                exact mul_le_mul_of_nonneg_left _hσTpi
                  (mul_nonneg (mul_nonneg (by norm_num) hpos₁) (Real.rpow_nonneg (by norm_num) σ₀))
            _ = 8 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ * Real.pi := by ring
  have hB :
      hinput.growth_constant + 1 =
        goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ + 1 := by
    rw [hinput.growth_constant_eq_value]
  calc
    (1 / (2 * Real.pi)) *
        |∫ t in (-2 * (T : ℝ))..(2 * (T : ℝ)),
            (goldbachPerronGaussianFMOneMinusHeatGapIntegrand M σ₀ (T : ℝ) 1 t).re|
        ≤ 8 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (σ₀ * (T : ℝ)) := hbound
    _ ≤ 8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 := by
      have hEq :
          8 * (hinput.growth_constant + 1) * (1 : ℝ) ^ σ₀ / (σ₀ * (T : ℝ)) =
            8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 := by
        dsimp [goldbachPerronFMPlusOneVerticalTailErrorTemplate]
        rw [max_eq_right (by exact_mod_cast hT), one_rpow, hB, one_mul]
        ring
      exact le_of_eq hEq

/-- Legacy name: honest bound is `8 ×` FMPlusOne via `‖1 − G_T‖ ≤ 2`. -/
theorem goldbach_perron_gaussian_kernel_minus_heat_mellin_normalized_le_four_fm_plus_one
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    |goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ (T : ℝ) 1 -
        goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ (T : ℝ)| ≤
      8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 :=
  goldbach_perron_gaussian_kernel_minus_heat_mellin_normalized_le_eight_fm_plus_one M T σ₀ hM hσ₀ hT
    hσT _hσTpi

/--
**Subgoal A (full Mellin inversion, exact):** Gaussian-smoothed discrete target equals the
legacy normalized Mellin pairing at `x = 1` (no explicit `G_T` in the integrand).
-/
def GoldbachMidpointGaussianKernelMellinInversionExactHypothesis (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (hT : 1 ≤ T) : Prop :=
  ∀ (M : ℕ),
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT])) =
      goldbachPerronGaussianMellinPairingAtUnitScaleNormalized M σ₀ T

/--
**Subgoal A (operational, error-bounded):** smoothed discrete target ≈ heat-weighted Mellin
pairing, with explicit budget absorbed into the right-edge tail.
-/
def GoldbachMidpointGaussianKernelMellinInversionHypothesis (σ₀ : ℝ) (T : ℕ) (hσ₀ : 0 < σ₀)
    (hT : 1 ≤ T) : Prop :=
  ∀ (M : ℕ) (hM : 0 < M),
    |goldbachGaussianSmoothedPerronDiscreteTarget M (T : ℝ)
        (goldbach_gaussian_height_pos_of_one_le T hT) -
        goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ (T : ℝ)| ≤
      goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT

theorem goldbach_midpoint_gaussian_kernel_mellin_inversion_exact_implies_normalized (σ₀ T : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (M : ℕ)
    (hA : GoldbachMidpointGaussianKernelMellinInversionExactHypothesis σ₀ T hσ₀ hT) :
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT])) =
      goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T 1 := by
  dsimp [GoldbachMidpointGaussianKernelMellinInversionExactHypothesis] at hA
  rw [← goldbach_perron_gaussian_mellin_pairing_normalized_eq_kernel M σ₀ T hσ₀]
  exact hA M

/--
Finite-height error in Subgoal A (vertical tails beyond `2T` before right-edge bookkeeping).
-/
def GoldbachMidpointGaussianMellinFiniteHeightErrorHypothesis (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (hT : 1 ≤ T) : Prop :=
  ∃ (δ : ℝ), 0 ≤ δ ∧
    ∀ (M : ℕ),
      |goldbachPerronGaussianMellinPairingAtUnitScaleNormalized M σ₀ T -
          goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T 1| ≤ δ

theorem goldbach_midpoint_gaussian_mellin_finite_height_error_zero (σ₀ T : ℝ) (hσ₀ : 0 < σ₀)
    (hT : 1 ≤ T) :
    GoldbachMidpointGaussianMellinFiniteHeightErrorHypothesis σ₀ T hσ₀ hT := by
  refine ⟨0, by simp, fun M => ?_⟩
  simp [goldbach_perron_gaussian_mellin_pairing_normalized_eq_kernel M σ₀ T hσ₀]

/--
**Subgoal A₂ (Mellin bridge on `Re s = σ₀`):** after Fourier inversion, the Gaussian-smoothed
discrete sum equals the normalized unit-scale Mellin pairing (finite-height proxy).
This is the `F_M`-coupled form of Subgoal A; proving A₂ is the main analytic workload.
-/
def GoldbachMidpointGaussianMellinBridgeHypothesis (σ₀ : ℝ) (T : ℕ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) :
    Prop :=
  GoldbachMidpointGaussianKernelMellinInversionHypothesis σ₀ T hσ₀ hT

theorem goldbach_midpoint_gaussian_kernel_mellin_inversion_of_mellin_bridge
    (σ₀ : ℝ) (T : ℕ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (hbridge : GoldbachMidpointGaussianMellinBridgeHypothesis σ₀ T hσ₀ hT) :
    GoldbachMidpointGaussianKernelMellinInversionHypothesis σ₀ T hσ₀ hT :=
  hbridge

/-!
Expected proof factorisation of `GoldbachMidpointGaussianMellinBridgeHypothesis`:

`GoldbachMidpointGaussianFourierInversionHypothesis` (A₁, discrete kernel mass)
  + `GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis` (A₀ lattice)
  + `GoldbachMidpointGaussianKernelVerticalTailHypothesis` (A₀ tail)
  ⇒ `GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis` (A₀)
  ⇒ Mellin bridge (A₂) ⇒ `GoldbachMidpointGaussianKernelMellinInversionHypothesis`.
-/

/--
Packaging of proved Subgoal A₀ components (lattice + vertical tail + discrete normalization).
-/
theorem goldbach_midpoint_gaussian_subgoal_a0_components (M T : ℕ) (hM : 0 < M) (hT : 1 ≤ T) :
    GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis M T ∧
      GoldbachMidpointGaussianKernelDiscreteLatticeHypothesis M T ∧
      GoldbachMidpointGaussianKernelVerticalTailHypothesis T := by
  refine ⟨goldbach_midpoint_gaussian_kernel_discrete_normalization M T hM hT, ?_, ?_⟩
  · exact goldbach_midpoint_gaussian_kernel_discrete_lattice_hypothesis M T hM hT
  · exact goldbach_midpoint_gaussian_kernel_vertical_tail_hypothesis T (Nat.succ_le_iff.mpr hT)

/-!
## Subgoal A₂ factorisation (kernel mass vs heat-weighted Mellin pairing)

Target (pure-kernel layer, before aggregate coupling):

`|∑_{1≤N≤M} K_T(N;M) − (1/2π) ∫_{|t|≤2T} F_M(σ₀+it) · G_T(t) · x^{σ₀+it}/(σ₀+it) dt|
  ≤ ε_A2(M,T,σ₀,x)`.

**Proof split**

1. **A₂.0 (Poisson → Mellin anchor, no `F_M`):**
   **Proved core:** `goldbach_midpoint_gaussian_kernel_near_vertical_heat_integral` —
   discrete kernel mass vs `∫_{|t|≤2T} G_T` with error `goldbachGaussianA20HeatKernelMellinLinkError`
   (= A₁ Poisson + vertical tail).
   **Mellin anchor:** `goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link` adds the
   `1/s` Perron weight via `goldbachGaussianHeatKernelVerticalMellinAnchorGap`; closed by
   `goldbach_midpoint_gaussian_heat_kernel_vertical_mellin_anchor_bridge` when `1 ≤ σ₀`.

2. **A₂.1 (Mellin inversion of `F_M` against `G_T`):**
   `GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis` —
   `|∫ (F_M−1)·G_T·x^s/s|/(2π)` bounded by `4 · goldbachPerronFMPlusOneVerticalTailErrorTemplate`
   (honest full-proxy coarse bound; `≤ 8 · goldbachPerronVerticalTailErrorTemplate` when `B_{M,σ} ≥ 1`).
   **Proved (Path 1):** `goldbach_midpoint_gaussian_f_mellin_anchor_bridge` under
   `σ₀ ≥ T`, `σ₀·T ≤ 2π`, `1 ≤ T`; infrastructure including
   `goldbach_perron_gaussian_mellin_minus_anchor_eq_fm_integral`, central/tail split,
   tail bound `goldbach_perron_gaussian_fm_minus_one_heat_mellin_tail_le_bookkeeping_bound`,
   full-integral bound `goldbach_perron_gaussian_fm_minus_one_heat_mellin_integral_normalized_le_bookkeeping`.
   **Path 2 (optional tighten):** `GoldbachMidpointGaussianFMellinCentralAnchorHypothesis` and
   `GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis_sharp` (single `B_{M,σ}` template).

3. **Combine (proved below):**
   `goldbach_midpoint_gaussian_mellin_kernel_pairing_of_anchor_and_bridge`.

The smoothed readout `∑ K·a_N` is then separated algebraically from the pure kernel mass by
`goldbach_smoothed_perron_discrete_target_kernel_gap_eq`; aggregate coupling does not re-enter
A₁/A₂ (`goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_kernel_pairing`).
-/

/--
**Subgoal A₂ kernel pairing (named input):** centred kernel mass vs heat-weighted Mellin
pairing at scale `x`, with explicit error absorbed into the right-edge tail budget.

This is the pure-kernel layer after A₁; the `F_M` factor enters when passing to the smoothed
aggregate target (`GoldbachMidpointGaussianSmoothedMellinPairingHypothesis`).

Provable from A₂.0 + A₂.1 via `goldbach_midpoint_gaussian_mellin_kernel_pairing_of_anchor_and_bridge`.
-/
def GoldbachMidpointGaussianMellinKernelPairingHypothesis (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
      goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ (T : ℝ) x| ≤
    goldbachGaussianA2MellinKernelPairingError M T σ₀ x

/--
**Subgoal A₂ smoothed pairing:** Gaussian-smoothed discrete target vs normalized heat-weighted
Mellin pairing at `x = 1` (the operational readout for the Cauchy left edge).
-/
def GoldbachMidpointGaussianSmoothedMellinPairingHypothesis (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) : Prop :=
  |goldbachGaussianSmoothedPerronDiscreteTarget M (T : ℝ)
      (goldbach_gaussian_height_pos_of_one_le T hT) -
      goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ (T : ℝ)| ≤
    goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT

/--
Pure-kernel Mellin anchor: kernel mass vs `G_T`-weighted Perron anchor (no `F_M`).
Provable from `goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_hypothesis` when `1 ≤ σ₀`.
-/
def GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ) -
      goldbachGaussianHeatKernelMellinAnchorNormalized σ₀ (T : ℝ) x| ≤
    goldbachGaussianA2HeatKernelMellinAnchorLinkError M T σ₀

theorem goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_hypothesis (M T : ℕ) (σ₀ : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T) :
    GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis M T σ₀ 1 hM hσ₀ hT (by norm_num) := by
  dsimp [GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis,
    goldbachGaussianA2HeatKernelMellinAnchorLinkError,
    goldbachGaussianHeatKernelMellinAnchorAtUnitScale,
    goldbachGaussianHeatKernelMellinAnchorNormalized]
  exact goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link_of_bridge M T σ₀ hM
    (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hT) hσ₁
    (goldbach_midpoint_gaussian_heat_kernel_vertical_mellin_anchor_bridge σ₀ T hσ₁
      (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hT))

theorem goldbach_gaussian_a2_mellin_kernel_pairing_error_decomposition (M T : ℕ) (σ₀ x : ℝ) :
    goldbachGaussianA2MellinKernelPairingError M T σ₀ x =
      goldbachGaussianA2HeatKernelMellinAnchorLinkError M T σ₀ +
        4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
  dsimp [goldbachGaussianA2MellinKernelPairingError]

/--
A₂.0 + A₂.1 ⇒ kernel–Mellin pairing: triangle inequality on the explicit error budget.
-/
theorem goldbach_midpoint_gaussian_mellin_kernel_pairing_of_anchor_and_bridge
    (M T : ℕ) (σ₀ x : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (hAnchor : GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis M T σ₀ x hM hσ₀ hT hx)
    (hBridge : GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis M T σ₀ x hM hσ₀ hT hx) :
    GoldbachMidpointGaussianMellinKernelPairingHypothesis M T σ₀ x hM hσ₀ hT hx := by
  dsimp [GoldbachMidpointGaussianMellinKernelPairingHypothesis,
    GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis,
    GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis,
    goldbachGaussianA2MellinKernelPairingError, goldbachPerronGaussianMellinMinusAnchorNormalized]
  set kernel := goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ)
  set mellin := goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ (T : ℝ) x
  set anchor := goldbachGaussianHeatKernelMellinAnchorNormalized σ₀ (T : ℝ) x
  have htri : |kernel - mellin| ≤ |kernel - anchor| + |anchor - mellin| := by
    calc
      |kernel - mellin| = |kernel - anchor + (anchor - mellin)| := by ring_nf
      _ ≤ |kernel - anchor| + |anchor - mellin| := abs_add_le _ _
  calc
    |kernel - mellin| ≤ |kernel - anchor| + |anchor - mellin| := htri
    _ ≤ goldbachGaussianA2HeatKernelMellinAnchorLinkError M T σ₀ +
          4 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) x := by
      gcongr
      · exact hAnchor
      · rw [abs_sub_comm anchor mellin]
        exact hBridge
    _ = goldbachGaussianA2MellinKernelPairingError M T σ₀ x :=
        (goldbach_gaussian_a2_mellin_kernel_pairing_error_decomposition M T σ₀ x).symm

theorem goldbach_midpoint_gaussian_kernel_mellin_inversion_of_smoothed_pairing
    (σ₀ : ℝ) (T : ℕ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (h : ∀ M (hM : 0 < M), GoldbachMidpointGaussianSmoothedMellinPairingHypothesis M T σ₀ hM hσ₀ hT) :
    GoldbachMidpointGaussianKernelMellinInversionHypothesis σ₀ T hσ₀ hT := by
  intro M hM
  exact h M hM

/--
Hypothesis (3) from hypothesis (2): kernel–Mellin pairing controls the kernel gap; aggregate
coupling is the exact algebraic remainder and does not re-invoke A₁.
-/
theorem goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_kernel_pairing
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (hk : GoldbachMidpointGaussianMellinKernelPairingHypothesis M T σ₀ 1 hM hσ₀ hT (by norm_num)) :
    GoldbachMidpointGaussianSmoothedMellinPairingHypothesis M T σ₀ hM hσ₀ hT := by
  dsimp [GoldbachMidpointGaussianSmoothedMellinPairingHypothesis,
    GoldbachMidpointGaussianMellinKernelPairingHypothesis, goldbachGaussianA2SmoothedMellinPairingError,
    goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized]
  dsimp [GoldbachMidpointGaussianMellinKernelPairingHypothesis] at hk
  have ht : 0 < (T : ℝ) := goldbach_gaussian_height_pos_of_one_le T hT
  have hgap := goldbach_smoothed_perron_discrete_target_kernel_gap_eq M (T : ℝ) ht
  set smoothed := goldbachGaussianSmoothedPerronDiscreteTarget M (T : ℝ) ht
  set mellin := goldbachPerronGaussianMellinPairingAtScaleNormalized M σ₀ (T : ℝ) 1
  set kernel := goldbachMidpointGaussianKernelTruncatedSum M (T : ℝ)
  set coupling := goldbachGaussianSmoothedAggregateCouplingSum M (T : ℝ) ht
  have hsplit : smoothed - mellin = (kernel - mellin) + coupling := by
    dsimp [smoothed, mellin, kernel, coupling]
    linarith [hgap]
  have hkm : |kernel - mellin| ≤ goldbachGaussianA2MellinKernelPairingError M T σ₀ 1 := by
    dsimp [kernel, mellin] at hk ⊢
    exact hk
  calc
    |smoothed - mellin| = |(kernel - mellin) + coupling| := by
      dsimp [smoothed, mellin, kernel, coupling]
      rw [hsplit]
    _ ≤ |kernel - mellin| + |coupling| := abs_add_le _ _
    _ ≤ goldbachGaussianA2MellinKernelPairingError M T σ₀ 1 + |coupling| :=
        add_le_add hkm le_rfl
    _ ≤ goldbachGaussianSmoothedAggregateCouplingErrorNat M T hT +
          goldbachGaussianA2MellinKernelPairingError M T σ₀ 1 := by
      dsimp [goldbachGaussianSmoothedAggregateCouplingErrorNat,
        goldbachGaussianSmoothedAggregateCouplingError, coupling]
      rw [add_comm]

theorem goldbach_midpoint_gaussian_mellin_kernel_pairing_hypothesis (M T : ℕ) (σ₀ : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    GoldbachMidpointGaussianMellinKernelPairingHypothesis M T σ₀ 1 hM hσ₀ hT (by norm_num) :=
  goldbach_midpoint_gaussian_mellin_kernel_pairing_of_anchor_and_bridge M T σ₀ 1 hM hσ₀ hT (by norm_num)
    (goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_hypothesis M T σ₀ hM hσ₀ hσ₁ hT)
    (goldbach_midpoint_gaussian_f_mellin_anchor_bridge M T σ₀ 1 hM hσ₀ hT (by norm_num) hσT _hσTpi)

theorem goldbach_midpoint_gaussian_smoothed_mellin_pairing_hypothesis (M T : ℕ) (σ₀ : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    GoldbachMidpointGaussianSmoothedMellinPairingHypothesis M T σ₀ hM hσ₀ hT :=
  goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_kernel_pairing M T σ₀ hM hσ₀ hT
    (goldbach_midpoint_gaussian_mellin_kernel_pairing_hypothesis M T σ₀ hM hσ₀ hσ₁ hT hσT _hσTpi)

/--
Smoothed pairing from A₂.0 + A₂.1 at unit scale (aggregate coupling handled algebraically).
-/
theorem goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_anchor_and_bridge
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T)
    (hσT : (T : ℝ) ≤ σ₀) (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    GoldbachMidpointGaussianSmoothedMellinPairingHypothesis M T σ₀ hM hσ₀ hT :=
  goldbach_midpoint_gaussian_smoothed_mellin_pairing_hypothesis M T σ₀ hM hσ₀ hσ₁ hT hσT _hσTpi

theorem goldbach_midpoint_gaussian_kernel_mellin_inversion_exact_of_legacy_pairing
    (σ₀ T : ℝ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (h : ∀ M,
      goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT])) =
        goldbachPerronGaussianMellinPairingAtUnitScaleNormalized M σ₀ T) :
    GoldbachMidpointGaussianKernelMellinInversionExactHypothesis σ₀ T hσ₀ hT :=
  h

/-!
Once `GoldbachMidpointGaussianMellinKernelPairingHypothesis` is proved — either directly or via
A₂.0 (`GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis`) plus A₂.1
(`GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis`) —
the smoothed readout follows from `goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_kernel_pairing`
without re-proving A₁: the aggregate coupling `∑ K·(a_N−1)` is the exact algebraic split from
`goldbach_smoothed_perron_discrete_target_kernel_gap_eq`.
-/

/-! ### Subgoal B / C and composite left-edge target -/

/--
**Subgoal B (Perron kernel identification):** on `Re s = σ₀`, the left vertical edge integral
with base `x` equals the normalized kernel integral against `F_M`.

Analytic content: `∫ F_M(σ₀+it) · x^{σ₀+it}/(σ₀+it) dt` is the Mellin–Perron pairing of `F_M`
with the vertical heat profile; for `σ₀ > 0` and `x > 0` this is the standard inversion
integrand (finite truncation in `M`).
-/
def GoldbachMidpointGaussianPerronKernelMatchHypothesis (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
    goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T x

/--
**Subgoal C (truncation error):** replacing the full vertical line `Im s ∈ ℝ` by the finite
height `[-2T, 2T]` is negligible in the Mellin inversion step at the truncation level `M`.

This is the finite-`T` proxy error; tail control is handled separately on the right edge.
-/
def GoldbachMidpointGaussianMellinTruncationHypothesis (M : ℕ) (σ₀ T x : ℝ)
    (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧
    |goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x -
        goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT]))| ≤
      ε

/--
**Composite Gaussian Mellin target:** left vertical edge = Gaussian-smoothed discrete target.
Wired as Subgoal B when Subgoal A is specialized to `x = 1` and kernel normalization matches.
-/
def GoldbachMidpointGaussianMellinLeftVerticalHypothesis (M : ℕ) (σ₀ T x : ℝ) (hT : 1 ≤ T) : Prop :=
  goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT]))

/--
Heat-kernel form: Gaussian weights against local aggregates match the Mellin–Perron kernel
integral on `Re s = σ₀` (Subgoal A at `x = 1`, before Perron kernel scaling).
-/
def GoldbachMidpointGaussianHeatKernelMellinHypothesis (M : ℕ) (σ₀ T x : ℝ) (hT : 1 ≤ T) : Prop :=
  goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T x =
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT]))

theorem goldbach_midpoint_gaussian_heat_kernel_mellin_iff_normalized_kernel (M : ℕ) (σ₀ T x : ℝ)
    (hT : 1 ≤ T) :
    GoldbachMidpointGaussianHeatKernelMellinHypothesis M σ₀ T x hT ↔
      goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T x =
        goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT])) :=
  Iff.rfl

theorem goldbach_midpoint_gaussian_heat_kernel_mellin_of_kernel_mellin_inversion_exact
    (σ₀ T : ℝ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (hA : GoldbachMidpointGaussianKernelMellinInversionExactHypothesis σ₀ T hσ₀ hT) (M : ℕ) :
    GoldbachMidpointGaussianHeatKernelMellinHypothesis M σ₀ T (1 : ℝ) hT := by
  dsimp [GoldbachMidpointGaussianHeatKernelMellinHypothesis,
    GoldbachMidpointGaussianKernelMellinInversionExactHypothesis] at hA ⊢
  rw [← goldbach_perron_gaussian_mellin_pairing_normalized_eq_kernel M σ₀ T hσ₀, hA M]

def GoldbachSmoothedPerronLeftEdgeMellinHypothesis (M : ℕ) (σ₀ σ T x : ℝ) (hT : 1 ≤ T) : Prop :=
  GoldbachMidpointGaussianMellinLeftVerticalHypothesis M σ₀ T x hT

theorem goldbach_smoothed_perron_left_edge_mellin_of_kernel_match_and_heat_kernel
    (M : ℕ) (σ₀ σ T x : ℝ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T) (hx : 0 < x)
    (hmatch : GoldbachMidpointGaussianPerronKernelMatchHypothesis M σ₀ T x hσ₀ hT hx)
    (hheat : GoldbachMidpointGaussianHeatKernelMellinHypothesis M σ₀ T x hT) :
    GoldbachSmoothedPerronLeftEdgeMellinHypothesis M σ₀ σ T x hT :=
  hmatch.trans hheat

/--
**Subgoal B (proved):** left vertical Perron edge = normalized `F_M`-weighted kernel integral.
-/
theorem goldbach_midpoint_gaussian_perron_kernel_match (M : ℕ) (σ₀ T x : ℝ) (hσ₀ : 0 < σ₀)
    (hT : 1 ≤ T) (hx : 0 < x) :
    GoldbachMidpointGaussianPerronKernelMatchHypothesis M σ₀ T x hσ₀ hT hx := by
  have hint :
      IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t) volume
        (-2 * T) (2 * T) :=
    (goldbach_truncated_perron_vertical_integrand_continuousOn M σ₀ x hσ₀ hx
      (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable
  have heq :
      goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
        goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ T x := by
    dsimp [goldbachPerronLeftVerticalEdgeIntegral, goldbachPerronGaussianLeftVerticalKernelIntegralNormalized,
      goldbachPerronGaussianLeftVerticalKernelIntegral]
    rw [← goldbach_intervalIntegral_re (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t) (-2 * T)
      (2 * T) hint]
    congr 1
  exact heq

theorem goldbach_smoothed_perron_horizontal_edges_vanish_of_complex
    (M : ℕ) (σ₀ σ T x : ℝ)
    (h : GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ T x)
    (hReal : GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x) :
    GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x :=
  hReal

theorem goldbach_smoothed_perron_cauchy_boundary_vanishes_of_horizontal_and_vertical_equality
    (M : ℕ) (σ₀ σ T x : ℝ)
    (hhoriz : GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x)
    (hlr :
      goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
        goldbachPerronRightVerticalEdgeIntegral M σ T x) :
    GoldbachSmoothedPerronCauchyBoundaryVanishes M σ₀ σ T x := by
  dsimp [GoldbachSmoothedPerronCauchyBoundaryVanishes, goldbachPerronCauchyRectangleBoundaryIntegral]
  rcases hhoriz with ⟨htop, hbottom⟩
  linarith

theorem goldbach_smoothed_perron_cauchy_boundary_vanishes_of_complex_goursat_and_horizontal
    (M : ℕ) (x σ₀ σ T : ℝ) (hσ₀ : 0 < σ₀) (hσ : 0 < σ) (hσ₀σ : σ₀ ≤ σ) (hx : 0 < x) (hT : 1 ≤ T)
    (hhorizComplex : GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ T x)
    (hhorizReal : GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x) :
    GoldbachSmoothedPerronCauchyBoundaryVanishes M σ₀ σ T x := by
  have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hT)
  have hlr :
      goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
        goldbachPerronRightVerticalEdgeIntegral M σ T x := by
    have hlr' :
        goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x =
          goldbachPerronRightVerticalEdgeComplexIntegral M σ T x := by
      have hcauchy :=
        goldbach_perron_contour_complex_rectangle_boundary_eq_zero M x σ₀ σ T hσ₀ hσ₀σ hx
      have hsum :
          goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T -
              goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T +
              Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x -
              Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x = 0 := by
        rw [← goldbach_perron_complex_rectangle_boundary_eq_edge_sum, hcauchy]
      rcases hhorizComplex with ⟨htop, hbottom⟩
      have hvert :
          Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x =
            Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x :=
        sub_eq_zero.mp (by simpa [htop, hbottom] using hsum)
      exact (smul_right_inj Complex.I_ne_zero).mp hvert.symm
    have hint₀ :
        IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t) volume
          (-2 * T) (2 * T) :=
      (goldbach_truncated_perron_vertical_integrand_continuousOn M σ₀ x hσ₀ hx
        (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable
    have hintσ :
        IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ x t) volume
          (-2 * T) (2 * T) :=
      (goldbach_truncated_perron_vertical_integrand_continuousOn M σ x hσ hx
        (Set.uIcc (-2 * T) (2 * T))).intervalIntegrable
    have hre :
        (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ₀ x t).re) =
          (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) := by
      rw [← goldbach_intervalIntegral_re _ _ _ hint₀, ← goldbach_intervalIntegral_re _ _ _ hintσ]
      dsimp [goldbachTruncatedPerronVerticalIntegrand, goldbachPerronContourIntegrand,
        goldbachPerronLeftVerticalEdgeComplexIntegral, goldbachPerronRightVerticalEdgeComplexIntegral]
      exact congrArg Complex.re hlr'
    exact congr_arg (fun r => (1 / (2 * Real.pi)) * r) hre
  exact goldbach_smoothed_perron_cauchy_boundary_vanishes_of_horizontal_and_vertical_equality M σ₀ σ T x
    hhorizReal hlr

/--
Relaxed left-edge budget: A₂ smoothed pairing error plus the pure-kernel vs heat-Mellin gap
(`F_M · (1 − G_T)` on the finite proxy; triangle bound `‖1 − G_T‖ ≤ 2` ⇒ eight `(B+1)`-templates).
-/
noncomputable def goldbachGaussianLeftEdgeMellinLinkError (M T : ℕ) (σ₀ : ℝ) (hT : 1 ≤ T) : ℝ :=
  goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT +
    8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1

theorem goldbach_gaussian_left_edge_mellin_link_error_nonneg (M T : ℕ) (hM : 0 < M) (hT : 1 ≤ T)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    0 ≤ goldbachGaussianLeftEdgeMellinLinkError M T σ₀ hT := by
  dsimp [goldbachGaussianLeftEdgeMellinLinkError]
  apply add_nonneg
  · exact goldbach_gaussian_a2_smoothed_mellin_pairing_error_nonneg M T hM hT σ₀ hσ₀
  · exact mul_nonneg (by norm_num)
      (goldbach_perron_fm_plus_one_tail_template_nonneg M σ₀ (T : ℝ) 1 hσ₀ (by norm_num))

/-! ## Fejér / Gaussian hybrid left-edge budget (partial Path A) -/

/--
Hybrid A₂ budget: Fejér aggregate coupling plus the Gaussian-chart kernel–Mellin slack.

Until a full Fejér heat/Mellin route exists, the analytic A₂.1–A₂.3 steps remain on the
Gaussian normalisation; only the structural coupling term switches to Fejér compact support.
-/
noncomputable def goldbachFejerGaussianHybridA2SmoothedMellinPairingError (M T : ℕ) (σ₀ : ℝ)
    (hT : 1 ≤ T) : ℝ :=
  goldbachFejerSmoothedAggregateCouplingErrorNat M T hT +
    goldbachGaussianA2MellinKernelPairingError M T σ₀ 1

noncomputable def goldbachFejerGaussianHybridLeftEdgeMellinLinkError (M T : ℕ) (σ₀ : ℝ)
    (hT : 1 ≤ T) : ℝ :=
  goldbachFejerGaussianHybridA2SmoothedMellinPairingError M T σ₀ hT +
    8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1

theorem goldbach_fejer_gaussian_hybrid_a2_smoothed_mellin_pairing_error_nonneg (M T : ℕ)
    (hM : 0 < M) (hT : 1 ≤ T) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    0 ≤ goldbachFejerGaussianHybridA2SmoothedMellinPairingError M T σ₀ hT := by
  dsimp [goldbachFejerGaussianHybridA2SmoothedMellinPairingError]
  apply add_nonneg
  · exact goldbach_fejer_smoothed_aggregate_coupling_error_nat_nonneg M T hT
  · exact goldbach_gaussian_a2_mellin_kernel_pairing_error_nonneg M T hM
      (lt_of_lt_of_le Nat.zero_lt_one hT) σ₀ 1 hσ₀ (by norm_num)

theorem goldbach_fejer_gaussian_hybrid_left_edge_mellin_link_error_nonneg (M T : ℕ) (hM : 0 < M)
    (hT : 1 ≤ T) (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    0 ≤ goldbachFejerGaussianHybridLeftEdgeMellinLinkError M T σ₀ hT := by
  dsimp [goldbachFejerGaussianHybridLeftEdgeMellinLinkError]
  apply add_nonneg
  · exact goldbach_fejer_gaussian_hybrid_a2_smoothed_mellin_pairing_error_nonneg M T hM hT σ₀ hσ₀
  · exact mul_nonneg (by norm_num)
      (goldbach_perron_fm_plus_one_tail_template_nonneg M σ₀ (T : ℝ) 1 hσ₀ (by norm_num))

theorem goldbach_fejer_gaussian_hybrid_a2_smoothed_mellin_pairing_error_le_coupling_bound_plus_kernel
    (M T : ℕ) (σ₀ : ℝ) (hM : 0 < M) (hT : 1 ≤ T) :
    goldbachFejerGaussianHybridA2SmoothedMellinPairingError M T σ₀ hT ≤
      goldbachFejerSmoothedAggregateCouplingBoundNat M T hT +
        goldbachGaussianA2MellinKernelPairingError M T σ₀ 1 := by
  dsimp [goldbachFejerGaussianHybridA2SmoothedMellinPairingError]
  gcongr
  exact goldbach_fejer_smoothed_aggregate_coupling_error_nat_le_bound M T hT

theorem goldbach_fejer_gaussian_hybrid_left_edge_le_gaussian_left_edge_of_coupling
    (M T : ℕ) (σ₀ : ℝ) (hT : 1 ≤ T)
    (h_coupling :
      goldbachFejerSmoothedAggregateCouplingErrorNat M T hT ≤
        goldbachGaussianSmoothedAggregateCouplingErrorNat M T hT) :
    goldbachFejerGaussianHybridLeftEdgeMellinLinkError M T σ₀ hT ≤
      goldbachGaussianLeftEdgeMellinLinkError M T σ₀ hT := by
  dsimp [goldbachFejerGaussianHybridLeftEdgeMellinLinkError, goldbachGaussianLeftEdgeMellinLinkError,
    goldbachFejerGaussianHybridA2SmoothedMellinPairingError, goldbachGaussianA2SmoothedMellinPairingError]
  linarith [h_coupling]

def GoldbachFejerGaussianHybridLeftEdgeMellinErrorHypothesis (M T : ℕ) (σ₀ : ℝ) (hT : 1 ≤ T) :
    Prop :=
  |goldbachPerronLeftVerticalEdgeIntegral M σ₀ (T : ℝ) 1 -
      goldbachFejerSmoothedPerronDiscreteTarget M (T : ℝ)
        (goldbach_gaussian_height_pos_of_one_le T hT)|
    ≤ goldbachFejerGaussianHybridLeftEdgeMellinLinkError M T σ₀ hT

def GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis (M T : ℕ) (σ₀ : ℝ) (hT : 1 ≤ T) : Prop :=
  |goldbachPerronLeftVerticalEdgeIntegral M σ₀ (T : ℝ) 1 -
      goldbachSmoothedPerronDiscreteTarget M
        (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT))|
    ≤ goldbachGaussianLeftEdgeMellinLinkError M T σ₀ hT

theorem goldbach_smoothed_perron_left_edge_mellin_error_of_a2_pipeline (M T : ℕ) (σ₀ : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi)
    (hSmoothed : GoldbachMidpointGaussianSmoothedMellinPairingHypothesis M T σ₀ hM hσ₀ hT) :
    GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis M T σ₀ hT := by
  dsimp [GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis,
    GoldbachMidpointGaussianSmoothedMellinPairingHypothesis]
  set left := goldbachPerronLeftVerticalEdgeIntegral M σ₀ (T : ℝ) 1
  set kernel := goldbachPerronGaussianLeftVerticalKernelIntegralNormalized M σ₀ (T : ℝ) 1
  set mellin := goldbachPerronGaussianMellinPairingAtUnitScaleWithHeatKernelNormalized M σ₀ (T : ℝ)
  set smoothed := goldbachGaussianSmoothedPerronDiscreteTarget M (T : ℝ)
    (goldbach_gaussian_height_pos_of_one_le T hT)
  have hmatch := goldbach_midpoint_gaussian_perron_kernel_match M σ₀ (T : ℝ) 1 hσ₀
    (by exact_mod_cast hT) (by norm_num)
  have hleft : left = kernel := hmatch
  have hdev :
      |kernel - mellin| ≤ 8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 :=
    goldbach_perron_gaussian_kernel_minus_heat_mellin_normalized_le_eight_fm_plus_one M T σ₀ hM hσ₀ hT
      hσT _hσTpi
  calc
    |left - smoothed| = |kernel - smoothed| := by rw [hleft]
    _ ≤ |kernel - mellin| + |mellin - smoothed| := by
        calc
          |kernel - smoothed| = |kernel - mellin + (mellin - smoothed)| := by ring_nf
          _ ≤ |kernel - mellin| + |mellin - smoothed| := abs_add_le _ _
    _ ≤ 8 * goldbachPerronFMPlusOneVerticalTailErrorTemplate M σ₀ (T : ℝ) 1 +
          goldbachGaussianA2SmoothedMellinPairingError M T σ₀ hT :=
      add_le_add hdev (by
        rw [abs_sub_comm mellin smoothed]
        exact hSmoothed)
    _ = goldbachGaussianLeftEdgeMellinLinkError M T σ₀ hT := by
        dsimp [goldbachGaussianLeftEdgeMellinLinkError]
        ring

theorem goldbach_smoothed_perron_left_edge_mellin_error_hypothesis (M T : ℕ) (σ₀ : ℝ)
    (hM : 0 < M) (hσ₀ : 0 < σ₀) (hσ₁ : 1 ≤ σ₀) (hT : 1 ≤ T) (hσT : (T : ℝ) ≤ σ₀)
    (_hσTpi : σ₀ * (T : ℝ) ≤ 2 * Real.pi) :
    GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis M T σ₀ hT :=
  goldbach_smoothed_perron_left_edge_mellin_error_of_a2_pipeline M T σ₀ hM hσ₀ hσ₁ hT hσT _hσTpi
    (goldbach_midpoint_gaussian_smoothed_mellin_pairing_hypothesis M T σ₀ hM hσ₀ hσ₁ hT hσT _hσTpi)

/--
Relaxed Cauchy rectangle: proved boundary from Goursat + complex horizontal vanishing;
left edge controlled by `GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis`.
Horizontal edges remain the named finite-`T` input (Subgoal B/C route).
-/
structure GoldbachSmoothedPerronCauchyRectangleErrorHypothesis (M T : ℕ) (σ x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) where
  σ₀ : ℝ
  σ₀_pos : 0 < σ₀
  σ₀_lt_σ : σ₀ < σ
  horizontal_complex_vanish :
    GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ (T : ℝ) x
  horizontal_vanish :
    GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ (T : ℝ) x
  left_edge_error :
    GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis M T σ₀ hT

def goldbach_smoothed_perron_cauchy_rectangle_error_hypothesis_of_a2_pipeline
    (M T : ℕ) (sigmaLeft σ x : ℝ) (hM : 0 < M) (hσLeft : 0 < sigmaLeft) (hσ : 0 < σ)
    (hσLeft_lt_σ : sigmaLeft < σ) (hσLeft₁ : 1 ≤ sigmaLeft) (hT : 1 ≤ T) (hx : 0 < x)
    (hσT : (T : ℝ) ≤ sigmaLeft) (_hσTpi : sigmaLeft * (T : ℝ) ≤ 2 * Real.pi)
    (hHorizComplex : GoldbachSmoothedPerronHorizontalComplexEdgesVanish M sigmaLeft σ (T : ℝ) x)
    (hHorizReal : GoldbachSmoothedPerronHorizontalEdgesVanish M sigmaLeft σ (T : ℝ) x) :
    GoldbachSmoothedPerronCauchyRectangleErrorHypothesis M T σ x hσ hT hx :=
  { σ₀ := sigmaLeft
    σ₀_pos := hσLeft
    σ₀_lt_σ := hσLeft_lt_σ
    horizontal_complex_vanish := hHorizComplex
    horizontal_vanish := hHorizReal
    left_edge_error :=
      goldbach_smoothed_perron_left_edge_mellin_error_of_a2_pipeline M T sigmaLeft hM hσLeft hσLeft₁
        hT hσT _hσTpi
        (goldbach_midpoint_gaussian_smoothed_mellin_pairing_hypothesis M T sigmaLeft hM hσLeft
          hσLeft₁ hT hσT _hσTpi) }

theorem goldbach_gaussian_smoothing_mellin_tail_error_of_cauchy_rectangle_error
    (M T : ℕ) (σ x : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hx1 : x = 1)
    (hrect : GoldbachSmoothedPerronCauchyRectangleErrorHypothesis M T σ x hσ hT hx) :
    |goldbachSmoothedPerronDiscreteTarget M
        (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
        goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) x -
          goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) x|
      ≤ goldbachGaussianLeftEdgeMellinLinkError M T hrect.σ₀ hT := by
  have hTpos : 0 < (T : ℝ) := goldbach_gaussian_height_pos_of_one_le T hT
  have hσ₀σ : hrect.σ₀ ≤ σ := le_of_lt hrect.σ₀_lt_σ
  have hboundary :=
    goldbach_smoothed_perron_cauchy_boundary_vanishes_of_complex_goursat_and_horizontal M x
      hrect.σ₀ σ (T : ℝ) hrect.σ₀_pos hσ hσ₀σ hx (by exact_mod_cast hT)
      hrect.horizontal_complex_vanish hrect.horizontal_vanish
  have hhoriz := hrect.horizontal_vanish
  have hright :=
    goldbach_perron_right_vertical_edge_eq_central_plus_tail M σ (T : ℝ) x hσ hTpos hx
  have hlr :
      goldbachPerronLeftVerticalEdgeIntegral M hrect.σ₀ (T : ℝ) x =
        goldbachPerronRightVerticalEdgeIntegral M σ (T : ℝ) x := by
    dsimp [GoldbachSmoothedPerronCauchyBoundaryVanishes, goldbachPerronCauchyRectangleBoundaryIntegral]
      at hboundary
    rcases hhoriz with ⟨htop, hbottom⟩
    linarith [hboundary, htop, hbottom]
  set smoothed := goldbachSmoothedPerronDiscreteTarget M
    (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT))
  set central := goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) x
  set tail := goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) x
  set leftEdge := goldbachPerronLeftVerticalEdgeIntegral M hrect.σ₀ (T : ℝ) 1
  have hleft := hrect.left_edge_error
  dsimp [GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis] at hleft
  subst hx1
  calc
    |smoothed - central - tail| = |smoothed - (central + tail)| := by ring_nf
    _ = |smoothed - leftEdge| := by
        rw [show central + tail = leftEdge from Eq.symm (hlr.trans hright)]
    _ ≤ goldbachGaussianLeftEdgeMellinLinkError M T hrect.σ₀ hT := by
        rw [abs_sub_comm smoothed leftEdge]
        exact hleft

theorem goldbach_truncated_perron_integrand_re_le_norm (M : ℕ) (σ x t : ℝ) :
    |(goldbachTruncatedPerronVerticalIntegrand M σ x t).re| ≤
      ‖goldbachTruncatedPerronVerticalIntegrand M σ x t‖ :=
  Complex.abs_re_le_norm _

theorem goldbach_smoothed_perron_bounded_tail_integral_le (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x| ≤
      input.growth_constant * x ^ σ / Real.pi := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hC : ∀ t, T ≤ |t| →
      ‖goldbachTruncatedPerronVerticalIntegrand M σ x t‖ ≤
        input.growth_constant * x ^ σ / T :=
    fun t ht =>
      goldbach_perron_integrand_norm_le_tail_from_growth M σ T x t input hx ht hT
  have hC' : ∀ t ∈ Set.uIcc T (2 * T),
      |(goldbachTruncatedPerronVerticalIntegrand M σ x t).re| ≤
        input.growth_constant * x ^ σ / T := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨htl, htr⟩ | ⟨htl, htr⟩
    · have htpos : 0 < t := lt_of_lt_of_le hTpos htl
      exact (goldbach_truncated_perron_integrand_re_le_norm M σ x t).trans
        (hC t (by rw [abs_of_pos htpos]; exact htl))
    · linarith [hTpos, htl]
  have hCneg : ∀ t ∈ Set.uIcc (-2 * T) (-T),
      |(goldbachTruncatedPerronVerticalIntegrand M σ x t).re| ≤
        input.growth_constant * x ^ σ / T := by
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨htl, htr⟩ | ⟨htl, htr⟩
    · have htneg : t < 0 := lt_of_le_of_lt htr (neg_neg_of_pos hTpos)
      have hTle : T ≤ |t| := by rw [abs_of_neg htneg]; linarith [htr]
      exact (goldbach_truncated_perron_integrand_re_le_norm M σ x t).trans (hC t hTle)
    · linarith [hTpos, htr]
  dsimp [goldbachTruncatedPerronVerticalTailIntegral]
  rw [abs_mul, abs_div, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hpos1 : 0 < T := hTpos
  have hpos2 : 0 < 2 * T := mul_pos two_pos hTpos
  have hle : T ≤ 2 * T := by linarith
  have hle' : -2 * T ≤ -T := by linarith
  have hpos1' : 0 < |2 * T - T| := by
    have : 2 * T - T = T := by ring
    rw [this, abs_of_pos hpos1]
    exact hpos1
  have hpos2' : 0 < |(-T) - (-2 * T)| := by
    have : (-T) - (-2 * T) = T := by ring
    rw [this, abs_of_pos hpos1]
    exact hpos1
  have hCnorm : ∀ t ∈ Set.uIcc T (2 * T),
      ‖(goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ ≤
        input.growth_constant * x ^ σ / T := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact hC' t ht
  have hCnegNorm : ∀ t ∈ Set.uIcc (-2 * T) (-T),
      ‖(goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ ≤
        input.growth_constant * x ^ σ / T := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact hCneg t ht
  have htail1 :
      ‖∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ ≤
        input.growth_constant * x ^ σ / T * |2 * T - T| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : T < t := by
      have hmin : min T (2 * T) = T := min_eq_left hle
      rwa [hmin] at htl
    have htr' : t ≤ 2 * T := by
      have hmax : max T (2 * T) = 2 * T := max_eq_right hle
      exact hmax ▸ htr
    exact hCnorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have htail2 :
      ‖∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ ≤
        input.growth_constant * x ^ σ / T * |(-T) - (-2 * T)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    rcases ht with ⟨htl, htr⟩
    have htl' : -2 * T < t := by
      have hmin : min (-2 * T) (-T) = -2 * T := min_eq_left hle'
      rwa [hmin] at htl
    have htr' : t ≤ -T := by
      have hmax : max (-2 * T) (-T) = -T := max_eq_right hle'
      exact hmax ▸ htr
    exact hCnegNorm t (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt htl', htr'⟩))
  have habs_sum :
      ‖(∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) +
          (∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re)‖ ≤
        ‖∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ +
          ‖∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ :=
    norm_add_le _ _
  calc (1 / (2 * Real.pi)) *
        |(∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) +
          (∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re)|
      ≤ (1 / (2 * Real.pi)) *
          (‖∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖ +
            ‖∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖) := by
        gcongr
        rw [← Real.norm_eq_abs]
        exact habs_sum
    _ ≤ (1 / (2 * Real.pi)) *
          (input.growth_constant * x ^ σ / T * T +
            input.growth_constant * x ^ σ / T * T) := by
      gcongr
      · calc
          ‖∫ t in T..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖
              ≤ input.growth_constant * x ^ σ / T * |2 * T - T| := htail1
          _ = input.growth_constant * x ^ σ / T * T := by
            have : 2 * T - T = T := by ring
            rw [this, abs_of_pos hpos1]
      · calc
          ‖∫ t in (-2 * T)..(-T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re‖
              ≤ input.growth_constant * x ^ σ / T * |(-T) - (-2 * T)| := htail2
          _ = input.growth_constant * x ^ σ / T * T := by
            have : (-T) - (-2 * T) = T := by ring
            rw [this, abs_of_pos hpos1]
    _ = input.growth_constant * x ^ σ / Real.pi := by
      field_simp
      ring

/--
**Tail integral bound** (two-ray bookkeeping constant).

From proved vertical growth on the bounded tail proxy, the normalized tail integral is at most
`2 · B_{M,σ} · x^σ / (σ · T)` when additionally `σ · T ≤ 2π` (always true in the
critical-line regime `σ = 1/2`, `T ≥ 1`).  This matches twice
`goldbachPerronVerticalTailErrorTemplate` when `T ≥ 1`.
-/
theorem goldbach_smoothed_perron_tail_integral_bound (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x| ≤
      goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input :=
  calc
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x|
        ≤ input.growth_constant * x ^ σ / Real.pi :=
      goldbach_smoothed_perron_bounded_tail_integral_le M σ T x hσ hT hx input
    _ ≤ 2 * input.growth_constant * x ^ σ / (σ * T) := by
      refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
      simpa [mul_comm, mul_left_comm, mul_assoc, two_mul] using
        mul_le_mul_of_nonneg_left hσT
          (mul_nonneg input.growth_constant_nonneg (Real.rpow_nonneg hx.le σ))

theorem goldbach_smoothed_perron_tail_integral_bound_template (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x| ≤
      2 * goldbachPerronVerticalTailErrorTemplate M σ T x :=
  calc
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x|
        ≤ goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input :=
      goldbach_smoothed_perron_tail_integral_bound M σ T x hσ hT hx hσT input
    _ = 2 * goldbachPerronVerticalTailErrorTemplate M σ T x :=
      goldbach_smoothed_perron_tail_bookkeeping_bound_eq_two_template M σ T x hσ hT hx.le input

theorem SmoothedGaussianPerronContourInversion_from_cauchy_rectangle_error (M T : ℕ) (σ x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hx1 : x = 1) (hσT : σ * (T : ℝ) ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hrect : GoldbachSmoothedPerronCauchyRectangleErrorHypothesis M T σ x hσ hT hx) :
    |goldbachSmoothedPerronDiscreteTarget M
        (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
        goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) x|
      ≤ goldbachSmoothedPerronTailContourBookkeepingBound M σ (T : ℝ) x input +
          goldbachGaussianLeftEdgeMellinLinkError M T hrect.σ₀ hT := by
  subst hx1
  have ht :=
    goldbach_gaussian_smoothing_mellin_tail_error_of_cauchy_rectangle_error M T σ 1 hσ hT (by norm_num) rfl
      hrect
  have htail := goldbach_smoothed_perron_tail_integral_bound M σ (T : ℝ) 1 hσ (by exact_mod_cast hT)
    (by norm_num) hσT input
  calc
    |goldbachSmoothedPerronDiscreteTarget M
          (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
        goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1|
        = |goldbachSmoothedPerronDiscreteTarget M
              (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
            goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1 -
              goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) 1 +
            goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) 1| := by ring_nf
    _ ≤ |goldbachSmoothedPerronDiscreteTarget M
            (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
          goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1 -
            goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) 1| +
        |goldbachTruncatedPerronVerticalTailIntegral M σ (T : ℝ) 1| := abs_add_le _ _
    _ ≤ goldbachSmoothedPerronTailContourBookkeepingBound M σ (T : ℝ) 1 input +
          goldbachGaussianLeftEdgeMellinLinkError M T hrect.σ₀ hT := by
      rw [add_comm]
      exact add_le_add htail ht

/--
Explicit relaxed contour error at unit scale (`x = 1`): tail bookkeeping plus left-edge Mellin link.
-/
noncomputable def goldbachSmoothedPerronCauchyRectangleErrorTotalBound (M T : ℕ) (σ σ₀ : ℝ)
    (hT : 1 ≤ T) (input : GoldbachSmoothedPerronContourInput M σ) : ℝ :=
  goldbachSmoothedPerronTailContourBookkeepingBound M σ (T : ℝ) 1 input +
    goldbachGaussianLeftEdgeMellinLinkError M T σ₀ hT

theorem goldbach_smoothed_perron_cauchy_rectangle_error_total_bound_nonneg (M T : ℕ) (σ σ₀ : ℝ)
    (hM : 0 < M) (hσ : 0 < σ) (hσ₀ : 0 < σ₀) (hT : 1 ≤ T)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    0 ≤ goldbachSmoothedPerronCauchyRectangleErrorTotalBound M T σ σ₀ hT input := by
  dsimp [goldbachSmoothedPerronCauchyRectangleErrorTotalBound]
  apply add_nonneg
  · exact goldbach_smoothed_perron_tail_contour_bookkeeping_bound_nonneg M σ (T : ℝ) 1 hσ
      (by exact_mod_cast hT) (by norm_num) input
  · exact goldbach_gaussian_left_edge_mellin_link_error_nonneg M T hM hT σ₀ hσ₀

/--
Relaxed analytic certificate from the Cauchy rectangle error route (Path A).
At `x = 1` the smoothed–central gap is bounded by tail bookkeeping plus left-edge Mellin error.
-/
structure SmoothedPerronRelaxedAnalyticCertificate (M T : ℕ) (σ : ℝ) where
  hσ : 0 < σ
  hT : 1 ≤ T
  σ₀ : ℝ
  σ₀_pos : 0 < σ₀
  contour_input : GoldbachSmoothedPerronContourInput M σ
  total_error_le :
    |goldbachSmoothedPerronDiscreteTarget M
        (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
        goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1|
      ≤ goldbachSmoothedPerronCauchyRectangleErrorTotalBound M T σ σ₀ hT contour_input

noncomputable def smoothedPerronRelaxedAnalyticCertificate_from_cauchy_rectangle_error
    (M T : ℕ) (σ : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hσT : σ * (T : ℝ) ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hrect : GoldbachSmoothedPerronCauchyRectangleErrorHypothesis M T σ 1 hσ hT (by norm_num)) :
    SmoothedPerronRelaxedAnalyticCertificate M T σ where
  hσ := hσ
  hT := hT
  σ₀ := hrect.σ₀
  σ₀_pos := hrect.σ₀_pos
  contour_input := input
  total_error_le :=
    SmoothedGaussianPerronContourInversion_from_cauchy_rectangle_error M T σ 1 hσ hT (by norm_num) rfl
      hσT input hrect

/-! ## Step 3: Euler–Maclaurin harmonic tail ↔ Perron chart (unit scale) -/

/--
Gaussian-smoothed Perron chart error at unit scale `x = 1`:

`smoothedTarget − centralVerticalIntegral`.
This is exactly the quantity bounded by `SmoothedPerronRelaxedAnalyticCertificate`.
-/
noncomputable def goldbachSmoothedPerronChartRemainderAtUnitScale (M T : ℕ) (σ : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) : ℝ :=
  goldbachSmoothedPerronDiscreteTarget M
      (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
    goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1

theorem goldbach_smoothed_perron_chart_remainder_at_unit_scale_eq (M T : ℕ) (σ : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) :
    goldbachSmoothedPerronChartRemainderAtUnitScale M T σ hσ hT =
      goldbachSmoothedPerronDiscreteTarget M
          (goldbachMidpointGaussianSmoother (T : ℝ) (goldbach_gaussian_height_pos_of_one_le T hT)) -
        goldbachTruncatedPerronVerticalIntegral M σ (T : ℝ) 1 :=
  rfl

theorem goldbach_smoothed_perron_relaxed_certificate_chart_eq (M T : ℕ) (σ : ℝ)
    (cert : SmoothedPerronRelaxedAnalyticCertificate M T σ) :
    |goldbachSmoothedPerronChartRemainderAtUnitScale M T σ cert.hσ cert.hT| ≤
      goldbachSmoothedPerronCauchyRectangleErrorTotalBound M T σ cert.σ₀ cert.hT
        cert.contour_input :=
  cert.total_error_le

/--
**Step 3 identification (exact):** the classical Euler–Maclaurin tail
`weightDifferenceEulerMaclaurinRemainder N` equals the smoothed Perron chart error
at aligned truncation `M = N`, height `T`, and unit scale `x = 1`.

This is the formal bridge between the harmonic/classical side (`Δ_N` tail) and the
Goldbach contour certificate (Path A left-edge + tail bookkeeping).
-/
structure GoldbachPerronEulerMaclaurinContourIdentification (N M T : ℕ) (σ : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) where
  hM : M = N
  em_remainder_eq_chart :
    weightDifferenceEulerMaclaurinRemainder N =
      goldbachSmoothedPerronChartRemainderAtUnitScale M T σ hσ hT

theorem goldbach_perron_em_remainder_abs_eq_chart_abs
    {N M T : ℕ} {σ : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N M T σ hσ hT) :
    |weightDifferenceEulerMaclaurinRemainder N| =
      |goldbachSmoothedPerronChartRemainderAtUnitScale M T σ hσ hT| := by
  rw [hId.em_remainder_eq_chart]

/--
Packaging of step 3 at an explicit bound `B`.
-/
def GoldbachSmoothedPerronEulerMaclaurinContourHolds (N : ℕ) (bound : ℝ) : Prop :=
  |weightDifferenceEulerMaclaurinRemainder N| ≤ bound

theorem goldbach_smoothed_perron_euler_maclaurin_contour_holds_of_identification_and_certificate
    {N T : ℕ} {σ σ₀ : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N N T σ hσ hT)
    (cert : SmoothedPerronRelaxedAnalyticCertificate N T σ) :
    GoldbachSmoothedPerronEulerMaclaurinContourHolds N
      (goldbachSmoothedPerronCauchyRectangleErrorTotalBound N T σ cert.σ₀ hT
        cert.contour_input) := by
  dsimp [GoldbachSmoothedPerronEulerMaclaurinContourHolds]
  rw [goldbach_perron_em_remainder_abs_eq_chart_abs hσ hT hId]
  exact cert.total_error_le

/--
Unified explicit-formula / Euler–Maclaurin contour remainder (classical side by definition).
Both harmonic and Perron routes should target this quantity at truncation `N`.
-/
noncomputable def goldbachExplicitFormulaEulerMaclaurinContourRemainder (N : ℕ) : ℝ :=
  weightDifferenceEulerMaclaurinRemainder N

/--
Explicit-formula contour duality: harmonic EM tail and Perron chart error are the same
contour remainder.  Instantiated from the discrete explicit formula + Goldbach
generating-function Mellin route (step 3 analytic content).
-/
structure GoldbachExplicitFormulaEulerMaclaurinContourDuality (N M T : ℕ) (σ : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) where
  hM : M = N
  perron_chart_eq_contour :
    goldbachSmoothedPerronChartRemainderAtUnitScale M T σ hσ hT =
      goldbachExplicitFormulaEulerMaclaurinContourRemainder N

theorem goldbach_perron_euler_maclaurin_contour_identification_of_explicit_formula_duality
    {N M T : ℕ} {σ : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T)
    (hDual : GoldbachExplicitFormulaEulerMaclaurinContourDuality N M T σ hσ hT) :
    GoldbachPerronEulerMaclaurinContourIdentification N M T σ hσ hT where
  hM := hDual.hM
  em_remainder_eq_chart := hDual.perron_chart_eq_contour.symm

theorem perron_contour_remainder_bound_of_identification_and_relaxed_certificate
    {N T : ℕ} {σ σ₀ : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hT : 1 ≤ T)
    (hId : GoldbachPerronEulerMaclaurinContourIdentification N N T σ hσ hT)
    (cert : SmoothedPerronRelaxedAnalyticCertificate N T σ) :
    ∃ B, 0 ≤ B ∧
      |weightDifferenceEulerMaclaurinRemainder N| ≤ B := by
  refine
    ⟨goldbachSmoothedPerronCauchyRectangleErrorTotalBound N T σ cert.σ₀ hT cert.contour_input,
      ?_, ?_⟩
  · exact goldbach_smoothed_perron_cauchy_rectangle_error_total_bound_nonneg N T σ cert.σ₀ hN hσ
      cert.σ₀_pos hT cert.contour_input
  · rw [goldbach_perron_em_remainder_abs_eq_chart_abs hσ hT hId]
    exact cert.total_error_le

/--
Named packaging of the tail-integral bound against the explicit template.
-/
def GoldbachPerronTailIntegralBoundHypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) : Prop :=
  |goldbachTruncatedPerronVerticalTailIntegral M σ T x| ≤
    goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input

theorem goldbach_perron_tail_integral_bound_hypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    GoldbachPerronTailIntegralBoundHypothesis M σ T x hσ hT hx input :=
  goldbach_smoothed_perron_tail_integral_bound M σ T x hσ hT hx hσT input

/--
Sharper single-template tail bound when `σ · T ≤ π` (e.g. `σ = 1/2`, `T ≥ 1`).
-/
theorem goldbach_smoothed_perron_tail_integral_le_single_template (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x| ≤
      goldbachPerronVerticalTailErrorTemplate M σ T x :=
  calc
    |goldbachTruncatedPerronVerticalTailIntegral M σ T x|
        ≤ input.growth_constant * x ^ σ / Real.pi :=
      goldbach_smoothed_perron_bounded_tail_integral_le M σ T x hσ hT hx input
    _ ≤ goldbachPerronVerticalTailErrorTemplate M σ T x := by
      dsimp [goldbachPerronVerticalTailErrorTemplate]
      rw [max_eq_right hT, input.growth_constant_eq_value]
      refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
      have hxσ : 0 < x ^ σ := Real.rpow_pos_of_pos hx σ
      have hgrowth :=
        goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg M σ
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hσT (mul_nonneg hgrowth hxσ.le)

/--
General smoothed analytic tail bound (any midpoint smoother `S`).
-/
def GoldbachSmoothedPerronAnalyticTailBound_for (M : ℕ) (σ T x : ℝ)
    (S : GoldbachMidpointSmoother) (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  |goldbachSmoothedPerronDiscreteTarget M S -
      goldbachTruncatedPerronVerticalIntegral M σ T x| ≤
    goldbachPerronVerticalTailErrorTemplate M σ T x

theorem goldbach_smoothed_perron_analytic_tail_bound_gaussian_eq_for (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) :
    GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx ↔
      GoldbachSmoothedPerronAnalyticTailBound_for M σ T x
        (goldbachMidpointGaussianSmoother T (by linarith)) hσ hT hx :=
  Iff.rfl

/--
Explicit quantified form requested for contour closure:

`|error| ≤ C / T` with `C = x^σ · B_{M,σ} / σ`.
-/
def GoldbachSmoothedPerronAnalyticTailBound_explicit (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) : Prop :=
  let tailBound := x ^ σ * input.growth_constant / (σ * T)
  0 ≤ tailBound ∧
    |goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
        goldbachTruncatedPerronVerticalIntegral M σ T x| ≤ tailBound

theorem goldbach_smoothed_perron_analytic_tail_bound_explicit_of_template (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (h : GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx) :
    GoldbachSmoothedPerronAnalyticTailBound_explicit M σ T x hσ hT hx input := by
  dsimp [GoldbachSmoothedPerronAnalyticTailBound_explicit]
  constructor
  · have htemplate :=
      goldbach_perron_tail_template_eq_growth_quotient M σ T x hσ hT hx.le input
    rw [← htemplate]
    exact goldbach_perron_vertical_tail_error_template_nonneg M σ T x hσ hx.le
  · have htemplate :=
      goldbach_perron_tail_template_eq_growth_quotient M σ T x hσ hT hx.le input
    dsimp only [GoldbachSmoothedPerronAnalyticTailBound] at h
    exact htemplate.symm ▸ h

theorem goldbach_smoothed_perron_analytic_tail_bound_eq_explicit (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx ↔
      GoldbachSmoothedPerronAnalyticTailBound_explicit M σ T x hσ hT hx input := by
  constructor
  · exact goldbach_smoothed_perron_analytic_tail_bound_explicit_of_template M σ T x hσ hT hx input
  · intro h
    dsimp [GoldbachSmoothedPerronAnalyticTailBound_explicit] at h
    dsimp [GoldbachSmoothedPerronAnalyticTailBound]
    rcases h with ⟨_, hbound⟩
    exact (goldbach_perron_tail_template_eq_growth_quotient M σ T x hσ hT hx.le input).symm ▸ hbound

theorem goldbach_smoothed_perron_chart_total_error_le_template (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (h : GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx) :
    |(smoothedTruncatedPerronFormula_gaussian M σ T x hσ hT hx).total_error| ≤
      (smoothedTruncatedPerronFormula_gaussian M σ T x hσ hT hx).error_bound := by
  dsimp [smoothedTruncatedPerronFormula_gaussian, GoldbachSmoothedPerronAnalyticTailBound] at h ⊢
  exact h

/--
**Contour inversion target** (Cauchy rectangle + Gaussian smoothing on `N`):

from holomorphy on `{Re s > 0}` and vertical growth `‖F_M(σ+it)‖ ≤ B_{M,σ}`,
the smoothed discrete readout differs from the truncated vertical Perron integral by
at most `x^σ B_{M,σ} / (σ T)` when `T ≥ 1`.
-/
def SmoothedGaussianPerronContourInversionHypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) : Prop :=
  GoldbachSmoothedPerronAnalyticTailBound_explicit M σ T x hσ hT hx input

/-! ## Contour inversion proof outline -/

/--
Contour strategy for closing `SmoothedGaussianPerronContourInversionHypothesis`.

* `rightVertical_smoothing_tail` — stay on `Re s = σ > 0`; Gaussian/Fejér smoothing on `N`
  matches the Mellin–Perron kernel; tail on `|t| ≥ T` is bounded using only `B_{M,σ}`.
* `leftShift_rectangle_residue` — standard rectangle with left edge `Re s = σ₀ < σ`;
  requires additional half-plane growth beyond the current `B_{M,σ}` certificate.
-/
inductive GoldbachSmoothedPerronContourStrategy
  | rightVertical_smoothing_tail
  | leftShift_rectangle_residue

/--
**Mellin–Perron compatibility (Gaussian smoothing on `N`).**

Bookkeeping decomposition: smoothed discrete = truncated vertical integral + remainder.
The **analytic** step is to identify that remainder with a tail contour integral on
`|t| ≥ T` and bound it using `GoldbachPerronIntegrandTailBoundFromGrowth`.
-/
def GoldbachGaussianSmoothingMellinHypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  ∃ (remainder : ℝ),
    goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) =
      goldbachTruncatedPerronVerticalIntegral M σ T x + remainder

theorem goldbach_gaussian_smoothing_mellin_decomposition (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) :
    GoldbachGaussianSmoothingMellinHypothesis M σ T x hσ hT hx := by
  dsimp [GoldbachGaussianSmoothingMellinHypothesis]
  set S := goldbachMidpointGaussianSmoother T (by linarith)
  set target := goldbachSmoothedPerronDiscreteTarget M S
  set integral := goldbachTruncatedPerronVerticalIntegral M σ T x
  refine ⟨target - integral, ?_⟩
  dsimp [target, integral]
  ring

/--
**Gaussian-smoothed Perron representation:** smoothed discrete target equals central
vertical integral plus normalized tail on the bounded two-ray proxy.

This is the contour inversion content; rearranging gives
`GoldbachGaussianSmoothingMellinTailIdentity`.
-/
def GoldbachGaussianSmoothingMellinPerronRepresentation (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith [hT])) =
    goldbachTruncatedPerronVerticalIntegral M σ T x +
      goldbachTruncatedPerronVerticalTailIntegral M σ T x

/--
Once complex horizontal edges vanish, Cauchy–Goursat gives `left_vertical = right_vertical` on the
rectangle; combined with `GoldbachSmoothedPerronLeftEdgeMellinHypothesis` this is the only
remaining analytic input for inversion.
-/
theorem goldbach_smoothed_perron_cauchy_rectangle_reduces_to_left_mellin_when_horiz_vanish
    (M : ℕ) (σ₀ σ T x : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (hσ₀ : 0 < σ₀) (hσ₀σ : σ₀ ≤ σ)
    (hhoriz : GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ T x)
    (hleft : GoldbachSmoothedPerronLeftEdgeMellinHypothesis M σ₀ σ T x hT) :
    GoldbachGaussianSmoothingMellinPerronRepresentation M σ T x hσ hT hx := by
  dsimp [GoldbachSmoothedPerronHorizontalComplexEdgesVanish,
    GoldbachSmoothedPerronLeftEdgeMellinHypothesis,
    GoldbachMidpointGaussianMellinLeftVerticalHypothesis,
    GoldbachGaussianSmoothingMellinPerronRepresentation] at hhoriz hleft ⊢
  rcases hhoriz with ⟨htop, hbottom⟩
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hright :=
    goldbach_perron_right_vertical_edge_eq_central_plus_tail M σ T x hσ hTpos hx
  have hcauchy :=
    goldbach_perron_contour_complex_rectangle_boundary_eq_zero M x σ₀ σ T hσ₀ hσ₀σ hx
  have hsum :
      goldbachPerronBottomHorizontalEdgeComplexIntegral M x σ₀ σ T -
        goldbachPerronTopHorizontalEdgeComplexIntegral M x σ₀ σ T +
        Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x -
        Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x = 0 := by
    rw [← goldbach_perron_complex_rectangle_boundary_eq_edge_sum, hcauchy]
  have hlr :
      goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x =
        goldbachPerronRightVerticalEdgeComplexIntegral M σ T x := by
    have hvert :
        Complex.I • goldbachPerronRightVerticalEdgeComplexIntegral M σ T x =
          Complex.I • goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x :=
      sub_eq_zero.mp (by simpa [htop, hbottom] using hsum)
    exact (smul_right_inj Complex.I_ne_zero).mp hvert.symm
  have hlr_re :
      (goldbachPerronLeftVerticalEdgeComplexIntegral M σ₀ T x).re =
        (goldbachPerronRightVerticalEdgeComplexIntegral M σ T x).re :=
    congrArg Complex.re hlr
  have hlr_edge :
      goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
        goldbachPerronRightVerticalEdgeIntegral M σ T x := by
    have hint₀ :
        IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t) volume
          (-2 * T) (2 * T) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith [hTpos])
        (goldbach_truncated_perron_vertical_integrand_continuousOn M σ₀ x hσ₀ hx
          (Set.Icc (-2 * T) (2 * T)))
    have hintσ :
        IntervalIntegrable (fun t => goldbachTruncatedPerronVerticalIntegrand M σ x t) volume
          (-2 * T) (2 * T) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith [hTpos])
        (goldbach_truncated_perron_vertical_integrand_continuousOn M σ x hσ hx
          (Set.Icc (-2 * T) (2 * T)))
    have hre :
        (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ₀ x t).re) =
          (∫ t in (-2 * T)..(2 * T), (goldbachTruncatedPerronVerticalIntegrand M σ x t).re) := by
      rw [← goldbach_intervalIntegral_re (fun t => goldbachTruncatedPerronVerticalIntegrand M σ₀ x t)
          (-2 * T) (2 * T) hint₀,
        ← goldbach_intervalIntegral_re (fun t => goldbachTruncatedPerronVerticalIntegrand M σ x t)
          (-2 * T) (2 * T) hintσ]
      dsimp [goldbachTruncatedPerronVerticalIntegrand, goldbachPerronContourIntegrand,
        goldbachPerronLeftVerticalEdgeComplexIntegral, goldbachPerronRightVerticalEdgeComplexIntegral]
      exact hlr_re
    exact congr_arg (fun r => (1 / (2 * Real.pi)) * r) hre
  rw [hleft.symm, hlr_edge, hright]

theorem goldbach_gaussian_mellin_perron_representation_of_cauchy_data (M : ℕ) (σ₀ σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (hboundary : GoldbachSmoothedPerronCauchyBoundaryVanishes M σ₀ σ T x)
    (hleft : GoldbachSmoothedPerronLeftEdgeMellinHypothesis M σ₀ σ T x hT)
    (hhoriz : GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x) :
    GoldbachGaussianSmoothingMellinPerronRepresentation M σ T x hσ hT hx := by
  dsimp [GoldbachGaussianSmoothingMellinPerronRepresentation,
    GoldbachSmoothedPerronCauchyBoundaryVanishes,
    GoldbachSmoothedPerronLeftEdgeMellinHypothesis,
    GoldbachSmoothedPerronHorizontalEdgesVanish,
    goldbachPerronCauchyRectangleBoundaryIntegral] at hboundary hleft hhoriz ⊢
  rcases hhoriz with ⟨htop, hbottom⟩
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hright :=
    goldbach_perron_right_vertical_edge_eq_central_plus_tail M σ T x hσ hTpos hx
  have hlr :
      goldbachPerronLeftVerticalEdgeIntegral M σ₀ T x =
        goldbachPerronRightVerticalEdgeIntegral M σ T x := by
    linarith [hboundary, htop, hbottom]
  exact hleft.symm.trans (hlr.trans hright)

/--
**Mellin–Perron tail identity (Gaussian smoothing):**

the smoothed discrete remainder equals the normalized tail integral on the bounded
two-ray proxy — this is the analytic input identifying the bookkeeping remainder with
`∫_{|t| ≥ T}` tail contribution.
-/
def GoldbachGaussianSmoothingMellinTailIdentity (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) : Prop :=
  goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
      goldbachTruncatedPerronVerticalIntegral M σ T x =
    goldbachTruncatedPerronVerticalTailIntegral M σ T x

theorem goldbach_gaussian_mellin_tail_identity_iff_perron_representation (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) :
    GoldbachGaussianSmoothingMellinTailIdentity M σ T x hσ hT hx ↔
      GoldbachGaussianSmoothingMellinPerronRepresentation M σ T x hσ hT hx := by
  dsimp [GoldbachGaussianSmoothingMellinTailIdentity,
    GoldbachGaussianSmoothingMellinPerronRepresentation]
  constructor
  · intro h
    linarith [h]
  · intro h
    linarith [h]

/--
Cauchy rectangle route: boundary integral + left-edge Mellin identification + vanishing
horizontal edges ⇒ Gaussian-smoothed Perron representation (hence Mellin tail identity).
-/
structure GoldbachSmoothedPerronCauchyRectangleHypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) where
  σ₀ : ℝ
  σ₀_pos : 0 < σ₀
  σ₀_lt_σ : σ₀ < σ
  boundary_vanishes :
    GoldbachSmoothedPerronCauchyBoundaryVanishes M σ₀ σ T x
  left_edge_mellin :
    GoldbachSmoothedPerronLeftEdgeMellinHypothesis M σ₀ σ T x hT
  horizontal_vanish :
    GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x

def goldbach_smoothed_perron_cauchy_rectangle_hypothesis_of_exact_left_edge
    (M : ℕ) (σ T x : ℝ) (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hσ₀_lt_σ : σ₀ < σ)
    (hHorizComplex : GoldbachSmoothedPerronHorizontalComplexEdgesVanish M σ₀ σ T x)
    (hHorizReal : GoldbachSmoothedPerronHorizontalEdgesVanish M σ₀ σ T x)
    (hLeft : GoldbachSmoothedPerronLeftEdgeMellinHypothesis M σ₀ σ T x hT) :
    GoldbachSmoothedPerronCauchyRectangleHypothesis M σ T x hσ hT hx :=
  { σ₀ := σ₀
    σ₀_pos := hσ₀
    σ₀_lt_σ := hσ₀_lt_σ
    boundary_vanishes :=
      goldbach_smoothed_perron_cauchy_boundary_vanishes_of_complex_goursat_and_horizontal M x σ₀ σ T
        hσ₀ hσ hσ₀_lt_σ.le hx hT hHorizComplex hHorizReal
    left_edge_mellin := hLeft
    horizontal_vanish := hHorizReal }

theorem goldbach_gaussian_mellin_perron_representation_of_cauchy_rectangle (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (hrect : GoldbachSmoothedPerronCauchyRectangleHypothesis M σ T x hσ hT hx) :
    GoldbachGaussianSmoothingMellinPerronRepresentation M σ T x hσ hT hx :=
  goldbach_gaussian_mellin_perron_representation_of_cauchy_data M hrect.σ₀ σ T x hσ hT hx
    hrect.boundary_vanishes hrect.left_edge_mellin hrect.horizontal_vanish

theorem goldbach_gaussian_smoothing_mellin_tail_identity_of_cauchy_rectangle (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (hrect : GoldbachSmoothedPerronCauchyRectangleHypothesis M σ T x hσ hT hx) :
    GoldbachGaussianSmoothingMellinTailIdentity M σ T x hσ hT hx :=
  (goldbach_gaussian_mellin_tail_identity_iff_perron_representation M σ T x hσ hT hx).mpr
    (goldbach_gaussian_mellin_perron_representation_of_cauchy_rectangle M σ T x hσ hT hx hrect)

/--
Right-vertical closure: Mellin tail identity + tail integral bound ⇒ inversion hypothesis.
-/
theorem SmoothedGaussianPerronContourInversion_from_mellin_tail_identity (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hmellin : GoldbachGaussianSmoothingMellinTailIdentity M σ T x hσ hT hx) :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input := by
  dsimp [SmoothedGaussianPerronContourInversionHypothesis,
    GoldbachSmoothedPerronAnalyticTailBound_explicit] at ⊢
  constructor
  · dsimp
    refine div_nonneg (mul_nonneg (Real.rpow_nonneg hx.le σ) input.growth_constant_nonneg) ?_
    refine mul_nonneg hσ.le ?_
    exact le_of_lt (lt_of_lt_of_le zero_lt_one hT)
  · dsimp [GoldbachGaussianSmoothingMellinTailIdentity] at hmellin
    rw [hmellin]
    have hbound :=
      goldbach_smoothed_perron_tail_integral_le_single_template M σ T x hσ hT hx hσT input
    have htemplate :=
      goldbach_perron_tail_template_eq_growth_quotient M σ T x hσ hT hx.le input
    exact htemplate.symm ▸ hbound

theorem SmoothedGaussianPerronContourInversion_from_mellin_tail_bookkeeping (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ 2 * Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hmellin : GoldbachGaussianSmoothingMellinTailIdentity M σ T x hσ hT hx) :
    |goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
        goldbachTruncatedPerronVerticalIntegral M σ T x| ≤
      goldbachSmoothedPerronTailContourBookkeepingBound M σ T x input := by
  rw [hmellin]
  exact goldbach_smoothed_perron_tail_integral_bound M σ T x hσ hT hx hσT input

theorem SmoothedGaussianPerronContourInversion_from_mellin_tail_and_contour_input (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hmellin : GoldbachGaussianSmoothingMellinTailIdentity M σ T x hσ hT hx) :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input :=
  SmoothedGaussianPerronContourInversion_from_mellin_tail_identity M σ T x hσ hT hx hσT input hmellin

theorem SmoothedGaussianPerronContourInversion_from_cauchy_rectangle (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x) (hσT : σ * T ≤ Real.pi)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (hrect : GoldbachSmoothedPerronCauchyRectangleHypothesis M σ T x hσ hT hx) :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input :=
  SmoothedGaussianPerronContourInversion_from_mellin_tail_and_contour_input M σ T x hσ hT hx hσT
    input
    (goldbach_gaussian_smoothing_mellin_tail_identity_of_cauchy_rectangle M σ T x hσ hT hx hrect)

/-- Pointwise integrand control on the tail ray `|t| ≥ T` from proved vertical growth. -/
def GoldbachPerronIntegrandTailBoundFromGrowth (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) : Prop :=
  ∀ t, T ≤ |t| →
    ‖goldbachTruncatedPerronVerticalIntegrand M σ x t‖ ≤
      input.growth_constant * x ^ σ / T

theorem goldbach_perron_integrand_tail_bound_from_growth (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    GoldbachPerronIntegrandTailBoundFromGrowth M σ T x hσ hT hx input := by
  intro t ht
  exact goldbach_perron_integrand_norm_le_tail_from_growth M σ T x t input hx ht hT

/--
**Proved from holomorphy input alone:** pointwise tail integrand control at scale `T`
using only `‖F_M(σ+it)‖ ≤ B_{M,σ}` (no contour shift to `Re s < σ`).
-/
theorem goldbach_smoothed_perron_contour_input_integrand_tail_bound (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) :
    GoldbachPerronIntegrandTailBoundFromGrowth M σ T x hσ hT hx input :=
  goldbach_perron_integrand_tail_bound_from_growth M σ T x hσ hT hx input

/--
Right-vertical strategy closure: Mellin compatibility + tail bound ⇒ explicit template.
-/
def GoldbachSmoothedPerronRightVerticalClosure (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ) : Prop :=
  GoldbachGaussianSmoothingMellinHypothesis M σ T x hσ hT hx ∧
    GoldbachPerronIntegrandTailBoundFromGrowth M σ T x hσ hT hx input ∧
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input

/--
Left-shift rectangle strategy: residue at the pole of `x^s/s` plus bounds on the
relocated vertical line and horizontal edges (requires growth on `Re s ≥ σ₀`).
-/
structure GoldbachSmoothedPerronLeftShiftRectangleHypothesis (M : ℕ) (σ T x : ℝ) where
  hσ : 0 < σ
  hT : 1 ≤ T
  hx : 0 < x
  σ₀ : ℝ
  σ₀_lt_σ : σ₀ < σ
  /-- Growth on the left vertical line `Re s = σ₀` (not supplied by default input). -/
  left_vertical_growth : ℝ
  left_vertical_growth_nonneg : 0 ≤ left_vertical_growth
  residue_main_term_matches_smoothed_target : Prop
  rectangle_remainder_le_template :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx
      (goldbachSmoothedPerronContourInput_pairDirichlet M σ hσ)

/--
Packaging of the recommended proof route (right vertical + smoothing) and the
alternative left-shift rectangle route.
-/
structure SmoothedGaussianPerronContourInversionOutline (M : ℕ) (σ T x : ℝ) where
  hσ : 0 < σ
  hT : 1 ≤ T
  hx : 0 < x
  input : GoldbachSmoothedPerronContourInput M σ
  strategy : GoldbachSmoothedPerronContourStrategy
  mellin :
    GoldbachGaussianSmoothingMellinHypothesis M σ T x hσ hT hx
  tail_from_growth :
    GoldbachPerronIntegrandTailBoundFromGrowth M σ T x hσ hT hx input
  inversion :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input

/--
**Target theorem** (contour inversion from holomorphy + growth):

given `GoldbachSmoothedPerronContourInput` (holomorphy + `B_{M,σ}` vertical bound),
Mellin compatibility of Gaussian smoothing, and tail control, conclude the explicit
template bound.  The analytic proof is packaged in `outline.inversion`.
-/
theorem GoldbachSmoothedPerronContourInversion_from_holomorphic_growth (M : ℕ) (σ T x : ℝ)
    (outline : SmoothedGaussianPerronContourInversionOutline M σ T x) :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x outline.hσ outline.hT outline.hx
      outline.input :=
  outline.inversion

theorem SmoothedGaussianPerronContourInversionOutline.tail_bound_from_input (M : ℕ) (σ T x : ℝ)
    (outline : SmoothedGaussianPerronContourInversionOutline M σ T x) :
    GoldbachPerronIntegrandTailBoundFromGrowth M σ T x outline.hσ outline.hT outline.hx
      outline.input :=
  goldbach_perron_integrand_tail_bound_from_growth M σ T x outline.hσ outline.hT outline.hx
    outline.input

theorem GoldbachSmoothedPerronAnalyticTailBound_of_contour_hypothesis (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (h : SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input) :
    GoldbachSmoothedPerronAnalyticTailBound M σ T x hσ hT hx :=
  (goldbach_smoothed_perron_analytic_tail_bound_eq_explicit M σ T x hσ hT hx input).mpr h

theorem goldbach_smoothed_perron_analytic_tail_bound_explicit_C_div_T (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (h : GoldbachSmoothedPerronAnalyticTailBound_explicit M σ T x hσ hT hx input) :
    |goldbachSmoothedPerronDiscreteTarget M (goldbachMidpointGaussianSmoother T (by linarith)) -
        goldbachTruncatedPerronVerticalIntegral M σ T x| ≤
      (x ^ σ * input.growth_constant / σ) / T := by
  dsimp [GoldbachSmoothedPerronAnalyticTailBound_explicit] at h
  rcases h with ⟨_, hbound⟩
  have hdiv :
      (x ^ σ * input.growth_constant / σ) / T =
        x ^ σ * input.growth_constant / (σ * T) := by field_simp
  rwa [← hdiv] at hbound

theorem goldbach_smoothed_perron_total_error_le_explicit (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (input : GoldbachSmoothedPerronContourInput M σ)
    (h : SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx input) :
    |(smoothedTruncatedPerronFormula_gaussian M σ T x hσ hT hx).total_error| ≤
      (x ^ σ * input.growth_constant / σ) / T := by
  dsimp [SmoothedGaussianPerronContourInversionHypothesis,
    GoldbachSmoothedPerronAnalyticTailBound_explicit, smoothedTruncatedPerronFormula_gaussian] at h ⊢
  rcases h with ⟨_, hbound⟩
  have hdiv :
      (x ^ σ * input.growth_constant / σ) / T =
        x ^ σ * input.growth_constant / (σ * T) := by field_simp
  rwa [← hdiv] at hbound

/--
Certificate: proved holomorphy + vertical growth + contour inversion hypothesis.
-/
structure SmoothedPerronAnalyticCertificate (M : ℕ) (σ T x : ℝ) where
  hσ : 0 < σ
  hT : 1 ≤ T
  hx : 0 < x
  contour_input : GoldbachSmoothedPerronContourInput M σ
  contour_input_σ_pos : contour_input.σ_pos = hσ
  inversion :
    SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx contour_input

theorem SmoothedPerronAnalyticCertificate.goldbach_analytic_tail_bound
    (M : ℕ) (σ T x : ℝ) (cert : SmoothedPerronAnalyticCertificate M σ T x) :
    GoldbachSmoothedPerronAnalyticTailBound M σ T x cert.hσ cert.hT cert.hx :=
  GoldbachSmoothedPerronAnalyticTailBound_of_contour_hypothesis M σ T x cert.hσ cert.hT cert.hx
    cert.contour_input cert.inversion

theorem SmoothedPerronAnalyticCertificate.total_error_le_template
    (M : ℕ) (σ T x : ℝ) (cert : SmoothedPerronAnalyticCertificate M σ T x) :
    |(smoothedTruncatedPerronFormula_gaussian M σ T x cert.hσ cert.hT cert.hx).total_error| ≤
      (smoothedTruncatedPerronFormula_gaussian M σ T x cert.hσ cert.hT cert.hx).error_bound :=
  goldbach_smoothed_perron_chart_total_error_le_template M σ T x cert.hσ cert.hT cert.hx
    (SmoothedPerronAnalyticCertificate.goldbach_analytic_tail_bound M σ T x cert)

theorem SmoothedPerronAnalyticCertificate.total_error_le_explicit
    (M : ℕ) (σ T x : ℝ) (cert : SmoothedPerronAnalyticCertificate M σ T x) :
    |(smoothedTruncatedPerronFormula_gaussian M σ T x cert.hσ cert.hT cert.hx).total_error| ≤
      (x ^ σ * cert.contour_input.growth_constant / σ) / T :=
  goldbach_smoothed_perron_total_error_le_explicit M σ T x cert.hσ cert.hT cert.hx cert.contour_input
    cert.inversion

noncomputable def smoothedTruncatedPerronFormula_gaussian_certified
    (M : ℕ) (σ T x : ℝ) (cert : SmoothedPerronAnalyticCertificate M σ T x) :
    SmoothedTruncatedPerronFormula M σ :=
  { smoothedTruncatedPerronFormula_gaussian M σ T x cert.hσ cert.hT cert.hx with
    analytic_tail_bound_holds :=
      GoldbachSmoothedPerronAnalyticTailBound M σ T x cert.hσ cert.hT cert.hx }

noncomputable def smoothedPerronAnalyticCertificate_pairDirichlet (M : ℕ) (σ T x : ℝ)
    (hσ : 0 < σ) (hT : 1 ≤ T) (hx : 0 < x)
    (hInversion : SmoothedGaussianPerronContourInversionHypothesis M σ T x hσ hT hx
      (goldbachSmoothedPerronContourInput_pairDirichlet M σ hσ)) :
    SmoothedPerronAnalyticCertificate M σ T x where
  hσ := hσ
  hT := hT
  hx := hx
  contour_input := goldbachSmoothedPerronContourInput_pairDirichlet M σ hσ
  contour_input_σ_pos := rfl
  inversion := hInversion

/-! ## Proof strategy bundle -/

/--
End-to-end analytic strategy:

`holomorphy + vertical growth + Perron ⇒ |weightDifferenceEulerMaclaurinRemainder N| ≤ bound`.

`SmoothedTruncatedPerronFormula` pins step 1 (smoothed discrete target + explicit tail decay).
`euler_maclaurin_contour_holds` pins step 3 (harmonic weight remainder).
-/
structure PerronContourRemainderStrategy (N : ℕ) (σ : ℝ) where
  truncationIndex : ℕ := N
  generating : GoldbachPartitionGeneratingFunction :=
    goldbachPartitionGeneratingFunctionOfPairDirichletSum truncationIndex
  holomorphic : IsHolomorphicGoldbachPartition generating
  truncation_aligns_weight : truncationIndex = N
  vertical_growth : HolomorphicVerticalGrowth σ
  growth_generating_eq : vertical_growth.generating = generating
  growth_sigma_matches : vertical_growth.growth.F = generating.F
  /-- Unsmoothed bookkeeping chart (definitional split only). -/
  perron : TruncatedPerronFormula truncationIndex σ
  perron_generating_eq : perron.generating = generating
  /-- Smoothed chart with explicit `O(T^{-δ})` tail bound on `error_bound`. -/
  smoothed_perron : SmoothedTruncatedPerronFormula truncationIndex σ
  smoothed_perron_generating_eq : smoothed_perron.generating = generating
  /-- Step 3: contour comparison yields a bound on the weight-difference EM tail. -/
  strategy_implies_remainder_bound :
    smoothed_perron.analytic_tail_bound_holds →
      smoothed_perron.euler_maclaurin_contour_holds →
        ∃ B, 0 ≤ B ∧ |weightDifferenceEulerMaclaurinRemainder N| ≤ B

theorem perron_strategy_truncation_aligns_weight (N : ℕ) :
    (goldbachPartitionGeneratingFunctionDefault N).F =
      goldbachMidpointGeometricGeneratingSumTruncated N := rfl

theorem perron_strategy_default_generating (N : ℕ) :
    goldbachPartitionGeneratingFunctionDefault N =
      goldbachPartitionGeneratingFunctionOfPairDirichletSum N := rfl

noncomputable def contourGrowthControlsEulerRemainder_of_strategy {N : ℕ} {σ : ℝ}
    (h : PerronContourRemainderStrategy N σ)
    (hAnalytic : h.smoothed_perron.analytic_tail_bound_holds)
    (hContour : h.smoothed_perron.euler_maclaurin_contour_holds) :
    ContourGrowthControlsEulerRemainder N where
  generating := h.generating
  remainderBound := (h.strategy_implies_remainder_bound hAnalytic hContour).choose
  remainder_bound_nonneg :=
    (h.strategy_implies_remainder_bound hAnalytic hContour).choose_spec.1
  holomorphic_implies_remainder_bound := fun _ =>
    (h.strategy_implies_remainder_bound hAnalytic hContour).choose_spec.2

noncomputable def goldbachHolomorphicRegularityCertificate_of_perron_strategy {N : ℕ} {σ : ℝ}
    (h : PerronContourRemainderStrategy N σ)
    (hDefault : h.generating = goldbachPartitionGeneratingFunctionDefault N)
    (hAnalytic : h.smoothed_perron.analytic_tail_bound_holds)
    (hContour : h.smoothed_perron.euler_maclaurin_contour_holds) :
    GoldbachHolomorphicRegularityCertificate N :=
  goldbachHolomorphicRegularityCertificate_of_default_contour
    (contourGrowthControlsEulerRemainder_at_default_truncation
      (contourGrowthControlsEulerRemainder_of_strategy h hAnalytic hContour)
      hDefault)

/-!
## Status

* **Pinned:** `goldbachPerronDiscreteTarget M` (unsmoothed cumulative aggregate);
  `goldbachSmoothedPerronDiscreteTarget M` (Gaussian/Fejér on midpoint index).
* **Proved tail decay:** `goldbachPerronVerticalTailErrorTemplate` with `δ = 1` via
  `goldbachPerronVerticalTailDecay_template` and vertical-growth constant `B_{M,σ}`.
* **Structured:** `GoldbachSmoothedPerronContourInput`, explicit `C/T` bound,
  `SmoothedGaussianPerronContourInversionHypothesis`, `SmoothedPerronAnalyticCertificate`.
* **Proved wiring:** contour hypothesis ⇒ `GoldbachSmoothedPerronAnalyticTailBound` ⇒
  `|total_error| ≤ error_bound` and `|total_error| ≤ C/T`.
* **Proved integrability:** `goldbach_perron_tail_integrable_at_height` from holomorphy of `F_M`
  and continuity of the Perron kernel on compact edges.
* **Cauchy scaffold (proved wiring):** Mathlib ↔ edge-sum bridge
  (`goldbach_perron_mathlib_complex_rectangle_boundary_eq_edge_sum`), Cauchy–Goursat
  (`goldbach_perron_contour_complex_rectangle_boundary_eq_zero`), horizontal template bounds,
  and reduction `goldbach_smoothed_perron_cauchy_rectangle_reduces_to_left_mellin_when_horiz_vanish`.
* **Named analytic inputs:** `GoldbachSmoothedPerronCauchyBoundaryVanishes`,
  `GoldbachSmoothedPerronHorizontalEdgesVanish`, and Subgoal A scaffold
  (`GoldbachMidpointGaussianKernelDiscreteNormalizationHypothesis`,
  `GoldbachMidpointGaussianFourierInversionHypothesis`,
  `GoldbachMidpointGaussianKernelMellinInversionHypothesis`, …).
* **Proved (Subgoal A₀):** `goldbach_midpoint_gaussian_kernel_discrete_normalization`,
  `goldbach_midpoint_gaussian_subgoal_a0_components` (lattice + vertical tail + A₀).
* **Proved (Poisson / ℤ-sum):** `goldbach_midpoint_gaussian_zsum_poisson_factor`
  (`Z = T√(2π) · dualZSum`, not `Z = T√(2π)` alone); dual excess `≥ 1`.
* **Proved (Subgoal A₁, Poisson route):** `goldbach_midpoint_gaussian_fourier_inversion_poisson`
  with explicit `goldbachGaussianA1PoissonFourierInversionError` (mirror gap + `2·`ℕ tail + full×dual excess).
* **Proved (Subgoal A₁, legacy partial):** `goldbach_midpoint_gaussian_fourier_inversion_one` (`M = 1`);
  `goldbach_midpoint_gaussian_fourier_inversion_of_lattice_error_le` (when lattice error ≤ coarse A₁ budget).
* **Proved (A₂.0 core + bridge):** `goldbach_midpoint_gaussian_kernel_near_vertical_heat_integral`
  (Poisson A₁ + vertical tail → finite-height heat integral);
  `goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link` (+ vertical→Mellin gap);
  **A₂.0b:** `goldbach_midpoint_gaussian_heat_kernel_vertical_mellin_anchor_bridge`
  (Poisson complement / `1/(σ₀+it)` Mellin anchor on `|t| ≤ 2T`, needs `1 ≤ σ₀`);
  bridge corollary `goldbach_midpoint_gaussian_heat_kernel_mellin_anchor_link_of_bridge`.
* **Named (Subgoal A₂):** heat-weighted `goldbachPerronGaussianMellinPairingAtScale` with `G_T`;
  factorised as A₂.0 (`GoldbachMidpointGaussianHeatKernelMellinAnchorHypothesis`) +
  A₂.1 (`GoldbachMidpointGaussianFMellinAnchorBridgeHypothesis`);
  combined by `goldbach_midpoint_gaussian_mellin_kernel_pairing_of_anchor_and_bridge`;
  `GoldbachMidpointGaussianMellinKernelPairingHypothesis` (kernel mass vs pairing + error);
  `GoldbachMidpointGaussianSmoothedMellinPairingHypothesis` (smoothed target vs pairing);
  wired to `GoldbachMidpointGaussianKernelMellinInversionHypothesis` via
  `goldbach_midpoint_gaussian_kernel_mellin_inversion_of_smoothed_pairing`.
* **Proved (A₂ wiring):** error budget split
  `goldbach_gaussian_a2_mellin_kernel_pairing_error_decomposition`;
  **Path 1 closure:** unconditional
  `goldbach_midpoint_gaussian_f_mellin_anchor_bridge`,
  `goldbach_midpoint_gaussian_mellin_kernel_pairing_hypothesis`,
  `goldbach_midpoint_gaussian_smoothed_mellin_pairing_hypothesis`,
  `goldbach_midpoint_gaussian_smoothed_mellin_pairing_of_anchor_and_bridge`.
* **Proved (coupling bounds):** `goldbach_gaussian_smoothed_aggregate_coupling_bound`
  (`|∑ K·(a_N−1)| ≤ B_{M,0} + ∑ K`); A₂ split
  `goldbach_gaussian_a2_smoothed_mellin_pairing_error_le_coupling_bound_plus_kernel`;
  `B_{M,σ} ≤ B_{M,0}` via `goldbach_smoothed_perron_growth_constant_le_unweighted_mass`.
* **Proved (Path A closure):** Subgoal B `goldbach_midpoint_gaussian_perron_kernel_match`;
  relaxed left-edge error `GoldbachSmoothedPerronLeftEdgeMellinErrorHypothesis` (A₂ + `8×` FMPlusOne);
  `GoldbachSmoothedPerronCauchyRectangleErrorHypothesis` from A₂ pipeline + horizontal inputs;
  tail identity with error at `x = 1`; contour inversion with relaxed budget;
  **Step 3 wiring:** `GoldbachPerronEulerMaclaurinContourIdentification` and
  `perronToWeightDifferenceBridge_of_identification_and_relaxed_certificate`
  (identification + certificate ⇒ `|weightDifferenceEulerMaclaurinRemainder N| ≤` Cauchy total).
* **Named (step 3 analytic content):** `GoldbachExplicitFormulaEulerMaclaurinContourDuality`
  — instantiate from discrete explicit formula + Goldbach Mellin contour.
* **Remaining:** prove duality; horizontal vanishing at finite `T`; Hardy-`Z` bridge into
  `ModelGuidedLocationBound`; Path 2 sharp A₂.1 optional.
* **Not claimed:** convergence `M → ∞`, full Euler–Maclaurin contour proof.
-/

end

end Hqiv.Story
