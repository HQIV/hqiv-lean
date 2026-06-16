import Hqiv.Story.S3GoldbachHolomorphicWeightBridge
import Hqiv.Story.S3SpectralResonanceChanneling
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Goldbach partition generating function and holomorphic remainder implication

Packages the complex generating function that carries the **holomorphy predicate**
for midpoint geometric-mean fields built from Goldbach partitions, and records the
target implication

`holomorphic regularity ⇒ |weightDifferenceEulerMaclaurinRemainder N| ≤ bound`

as an explicit Lean statement wired into `WeightDifferenceRemainderBound`,
`WeightDifferenceAsymptoticSlot`, and `ModelGuidedLocationBound`.

## Honesty

* `goldbachMidpointGeometricGeneratingSumTruncated` is a concrete Dirichlet-style
  sum over Goldbach midpoint pairs, weighted by `√{pq}` and scaled by `(2N)^{−s}`.
* Holomorphy of the **finite** truncation is proved on the critical half-plane
  `{Re s > 1/2}`; the Euler–Maclaurin / contour implication remains named input.
* No claim that this generating function equals ζ or the harmonic rolling weights.
-/

namespace Hqiv.Story

noncomputable section

open Real Complex Set Hqiv.Geometry
open Complex

/-! ## Generating function carrier -/

/--
Goldbach-partition generating function chart.

`F` is the complex generating function built from Goldbach prime-pair / midpoint
data; `midpointGeometricMeanAt N` is the real midpoint geometric-mean readout at
truncation index `N` (discrete side of the bridge).
-/
structure GoldbachPartitionGeneratingFunction where
  /-- Complex generating function `F(z)`. -/
  F : ℂ → ℂ
  /-- Open holomorphy domain (unit disk, half-plane, etc.). -/
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  /-- Midpoint geometric-mean readout at truncation `N`. -/
  midpointGeometricMeanAt : ℕ → ℝ
  /-- Readout is nonnegative (square-root aggregate). -/
  midpoint_geometric_mean_nonneg :
    ∀ N, 0 ≤ midpointGeometricMeanAt N

/-- Holomorphy predicate on the generating function. -/
def IsHolomorphicGoldbachPartition (G : GoldbachPartitionGeneratingFunction) : Prop :=
  DifferentiableOn ℂ G.F G.domain

/--
Midpoint geometric-mean field bundled with its generating function.
-/
structure MidpointGeometricMeanHolomorphicField where
  generating : GoldbachPartitionGeneratingFunction
  /-- Holomorphic regularity of `generating.F` on `generating.domain`. -/
  holomorphic : IsHolomorphicGoldbachPartition generating

/-! ## Critical half-plane domain -/

/-- Open half-plane `{Re s > σ}` (contains the critical line `Re s = 1/2` when `σ < 1/2`). -/
def goldbachGeneratingHalfPlane (σ : ℝ) : Set ℂ :=
  {s : ℂ | σ < s.re}

theorem goldbachGeneratingHalfPlane_isOpen (σ : ℝ) :
    IsOpen (goldbachGeneratingHalfPlane σ) :=
  isOpen_lt continuous_const continuous_re

theorem critical_line_point_in_goldbach_generating_halfPlane (t : ℝ) :
    (1 / 2 : ℝ) + t * Complex.I ∈ goldbachGeneratingHalfPlane (0 : ℝ) := by
  simp [goldbachGeneratingHalfPlane]

/-! ## Discrete Goldbach midpoint aggregate -/

/--
Finite sum of `√{p·(2N−p)}` over Goldbach midpoint candidates at `N`.
-/
noncomputable def goldbachMidpointGeometricAggregate (N : ℕ) : ℝ :=
  (goldbachMidpointCandidates N).sum fun p =>
    Real.sqrt ((p * (2 * N - p) : ℝ))

theorem goldbach_midpoint_geometric_aggregate_nonneg (N : ℕ) :
    0 ≤ goldbachMidpointGeometricAggregate N := by
  dsimp [goldbachMidpointGeometricAggregate]
  refine Finset.sum_nonneg fun p _ => Real.sqrt_nonneg _

/--
Cumulative geometric-mean readout up to truncation `M`:

`∑_{1≤N≤M} ∑_{p∈𝒞(N)} √{p(2N−p)}`.

This is the **default Perron discrete target** (unsmoothed): the pair-Dirichlet
generating sum `F_M(s)` is its Dirichlet transform with weight `(2N)^{−s}` on each
midpoint layer.  It is *not* `weightDifferenceEulerMaclaurinRemainder N`; that
remainder is downstream after Euler–Maclaurin comparison to harmonic weights.
-/
noncomputable def goldbachMidpointGeometricCumulativeAggregate (M : ℕ) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M, goldbachMidpointGeometricAggregate N

theorem goldbach_midpoint_geometric_cumulative_aggregate_nonneg (M : ℕ) :
    0 ≤ goldbachMidpointGeometricCumulativeAggregate M := by
  dsimp [goldbachMidpointGeometricCumulativeAggregate]
  refine Finset.sum_nonneg fun N _ =>
    goldbach_midpoint_geometric_aggregate_nonneg N

/--
Default Perron discrete target at truncation `M` (alias for the cumulative aggregate).
-/
noncomputable abbrev goldbachPerronDiscreteTarget (M : ℕ) : ℝ :=
  goldbachMidpointGeometricCumulativeAggregate M

theorem goldbach_perron_discrete_target_eq_cumulative (M : ℕ) :
    goldbachPerronDiscreteTarget M = goldbachMidpointGeometricCumulativeAggregate M := rfl

/-! ## Pair-weighted Dirichlet generating function -/

/-- Complex power `n^{−s}` via `exp(−s·log n)` (holomorphic in `s` for `n > 0`). -/
noncomputable def natCpowNeg (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * Complex.log (n : ℂ))

theorem nat_cpow_neg_eq {n : ℕ} (hn : 0 < n) (s : ℂ) :
    natCpowNeg n s = (n : ℂ) ^ (-s) := by
  dsimp [natCpowNeg]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  ring_nf

theorem differentiable_nat_cpow_neg (n : ℕ) (hn : 0 < n) :
    Differentiable ℂ (natCpowNeg n) := by
  unfold natCpowNeg
  have hconst : Differentiable ℂ (fun (_ : ℂ) => Complex.log (n : ℂ)) := differentiable_const _
  have hlin : Differentiable ℂ (fun s => s * Complex.log (n : ℂ)) :=
    Differentiable.mul differentiable_id hconst
  have hneg : Differentiable ℂ (fun s => -s * log (n : ℂ)) := by
    convert Differentiable.neg hlin using 1
    funext s
    simp
  exact Differentiable.cexp hneg

theorem differentiableOn_nat_cpow_neg (n : ℕ) (hn : 0 < n) (S : Set ℂ) :
    DifferentiableOn ℂ (natCpowNeg n) S :=
  (differentiable_nat_cpow_neg n hn).differentiableOn

/-! ## Vertical-line modulus bounds -/

/--
Modulus of `natCpowNeg n s` depends only on `Re s`: `‖n^{−s}‖ = n^{−Re s}`.
-/
theorem nat_cpow_neg_norm (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖natCpowNeg n s‖ = (n : ℝ) ^ (-s.re) := by
  rw [nat_cpow_neg_eq hn, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

/--
On the vertical line `s = σ + it`, the modulus is constant in `t`:

`‖(2n)^{−(σ+it)}‖ = (2n)^{−σ}`.
-/
theorem nat_cpow_neg_norm_on_vertical (n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    ‖natCpowNeg n (σ + t * I)‖ = (n : ℝ) ^ (-σ) := by
  rw [nat_cpow_neg_norm n hn]
  simp [Complex.add_re, Complex.I_re, Complex.mul_re]

theorem nat_cpow_neg_norm_on_vertical_two_mul (N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    ‖natCpowNeg (2 * N) (σ + t * I)‖ = (2 * N : ℝ) ^ (-σ) := by
  rw [nat_cpow_neg_norm_on_vertical (2 * N) σ t (by omega)]
  norm_cast

/--
Dirichlet term for a Goldbach midpoint pair: `√{pq} · (2N)^{−s}`.

The even target `2N` sets the scale; the geometric mean `√{pq}` is the pair weight
matching the critical-line normalization proved in `S3GoldbachHolomorphicWeightBridge`.
-/
noncomputable def goldbachMidpointPairGeometricDirichletTerm
    {N p q : ℕ} (h : GoldbachMidpointPair N p q) (s : ℂ) : ℂ :=
  (midpointPairGeometricMean h : ℂ) * natCpowNeg (2 * N) s

theorem goldbach_midpoint_pair_dirichlet_term_eq {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) (s : ℂ) :
    goldbachMidpointPairGeometricDirichletTerm h s =
      Real.sqrt ((p * q : ℝ)) * natCpowNeg (2 * N) s := by
  dsimp [goldbachMidpointPairGeometricDirichletTerm, midpointPairGeometricMean]

theorem goldbach_midpoint_pair_of_candidate {N p : ℕ}
    (hp : p ∈ goldbachMidpointCandidates N) :
    GoldbachMidpointPair N p (2 * N - p) := by
  rw [goldbachMidpointCandidates, Finset.mem_filter] at hp
  rcases hp with ⟨_, hpCond⟩
  rcases hpCond with ⟨hpPrime, hqPrime, hpLe, hNLe⟩
  exact ⟨hpPrime, hqPrime, hpLe, hNLe, by omega⟩

/--
Finite truncated generating function:

`F_M(s) = ∑_{N≤M} ∑_{p∈𝒞(N)} √(p(2N−p))·(2N)^{−s}`.
-/
noncomputable def goldbachMidpointGeometricGeneratingSumTruncated (M : ℕ) (s : ℂ) : ℂ :=
  ∑ N ∈ Finset.Icc 1 M,
    ∑ p ∈ goldbachMidpointCandidates N,
      (Real.sqrt ((p * (2 * N - p) : ℝ)) : ℂ) * natCpowNeg (2 * N) s

noncomputable def goldbachMidpointGeometricDirichletSummand (N p : ℕ) (s : ℂ) : ℂ :=
  (Real.sqrt ((p * (2 * N - p) : ℝ)) : ℂ) * natCpowNeg (2 * N) s

theorem goldbach_midpoint_geometric_generating_sum_truncated_eq_summand_sum (M : ℕ) (s : ℂ) :
    goldbachMidpointGeometricGeneratingSumTruncated M s =
      ∑ N ∈ Finset.Icc 1 M,
        ∑ p ∈ goldbachMidpointCandidates N,
          goldbachMidpointGeometricDirichletSummand N p s := by
  rfl

/--
Coefficient sum (geometric weights only, no `(2N)^{−σ}` decay).
-/
noncomputable def goldbachMidpointGeometricCoefficientSum (M : ℕ) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M,
    ∑ p ∈ goldbachMidpointCandidates N,
      Real.sqrt ((p * (2 * N - p) : ℝ))

theorem goldbach_midpoint_geometric_coefficient_sum_nonneg (M : ℕ) :
    0 ≤ goldbachMidpointGeometricCoefficientSum M := by
  dsimp [goldbachMidpointGeometricCoefficientSum]
  refine Finset.sum_nonneg fun N _ => Finset.sum_nonneg fun p _ => Real.sqrt_nonneg _

/--
Unweighted Goldbach geometric mass through truncation `M`:

`∑_{N≤M} ∑_{p∈𝒞(N)} √{p(2N−p)}` — equals `B_{M,0}` in the vertical-bound chart.
-/
noncomputable abbrev goldbachMidpointGeometricUnweightedMass (M : ℕ) : ℝ :=
  goldbachMidpointGeometricCoefficientSum M

theorem goldbach_midpoint_geometric_unweighted_mass_nonneg (M : ℕ) :
    0 ≤ goldbachMidpointGeometricUnweightedMass M :=
  goldbach_midpoint_geometric_coefficient_sum_nonneg M

theorem goldbach_midpoint_geometric_aggregate_le_unweighted_mass (M N : ℕ)
    (hN : N ∈ Finset.Icc 1 M) :
    goldbachMidpointGeometricAggregate N ≤ goldbachMidpointGeometricUnweightedMass M := by
  dsimp [goldbachMidpointGeometricUnweightedMass, goldbachMidpointGeometricCoefficientSum]
  exact Finset.single_le_sum (fun N' _ => goldbach_midpoint_geometric_aggregate_nonneg N') hN

theorem goldbach_midpoint_geometric_cumulative_aggregate_eq_coefficient_sum (M : ℕ) :
    goldbachMidpointGeometricCumulativeAggregate M = goldbachMidpointGeometricCoefficientSum M := by
  rfl

theorem goldbach_perron_discrete_target_eq_coefficient_sum (M : ℕ) :
    goldbachPerronDiscreteTarget M = goldbachMidpointGeometricCoefficientSum M := by
  rw [goldbach_perron_discrete_target_eq_cumulative,
    goldbach_midpoint_geometric_cumulative_aggregate_eq_coefficient_sum]

/--
Explicit vertical-line bound value for `F_M(σ + it)`:

`∑_{N≤M} ∑_p √{p(2N−p)} · (2N)^{−σ}` (independent of `t`).
-/
noncomputable def goldbachMidpointGeometricGeneratingSumVerticalBoundValue (M : ℕ) (σ : ℝ) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M,
    ∑ p ∈ goldbachMidpointCandidates N,
      Real.sqrt ((p * (2 * N - p) : ℝ)) * (2 * N : ℝ) ^ (-σ)

theorem goldbach_midpoint_geometric_generating_sum_vertical_bound_value_nonneg
    (M : ℕ) (σ : ℝ) :
    0 ≤ goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ := by
  dsimp [goldbachMidpointGeometricGeneratingSumVerticalBoundValue]
  refine Finset.sum_nonneg fun N _ => Finset.sum_nonneg fun p _ => ?_
  positivity

theorem goldbach_midpoint_geometric_unweighted_mass_eq_vertical_bound_at_zero (M : ℕ) :
    goldbachMidpointGeometricUnweightedMass M =
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M 0 := by
  dsimp [goldbachMidpointGeometricUnweightedMass,
    goldbachMidpointGeometricCoefficientSum,
    goldbachMidpointGeometricGeneratingSumVerticalBoundValue]
  refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun p _ => ?_
  simp [Real.rpow_zero]

theorem goldbach_midpoint_geometric_generating_sum_vertical_bound_value_zero_eq_coefficient_sum
    (M : ℕ) :
    goldbachMidpointGeometricGeneratingSumVerticalBoundValue M 0 =
      goldbachMidpointGeometricCoefficientSum M :=
  goldbach_midpoint_geometric_unweighted_mass_eq_vertical_bound_at_zero M |>.symm

private theorem goldbach_midpoint_two_mul_ge_one (N : ℕ) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ 2 * N := by
  have h : 1 ≤ 2 * N := by omega
  exact_mod_cast h

theorem goldbach_midpoint_geometric_generating_sum_vertical_bound_value_le_unweighted
    (M : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ ≤
      goldbachMidpointGeometricUnweightedMass M := by
  dsimp [goldbachMidpointGeometricGeneratingSumVerticalBoundValue,
    goldbachMidpointGeometricUnweightedMass, goldbachMidpointGeometricCoefficientSum]
  refine Finset.sum_le_sum fun N hNMem => Finset.sum_le_sum fun p _ => ?_
  have hn : (1 : ℝ) ≤ 2 * N :=
    goldbach_midpoint_two_mul_ge_one N (Finset.mem_Icc.mp hNMem).1
  have hrpow : (2 * N : ℝ) ^ (-σ) ≤ 1 := by
    calc (2 * N : ℝ) ^ (-σ)
        ≤ (2 * N : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn (neg_nonpos.mpr hσ)
      _ = 1 := by simp
  simpa [mul_one] using
    mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg ((p * (2 * N - p) : ℝ)))

theorem goldbach_midpoint_geometric_dirichlet_summand_norm_le_vertical
    (N p : ℕ) (σ t : ℝ) (hN : 0 < N) :
    ‖goldbachMidpointGeometricDirichletSummand N p (σ + t * I)‖ ≤
      Real.sqrt ((p * (2 * N - p) : ℝ)) * (2 * N : ℝ) ^ (-σ) := by
  dsimp [goldbachMidpointGeometricDirichletSummand]
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [nat_cpow_neg_norm_on_vertical_two_mul N σ t hN]

theorem goldbach_midpoint_geometric_dirichlet_summand_norm_le_at_re_ge
    (N p : ℕ) (σ₀ s_re γ : ℝ) (hN : 0 < N) (hσ₀ : 0 < σ₀) (hs : σ₀ ≤ s_re) :
    ‖goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)‖ ≤
      Real.sqrt ((p * (2 * N - p) : ℝ)) * (2 * N : ℝ) ^ (-σ₀) := by
  dsimp [goldbachMidpointGeometricDirichletSummand]
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [nat_cpow_neg_norm (2 * N) (by omega) (s_re + γ * I)]
  simp [Complex.add_re, Complex.I_re, Complex.mul_re]
  have hn : 1 ≤ (2 * N : ℝ) := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) := by simpa using Nat.cast_le.mpr (Nat.succ_le_of_lt hN)
    nlinarith
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs)) ?_
  positivity

theorem goldbach_midpoint_geometric_generating_sum_truncated_norm_le_vertical_bound_at_re_ge
    (M : ℕ) (σ₀ s_re γ : ℝ) (hσ₀ : 0 < σ₀) (hs : σ₀ ≤ s_re) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (s_re + γ * I)‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ := by
  rw [goldbach_midpoint_geometric_generating_sum_truncated_eq_summand_sum]
  dsimp [goldbachMidpointGeometricGeneratingSumVerticalBoundValue]
  calc
    ‖∑ N ∈ Finset.Icc 1 M,
        ∑ p ∈ goldbachMidpointCandidates N,
          goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)‖ ≤
        ∑ N ∈ Finset.Icc 1 M,
          ‖∑ p ∈ goldbachMidpointCandidates N,
            goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)‖ :=
      norm_sum_le (Finset.Icc 1 M) fun N =>
        ∑ p ∈ goldbachMidpointCandidates N,
          goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
        ∑ p ∈ goldbachMidpointCandidates N,
          ‖goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)‖ :=
      Finset.sum_le_sum fun N _ =>
        norm_sum_le (goldbachMidpointCandidates N) fun p =>
          goldbachMidpointGeometricDirichletSummand N p (s_re + γ * I)
    _ ≤ goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ₀ :=
      Finset.sum_le_sum fun N hNMem =>
        Finset.sum_le_sum fun p _ =>
          goldbach_midpoint_geometric_dirichlet_summand_norm_le_at_re_ge N p σ₀ s_re γ
            (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hNMem).1) hσ₀ hs

theorem goldbach_midpoint_geometric_generating_sum_vertical_bound (M : ℕ) (σ t : ℝ) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated M (σ + t * I)‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ := by
  rw [goldbach_midpoint_geometric_generating_sum_truncated_eq_summand_sum]
  dsimp [goldbachMidpointGeometricGeneratingSumVerticalBoundValue]
  calc
    ‖∑ N ∈ Finset.Icc 1 M,
        ∑ p ∈ goldbachMidpointCandidates N,
          goldbachMidpointGeometricDirichletSummand N p (σ + t * I)‖ ≤
        ∑ N ∈ Finset.Icc 1 M,
          ‖∑ p ∈ goldbachMidpointCandidates N,
            goldbachMidpointGeometricDirichletSummand N p (σ + t * I)‖ :=
      norm_sum_le (Finset.Icc 1 M) fun N =>
        ∑ p ∈ goldbachMidpointCandidates N,
          goldbachMidpointGeometricDirichletSummand N p (σ + t * I)
    _ ≤ ∑ N ∈ Finset.Icc 1 M,
        ∑ p ∈ goldbachMidpointCandidates N,
          ‖goldbachMidpointGeometricDirichletSummand N p (σ + t * I)‖ :=
      Finset.sum_le_sum fun N _ =>
        norm_sum_le (goldbachMidpointCandidates N) fun p =>
          goldbachMidpointGeometricDirichletSummand N p (σ + t * I)
    _ ≤ goldbachMidpointGeometricGeneratingSumVerticalBoundValue M σ :=
      Finset.sum_le_sum fun N hNMem =>
        Finset.sum_le_sum fun p _ =>
          goldbach_midpoint_geometric_dirichlet_summand_norm_le_vertical N p σ t
            (Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hNMem).1)

theorem goldbach_midpoint_geometric_generating_sum_vertical_bound_default
    (N : ℕ) (σ t : ℝ) :
    ‖goldbachMidpointGeometricGeneratingSumTruncated N (σ + t * I)‖ ≤
      goldbachMidpointGeometricGeneratingSumVerticalBoundValue N σ :=
  goldbach_midpoint_geometric_generating_sum_vertical_bound N σ t

theorem goldbach_midpoint_geometric_dirichlet_summand_differentiableOn (N p : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ (goldbachMidpointGeometricDirichletSummand N p)
      (goldbachGeneratingHalfPlane (0 : ℝ)) := by
  have hf := differentiableOn_nat_cpow_neg (2 * N) (by omega)
    (goldbachGeneratingHalfPlane (0 : ℝ))
  let c : ℂ := (Real.sqrt ((p * (2 * N - p) : ℝ)) : ℂ)
  have hc := differentiableOn_const (𝕜 := ℂ) (s := goldbachGeneratingHalfPlane (0 : ℝ)) c
  unfold goldbachMidpointGeometricDirichletSummand
  exact DifferentiableOn.mul hc hf

theorem goldbach_midpoint_geometric_generating_sum_truncated_differentiableOn (M : ℕ) :
    DifferentiableOn ℂ (goldbachMidpointGeometricGeneratingSumTruncated M)
      (goldbachGeneratingHalfPlane (0 : ℝ)) := by
  unfold goldbachMidpointGeometricGeneratingSumTruncated
  refine DifferentiableOn.fun_sum fun N hN => DifferentiableOn.fun_sum fun p hp => ?_
  have hNpos : 0 < N :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hN).1
  exact goldbach_midpoint_geometric_dirichlet_summand_differentiableOn N p hNpos

theorem mem_goldbachGeneratingHalfPlane_of_pos_re (s : ℂ) (hs : 0 < s.re) :
    s ∈ goldbachGeneratingHalfPlane (0 : ℝ) := by
  simp [goldbachGeneratingHalfPlane, hs]

theorem mem_goldbachGeneratingHalfPlane_vertical (σ t : ℝ) (hσ : 0 < σ) :
    σ + t * I ∈ goldbachGeneratingHalfPlane (0 : ℝ) :=
  mem_goldbachGeneratingHalfPlane_of_pos_re (σ + t * I) (by simp [hσ])

theorem goldbach_midpoint_geometric_generating_sum_truncated_continuousOn (M : ℕ) :
    ContinuousOn (goldbachMidpointGeometricGeneratingSumTruncated M)
      (goldbachGeneratingHalfPlane (0 : ℝ)) :=
  (goldbach_midpoint_geometric_generating_sum_truncated_differentiableOn M).continuousOn

theorem goldbach_partition_generating_differentiableOn
    (G : GoldbachPartitionGeneratingFunction)
    (h : IsHolomorphicGoldbachPartition G) :
    DifferentiableOn ℂ G.F G.domain := h

noncomputable def goldbachPartitionGeneratingFunctionOfPairDirichletSum (M : ℕ) :
    GoldbachPartitionGeneratingFunction where
  F := goldbachMidpointGeometricGeneratingSumTruncated M
  domain := goldbachGeneratingHalfPlane (0 : ℝ)
  isOpen_domain := goldbachGeneratingHalfPlane_isOpen 0
  midpointGeometricMeanAt := goldbachMidpointGeometricAggregate
  midpoint_geometric_mean_nonneg := goldbach_midpoint_geometric_aggregate_nonneg

theorem goldbach_pair_dirichlet_generating_holomorphic (M : ℕ) :
    IsHolomorphicGoldbachPartition (goldbachPartitionGeneratingFunctionOfPairDirichletSum M) :=
  goldbach_midpoint_geometric_generating_sum_truncated_differentiableOn M

/-! ## Canonical pair-Dirichlet carrier (default for the pipeline) -/

/-- Canonical generating function: pair Dirichlet sum truncated at `M`. -/
noncomputable abbrev goldbachPartitionGeneratingFunctionCanonical (M : ℕ) :=
  goldbachPartitionGeneratingFunctionOfPairDirichletSum M

/--
Default truncation for weight index `N`: align the generating sum with `N`
(`F_N` sums midpoint pairs up to the same truncation as the weight readout).
-/
noncomputable abbrev goldbachPartitionGeneratingFunctionDefault (N : ℕ) :=
  goldbachPartitionGeneratingFunctionCanonical N

theorem goldbach_partition_generating_default_eq_pair_dirichlet (N : ℕ) :
    goldbachPartitionGeneratingFunctionDefault N =
      goldbachPartitionGeneratingFunctionOfPairDirichletSum N := rfl

noncomputable def midpointGeometricMeanHolomorphicFieldOfPairDirichletSum (M : ℕ) :
    MidpointGeometricMeanHolomorphicField where
  generating := goldbachPartitionGeneratingFunctionOfPairDirichletSum M
  holomorphic := goldbach_pair_dirichlet_generating_holomorphic M

/-- Canonical holomorphic field at truncation `M`. -/
noncomputable abbrev midpointGeometricMeanHolomorphicFieldCanonical (M : ℕ) :=
  midpointGeometricMeanHolomorphicFieldOfPairDirichletSum M

/-- Default holomorphic field for weight index `N` (truncation `M = N`). -/
noncomputable abbrev midpointGeometricMeanHolomorphicFieldDefault (N : ℕ) :=
  midpointGeometricMeanHolomorphicFieldCanonical N

theorem midpoint_geometric_mean_holomorphic_field_default_generating (N : ℕ) :
    (midpointGeometricMeanHolomorphicFieldDefault N).generating =
      goldbachPartitionGeneratingFunctionDefault N := rfl

theorem midpoint_geometric_mean_holomorphic_field_default_holomorphic (N : ℕ) :
    IsHolomorphicGoldbachPartition
      (midpointGeometricMeanHolomorphicFieldDefault N).generating :=
  goldbach_pair_dirichlet_generating_holomorphic N

/-- Legacy alias (`M = 0` ⇒ zero generating function). -/
noncomputable abbrev goldbachPartitionGeneratingFunctionOfMidpointAggregate :=
  goldbachPartitionGeneratingFunctionCanonical 0

noncomputable abbrev midpointGeometricMeanHolomorphicFieldOfMidpointAggregate :
    MidpointGeometricMeanHolomorphicField :=
  midpointGeometricMeanHolomorphicFieldCanonical 0

/-! ## Critical-line weight normalization -/

theorem goldbach_midpoint_even_spectral_line_eq (N : ℕ) (s : ℂ) (hN : 0 < N) :
    natCpowNeg (2 * N) s = so4SpectralLine (2 * N) s := by
  dsimp [so4SpectralLine]
  exact nat_cpow_neg_eq (by omega) s

theorem goldbach_midpoint_even_weight_norm_at_critical_line (N : ℕ) (t : ℝ) (hN : 0 < N) :
    ‖natCpowNeg (2 * N) ((1 / 2 : ℝ) + t * Complex.I)‖ = (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [nat_cpow_neg_eq (by omega) ((1 / 2 : ℝ) + t * Complex.I)]
  set s : ℂ := ((1 / 2 : ℝ) + t * Complex.I)
  let m : ℕ := 2 * N
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hnorm : ‖(m : ℂ) ^ (-s)‖ = (m : ℝ) ^ (-s.re) := by
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hmpos (-s)
  rw [hnorm]
  have hsre : s.re = (1 / 2 : ℝ) := by simp [s]
  simp only [Complex.neg_re, hsre, m, Nat.cast_mul]
  norm_cast

theorem goldbach_midpoint_pair_dirichlet_norm_at_critical_line {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) (t : ℝ) :
    ‖goldbachMidpointPairGeometricDirichletTerm h ((1 / 2 : ℝ) + t * Complex.I)‖ =
      midpointPairGeometricMean h * (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  dsimp [goldbachMidpointPairGeometricDirichletTerm, midpointPairGeometricMean]
  have hNpos : 0 < N :=
    Nat.lt_trans Nat.zero_lt_one
      (Nat.lt_of_lt_of_le Nat.one_lt_two (le_trans h.1.two_le h.2.2.1))
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    goldbach_midpoint_even_weight_norm_at_critical_line N t hNpos]

theorem goldbach_midpoint_pair_dirichlet_norm_product_weight {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) (t : ℝ) :
    ‖goldbachMidpointPairGeometricDirichletTerm h ((1 / 2 : ℝ) + t * Complex.I)‖ *
        ‖so4SpectralLine (p * q) ((1 / 2 : ℝ) + t * Complex.I)‖ =
      (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set s : ℂ := (1 / 2 : ℝ) + t * Complex.I
  rw [goldbach_midpoint_pair_dirichlet_norm_at_critical_line h t]
  calc midpointPairGeometricMean h * (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) *
      ‖so4SpectralLine (p * q) s‖
      _ = (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) *
          (midpointPairGeometricMean h * ‖so4SpectralLine (p * q) s‖) := by ring
      _ = (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) * 1 := by
        rw [midpoint_pair_geometric_mean_normalizes_joint_weight h (by simp [s]), mul_one]
      _ = (2 * N : ℝ) ^ (-(1 / 2 : ℝ)) := by simp

/-! ## Explicit holomorphic ⇒ remainder implication -/

/--
**Target analytic implication (Option B packaging).**

Assuming holomorphic regularity of the midpoint geometric-mean generating field,
the Euler–Maclaurin tail `weightDifferenceEulerMaclaurinRemainder N` is bounded.

The implication is recorded as a Prop field — instantiate when the analytic proof
is available.
-/
structure HolomorphicMeanControlsWeightRemainder (N : ℕ) where
  meanField : MidpointGeometricMeanHolomorphicField
  remainderBound : ℝ
  remainder_bound_nonneg : 0 ≤ remainderBound
  /-- Explicit implication: holomorphy ⇒ bounded remainder tail. -/
  holomorphic_implies_remainder_bound :
    IsHolomorphicGoldbachPartition meanField.generating →
      |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound

/--
Holomorphic certificate: field + implication + witnessed holomorphy.
-/
structure GoldbachHolomorphicRegularityCertificate (N : ℕ) extends
    HolomorphicMeanControlsWeightRemainder N where
  holomorphic_witness :
    IsHolomorphicGoldbachPartition meanField.generating

/-! ## Contour / Cauchy growth input -/

/--
Contour-integration / Cauchy-growth packaging: holomorphic `F` on a half-plane with
controlled growth along vertical lines should bound the Euler–Maclaurin tail.

Recorded as explicit input — instantiate when the analytic comparison to
`weightDifferenceEulerMaclaurinRemainder` is available.
-/
structure ContourGrowthControlsEulerRemainder (N : ℕ) where
  generating : GoldbachPartitionGeneratingFunction
  remainderBound : ℝ
  remainder_bound_nonneg : 0 ≤ remainderBound
  holomorphic_implies_remainder_bound :
    IsHolomorphicGoldbachPartition generating →
      |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound

/--
Contour growth certificate using the **default** pair-Dirichlet generating function
`goldbachPartitionGeneratingFunctionDefault N`.
-/
structure ContourGrowthControlsEulerRemainderAtDefaultTruncation (N : ℕ) where
  contour : ContourGrowthControlsEulerRemainder N
  generating_is_default :
    contour.generating = goldbachPartitionGeneratingFunctionDefault N

/--
Bidirectional bridge: forward direction matches `HolomorphicMeanControlsWeightRemainder`;
reverse direction records that a remainder bound may certify holomorphic extension
(named target for explicit-formula / Euler–Maclaurin duality).
-/
structure GoldbachHolomorphyEulerRemainderBridge (N : ℕ) where
  generating : GoldbachPartitionGeneratingFunction
  remainderBound : ℝ
  remainder_bound_nonneg : 0 ≤ remainderBound
  holomorphic_implies_remainder_bound :
    IsHolomorphicGoldbachPartition generating →
      |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound
  remainder_bound_implies_holomorphic :
    |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound →
      IsHolomorphicGoldbachPartition generating

noncomputable def holomorphicMeanControlsWeightRemainder_of_contour_growth {N : ℕ}
    (h : ContourGrowthControlsEulerRemainder N)
    (hHol : IsHolomorphicGoldbachPartition h.generating) :
    HolomorphicMeanControlsWeightRemainder N where
  meanField := { generating := h.generating, holomorphic := hHol }
  remainderBound := h.remainderBound
  remainder_bound_nonneg := h.remainder_bound_nonneg
  holomorphic_implies_remainder_bound := h.holomorphic_implies_remainder_bound

noncomputable def contourGrowthControlsEulerRemainder_of_bridge {N : ℕ}
    (b : GoldbachHolomorphyEulerRemainderBridge N) :
    ContourGrowthControlsEulerRemainder N where
  generating := b.generating
  remainderBound := b.remainderBound
  remainder_bound_nonneg := b.remainder_bound_nonneg
  holomorphic_implies_remainder_bound := b.holomorphic_implies_remainder_bound

noncomputable def holomorphicMeanControlsWeightRemainder_of_bridge_forward {N : ℕ}
    (b : GoldbachHolomorphyEulerRemainderBridge N)
    (hHol : IsHolomorphicGoldbachPartition b.generating) :
    HolomorphicMeanControlsWeightRemainder N :=
  holomorphicMeanControlsWeightRemainder_of_contour_growth
    (contourGrowthControlsEulerRemainder_of_bridge b) hHol

/--
Bidirectional bridge: a witnessed remainder bound yields holomorphy, then the forward
implication is available as `HolomorphicMeanControlsWeightRemainder`.
-/
noncomputable def holomorphicMeanControlsWeightRemainder_of_bridge_bidirectional {N : ℕ}
    (b : GoldbachHolomorphyEulerRemainderBridge N)
    (hRem : |weightDifferenceEulerMaclaurinRemainder N| ≤ b.remainderBound) :
    HolomorphicMeanControlsWeightRemainder N :=
  holomorphicMeanControlsWeightRemainder_of_bridge_forward b
    (b.remainder_bound_implies_holomorphic hRem)

noncomputable def holomorphicMeanControlsWeightRemainder_of_pair_dirichlet_holomorphic {N M : ℕ}
    (h : ContourGrowthControlsEulerRemainder N)
    (hEq : h.generating = goldbachPartitionGeneratingFunctionOfPairDirichletSum M) :
    HolomorphicMeanControlsWeightRemainder N :=
  holomorphicMeanControlsWeightRemainder_of_contour_growth h (by
    rw [hEq]
    exact goldbach_pair_dirichlet_generating_holomorphic M)

noncomputable def contourGrowthControlsEulerRemainder_at_default_truncation {N : ℕ}
    (h : ContourGrowthControlsEulerRemainder N)
    (hDefault : h.generating = goldbachPartitionGeneratingFunctionDefault N) :
    ContourGrowthControlsEulerRemainderAtDefaultTruncation N where
  contour := h
  generating_is_default := hDefault

noncomputable def holomorphicMeanControlsWeightRemainder_of_default_pair_dirichlet {N : ℕ}
    (h : ContourGrowthControlsEulerRemainderAtDefaultTruncation N) :
    HolomorphicMeanControlsWeightRemainder N where
  meanField := midpointGeometricMeanHolomorphicFieldDefault N
  remainderBound := h.contour.remainderBound
  remainder_bound_nonneg := h.contour.remainder_bound_nonneg
  holomorphic_implies_remainder_bound := fun hHol =>
    h.contour.holomorphic_implies_remainder_bound
      (by
        simpa [midpoint_geometric_mean_holomorphic_field_default_generating,
          h.generating_is_default] using hHol)

noncomputable def goldbachHolomorphicRegularityCertificate_of_default_contour {N : ℕ}
    (h : ContourGrowthControlsEulerRemainderAtDefaultTruncation N) :
    GoldbachHolomorphicRegularityCertificate N where
  meanField := midpointGeometricMeanHolomorphicFieldDefault N
  remainderBound := h.contour.remainderBound
  remainder_bound_nonneg := h.contour.remainder_bound_nonneg
  holomorphic_implies_remainder_bound :=
    (holomorphicMeanControlsWeightRemainder_of_default_pair_dirichlet h).holomorphic_implies_remainder_bound
  holomorphic_witness := midpoint_geometric_mean_holomorphic_field_default_holomorphic N

theorem goldbach_holomorphic_regularity_certificate_default_holomorphic {N : ℕ}
    (cert : GoldbachHolomorphicRegularityCertificate N)
    (hMean :
      cert.meanField = midpointGeometricMeanHolomorphicFieldDefault N) :
    IsHolomorphicGoldbachPartition
      (goldbachPartitionGeneratingFunctionDefault N) := by
  simpa [hMean, midpoint_geometric_mean_holomorphic_field_default_generating]
    using cert.holomorphic_witness

/-! ## Wiring into the weight-difference pipeline (proved) -/

/--
From the explicit holomorphic implication, obtain `WeightDifferenceRemainderBound`.
-/
noncomputable def weightDifferenceRemainderBound_of_holomorphic_mean {N : ℕ}
    (h : HolomorphicMeanControlsWeightRemainder N)
    (hHol : IsHolomorphicGoldbachPartition h.meanField.generating) :
    WeightDifferenceRemainderBound N where
  remainderBound := h.remainderBound
  remainderBound_nonneg := h.remainder_bound_nonneg
  remainder_le := h.holomorphic_implies_remainder_bound hHol

noncomputable def weightDifferenceRemainderBound_of_holomorphic_certificate {N : ℕ}
    (cert : GoldbachHolomorphicRegularityCertificate N) :
    WeightDifferenceRemainderBound N where
  remainderBound := cert.remainderBound
  remainderBound_nonneg := cert.remainder_bound_nonneg
  remainder_le := cert.holomorphic_implies_remainder_bound cert.holomorphic_witness

noncomputable def weightDifferenceAsymptoticSlot_of_holomorphic_certificate {N : ℕ}
    (cert : GoldbachHolomorphicRegularityCertificate N) :
    WeightDifferenceAsymptoticSlot N :=
  weightDifferenceAsymptoticSketch N (weightDifferenceRemainderBound_of_holomorphic_certificate cert)

noncomputable def goldbachHolomorphicWeightBridge_of_certificate {N : ℕ}
    (cert : GoldbachHolomorphicRegularityCertificate N) :
    GoldbachHolomorphicWeightBridge N where
  remainderBound := cert.remainderBound
  remainder_bound_nonneg := cert.remainder_bound_nonneg
  euler_remainder_le :=
    cert.holomorphic_implies_remainder_bound cert.holomorphic_witness
  main_term_is_leading := weight_difference_leading_decomposition N

noncomputable def modelGuidedLocationBound_of_holomorphic_certificate {N : ℕ}
    (coverHeight : ℝ) (hT : 0 < coverHeight)
    (deviationBound : ℝ) (hδ : 0 ≤ deviationBound)
    (cert : GoldbachHolomorphicRegularityCertificate N)
    (hε :
      |weightDifference N| / max 1 (partialVonMangoldtWeight N) ≤ deviationBound) :
    ModelGuidedLocationBound N :=
  modelGuidedLocationBound_of_goldbach_holomorphic coverHeight hT deviationBound hδ
    (goldbachHolomorphicWeightBridge_of_certificate cert) hε

/--
Full pipeline: holomorphic certificate ⇒ asymptotic slot ⇒ location bound.
-/
structure GoldbachHolomorphicWeightPipeline (N : ℕ) where
  certificate : GoldbachHolomorphicRegularityCertificate N
  asymptoticSlot : WeightDifferenceAsymptoticSlot N :=
    weightDifferenceAsymptoticSlot_of_holomorphic_certificate certificate
  remainderBound : WeightDifferenceRemainderBound N :=
    weightDifferenceRemainderBound_of_holomorphic_certificate certificate
  weightBridge : GoldbachHolomorphicWeightBridge N :=
    goldbachHolomorphicWeightBridge_of_certificate certificate

noncomputable def goldbachHolomorphicWeightPipeline_default {N : ℕ}
    (cert : GoldbachHolomorphicRegularityCertificate N)
    (hMean : cert.meanField = midpointGeometricMeanHolomorphicFieldDefault N) :
    GoldbachHolomorphicWeightPipeline N where
  certificate := cert
  asymptoticSlot := weightDifferenceAsymptoticSlot_of_holomorphic_certificate cert
  remainderBound := weightDifferenceRemainderBound_of_holomorphic_certificate cert
  weightBridge := goldbachHolomorphicWeightBridge_of_certificate cert

/-!
## Status

* **Canonical carrier:** `goldbachPartitionGeneratingFunctionDefault N` /
  `midpointGeometricMeanHolomorphicFieldDefault N` (pair Dirichlet, truncation `M = N`).
* **Proved holomorphy:** `goldbach_pair_dirichlet_generating_holomorphic` on `{Re s > 0}`.
* **Contour packaging:** `ContourGrowthControlsEulerRemainderAtDefaultTruncation`,
  `holomorphicMeanControlsWeightRemainder_of_default_pair_dirichlet`,
  `goldbachHolomorphicRegularityCertificate_of_default_contour`.
* **Analytic outline:** `S3GoldbachPerronContourRemainder` (Perron + vertical growth strategy).
* **Next:** replace placeholder growth in `perronContourRemainderStrategyDefault` with
  real vertical estimates; prove Perron and Euler–Maclaurin contour flags.
-/

end

end Hqiv.Story
