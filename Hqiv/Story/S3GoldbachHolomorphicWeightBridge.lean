import Hqiv.Story.S3CumulativeHarmonicPhase
import Hqiv.Story.S3ZeroHolonomyGoldbachChain
import Hqiv.Story.S3ModelGuidedLocationBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Goldbach midpoint geometric mean → weight-difference remainder bridge

Goldbach partitions of even numbers correspond (via null-lattice rolling steps) to
midpoint additive configurations `p + q = 2N`.  Each partition has a **geometric
mean** `√{pq}` at the midpoint `N`.

On the critical line, that geometric mean **normalizes** the joint spectral weight
of the pair (`midpoint_pair_geometric_mean_normalizes_joint_weight`).  Requiring
holomorphic extension of the midpoint geometric-mean field (in the Goldbach prime
generating function) is the analytic input that should collapse the Euler–Maclaurin
tail of

`Δ_N = totalArcHarmonicWeight N − partialVonMangoldtWeight N`

to a controllable remainder after the exact main term

`Λ_N − π (log N)²` (`weightDifferenceLeadingTerm`).

## Proved here

* midpoint geometric mean `≤ N` (AM–GM);
* critical-line normalization `√{pq} · ‖(pq)^{−s}‖ = 1`;
* algebraic packaging into `WeightDifferenceRemainderBound` and
  `ModelGuidedLocationBound`.

## Named analytic input (not proved here)

`GoldbachHolomorphicWeightBridge` — holomorphic regularity of midpoint geometric
means forces a bound on `weightDifferenceEulerMaclaurinRemainder`.
-/

namespace Hqiv.Story

noncomputable section

open Real Complex Hqiv.Geometry

/-! ## Goldbach partition ↔ midpoint -/

/-- Midpoint index for an even Goldbach target `n = 2N`. -/
noncomputable def goldbachPartitionMidpoint (n : ℕ) : ℕ :=
  n / 2

theorem goldbach_partition_midpoint_even {n : ℕ} (hn : Even n) :
    2 * goldbachPartitionMidpoint n = n := by
  obtain ⟨k, rfl⟩ := hn
  simp only [goldbachPartitionMidpoint]
  omega

theorem goldbach_midpoint_pair_of_partition {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    GoldbachPair (2 * N) p q :=
  goldbach_pair_of_midpoint_pair h

/-! ## Midpoint geometric mean -/

/-- Arithmetic geometric mean `√{pq}` for a Goldbach midpoint pair. -/
noncomputable def midpointPairGeometricMean {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) : ℝ :=
  Real.sqrt ((p * q : ℝ))

theorem midpoint_pair_geometric_mean_nonneg {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    0 ≤ midpointPairGeometricMean h := Real.sqrt_nonneg _

/-- AM–GM: `√{pq} ≤ N` for midpoint pairs (`p + q = 2N`, `p ≤ N ≤ q`). -/
theorem midpoint_pair_geometric_mean_le_midpoint {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) :
    midpointPairGeometricMean h ≤ (N : ℝ) := by
  dsimp [midpointPairGeometricMean]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · exact_mod_cast midpoint_pair_product_le h

/--
On `Re s = 1/2`, the geometric mean normalizes the joint pair line:

`√{pq} · ‖(pq)^{−s}‖ = 1`.
-/
theorem midpoint_pair_geometric_mean_normalizes_joint_weight {N p q : ℕ}
    (h : GoldbachMidpointPair N p q) {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    midpointPairGeometricMean h * ‖so4SpectralLine (p * q) s‖ = 1 := by
  dsimp [midpointPairGeometricMean]
  have hp2 := h.1.two_le
  have hq2 := h.2.1.two_le
  have hpq2 : 2 ≤ p * q := le_trans hp2 (Nat.le_mul_of_pos_right p h.2.1.pos)
  have hpqpos : 0 < (p * q : ℝ) := by positivity
  have hsq : ‖so4SpectralLine (p * q) s‖ ^ 2 = ((p * q : ℕ) : ℝ)⁻¹ :=
    (so4SpectralLine_sq_weight hpq2).mpr hs
  have hnn : 0 ≤ Real.sqrt ((p * q : ℝ)) * ‖so4SpectralLine (p * q) s‖ := by positivity
  have hsq_prod :
      (Real.sqrt ((p * q : ℝ)) * ‖so4SpectralLine (p * q) s‖) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hpqpos), hsq]
    norm_cast
    field_simp [hpqpos.ne']
  have hsq_mean :
      (midpointPairGeometricMean h * ‖so4SpectralLine (p * q) s‖) ^ 2 = 1 := by
    simpa [midpointPairGeometricMean] using hsq_prod
  rcases sq_eq_one_iff.mp hsq_mean with h | h
  · exact h
  · dsimp [midpointPairGeometricMean] at h hnn ⊢
    linarith

/-! ## Rolling harmonic weight alias -/

/-- Cumulative harmonic rolling weight (null-lattice arc sum). -/
noncomputable abbrev rollingHarmonicWeightUpTo (N : ℕ) : ℝ :=
  totalArcHarmonicWeight N

theorem rolling_harmonic_weight_eq_total_arc (N : ℕ) :
    rollingHarmonicWeightUpTo N = totalArcHarmonicWeight N := rfl

/-! ## Holomorphic geometric-mean bridge (named input) -/

/--
Holomorphic regularity of midpoint geometric means in the Goldbach generating
function.

**Target analytic content:** holomorphic extension controls the Euler–Maclaurin
tail of `Δ_N` after the exact main term `weightDifferenceLeadingTerm N`.

Not instantiated here — this is the Goldbach → von Mangoldt/harmonic remainder
bridge the user described.
-/
structure GoldbachHolomorphicWeightBridge (N : ℕ) where
  /-- Controllable tail after subtracting `Λ_N − π(log N)²`. -/
  remainderBound : ℝ
  remainder_bound_nonneg : 0 ≤ remainderBound
  /-- Bound on the exact Euler–Maclaurin remainder. -/
  euler_remainder_le :
    |weightDifferenceEulerMaclaurinRemainder N| ≤ remainderBound
  /-- Main term identification (exact algebra; not asymptotic cancellation). -/
  main_term_is_leading :
    weightDifference N =
      weightDifferenceLeadingTerm N + weightDifferenceEulerMaclaurinRemainder N

/--
Every holomorphic bridge immediately supplies `WeightDifferenceRemainderBound`.
-/
noncomputable def weightDifferenceRemainderBound_of_goldbach_holomorphic {N : ℕ}
    (h : GoldbachHolomorphicWeightBridge N) : WeightDifferenceRemainderBound N where
  remainderBound := h.remainderBound
  remainderBound_nonneg := h.remainder_bound_nonneg
  remainder_le := h.euler_remainder_le

/--
Asymptotic slot from the Goldbach holomorphic bridge.
-/
noncomputable def weightDifferenceAsymptoticSketch_of_goldbach_holomorphic {N : ℕ}
    (h : GoldbachHolomorphicWeightBridge N) : WeightDifferenceAsymptoticSlot N :=
  weightDifferenceAsymptoticSketch N (weightDifferenceRemainderBound_of_goldbach_holomorphic h)

/--
Location bound from Goldbach holomorphic input + normalized remainder control.
-/
noncomputable def modelGuidedLocationBound_of_goldbach_holomorphic {N : ℕ}
    (coverHeight : ℝ) (hT : 0 < coverHeight)
    (deviationBound : ℝ) (hδ : 0 ≤ deviationBound)
    (hBridge : GoldbachHolomorphicWeightBridge N)
    (hε :
      |weightDifference N| / max 1 (partialVonMangoldtWeight N) ≤ deviationBound) :
    ModelGuidedLocationBound N :=
  modelGuidedLocationBound_from_remainder coverHeight hT deviationBound hδ
    (weightDifferenceRemainderBound_of_goldbach_holomorphic hBridge) hε

theorem goldbach_holomorphic_main_term_formula {N : ℕ}
    (h : GoldbachHolomorphicWeightBridge N) :
    weightDifference N =
      (partialVonMangoldtWeight N - totalArcHarmonicWeightLeadingApprox N) +
        weightDifferenceEulerMaclaurinRemainder N := by
  simpa [weightDifferenceLeadingTerm] using h.main_term_is_leading

/-!
## Status

* **Proved:** midpoint GM `≤ N`; critical-line normalization; remainder packaging.
* **Named input:** `GoldbachHolomorphicWeightBridge` — holomorphic GM regularity
  ⇒ bounded `weightDifferenceEulerMaclaurinRemainder`.
* **Exact main term:** `Δ_N = (Λ_N − π(log N)²) + tail`; tail is what holomorphicity
  should control.
* **Next:** prove `GoldbachHolomorphicWeightBridge` from null-lattice rolling +
  generating-function holomorphy; feed into `ExplicitFormulaLocationInput`.
-/

end

end Hqiv.Story
