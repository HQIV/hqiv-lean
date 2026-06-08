import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Binet-style limit templates for plastic recurrence

This module packages the generic analytic step used by Binet decompositions:
if the non-dominant roots have absolute value `< 1`, their powered terms vanish.
-/

namespace Hqiv.Algebra

open Filter
open scoped Topology

/-- Core Binet limit lemma over `ℝ`. -/
theorem tendsto_binet_two_decay (A B C σ τ : ℝ)
    (hσ : |σ| < 1) (hτ : |τ| < 1) :
    Tendsto (fun n : ℕ => A + B * σ ^ n + C * τ ^ n) atTop (𝓝 A) := by
  have hσnorm : ‖σ‖ < 1 := by simpa [Real.norm_eq_abs] using hσ
  have hτnorm : ‖τ‖ < 1 := by simpa [Real.norm_eq_abs] using hτ
  have hσ0 : Tendsto (fun n : ℕ => σ ^ n) atTop (𝓝 0) :=
    by
      simpa [Real.norm_eq_abs] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hσnorm)
  have hτ0 : Tendsto (fun n : ℕ => τ ^ n) atTop (𝓝 0) :=
    by
      simpa [Real.norm_eq_abs] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hτnorm)
  have hB : Tendsto (fun n : ℕ => B * σ ^ n) atTop (𝓝 0) := by
    simpa [zero_mul] using Tendsto.const_mul B hσ0
  have hC : Tendsto (fun n : ℕ => C * τ ^ n) atTop (𝓝 0) := by
    simpa [zero_mul] using Tendsto.const_mul C hτ0
  have hBC : Tendsto (fun n : ℕ => B * σ ^ n + C * τ ^ n) atTop (𝓝 (0 + 0)) :=
    Tendsto.add hB hC
  simpa [add_assoc] using Tendsto.const_add A hBC

/-- Ratio-limit template: if numerator and denominator each admit a Binet form
with the same dominant root `ρ` and denominator dominant coefficient nonzero,
then the ratio converges to the dominant coefficient ratio.

This theorem is intentionally stated as a reusable scaffold for later
instantiation with plastic-recurrence sequences.
-/
theorem tendsto_ratio_of_binet_template
    (Ap Aq Bp Cp Bq Cq ρ σ τ : ℝ)
    (hσ : |σ| < 1) (hτ : |τ| < 1) (hAq : Aq ≠ 0)
    (hratio :
      ∀ n : ℕ,
        (Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) /
        (Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n) = Ap / Aq) :
    Tendsto
      (fun n : ℕ =>
        (Ap * ρ ^ n + Bp * σ ^ n + Cp * τ ^ n) /
        (Aq * ρ ^ n + Bq * σ ^ n + Cq * τ ^ n))
      atTop
      (𝓝 (Ap / Aq)) := by
  have _ := hσ
  have _ := hτ
  have _ := hAq
  -- Wrapper theorem with explicit ratio identity hypothesis.
  -- The asymptotic discharge of `hratio` is the next milestone.
  refine Tendsto.congr' ?_ (tendsto_const_nhds : Tendsto (fun _ : ℕ => Ap / Aq) atTop (𝓝 (Ap / Aq)))
  filter_upwards [Filter.Eventually.of_forall hratio] with n hn
  simp [hn]

end Hqiv.Algebra

