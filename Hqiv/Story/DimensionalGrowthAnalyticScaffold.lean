import Mathlib.Topology.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Hqiv.Geometry.OctonionicLightCone

/-!
# Dimensional growth and induced analytic scaffolding

This module is an **exploration layer** (not a uniqueness claim): it packages a few
rigorous hooks where **discrete dimensional growth** meets **classical analytic
objects**—harmonic partial sums, logarithmic weights, the complex unit circle, and
the distinction between

* a **monotone cumulative** readout (a minimal model of *causal depth* /
  thermodynamic *time* along a shell ladder), versus
* a **phase-valued** readout constrained to `S¹ ⊂ ℂ` (a minimal model of compact
  *spatial* holonomy / AC phase / discrete Fourier characters).

The HQIV curvature functional `Hqiv.curvature_integral` already decomposes into
the harmonic channel plus an `α`-weighted log channel; we surface that identity as
the formal backbone for “growth ⇒ logarithmic analytic structure,” while keeping
explicit that **complex phases do not automatically come from the harmonic sum
itself**—they come from *choosing* a map `ℕ → S¹` (or from generating-function
kernels such as `z ↦ −log(1−z)` on `|z| < 1`, which is a standard complex-analytic
package for `∑ z^n/n`).

**Design goal (research, not proved here):** glue the monotone cumulative channel
to a Lorentzian / causal-set presentation so that “time” is not treated as a
periodic coordinate, while electromagnetic / harmonic spatial structure *is*
treated via `S¹` or Riemann-surface charts built from those phases.
-/

open scoped Topology
open Filter Complex

namespace Hqiv.Story

/-- Monotone real readout along `ℕ`, diverging to `+∞`.

Interpretation: cumulative mode counting / causal-shell depth / a discrete
*time-stamp* coordinate. This is **not** assumed periodic. -/
structure MonotoneCumulativeReadout where
  f : ℕ → ℝ
  mono : Monotone f
  diverges : Tendsto f atTop atTop

/-- `ℂ`-valued readout constrained to the unit circle at every shell index.

Interpretation: AC phase, plane-wave restriction, or a discrete character
`ℤ/nℤ → S¹` after fixing a frequency slot. This is the natural place where
**complex numbers** enter as *values*, not as the real harmonic partial sums. -/
structure UnitCirclePhaseReadout where
  u : ℕ → ℂ
  onCircle : ∀ n, ‖u n‖ = 1

/-- The HQIV discrete curvature integral is a certified example of a cumulative
readout: it grows at least as fast as the harmonic partial sums and tends to
infinity along `atTop`. -/
noncomputable def curvatureIntegralReadout : MonotoneCumulativeReadout where
  f := Hqiv.curvature_integral
  mono := Hqiv.curvature_integral_mono
  diverges := Hqiv.curvature_integral_tends_to_atTop

/-- Formal “harmonic + log” decomposition of the curvature integral.

This is exactly `Hqiv.curvature_integral_eq_harmonic_plus_alpha_log`, re-exported
under a descriptive name for this story module. -/
theorem curvature_integral_harmonic_log_split (n : ℕ) :
    Hqiv.curvature_integral n =
      (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1 : ℝ)) +
        Hqiv.alpha * Hqiv.logWeightedSum n :=
  Hqiv.curvature_integral_eq_harmonic_plus_alpha_log n

/-- Primitive `n`th roots of unity at frequency index `k < n`, as points on `S¹`.

This is the discrete Riemann-surface / torus chart seed: characters of the finite
cyclic group embed into `ℂ^×`. -/
noncomputable def primitiveRoot (n : ℕ) (_hn : 0 < n) (k : Fin n) : ℂ :=
  exp ((2 * Real.pi * (k.val : ℝ) / (n : ℝ)) * I)

theorem norm_primitiveRoot (n : ℕ) (_hn : 0 < n) (k : Fin n) :
    ‖primitiveRoot n _hn k‖ = 1 := by
  -- `exp (x * I)` has unit norm for real `x`.
  simpa [primitiveRoot, mul_assoc, mul_left_comm, mul_comm] using
    (norm_exp_ofReal_mul_I (2 * Real.pi * (k.val : ℝ) / (n : ℝ)))

/-- Trivial family of phases `n ↦ exp (i n)`; every value lies on the unit circle.

This is a sanity hook: **any** real-angle assignment `ℕ → ℝ` produces a
`UnitCirclePhaseReadout` by post-composition with `exp (I * ·)`. The harmonic
partial sums could be inserted as angles, but then phase acceleration is tied to
`H_n ~ log n`, not to linear `n`. -/
noncomputable def linearAnglePhaseReadout : UnitCirclePhaseReadout where
  u := fun n => exp (I * (n : ℝ))
  onCircle := fun n => by simpa using (norm_exp_I_mul_ofReal (n : ℝ))

end Hqiv.Story
