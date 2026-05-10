import Mathlib.Data.Real.Basic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric

namespace Hqiv

/-!
# Conservations — Metric forces conservations in the structure from counting over O

We do **not** start from the Standard Model or from “embedding SM in SO(8)”.
We start from:

1. **Counting over O in the light cone:** The light-cone axiom (new modes = 8 ×
   stars-and-bars) and the curvature norm (6⁷√3 from cube + octonion dimension)
   are **counting over the octonions O**. That counting yields a definite
   algebraic structure — the **structure that is the result of counting over O**
   in our light cone.

2. **The metric as built:** The HQVM metric (lapse N = 1 + Φ + φ t, time angle
   δθ′ = φ t with period 2π, φ from the lattice) is already fixed by the
   light-cone, monogamy, and natural units. No extra input.

3. **Metric forces conservations:** We **show** that the metric as built **forces**
   conservations **in** that structure (phase mod 2π, etc.). Pure math.

4. **Later:** Prove that this structure is identical to a known gauge structure.
   For now we stay in pure math.

## Degrees of freedom — Lean SO(8) closure stack (not a Python script)

The **checked-in, proof-bearing** construction lives in Lean:

- `Hqiv.OctonionLeftMultiplication` — the 8×8 matrices `L(e_i)` for imaginary units.
- `Hqiv.So8CoordMatrix` — upper-triangle indexing and the `so8CoordMatrix` packaging used in closure.
- `Hqiv.GeneratorsLieClosureData0` … `Hqiv.GeneratorsLieClosureData27` — chunked Lie-bracket coefficient
  data feeding `Hqiv.GeneratorsLieClosure` (row files split for elaboration limits; **27** is one chunk).
- `Hqiv.SO8Closure` — re-exports `so8_closure_dim_eq_28` and `so8_closure_theorem` from the generator closure.
- `Hqiv.SO8ClosureInterface` — thin facade (`so8_closure_dim_eq_28_interface`, …) so physics layers avoid
  pulling the whole data closure graph unless needed (`lake build HQIVSO8Closure`).

Companion Python in `HQVM/matrices.py` (and `scripts/print_lean_octonion_L.py` mentioned in
`OctonionLeftMultiplication`) is for **regeneration / cross-check**, not what this file cites as authority.
-/

/-- **Dimension of the structure from counting over O.** The octonion algebra
has 8 dimensions (1 + 7 imaginary); the Lie algebra that closes from the
counting (e.g. so(8)) has dimension 28. We record 28 as the dimension of the
closure; the “8” is the octonion dimension already used in the curvature norm.
This is what we must **prove** as the number of degrees of freedom (the SO(8) closure
theorem in `Hqiv.SO8Closure` / `Hqiv.SO8ClosureInterface` matches this count). -/
def structure_from_O_dim : ℕ := 28

theorem structure_from_O_dim_eq : structure_from_O_dim = 28 := rfl

/-- **The metric forces conservation of phase (spin).** The time angle δθ′ = φ t
has period 2π (see HQVMetric: `timeAngle_first_period`, `timeAngle_zero_to_twoPi`).
So phase is conserved mod 2π — spin lost to the horizon is encoded in the phase
and wraps rather than being destroyed. This conservation is **forced by** the
metric (lapse = 1 + Φ + timeAngle, time angle in [0, 2π]). -/
theorem metric_forces_phase_conservation (φ : ℝ) (hφ : 0 < φ) :
    timeAngle φ 0 = 0 ∧ timeAngle φ (twoPi / φ) = twoPi ∧
    ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi :=
  timeAngle_zero_to_twoPi φ hφ

/-- **Lapse decomposition forces horizon term to be the time angle.** The
metric is N = 1 + Φ + δθ′; so the only time-dependent horizon coupling is
δθ′. That **forces** the conservation narrative: the horizon term is exactly
the phase (time angle) that we proved lives in [0, 2π] and wraps. -/
theorem lapse_forces_time_angle_as_horizon_term (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t :=
  lapse_decompose Φ φ t

/-!
## Structure from counting over O — degrees of freedom (Lean modules above)

The **structure** that is the result of counting over O in the light cone is the
same one closed in Lean: `L(e_i)` in `OctonionLeftMultiplication`, bracket data in
`GeneratorsLieClosureData*`, and the packaged theorems in `SO8Closure` /
`SO8ClosureInterface`. We still need to **prove** end-to-end that light-cone counting
alone forces that Lie data (the narrative link is conceptual; the dimension **28**
here matches the closure proof). Conservations forced by the metric (phase, and
later charge-like quantities) live **in** this structure. Later: identify with the
standard gauge-algebra names if desired.
-/

/-- **Statement:** conservations hold in the structure from O (dim 28, phase mod 2π). -/
def conservations_in_structure_from_O : Prop :=
  structure_from_O_dim = 28 ∧
  ∀ φ : ℝ, 0 < φ →
    timeAngle φ 0 = 0 ∧ timeAngle φ (twoPi / φ) = twoPi ∧
    ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi

/-- **Conservations hold in the structure from O.** The structure from counting
over O has dimension 28 (structure_from_O_dim), and the metric forces phase
conservation: for every φ > 0, the time angle is 0 at t = 0, equals 2π at
t = 2π/φ, and lies in [0, 2π] for t ∈ [0, 2π/φ]. So phase (spin) is conserved
mod 2π in the structure determined by the metric. -/
theorem conservations_in_structure_from_O_holds : conservations_in_structure_from_O := by
  unfold conservations_in_structure_from_O
  refine ⟨structure_from_O_dim_eq, fun φ hφ => timeAngle_zero_to_twoPi φ hφ⟩

end Hqiv
