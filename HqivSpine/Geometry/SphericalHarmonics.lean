import HqivSpine.Physics.Exclusion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# `HqivSpine.Geometry.SphericalHarmonics` — S² spectrum ↔ null-shell mode ladder

On `S²` the eigenfunctions of `−Δ` are the spherical harmonics `Y_{ℓm}`, with degeneracy `2ℓ+1`
per degree `ℓ`, so the cumulative number of modes with `ℓ ≤ L` is
`∑_{ℓ=0}^{L} (2ℓ+1) = (L+1)²` (`sum_two_mul_add_one_range_succ_sq`).

The spine's discrete horizon capacity is `cumulativeModes m = 4(m+1)(m+2)` (`Physics.Exclusion`):
the same `Θ(m²)` angular bookkeeping, carrying the **octonion factor 4** and the shell shift
`(m+2)(m+1)` versus `(m+1)²`. In the refinement limit the two agree up to that factor:

`cumulativeModes m / (m+1)² → 4`  (`tendsto_cumulativeModes_div_sphericalHarmonicCumulative`),

so the discrete shell ladder matches continuum angular-mode counting up to the fixed `4`. As a
capacity readout, the smallest shell reaching the `64 = 8×8` real-dof threshold (one fermion
generation) is `m = 3` (value `80`), with `m = 2` (value `48`) below
(`minimal_shell_ge_sixty_four`).

Rebased on the spine's `cumulativeModes`; Mathlib + spine only, no legacy `Hqiv.*`, no `sorry`,
no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Geometry

open HqivSpine.Physics
open scoped BigOperators Topology
open Finset Filter

/-- **Cumulative spherical-harmonic degeneracy on `S²`:** `∑_{ℓ=0}^{L} (2ℓ+1) = (L+1)²`. -/
theorem sum_two_mul_add_one_range_succ_sq (L : ℕ) :
    ∑ l ∈ range (L + 1), (2 * l + 1) = (L + 1) ^ 2 := by
  induction L with
  | zero => rfl
  | succ L ih => rw [sum_range_succ, ih]; ring

/-- Cumulative spherical-harmonic degeneracy with cutoff `L = m` as a real scalar: `(m+1)²`. -/
noncomputable abbrev sphericalHarmonicCumulativeCount (m : ℕ) : ℝ := ((m : ℝ) + 1) ^ 2

/-- Mode count on `S²` up to degree `5` is `36 = 6²`. -/
theorem spherical_mode_count_upto_degree_five :
    ∑ l ∈ range 6, (2 * l + 1) = 36 := by
  rw [sum_two_mul_add_one_range_succ_sq 5]; norm_num

/-- The shell capacity over the spherical-harmonic cumulative count is `4 + 4/(m+1)`. -/
theorem cumulativeModes_div_sphericalHarmonicCumulative (m : ℕ) :
    (cumulativeModes m : ℝ) / sphericalHarmonicCumulativeCount m = 4 + 4 / ((m : ℝ) + 1) := by
  have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hden : sphericalHarmonicCumulativeCount m ≠ 0 := by
    unfold sphericalHarmonicCumulativeCount; positivity
  rw [div_eq_iff hden]
  unfold sphericalHarmonicCumulativeCount
  rw [cumulativeModes_eq]
  push_cast
  field_simp
  ring

/-- **Refinement limit:** the discrete horizon capacity divided by the `(L+1)²` spherical-harmonic
cumulative count (`L = m`) tends to the octonion factor `4`. Same quadratic degeneracy class as
angular modes on `S²`; the discrete ladder matches continuum counting in the large-shell limit. -/
theorem tendsto_cumulativeModes_div_sphericalHarmonicCumulative :
    Tendsto (fun m : ℕ => (cumulativeModes m : ℝ) / sphericalHarmonicCumulativeCount m) atTop
      (𝓝 (4 : ℝ)) := by
  refine (tendsto_congr cumulativeModes_div_sphericalHarmonicCumulative).mpr ?_
  have h0 : Tendsto (fun m : ℕ => (4 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 : ℝ)
  simpa using (tendsto_const_nhds (x := (4 : ℝ))).add h0

/-- Cumulative **new** modes from shell `0` through `M` equals `cumulativeModes M` (definitional
on the spine: `cumulativeModes` is exactly this triangular sum). -/
theorem sum_newModes_eq_cumulativeModes (M : ℕ) :
    ∑ i ∈ range (M + 1), newModes i = cumulativeModes M := rfl

/-! ## Capacity threshold: 64 = 8×8 real dof (one fermion generation) -/

theorem cumulativeModes_three_ge_sixty_four : 64 ≤ cumulativeModes 3 := by
  rw [cumulativeModes_eq]; norm_num

theorem cumulativeModes_two_lt_sixty_four : cumulativeModes 2 < 64 := by
  rw [cumulativeModes_eq]; norm_num

/-- The smallest shell whose `cumulativeModes` reaches `64 = 8×8`: `m = 3` (`80`), with `m = 2`
(`48`) below. -/
theorem minimal_shell_ge_sixty_four :
    64 ≤ cumulativeModes 3 ∧ cumulativeModes 2 < 64 :=
  ⟨cumulativeModes_three_ge_sixty_four, cumulativeModes_two_lt_sixty_four⟩

end HqivSpine.Geometry
