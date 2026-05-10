import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.ContinuumMetricGradient

/-!
# HQVM inverse metric on the `Fin 4` continuum chart (constant patch)

Connects the synchronous HQVM inverse metric from [`HQVMetric`](Hqiv.Geometry.HQVMetric) to the
generic `gInvAt` slot in [`ContinuumMetricGradient`](Hqiv.Geometry.ContinuumMetricGradient) /
[`ContinuumOmaxwellClosure`](Hqiv.Physics.ContinuumOmaxwellClosure).

**Constant patch:** `hqvmInverseMetricConst N a Φ` ignores the chart basepoint and returns
`HQVM_inverseMetric N a Φ` everywhere — the correct model for frozen background scalars on a
small coordinate neighborhood.

**Minkowski limit:** at `N = 1`, `a = 1`, `Φ = 0`, the HQVM inverse agrees with
`flatMinkowskiInv` (`(-,+,+,+)` in index order `0…3`).
-/

namespace Hqiv.Geometry

noncomputable section

open scoped BigOperators

/-- Constant HQVM inverse metric as a chart map `c ↦ HQVM_inverseMetric N a Φ`. -/
noncomputable def hqvmInverseMetricConst (N a Φ : ℝ) : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ :=
  fun _ => HQVM_inverseMetric N a Φ

@[simp]
theorem hqvmInverseMetricConst_apply (N a Φ : ℝ) (c : Fin 4 → ℝ) :
    hqvmInverseMetricConst N a Φ c = HQVM_inverseMetric N a Φ :=
  rfl

theorem contravariantGradientComponentsAt_hqvmInverseMetricConst (N a Φ : ℝ)
    (φ : (Fin 4 → ℝ) → ℝ) (c : Fin 4 → ℝ) :
    contravariantGradientComponentsAt (hqvmInverseMetricConst N a Φ) φ c =
      contravariantGradientComponents (HQVM_inverseMetric N a Φ) φ c := by
  simp [contravariantGradientComponentsAt, hqvmInverseMetricConst]

/-!
### Minkowski limit (`flatMinkowskiInv`)
-/

theorem HQVM_inverseMetric_eq_flatMinkowskiInv :
    HQVM_inverseMetric 1 1 0 = flatMinkowskiInv := by
  funext ν μ
  fin_cases ν <;> fin_cases μ <;>
    simp [HQVM_inverseMetric, flatMinkowskiInv, HQVM_spatial_coeff]

theorem hqvmInverseMetricConst_Minkowski_eq_flatMinkowskiInv (c : Fin 4 → ℝ) :
    hqvmInverseMetricConst 1 1 0 c = flatMinkowskiInv := by
  simp [hqvmInverseMetricConst, HQVM_inverseMetric_eq_flatMinkowskiInv]

theorem contravariantGradientComponents_hqvmMinkowski_eq_flatMinkowskiInv (φ : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) :
    contravariantGradientComponents (HQVM_inverseMetric 1 1 0) φ c =
      contravariantGradientComponents flatMinkowskiInv φ c := by
  rw [HQVM_inverseMetric_eq_flatMinkowskiInv]

theorem contravariantGradientComponentsAt_hqvmMinkowski_eq_flatMinkowskiInv (φ : (Fin 4 → ℝ) → ℝ)
    (c : Fin 4 → ℝ) :
    contravariantGradientComponentsAt (hqvmInverseMetricConst 1 1 0) φ c =
      contravariantGradientComponents flatMinkowskiInv φ c := by
  simp [contravariantGradientComponentsAt_hqvmInverseMetricConst,
    contravariantGradientComponents_hqvmMinkowski_eq_flatMinkowskiInv]

end

end Hqiv.Geometry
