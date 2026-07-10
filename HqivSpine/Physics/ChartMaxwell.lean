import HqivSpine.Physics.Shell
import HqivSpine.Geometry.ContinuumChart
import HqivSpine.Geometry.MetricGradient

/-!
# `HqivSpine.Physics.ChartMaxwell` — O→chart Maxwell hooks

Mined from legacy `ModifiedMaxwell` / `ContinuumOmaxwellClosure`: the lock-in chart readout of
`∇φ` and `div J` on the flat `Fin 4` continuum hook. The φ-ladder field is anchored to
`phi(m) = 2(m+1)` at the lock-in shell.

Honest scope: flat-chart Maxwell identities (constant-φ limit, constant-source divergence)
— HQVM covariant O-Maxwell discharge is in `CovariantOMaxwell`.
-/

namespace HqivSpine.Physics.ChartMaxwell

open HqivSpine.Geometry.ContinuumChart
open HqivSpine.Geometry.MetricGradient
open HqivSpine.Physics

/-- Lock-in chart basepoint: time slot carries `φ(referenceM)`. -/
noncomputable def lockinChartPoint : Fin 4 → ℝ :=
  fun μ => if μ = (0 : Fin 4) then (phi referenceM : ℝ) else 0

/-- Scalar φ on the chart from the lock-in shell (flat limit: constant in space). -/
noncomputable def phiLockinField (_c : Fin 4 → ℝ) : ℝ := (phi referenceM : ℝ)

theorem phiLockinField_eq : phiLockinField = fun _ => (phi referenceM : ℝ) := rfl

/-- **(∇φ)_ν** at the lock-in readout (Euclidean chart gradient). -/
noncomputable def gradPhiLockin (ν : Fin 4) : ℝ :=
  coordsGradientComponents phiLockinField lockinChartPoint ν

theorem gradPhiLockin_zero (ν : Fin 4) : gradPhiLockin ν = 0 := by
  unfold gradPhiLockin phiLockinField
  rw [coordsGradientComponents_const (phi referenceM : ℝ) lockinChartPoint, Pi.zero_apply]

/-- Divergence of a spatially constant 4-current (charge conservation in the constant limit). -/
noncomputable def divMuConst (f : Fin 4 → ℝ) : ℝ :=
  coordsDivergence (fun _ => f) lockinChartPoint

theorem divMuConst_zero (f : Fin 4 → ℝ) : divMuConst f = 0 := by
  exact coordsDivergence_const f lockinChartPoint

/-- Divergence of a general coordinate vector field at `c`. -/
noncomputable def divMuField (V : (Fin 4 → ℝ) → Fin 4 → ℝ) (c : Fin 4 → ℝ) : ℝ :=
  coordsDivergence V c

/-- Minkowski-raised gradient of φ at lock-in (time component picks up a minus). -/
noncomputable def gradPhiMinkowskiLockin (ν : Fin 4) : ℝ :=
  contravariantGradientComponents flatMinkowskiInv phiLockinField lockinChartPoint ν

theorem gradPhiMinkowskiLockin_zero (ν : Fin 4) (hν : ν ≠ 0) :
    gradPhiMinkowskiLockin ν = 0 := by
  unfold gradPhiMinkowskiLockin
  have hpart (μ : Fin 4) : partialComponents phiLockinField lockinChartPoint μ = 0 := by
    unfold phiLockinField
    exact partialComponents_const (phi referenceM : ℝ) lockinChartPoint μ
  simp only [contravariantGradientComponents, flatMinkowskiInv]
  rw [Finset.sum_eq_single ν]
  · simp [hpart, hν]
  · intro μ _ hμ; simp [hpart, Ne.symm hμ]
  · simp

structure chartMaxwellFlatDischarged : Prop where
  grad_phi_zero : ∀ ν, gradPhiLockin ν = 0
  div_const_zero : ∀ f : Fin 4 → ℝ, divMuConst f = 0

theorem chartMaxwellFlatDischarged_holds : chartMaxwellFlatDischarged where
  grad_phi_zero := gradPhiLockin_zero
  div_const_zero := divMuConst_zero

end HqivSpine.Physics.ChartMaxwell
