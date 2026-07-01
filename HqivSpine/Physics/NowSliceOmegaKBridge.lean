import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceCausalDiamond
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NowSliceOmegaKBridge` — `Ω_k` on the continuous horizon chart

Primary spatial curvature on the now slice is the chart ratio
`omegaKPartial m = omegaKChart m = omegaKContinuous (xiOfShell m) xiLockin`.
The left-sample shell sum `curvatureIntegral` remains for harmonic bounds only.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NowSliceOmegaKBridge

open HqivSpine.Physics
open HqivSpine.Physics.ContinuousHorizon
open HqivSpine.Physics.NowSliceFromLattice
open HqivSpine.Physics.CausalDiamond

theorem omegaKPartial_eq_chart (m : ℕ) : omegaKPartial m = omegaKChart m := rfl

theorem omegaKPartial_eq_continuous (m : ℕ) :
    omegaKPartial m = omegaKContinuous (xiOfShell m) xiLockin :=
  omegaKPartial_eq_omegaKContinuous m

theorem omegaKDiscretePartial_eq (m : ℕ) :
    omegaKDiscretePartial m = curvatureIntegral m / curvatureIntegral referenceM := by
  unfold omegaKDiscretePartial omegaKAtHorizon referenceM
  rfl

structure NowSliceOmegaKBridgeClosure where
  chart_identification :
    ∀ m, omegaKPartial m = omegaKContinuous (xiOfShell m) xiLockin
  lockin : omegaKPartial referenceM = 1
  strict_mono :
    ∀ {m1 m2 : ℕ}, m1 < m2 → m2 ≤ referenceM → omegaKPartial m1 < omegaKPartial m2
  causal_diamond :
    ∀ e : Event, e.slice.omegaK = omegaKPartial e.shell
  harmonic_bound : ∀ n, harmonicSum n ≤ curvatureIntegral n

noncomputable def nowSliceOmegaKBridgeClosure : NowSliceOmegaKBridgeClosure where
  chart_identification := omegaKPartial_eq_omegaKContinuous
  lockin := omegaKPartial_at_referenceM
  strict_mono := fun h hm => omegaKPartial_strictMono h hm
  causal_diamond := fun e => event_omegaK_is_discrete e
  harmonic_bound := harmonicSum_le_curvatureIntegral

theorem referenceM_nowSliceOmegaKBridge_closed :
    Nonempty NowSliceOmegaKBridgeClosure :=
  ⟨nowSliceOmegaKBridgeClosure⟩

end HqivSpine.Physics.NowSliceOmegaKBridge
