import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceOmegaKBridge
import HqivSpine.Physics.BulkHyperboloidDynamics
import HqivSpine.Physics.NowSliceCausalDiamond
import HqivSpine.Physics.HQVMGeodesics
import HqivSpine.Physics.CovariantOMaxwell
import HqivSpine.Geometry.Lorentz
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NowSliceClosure` — consolidated now-slice discharge

The observer's **now slice** is the sole physical anchor: curvatures `(φ, Φ, Ω_k, t)` plus the
ADM lapse `N = 1 + Φ + φ·t`. This module bundles everything discharged on that chart up to
lock-in `referenceM = 4`:

| Layer | Status | Spine module |
|-------|--------|--------------|
| Null-lattice `(φ, Φ)` + lock-in readout | closed | `NowSliceFromLattice` |
| Spatial curvature `Ω_k = omegaKChart` | closed | `NowSliceOmegaKBridge` |
| Homogeneous bulk clock `dτ/dt = N(t)` | closed | `BulkHyperboloidDynamics` |
| Causal-diamond apex + `(α,γ)` evaluation | closed | `NowSliceCausalDiamond` |
| Forward-null geodesics on the discrete chart | closed | `Geometry.Lorentz` |
| HQVM Christoffel + comoving / inhomogeneous lapse geodesics | closed | `HQVMGeodesics` |
| Covariant plasma O-Maxwell on HQVM chart | closed | `CovariantOMaxwell` |
| Non-comoving timelike/spacelike geodesics (flat-jet chart) | closed | `HQVMGeodesics` |

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NowSliceClosure

open NowSliceFromLattice
open NowSliceOmegaKBridge
open CausalDiamond
open HqivSpine.Geometry

structure NowSliceClosure where
  /-- Lock-in diamond `(φ, Φ, Ω_k, t, N) = (1, 0, 1, 4, 5)`. -/
  lockin_readout :
    lockinNowSlice.phi = 1 ∧
    lockinNowSlice.bigPhi = 0 ∧
    lockinNowSlice.omegaK = 1 ∧
    lockinNowSlice.apparentAge = 4 ∧
    lockinNowSlice.massUnit = 5
  /-- Wall-clock age `12` and ratio `3` at lock-in. -/
  lockin_ages :
    lockinNowSlice.wallClockAge = 12 ∧
    lockinNowSlice.wallClockAge / lockinNowSlice.apparentAgeValue = 3
  /-- Chart identification `Ω_k(m) = omegaKContinuous (xiOfShell m) xiLockin`. -/
  omegaK_bridge : Nonempty NowSliceOmegaKBridgeClosure
  /-- Homogeneous bulk `H(t) = N(t)`, `dτ/dt = N`, lock-in `H(4) = massUnit`. -/
  bulk_clock : Nonempty BulkHyperboloidDynamicsClosure
  /-- Local causal diamond + global imprint evaluation map. -/
  causal_diamond : Nonempty CausalDiamondClosure
  /-- Forward-null preservation and chart equivariance on the discrete `1+1` chart. -/
  null_chart_geodesic : LorentzClosure
  /-- HQVM Christoffel jet, comoving time geodesic, spatial lapse gradients. -/
  hqvm_geodesics : Nonempty HQVMGeodesics.HQVMGeodesicsClosure
  /-- Covariant plasma O-Maxwell: Christoffel divergence, flat-jet surrogate, schematic `J_O`. -/
  covariant_omaxwell : CovariantOMaxwell.CovariantOMaxwellClosure

noncomputable def nowSliceClosure : NowSliceClosure where
  lockin_readout :=
    ⟨lockinNowSlice_fields.1,
      lockinNowSlice_fields.2.1,
      lockinNowSlice_fields.2.2.1,
      lockinNowSlice_fields.2.2.2,
      lockinNowSlice_massUnit⟩
  lockin_ages := ⟨lockinNowSlice_wallClockAge, lockinNowSlice_ageRatio⟩
  omegaK_bridge := referenceM_nowSliceOmegaKBridge_closed
  bulk_clock := ⟨bulkHyperboloidDynamics⟩
  causal_diamond := ⟨causalDiamondClosure⟩
  null_chart_geodesic := lorentz_closure
  hqvm_geodesics := HQVMGeodesics.referenceM_hqvm_geodesics_closed
  covariant_omaxwell := CovariantOMaxwell.covariantOMaxwellClosure

theorem referenceM_now_slice_closure_closed : Nonempty NowSliceClosure :=
  ⟨nowSliceClosure⟩

end HqivSpine.Physics.NowSliceClosure
