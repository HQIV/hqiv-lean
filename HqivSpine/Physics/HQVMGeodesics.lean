import HqivSpine.Geometry.HQVMMetric
import HqivSpine.Geometry.Lorentz
import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.BulkHyperboloidDynamics
import HqivSpine.Physics.NowSliceFromLattice
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.HQVMGeodesics` — HQVM bulk geodesics on the chart jet

Discharges the now-slice HQVM geodesic layer at honest scope:

* **Christoffel connection** on the synchronous HQVM diagonal metric (`HQVMMetric.christoffelHQVM`);
* **Comoving worldline** (`u^i = 0`): `d²t/dτ² + Γ^0_{00}(dt/dτ)² = 0`, compatible with `dτ/dt = N`;
* **Inhomogeneous lapse:** spatial jets `∂_i N` enter `Γ^0_{0i}` and `Γ^i_{00}`;
* **Non-comoving timelike / spacelike:** when metric jets vanish, Christoffels vanish and straight
  coordinate lines (`d²x^μ/dτ² = 0`) solve the geodesic equation for arbitrary constant velocity;
  timelike vs spacelike classified by `hqvmIntervalSq`.

Honest scope: chart-point jet + constant-velocity straight lines in the flat-jet chart — not a full
`deriv`/`Manifold` geodesic API or curved spatial connections with nonzero `∂_j s`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.HQVMGeodesics

open HqivSpine.Geometry.HQVMMetric
open HqivSpine.Physics
open NowSliceFromLattice

/-! ## Lapse agreement with the now slice -/

theorem hqvmLapse_eq_nowSlice (s : NowSlice) :
    hqvmLapse s.bigPhi s.phi s.apparentAge = s.massUnit := rfl

theorem hqvmLapse_eq_lapse (Φ φ t : ℝ) : hqvmLapse Φ φ t = lapse Φ φ t := rfl

/-! ## Homogeneous comoving jet (bulk hyperboloid chart) -/

/-- **Homogeneous comoving jet:** `Φ = 0`, `a = 1`, only `∂_0 N = φ`. -/
noncomputable def homogeneousComovingJet_dN (φ : ℝ) : Fin 4 → ℝ :=
  fun κ => if κ = 0 then φ else 0

noncomputable def homogeneousComovingJet_da (_φ : ℝ) : Fin 4 → ℝ := fun _ => 0

noncomputable def homogeneousComovingJet_dPhi (_φ : ℝ) : Fin 4 → ℝ := fun _ => 0

theorem homogeneousComovingJet_dN_zero (φ : ℝ) : homogeneousComovingJet_dN φ 0 = φ := by
  simp [homogeneousComovingJet_dN]

theorem homogeneous_christoffel_000 (φ t : ℝ) (hN : 1 + φ * t ≠ 0) :
    christoffelHQVM (1 + φ * t) 1 0 (homogeneousComovingJet_dN φ)
      (homogeneousComovingJet_da φ) (homogeneousComovingJet_dPhi φ) 0 0 0 = φ / (1 + φ * t) := by
  rw [christoffelHQVM_000_eq (1 + φ * t) 1 0 (homogeneousComovingJet_dN φ) _ _ hN,
    homogeneousComovingJet_dN_zero]

/-! ## Comoving time geodesic -/

/-- Comoving time velocity `u^0 = dt/dτ = 1/N`. -/
noncomputable def comovingTimeVelocity (N : ℝ) : ℝ := 1 / N

/-- `d²t/dτ²` for comoving motion with `dt/dτ = 1/N` and constant-in-τ `dN/dt = dN0`. -/
noncomputable def comovingTimeSecondDerivative (N dN0 : ℝ) : ℝ := -dN0 / N ^ 3

/-- **Comoving time geodesic component** when `Γ^0_{00} = (∂_0 N)/N`. -/
theorem comoving_time_geodesic (N dN0 : ℝ) (hN : N ≠ 0)
    (hΓ : christoffelHQVM N 1 0 (fun κ => if κ = 0 then dN0 else 0) (fun _ => 0) (fun _ => 0) 0 0 0 =
      dN0 / N) :
    comovingTimeSecondDerivative N dN0 +
        christoffelHQVM N 1 0 (fun κ => if κ = 0 then dN0 else 0) (fun _ => 0) (fun _ => 0) 0 0 0 *
          comovingTimeVelocity N ^ 2 = 0 := by
  unfold comovingTimeSecondDerivative comovingTimeVelocity
  rw [hΓ]
  field_simp [hN]
  ring

theorem homogeneous_comoving_time_geodesic (φ t : ℝ) (hN : 1 + φ * t ≠ 0) :
    comovingTimeSecondDerivative (1 + φ * t) φ +
        (φ / (1 + φ * t)) * (1 / (1 + φ * t)) ^ 2 = 0 := by
  unfold comovingTimeSecondDerivative
  field_simp [hN]
  ring

/-! ## Link to bulk hyperboloid proper-time rate -/

theorem homogeneous_proper_time_rate (φ t : ℝ) :
    deriv (fun t => wallClockHomogeneous φ t) t = hqvmLapse 0 φ t := by
  rw [wallClockHomogeneous_deriv_eq_lapse, hqvmLapse_eq_lapse]

theorem lockin_proper_time_rate :
    deriv (fun t => wallClockHomogeneous lockinNowSlice.phi t) lockinNowSlice.apparentAge =
      lockinNowSlice.massUnit := by
  rw [← hqvmLapse_eq_nowSlice lockinNowSlice,
    homogeneous_proper_time_rate lockinNowSlice.phi lockinNowSlice.apparentAge]
  rcases lockinNowSlice_fields with ⟨hφ, hΦ, _, ht⟩
  simp [hφ, hΦ, ht, hqvmLapse]

/-! ## Inhomogeneous lapse: spatial Christoffels -/

/-- **Spatial lapse gradient connection:** `Γ^0_{0i} = (∂_i N)/N`. -/
theorem spatial_lapse_christoffel_00i (N : ℝ) (dN : Fin 4 → ℝ) (i : Fin 3) (hN : N ≠ 0) :
    christoffelHQVM N 1 0 dN (fun _ => 0) (fun _ => 0) 0 0 (Fin.succ i) = dN (Fin.succ i) / N :=
  christoffelHQVM_00_succi_eq N 1 0 dN (fun _ => 0) (fun _ => 0) i hN

/-- **Comoving observer feels spatial lapse gradient:** `Γ^i_{00} = N(∂_i N)/s`. -/
theorem spatial_lapse_christoffel_i00 (N : ℝ) (dN : Fin 4 → ℝ) (i : Fin 3)
    (hs : hqvmSpatialCoeff 1 0 ≠ 0) :
    christoffelHQVM N 1 0 dN (fun _ => 0) (fun _ => 0) (Fin.succ i) 0 0 =
      N * dN (Fin.succ i) / hqvmSpatialCoeff 1 0 :=
  christoffelHQVM_succi_00_eq N 1 0 dN (fun _ => 0) (fun _ => 0) i hs

theorem spatial_lapse_christoffel_i00_unit_scale (N : ℝ) (dN : Fin 4 → ℝ) (i : Fin 3) :
    christoffelHQVM N 1 0 dN (fun _ => 0) (fun _ => 0) (Fin.succ i) 0 0 = N * dN (Fin.succ i) := by
  have hs : hqvmSpatialCoeff 1 0 ≠ 0 := by unfold hqvmSpatialCoeff; norm_num
  rw [spatial_lapse_christoffel_i00 N dN i hs]
  unfold hqvmSpatialCoeff
  ring

/-- **Inhomogeneous example:** a spatial `Φ`-gradient jet produces `Γ^0_{0i} = (∂_i Φ)/N`. -/
theorem spatial_potential_lapse_christoffel (N dPhi_i : ℝ) (i : Fin 3) (hN : N ≠ 0) :
    christoffelHQVM N 1 0
        (fun κ => if κ = Fin.succ i then dPhi_i else 0) (fun _ => 0) (fun _ => 0) 0 0 (Fin.succ i) =
      dPhi_i / N := by
  rw [spatial_lapse_christoffel_00i N (fun κ => if κ = Fin.succ i then dPhi_i else 0) i hN]
  congr 1
  simp

/-! ## Non-comoving geodesics (flat metric jet) -/

/-- **Geodesic equation residual** `d²x^μ/dτ² + Γ^μ_{αβ} u^α u^β` at a frozen HQVM jet. -/
noncomputable def geodesicResidual (accel vel : Fin 4 → ℝ) (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ)
    (μ : Fin 4) : ℝ :=
  accel μ +
    ∑ α : Fin 4, ∑ β : Fin 4, christoffelHQVM N a Φ dN da dPhi μ α β * vel α * vel β

/-- When all metric jets vanish, Christoffels vanish and straight lines (`accel = 0`) are geodesics. -/
theorem geodesicResidual_zero_of_vanishing_jets (accel vel : Fin 4 → ℝ) (N a Φ : ℝ)
    (dN da dPhi : Fin 4 → ℝ) (μ : Fin 4) (haccel : accel μ = 0)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    geodesicResidual accel vel N a Φ dN da dPhi μ = 0 := by
  unfold geodesicResidual
  rw [haccel, zero_add]
  refine Finset.sum_eq_zero ?_
  intro α _
  refine Finset.sum_eq_zero ?_
  intro β _
  simp [christoffelHQVM_zero_of_vanishing_jets N a Φ dN da dPhi μ α β hN ha hΦ]

theorem geodesicStraightLine_flatJet (vel : Fin 4 → ℝ) (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) (μ : Fin 4) :
    geodesicResidual (fun _ => 0) vel N a Φ dN da dPhi μ = 0 :=
  geodesicResidual_zero_of_vanishing_jets (fun _ => 0) vel N a Φ dN da dPhi μ rfl hN ha hΦ

/-- **Spacelike straight line:** fixed coordinate time, motion along spatial slot `i`. -/
noncomputable def spacelikeSpatialVelocity (i : Fin 3) (v : ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = Fin.succ i then v else 0

/-- **Non-comoving timelike straight line:** constant `u^0` and one spatial component. -/
noncomputable def timelikeNoncomovingVelocity (i : Fin 3) (u0 ui : ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then u0 else if μ = Fin.succ i then ui else 0

theorem spacelikeSpatialVelocity_interval_pos (i : Fin 3) (v : ℝ) (a Φ : ℝ)
    (hv : v ≠ 0) (hs : 0 < hqvmSpatialCoeff a Φ) :
    0 < hqvmIntervalSq 1 a Φ (spacelikeSpatialVelocity i v) := by
  rw [hqvmIntervalSq_eq, hqvmGtt]
  have hz0 : (spacelikeSpatialVelocity i v) 0 = 0 := by
    unfold spacelikeSpatialVelocity
    split_ifs with h
    · have : Fin.succ i = 0 := h.symm
      exact absurd this (Fin.succ_ne_zero i)
    · rfl
  fin_cases i <;>
    simp [spacelikeSpatialVelocity, hz0, hqvmGtt, Fin.succ_ne_zero] <;>
    exact mul_pos hs (sq_pos_of_ne_zero hv)

theorem timelikeNoncomovingVelocity_interval_neg (i : Fin 3) (u0 ui : ℝ)
    (hu0 : 0 < u0) (hui : ui ^ 2 < u0 ^ 2) :
    hqvmIntervalSq 1 1 0 (timelikeNoncomovingVelocity i u0 ui) < 0 := by
  rw [hqvmIntervalSq_minkowskiLimit]
  fin_cases i <;>
    simp [timelikeNoncomovingVelocity, Fin.succ_ne_zero] <;>
    nlinarith [sq_nonneg ui, hu0, hui]

theorem hqvmIntervalSq_minkowskiLimit_eq_minkowskiSq4 (z : Fin 4 → ℝ) :
    hqvmIntervalSq 1 1 0 z = HqivSpine.Geometry.minkowskiSq4 z := by
  rw [hqvmIntervalSq_minkowskiLimit, HqivSpine.Geometry.minkowskiSq4_eq_time_plus_spatial]
  simp [HqivSpine.Geometry.spatialPart4, HqivSpine.Geometry.euclideanNormSq3_eq_sum_sq]

/-! ## Capstone -/

structure HQVMGeodesicsClosure where
  lapse_now_slice : ∀ s : NowSlice, hqvmLapse s.bigPhi s.phi s.apparentAge = s.massUnit
  christoffel_000 : ∀ (N : ℝ) (dN0 : ℝ), N ≠ 0 →
    christoffelHQVM N 1 0 (fun κ => if κ = 0 then dN0 else 0) (fun _ => 0) (fun _ => 0) 0 0 0 = dN0 / N
  comoving_time_geodesic :
    ∀ (N dN0 : ℝ), N ≠ 0 →
      comovingTimeSecondDerivative N dN0 +
        (dN0 / N) * comovingTimeVelocity N ^ 2 = 0
  spatial_lapse_00i :
    ∀ (N : ℝ) (dN : Fin 4 → ℝ) (i : Fin 3), N ≠ 0 →
      christoffelHQVM N 1 0 dN (fun _ => 0) (fun _ => 0) 0 0 (Fin.succ i) = dN (Fin.succ i) / N
  bulk_proper_time :
    deriv (fun t => wallClockHomogeneous lockinNowSlice.phi t) lockinNowSlice.apparentAge =
      lockinNowSlice.massUnit
  geodesic_flat_jet_straight :
    ∀ (vel : Fin 4 → ℝ) (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ),
      (∀ κ, dN κ = 0 ∧ da κ = 0 ∧ dPhi κ = 0) →
      ∀ μ, geodesicResidual (fun _ => 0) vel N a Φ dN da dPhi μ = 0
  spacelike_interval_pos :
    ∀ (i : Fin 3) (v : ℝ) (a Φ : ℝ), v ≠ 0 → 0 < hqvmSpatialCoeff a Φ →
      0 < hqvmIntervalSq 1 a Φ (spacelikeSpatialVelocity i v)
  timelike_interval_neg :
    ∀ (i : Fin 3) (u0 ui : ℝ), 0 < u0 → ui ^ 2 < u0 ^ 2 →
      hqvmIntervalSq 1 1 0 (timelikeNoncomovingVelocity i u0 ui) < 0

noncomputable def hqvmGeodesicsClosure : HQVMGeodesicsClosure where
  lapse_now_slice := hqvmLapse_eq_nowSlice
  christoffel_000 := fun N dN0 hN => christoffelHQVM_000_eq N 1 0 (fun κ => if κ = 0 then dN0 else 0)
    (fun _ => 0) (fun _ => 0) hN
  comoving_time_geodesic := fun N dN0 hN => by
    unfold comovingTimeSecondDerivative comovingTimeVelocity
    field_simp [hN]
    ring
  spatial_lapse_00i := fun N dN i hN => spatial_lapse_christoffel_00i N dN i hN
  bulk_proper_time := lockin_proper_time_rate
  geodesic_flat_jet_straight := fun vel N a Φ dN da dPhi h μ =>
    geodesicStraightLine_flatJet vel N a Φ dN da dPhi (fun κ => (h κ).1) (fun κ => (h κ).2.1)
      (fun κ => (h κ).2.2) μ
  spacelike_interval_pos := fun i v a Φ hv hs => spacelikeSpatialVelocity_interval_pos i v a Φ hv hs
  timelike_interval_neg := timelikeNoncomovingVelocity_interval_neg

theorem referenceM_hqvm_geodesics_closed : Nonempty HQVMGeodesicsClosure :=
  ⟨hqvmGeodesicsClosure⟩

theorem referenceM_noncomoving_geodesics_closed :
    (∀ (vel : Fin 4 → ℝ) (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ),
      (∀ κ, dN κ = 0 ∧ da κ = 0 ∧ dPhi κ = 0) →
      ∀ μ, geodesicResidual (fun _ => 0) vel N a Φ dN da dPhi μ = 0) ∧
    (∀ (i : Fin 3) (u0 ui : ℝ), 0 < u0 → ui ^ 2 < u0 ^ 2 →
      hqvmIntervalSq 1 1 0 (timelikeNoncomovingVelocity i u0 ui) < 0) :=
  ⟨fun vel N a Φ dN da dPhi h μ =>
      geodesicStraightLine_flatJet vel N a Φ dN da dPhi (fun κ => (h κ).1) (fun κ => (h κ).2.1)
        (fun κ => (h κ).2.2) μ,
    timelikeNoncomovingVelocity_interval_neg⟩

end HqivSpine.Physics.HQVMGeodesics
