import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.Age
import HqivSpine.Physics.Gravity
import HqivSpine.Physics.NowSliceFromLattice
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.BulkHyperboloidDynamics` — dynamical `H(t)` on the bulk hyperboloid chart

The open item in `Frontiers.nowSliceCurvatureFrontier` — dynamical `H(t)` from the bulk
hyperboloid — closes here in the **homogeneous HQVM chart** carried by the spine now slice:

* **ADM lapse** `N(t) = 1 + Φ + φ·t` (`NowSlice.lapse`);
* **homogeneous Hubble readout** `H(t) = N(t)` when `Φ = 0` (`hubbleOfTime`);
* **proper-time rate** `dτ/dt = N(t)` — the wall-clock age `t + φ·t²/2` has derivative `N(t)`
  (`wallClockHomogeneous_hasDerivAt`);
* **lock-in** `(φ, t) = (1, 4)` gives `H(4) = 5 = massUnit` and `gEff(φ) = φ` at the Planck pole
  (`lockin_phi_is_gEff_fixed_point`).

The tug-of-war fixed points `φ = 0` (horizon) and `φ = 1` (Planck pole) from `Gravity` anchor
the bulk ends; lock-in sits at the positive fixed point with `G_eff = H`.

Honest scope: **scalar synchronous-comoving bulk clock** — not full manifold geodesics.
Discrete `Ω_k` on the slice is primary (`NowSliceCausalDiamond`); continuous `ξ` is export only.
-/

namespace HqivSpine.Physics

open NowSliceFromLattice

/-! ## Homogeneous wall-clock flow -/

/-- **Homogeneous wall-clock age** `τ(t) = t + φ·t²/2` (`Age.NowSlice.wallClockAge` with `Φ = 0`). -/
noncomputable def wallClockHomogeneous (φ t : ℝ) : ℝ :=
  t + φ * t ^ 2 / 2

theorem wallClockHomogeneous_eq_slice (s : NowSlice) :
    wallClockHomogeneous s.phi s.apparentAge = s.wallClockAge := rfl

theorem wallClockHomogeneous_hasDerivAt (φ t : ℝ) :
    HasDerivAt (fun t => wallClockHomogeneous φ t) (lapse 0 φ t) t := by
  unfold wallClockHomogeneous lapse
  have h1 : HasDerivAt (fun t => t) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun t => φ * t ^ 2 / 2) (φ * t) t := by
    simpa [pow_one, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_pow 2 t).const_mul φ).div_const 2
  convert h1.add h2 using 1
  ring

theorem wallClockHomogeneous_deriv_eq_lapse (φ t : ℝ) :
    deriv (fun t => wallClockHomogeneous φ t) t = lapse 0 φ t :=
  (wallClockHomogeneous_hasDerivAt φ t).deriv

/-! ## Dynamical Hubble parameter H(t) -/

/-- **Bulk Hubble readout** `H(t) = N(t) = 1 + φ·t` in the homogeneous chart (`Φ = 0`). -/
noncomputable def hubbleOfTime (φ t : ℝ) : ℝ :=
  lapse 0 φ t

theorem hubbleOfTime_eq (φ t : ℝ) : hubbleOfTime φ t = 1 + φ * t := by
  unfold hubbleOfTime lapse
  ring

theorem hubbleOfTime_eq_gravity_hubble_plus_one (φ t : ℝ) :
    hubbleOfTime φ t = hubble φ * t + 1 := by
  rw [hubbleOfTime_eq, hubble_eq]; ac_rfl

theorem hubbleOfTime_mono_t (φ t₁ t₂ : ℝ) (hφ : 0 ≤ φ) (ht : t₁ ≤ t₂) :
    hubbleOfTime φ t₁ ≤ hubbleOfTime φ t₂ := by
  rw [hubbleOfTime_eq, hubbleOfTime_eq]
  have : φ * t₁ ≤ φ * t₂ := mul_le_mul_of_nonneg_left ht hφ
  linarith

theorem hubbleOfTime_at_lockin_chart : hubbleOfTime 1 4 = 5 := by
  rw [hubbleOfTime_eq]
  norm_num

theorem lockin_hubbleOfTime_eq_massUnit :
    hubbleOfTime lockinNowSlice.phi lockinNowSlice.apparentAge = lockinNowSlice.massUnit := by
  rcases lockinNowSlice_fields with ⟨hφ, _, _, ht⟩
  rw [hφ, ht, lockinNowSlice_massUnit, hubbleOfTime_at_lockin_chart]

theorem lockin_wallClock_deriv_eq_massUnit :
    deriv (fun t => wallClockHomogeneous lockinNowSlice.phi t) lockinNowSlice.apparentAge =
      lockinNowSlice.massUnit := by
  rcases lockinNowSlice_fields with ⟨hφ, _, _, ht⟩
  rw [wallClockHomogeneous_deriv_eq_lapse, hφ, ht, lockinNowSlice_massUnit]
  unfold lapse
  norm_num

/-! ## Lock-in at the Planck-pole fixed point -/

theorem lockin_phi_is_gEff_fixed_point :
    gEff lockinNowSlice.phi = lockinNowSlice.phi := by
  rcases lockinNowSlice_fields with ⟨hφ, _, _, _⟩
  rw [hφ, gEff_one]

theorem lockin_phi_is_hubble_fixed_point :
    hubble lockinNowSlice.phi = lockinNowSlice.phi := by
  rcases lockinNowSlice_fields with ⟨hφ, _, _, _⟩
  rw [hφ, hubble_eq]

/-! ## Capstone -/

structure BulkHyperboloidDynamicsClosure where
  /-- Wall-clock derivative equals the lapse (proper-time rate). -/
  wall_clock_rate : ∀ φ t, deriv (fun t => wallClockHomogeneous φ t) t = lapse 0 φ t
  /-- Dynamical Hubble equals lapse in the homogeneous chart. -/
  hubble_is_lapse : ∀ φ t, hubbleOfTime φ t = lapse 0 φ t
  /-- Lock-in chart: `H(4) = massUnit = 5`. -/
  lockin_hubble_mass_unit : hubbleOfTime lockinNowSlice.phi lockinNowSlice.apparentAge =
    lockinNowSlice.massUnit
  /-- Lock-in sits at the Planck-pole varying-G fixed point. -/
  lockin_gEff_fixed : gEff lockinNowSlice.phi = lockinNowSlice.phi

noncomputable def bulkHyperboloidDynamics : BulkHyperboloidDynamicsClosure where
  wall_clock_rate := wallClockHomogeneous_deriv_eq_lapse
  hubble_is_lapse := fun _ _ => rfl
  lockin_hubble_mass_unit := lockin_hubbleOfTime_eq_massUnit
  lockin_gEff_fixed := lockin_phi_is_gEff_fixed_point

end HqivSpine.Physics
