import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.RindlerDetuning
import HqivSpine.Physics.Gravity
import HqivSpine.Physics.Age
import HqivSpine.Physics.Baryogenesis
import HqivSpine.Physics.NowSliceFromLattice

/-!
# `HqivSpine.Physics.NowSliceHorizon` — now slice meets the continuous chart

Bridges the explicit `NowSlice` anchor to the continuous-ξ and Rindler-detuning layers:

* lapse increment `Φ + φ·t` feeds global detuning;
* `φ` on the slice is the homogeneous Hubble rate (`Gravity.hubble`);
* lock-in horizon coordinate `ξ = 5` is the continuous face of `referenceM = 4`;
* lattice-derived lock-in slice in `NowSliceFromLattice.lockinNowSlice`.

Honest scope: **identifications and readout hooks**. Discrete `(φ, Φ, Ω_k)` from the null
lattice are in `NowSliceFromLattice`; dynamical `H(t)` from the bulk hyperboloid remains open
in `Frontiers.nowSliceCurvatureFrontier`.
-/

namespace HqivSpine.Physics.NowSliceHorizon

open HqivSpine.Physics
open ContinuousHorizon
open RindlerDetuning
open NowSliceFromLattice

/-- Lapse increment above unity: `N − 1 = Φ + φ·t`. -/
def lapseIncrement (s : NowSlice) : ℝ := s.bigPhi + s.phi * s.apparentAge

theorem lapseIncrement_eq (s : NowSlice) :
    s.massUnit - 1 = lapseIncrement s := by
  rw [NowSlice.massUnit_eq, lapseIncrement]; ring

/-- Global detuning hypothesis from the now slice and a scalar coefficient `λ`. -/
def detuningHypothesis (s : NowSlice) (lambda : ℝ) : GlobalDetuningHypothesis :=
  globalDetuningFromNowSlice lambda s.bigPhi s.phi s.apparentAge

theorem deltaGlobal_nowSlice (s : NowSlice) (lambda : ℝ) :
    deltaGlobal (detuningHypothesis s lambda) = lambda * lapseIncrement s := by
  unfold deltaGlobal detuningHypothesis globalDetuningFromNowSlice lapseIncrement; ring

/-- The slice expansion curvature is the homogeneous Hubble rate. -/
theorem hubble_from_nowSlice (s : NowSlice) : hubble s.phi = s.phi := rfl

/-- Effective gravity coupling at the slice expansion rate. -/
noncomputable def gEffNow (s : NowSlice) : ℝ := gEff s.phi

theorem gEffNow_eq (s : NowSlice) : gEffNow s = s.phi ^ (3 / 5 : ℝ) := by
  unfold gEffNow gEff; rw [alphaEM_eq]

/-- Curvature imprint at shell `m` on the slice. -/
noncomputable def imprint (s : NowSlice) (m : ℕ) : ℝ := s.curvatureImprint m

/-- Continuous lock-in coordinate from the discrete anchor. -/
theorem xiLockin_from_referenceM : xiLockin = xiOfShell referenceM := rfl

/-- The lattice lock-in slice carries `massUnit = referenceM + 1 = 5`. -/
theorem lockin_massUnit_eq_xiLockin :
    lockinNowSlice.massUnit = xiLockin := by
  rw [lockinNowSlice_massUnit, xiLockin_from_referenceM, xiOfShell_referenceM]

/-- Lock-in homogeneous gravity: `G_eff(φ=1) = 1`. -/
theorem lockin_gEff_eq_one : gEff lockinNowSlice.phi = 1 := by
  rw [lockinNowSlice_fields.1, gEff_one]

/-- Lock-in wall-clock age `t + φ·t²/2 = 12` at `(φ, t) = (1, 4)`. -/
theorem lockin_wallClockAge_eq_twelve :
    lockinNowSlice.wallClockAge = 12 :=
  lockinNowSlice_wallClockAge

/-- Lock-in age ratio wall-clock / apparent `= 3`. -/
theorem lockin_ageRatio_eq_three :
    lockinNowSlice.wallClockAge / lockinNowSlice.apparentAgeValue = 3 :=
  lockinNowSlice_ageRatio

/-- Lock-in baryon asymmetry `η = Ω_k · δ_E = δ_E(referenceM)` (since `Ω_k = 1`). -/
theorem lockin_baryonAsymmetry_eq_deltaE :
    baryonAsymmetry lockinNowSlice baryogenesisShell = deltaE referenceM := by
  rw [baryonAsymmetry_lockin, lockinNowSlice_fields.2.2.1, one_mul]

end HqivSpine.Physics.NowSliceHorizon
