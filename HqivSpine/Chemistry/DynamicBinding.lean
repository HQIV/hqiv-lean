import HqivSpine.Chemistry.BondedHorizon
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.Shell
import HqivSpine.Foundation.Carrier
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `HqivSpine.Chemistry.DynamicBinding` — finite-site binding factorization

Golfed from legacy `DynamicBindingChart`: the post-surplus binding readout

`E_bind = η · surplus · geomean(vev) · κ(ξ) · EV/λ`,

with every factor structural. LiH/H₂O numerics need the bonded-horizon surplus input.

Honest scope: **factorization theorems** — not GMTKN55 fit literals.
-/

namespace HqivSpine.Chemistry.DynamicBinding

open HqivSpine.Chemistry.BondedHorizon
open HqivSpine.Physics.ContinuousHorizon
open HqivSpine.Physics
open HqivSpine.Foundation

/-- Compton triplet on discrete shell indices (not `ξ` directly). -/
structure ComptonTriplet where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ

def comptonTripletH2 : ComptonTriplet :=
  { m0 := referenceM, m1 := referenceM, m2 := referenceM }

def comptonTripletHeavyHydride : ComptonTriplet :=
  { m0 := referenceM + 1, m1 := referenceM + 2, m2 := referenceM }

/-- TUFT vev factor relative to lock-in: `φ(ξ)/φ(ξ_lock)`. -/
noncomputable def tuftVevFactorAtXi (ξ : ℝ) : ℝ :=
  phiOfXi ξ / phiOfXi xiLockin

theorem tuftVevFactorAtXi_lockin : tuftVevFactorAtXi xiLockin = 1 := by
  unfold tuftVevFactorAtXi
  have h : phiOfXi xiLockin ≠ 0 := by
    unfold phiOfXi xiLockin xiOfShell referenceM; norm_num
  field_simp [h]

/-- Geometric mean of vev factors on a triplet. -/
noncomputable def tuftVevGeometricMean (t : ComptonTriplet) : ℝ :=
  Real.rpow (tuftVevFactorAtXi (xiOfShell t.m0) *
    tuftVevFactorAtXi (xiOfShell t.m1) * tuftVevFactorAtXi (xiOfShell t.m2)) (1 / 3)

/-- Curvature feedback at horizon coordinate `ξ`: `γ · (4/8) · σ(ξ)/σ(ξ_lock)`. -/
noncomputable def dynamicBindingCurvatureAtXi (ξ : ℝ) : ℝ :=
  gammaHQIV * (4 / (carrierMultiplicity : ℝ)) * sigmaXi ξ / sigmaXi xiLockin

theorem dynamicBindingCurvatureAtXi_lockin :
    dynamicBindingCurvatureAtXi xiLockin = gammaHQIV * (4 / (carrierMultiplicity : ℝ)) := by
  unfold dynamicBindingCurvatureAtXi
  have hσ : sigmaXi xiLockin ≠ 0 := by
    unfold xiLockin
    rw [sigmaXi_xiOfShell]
    exact ne_of_gt (shellShape_pos referenceM)
  field_simp [hσ]

/-- Full dynamic binding readout (dimensionless core). -/
structure DynamicBindingReadout where
  eta : ℝ
  surplus : ℝ
  vevGeomean : ℝ
  kappa : ℝ

noncomputable def dynamicBindingCore (r : DynamicBindingReadout) : ℝ :=
  r.eta * r.surplus * r.vevGeomean * r.kappa

theorem dynamicBindingCore_mul (η surplus vev κ : ℝ) :
    dynamicBindingCore { eta := η, surplus := surplus, vevGeomean := vev, kappa := κ }
      = η * surplus * vev * κ := rfl

/-- H₂ readout scaffold at lock-in shells. -/
noncomputable def h2DynamicReadout (surplus : ℝ) : DynamicBindingReadout :=
  { eta := 1
    surplus := surplus
    vevGeomean := tuftVevGeometricMean comptonTripletH2
    kappa := dynamicBindingCurvatureAtXi xiLockin }

theorem dynamicBinding_factorization (r : DynamicBindingReadout) :
    dynamicBindingCore r = r.eta * r.surplus * r.vevGeomean * r.kappa := rfl

end HqivSpine.Chemistry.DynamicBinding
