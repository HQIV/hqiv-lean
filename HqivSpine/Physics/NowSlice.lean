import HqivSpine.Physics.Curvature

/-!
# `HqivSpine.Physics.NowSlice` — the only physical anchor

The HQIV framework is parameter-free once the discrete null lattice and bulk
hyperboloid are fixed; the single remaining input is the observer's **now slice**.
That slice is *not* a mass — it carries curvature bookkeeping:

* `phi` — the time-angle / expansion-rate curvature `φ` at "now";
* `bigPhi` — the weak-field gravitational potential `Φ`;
* `omegaK` — the true spatial curvature `Ω_k`;
* `apparentAge` — the coordinate age `t` locating the slice.

The dimensionless **now-scale** is the ADM lapse `N = 1 + Φ + φ·t`. Everything
downstream is `massUnit × (dimensionless ratio)`. Anchoring on a hard proton MeV
value would collapse all of these curvatures into one opaque number and *mask*
them; here they stay explicit, and the proton is a readout from this slice.

The slice's curvature imprint `Ω_k · δ_E(m)` reuses the combinatorial `δ_E` from
`Curvature`; the load-bearing `1/(m+1)` discreteness is proved there.

**Causal-diamond reading:** the slice is the **local apex chart** of an observer's
finite causal patch on the null lattice — time, place, lapse `N`, and discrete `Ω_k`.
Global imprint glue `(α,γ) = (3/5,2/5)` is **not** stored on the slice; it enters only
through the evaluation map in `NowSliceCausalDiamond`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **The HQVM lapse** `N = 1 + Φ + φ·t`: the dimensionless now-scale. -/
def lapse (bigPhi phi t : ℝ) : ℝ := 1 + bigPhi + phi * t

/-- **The observer's now slice** — the single physical anchor of the spine,
carrying the curvatures that must be bookkept rather than masked by a mass. -/
structure NowSlice where
  /-- Time-angle / expansion-rate curvature `φ` at "now". -/
  phi : ℝ
  /-- Weak-field gravitational potential `Φ`. -/
  bigPhi : ℝ
  /-- True spatial curvature `Ω_k`. -/
  omegaK : ℝ
  /-- Apparent (coordinate) age `t` locating the slice. -/
  apparentAge : ℝ

/-- **The dimensionless now-scale** = the lapse at the now slice. All masses are
this times a dimensionless ratio. -/
def NowSlice.massUnit (s : NowSlice) : ℝ := lapse s.bigPhi s.phi s.apparentAge

theorem NowSlice.massUnit_eq (s : NowSlice) :
    s.massUnit = 1 + s.bigPhi + s.phi * s.apparentAge := rfl

/-- **Forward-time, weak-field positivity** of the now-scale. -/
theorem NowSlice.massUnit_pos (s : NowSlice)
    (hPhi : 0 < 1 + s.bigPhi) (hphi : 0 ≤ s.phi) (ht : 0 ≤ s.apparentAge) :
    0 < s.massUnit := by
  rw [NowSlice.massUnit_eq]
  have : 0 ≤ s.phi * s.apparentAge := mul_nonneg hphi ht
  linarith

/-- **Mass readout from the now slice:** the now-scale times a dimensionless ratio. -/
noncomputable def NowSlice.readout (s : NowSlice) (dimensionless : ℝ) : ℝ :=
  s.massUnit * dimensionless

/-! ## The slice curvature imprint -/

/-- **Slice curvature imprint at shell `m`:** the true curvature `Ω_k` times the
combinatorial imprint `δ_E(m) = N₆₇ · shellShape m` from `Curvature`. -/
noncomputable def NowSlice.curvatureImprint (s : NowSlice) (m : ℕ) : ℝ :=
  s.omegaK * deltaE m

/-- At the innermost shell the imprint is `Ω_k · N₆₇` (`shellShape 0 = 1`). -/
theorem NowSlice.curvatureImprint_zero (s : NowSlice) :
    s.curvatureImprint 0 = s.omegaK * curvatureNorm := by
  rw [NowSlice.curvatureImprint, deltaE_zero]

/-- A slice with positive true curvature has a positive imprint at every shell. -/
theorem NowSlice.curvatureImprint_pos (s : NowSlice) (hΩ : 0 < s.omegaK) (m : ℕ) :
    0 < s.curvatureImprint m :=
  mul_pos hΩ (deltaE_pos m)

end HqivSpine.Physics
