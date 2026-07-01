import HqivSpine.Physics.NowSlice

/-!
# `HqivSpine.Physics.Age` — wall-clock vs apparent age from the now slice

The ADM lapse `N = 1 + φ·t` (homogeneous limit, `Φ = 0`) relates proper time to
coordinate time, so the now slice fixes both ages:

* **apparent age** = the coordinate time `t` to "now";
* **wall-clock age** = `∫₀ᵗ N = t + φ·t²/2` (the unique antiderivative vanishing at 0);
* **age ratio** = `1 + φ·t/2`.

These are pure consequences of the slice's `φ` and `t` — no extra input. (The
paper's wall-clock/apparent ≈ 3.96 comes from the full dynamics; here we record the
homogeneous closed form.)
-/

namespace HqivSpine.Physics

/-- **Apparent age** = coordinate time to the now slice. -/
def NowSlice.apparentAgeValue (s : NowSlice) : ℝ := s.apparentAge

/-- **Wall-clock age** in the homogeneous limit: `t + φ·t²/2`. -/
noncomputable def NowSlice.wallClockAge (s : NowSlice) : ℝ :=
  s.apparentAge + s.phi * s.apparentAge ^ 2 / 2

/-- **Age ratio** wall-clock / apparent `= 1 + φ·t/2` for a slice with `t ≠ 0`. -/
theorem NowSlice.ageRatio_eq (s : NowSlice) (ht : s.apparentAge ≠ 0) :
    s.wallClockAge / s.apparentAgeValue = 1 + s.phi * s.apparentAge / 2 := by
  unfold NowSlice.wallClockAge NowSlice.apparentAgeValue
  rw [div_eq_iff ht]
  ring

/-- **Wall-clock exceeds apparent age** for forward expansion (`φ > 0`, `t > 0`). -/
theorem NowSlice.wallClockAge_gt_apparent (s : NowSlice)
    (hphi : 0 < s.phi) (ht : 0 < s.apparentAge) :
    s.apparentAgeValue < s.wallClockAge := by
  unfold NowSlice.wallClockAge NowSlice.apparentAgeValue
  have : 0 < s.phi * s.apparentAge ^ 2 / 2 := by positivity
  linarith

/-- **The lapse is the derivative rate of proper time:** `N(t) = 1 + φ·t` matches the
slope of the wall-clock age. -/
theorem NowSlice.lapse_homogeneous (s : NowSlice) :
    lapse 0 s.phi s.apparentAge = 1 + s.phi * s.apparentAge := by
  unfold lapse; ring

end HqivSpine.Physics
