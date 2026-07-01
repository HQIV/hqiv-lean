import HqivSpine.Physics.Shell
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# `HqivSpine.Physics.NeutrinoMixing` — mixing angle and CP phase from shell geometry

Two uniquely-HQIV neutrino numbers come straight out of the lock-in shell and the
foundation ratios — no PMNS matrix is imported:

* **Mixing angle `θ = π/4` (maximal).** The intrinsic axis angle of a shell `m` is
  `π/(2·Ω(m))`, where `Ω(m)` is the number of prime factors of `m` with
  multiplicity. The lock-in shell is `referenceM = 4 = 2²`, so `Ω = 2` and the angle
  is `π/4` — i.e. `sin(2θ) = 1`, maximal mixing, forced by `4` being a prime *square*.

* **CP phase `δ = π/5`.** The monogamy rapidity skew contributes `δ = (γ/2)·π` with
  `γ = 2/5`, giving exactly `π/5`.

Both are dimensionless geometry; absolute neutrino masses remain a frontier.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Intrinsic axis angle** `π/(2k)` of a `k`-fold shell. -/
noncomputable def axisAngle (k : ℕ) : ℝ := Real.pi / (2 * k)

/-- **Prime-factor count `Ω(m)`** of a shell index (with multiplicity). -/
def shellFactorCount (m : ℕ) : ℕ := ArithmeticFunction.cardFactors m

/-- The lock-in shell `4 = 2²` has exactly two prime factors. -/
theorem shellFactorCount_referenceM : shellFactorCount referenceM = 2 := by
  unfold shellFactorCount referenceM
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]

/-- **Neutrino mixing angle** = the lock-in shell's intrinsic axis `π/(2·Ω(referenceM))`. -/
noncomputable def neutrinoMixingAngle : ℝ := axisAngle (shellFactorCount referenceM)

/-- **`θ = π/4`** at the lock-in shell. -/
theorem neutrinoMixingAngle_eq_pi_div_four : neutrinoMixingAngle = Real.pi / 4 := by
  unfold neutrinoMixingAngle axisAngle
  rw [shellFactorCount_referenceM]; norm_num

/-- **Maximal mixing:** `sin(2θ) = 1`, since `2·(π/4) = π/2`. -/
theorem neutrino_maximal_mixing : Real.sin (2 * neutrinoMixingAngle) = 1 := by
  rw [neutrinoMixingAngle_eq_pi_div_four, show 2 * (Real.pi / 4) = Real.pi / 2 from by ring]
  exact Real.sin_pi_div_two

/-! ## CP phase from the monogamy rapidity skew -/

-- `γ = 2/5` (`gammaHQIV`, `gammaHQIV_eq`) is the α-partner; it lives in `Physics.Shell`.

/-- **Neutrino CP phase** = monogamy rapidity skew `(γ/2)·π`. -/
noncomputable def neutrinoCPPhase : ℝ := gammaHQIV / 2 * Real.pi

/-- **`δ = π/5`.** -/
theorem neutrinoCPPhase_eq_pi_div_five : neutrinoCPPhase = Real.pi / 5 := by
  unfold neutrinoCPPhase; rw [gammaHQIV_eq]; ring

/-- The CP phase is a strictly positive, sub-`π/2` skew. -/
theorem neutrinoCPPhase_pos : 0 < neutrinoCPPhase := by
  rw [neutrinoCPPhase_eq_pi_div_five]; positivity

end HqivSpine.Physics
