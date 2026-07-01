import HqivSpine.Physics.NowSlice

/-!
# `HqivSpine.Physics.Baryogenesis` — baryon asymmetry from the curvature imprint

The baryon asymmetry is a **readout of the now-slice curvature**, not a fitted
number. It is the true spatial curvature `Ω_k` weighted by the combinatorial
imprint `δ_E(m) = N₆₇ · shellShape m` at the QCD/lock-in shell:

`η(s, m) = Ω_k · δ_E(m) = Ω_k · 6⁷√3 · (1/(m+1)) · (1 + α·ln(m+1))`.

It is positive for positive curvature and **strictly decays in the shell index**
(via the `1/(m+1)` imprint), so the discrete shell is load-bearing. The observed
`η ≈ 6.10×10⁻¹⁰` is a comparison value, quarantined below — never an input.
-/

namespace HqivSpine.Physics

/-- **QCD/lock-in baryogenesis shell** = the proton lock-in shell `referenceM`. -/
def baryogenesisShell : ℕ := referenceM

/-- **Baryon asymmetry** as a now-slice curvature readout `Ω_k · δ_E(m)`. -/
noncomputable def baryonAsymmetry (s : NowSlice) (m : ℕ) : ℝ :=
  s.curvatureImprint m

theorem baryonAsymmetry_eq (s : NowSlice) (m : ℕ) :
    baryonAsymmetry s m = s.omegaK * deltaE m := rfl

/-- **Positive curvature gives a positive asymmetry** at every shell. -/
theorem baryonAsymmetry_pos (s : NowSlice) (hΩ : 0 < s.omegaK) (m : ℕ) :
    0 < baryonAsymmetry s m :=
  s.curvatureImprint_pos hΩ m

/-- The asymmetry at lock-in is `Ω_k · δ_E(referenceM)`. -/
theorem baryonAsymmetry_lockin (s : NowSlice) :
    baryonAsymmetry s baryogenesisShell = s.omegaK * deltaE referenceM := rfl

/-- **Comparison only:** the observed baryon asymmetry `η ≈ 6.10×10⁻¹⁰`. This is the
number a curvature readout is compared against, never a spine input. -/
def eta_observed_comparison : ℝ := 6.10e-10

theorem eta_observed_comparison_pos : 0 < eta_observed_comparison := by
  unfold eta_observed_comparison; norm_num

end HqivSpine.Physics
