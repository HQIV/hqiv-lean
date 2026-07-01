import HqivSpine.Physics.Baryogenesis

/-!
# `HqivSpine.Physics.BBN` — primordial light-element abundances

Big-Bang nucleosynthesis as a **structural readout** of one ratio — the frozen-out neutron-to-proton
ratio `r = n/p` — with its single cosmological input, the baryon-to-photon ratio, supplied by the
`Baryogenesis` now-slice curvature readout (no PDG abundance fit, no MeV literal).

* **Nucleon fractions.** `X_n = r/(1+r)`, `X_p = 1/(1+r)` partition the baryons (`fractions_sum_one`).
* **Helium-4 mass fraction.** Every surviving neutron is locked into a `⁴He` nucleus dragging one
  proton, so `Y_p = 2·X_n = 2r/(1+r)` (`helium4MassFraction_eq_two_neutronFraction`). It is
  nonnegative, monotone increasing in `r` (`helium4MassFraction_mono`), and stays below `1` exactly
  when `r < 1` (`helium4MassFraction_lt_one_iff`) — the standard neutron-poor freeze-out.
* **Baryon-to-photon input.** `η = Ω_k·δ_E(referenceM)` is the `Baryogenesis` curvature asymmetry at
  the lock-in shell (`baryonToPhoton_eq`), positive for positive curvature (`baryonToPhoton_pos`):
  BBN's one free parameter is downstream of the now slice, not an input.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.BBN

open HqivSpine.Physics

/-! ## Nucleon fractions from the frozen-out `n/p` ratio -/

/-- **Neutron fraction** `X_n = r/(1+r)` from the `n/p` ratio `r`. -/
noncomputable def neutronFraction (r : ℝ) : ℝ := r / (1 + r)

/-- **Proton fraction** `X_p = 1/(1+r)`. -/
noncomputable def protonFraction (r : ℝ) : ℝ := 1 / (1 + r)

theorem neutronFraction_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ neutronFraction r := by
  unfold neutronFraction
  have hpos : (0 : ℝ) < 1 + r := by linarith
  positivity

theorem protonFraction_pos (r : ℝ) (hr : 0 ≤ r) : 0 < protonFraction r := by
  unfold protonFraction
  have hpos : (0 : ℝ) < 1 + r := by linarith
  positivity

/-- The two nucleon fractions partition the baryons: `X_n + X_p = 1`. -/
theorem fractions_sum_one (r : ℝ) (hr : 0 ≤ r) :
    neutronFraction r + protonFraction r = 1 := by
  unfold neutronFraction protonFraction
  have h1 : (1 : ℝ) + r ≠ 0 := by positivity
  field_simp
  ring

/-! ## Helium-4 mass fraction -/

/-- **Primordial `⁴He` mass fraction** `Y_p = 2r/(1+r)` (every neutron pairs with a proton). -/
noncomputable def helium4MassFraction (r : ℝ) : ℝ := 2 * r / (1 + r)

theorem helium4MassFraction_eq_two_neutronFraction (r : ℝ) :
    helium4MassFraction r = 2 * neutronFraction r := by
  unfold helium4MassFraction neutronFraction; ring

theorem helium4MassFraction_nonneg (r : ℝ) (hr : 0 ≤ r) : 0 ≤ helium4MassFraction r := by
  unfold helium4MassFraction
  have : (0 : ℝ) < 1 + r := by linarith
  positivity

/-- `Y_p` increases with the neutron-to-proton ratio. -/
theorem helium4MassFraction_mono {r r' : ℝ} (hr : 0 ≤ r) (h : r ≤ r') :
    helium4MassFraction r ≤ helium4MassFraction r' := by
  unfold helium4MassFraction
  have h1 : (0 : ℝ) < 1 + r := by linarith
  have h2 : (0 : ℝ) < 1 + r' := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [hr, h]

/-- **Neutron-poor freeze-out:** the helium mass fraction is below `1` exactly when `r < 1`. -/
theorem helium4MassFraction_lt_one_iff (r : ℝ) (hr : 0 ≤ r) :
    helium4MassFraction r < 1 ↔ r < 1 := by
  unfold helium4MassFraction
  have h1 : (0 : ℝ) < 1 + r := by linarith
  rw [div_lt_one h1]
  constructor <;> intro h <;> linarith

/-! ## The baryon-to-photon input from the curvature readout -/

/-- **Baryon-to-photon ratio** as the `Baryogenesis` curvature asymmetry at the lock-in shell. -/
noncomputable def baryonToPhoton (s : NowSlice) : ℝ := baryonAsymmetry s baryogenesisShell

theorem baryonToPhoton_eq (s : NowSlice) : baryonToPhoton s = s.omegaK * deltaE referenceM :=
  baryonAsymmetry_lockin s

/-- A positive-curvature slice gives a positive baryon-to-photon ratio — BBN's only input is fixed by
the now slice. -/
theorem baryonToPhoton_pos (s : NowSlice) (hΩ : 0 < s.omegaK) : 0 < baryonToPhoton s :=
  baryonAsymmetry_pos s hΩ baryogenesisShell

end HqivSpine.Physics.BBN
