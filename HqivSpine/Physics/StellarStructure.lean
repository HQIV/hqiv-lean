import HqivSpine.Physics.NowSlice

/-!
# `HqivSpine.Physics.StellarStructure` — the hydrostatic φ-shell profile

A star is the spine's shell ladder read radially: pressure stratified by the per-shell curvature
shape `shellShape m = (1/(m+1))(1 + α·ln(m+1))` from `Curvature`. With a central pressure scale
`K > 0` the **stellar pressure** is `P(m) = K·shellShape m`.

* **Central maximum.** `P(0) = K` (`stellarPressure_center`); every outer shell is softer
  (`stellarPressure_le_center`) and the profile is strictly decreasing outward
  (`stellarPressure_strictAnti`) — a real pressure gradient pointing inward.
* **Discrete hydrostatic equilibrium.** Each shell's inner pressure equals the next-out pressure
  plus the shell's own weight, `P(m) = P(m+1) + w(m)` (`hydrostatic_balance`), and the support
  `w(m)` is strictly positive (`hydrostaticSupport_pos`): every shell is genuinely held up.
* **Now-slice anchoring.** Taking `K = Ω_k·N₆₇`, the stellar profile *is* the now-slice curvature
  imprint (`stellarPressure_eq_curvatureImprint`): a positively-curved slice (`Ω_k > 0`) gives a
  positive, outward-decreasing star (`curvatureImprint_pos`, `curvatureImprint_strictAnti`) — no new
  input beyond the now slice.

Bundled in `StellarClosure` / `stellar_structure_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.StellarStructure

open HqivSpine.Physics HqivSpine.Foundation

/-! ## The stellar pressure profile -/

/-- **Stellar pressure** at shell `m`: central scale `K` stratified by the φ-shell shape. -/
noncomputable def stellarPressure (K : ℝ) (m : ℕ) : ℝ := K * shellShape m

theorem stellarPressure_pos {K : ℝ} (hK : 0 < K) (m : ℕ) : 0 < stellarPressure K m :=
  mul_pos hK (shellShape_pos m)

/-- **Central pressure** `P(0) = K` (`shellShape 0 = 1`). -/
theorem stellarPressure_center (K : ℝ) : stellarPressure K 0 = K := by
  rw [stellarPressure, shellShape_zero, mul_one]

/-- The pressure profile **strictly decreases outward** (inward-pointing gradient). -/
theorem stellarPressure_strictAnti {K : ℝ} (hK : 0 < K) : StrictAnti (stellarPressure K) := by
  intro a b hab
  unfold stellarPressure
  exact mul_lt_mul_of_pos_left (shellShape_strictAnti hab) hK

/-- The core carries the **maximum** pressure. -/
theorem stellarPressure_le_center {K : ℝ} (hK : 0 < K) (m : ℕ) :
    stellarPressure K m ≤ stellarPressure K 0 :=
  (stellarPressure_strictAnti hK).antitone (Nat.zero_le m)

/-! ## Discrete hydrostatic equilibrium -/

/-- **Hydrostatic support** of shell `m`: the inward pressure drop to the next shell out. -/
noncomputable def hydrostaticSupport (K : ℝ) (m : ℕ) : ℝ :=
  stellarPressure K m - stellarPressure K (m + 1)

/-- Every shell is genuinely held up: the support is strictly positive. -/
theorem hydrostaticSupport_pos {K : ℝ} (hK : 0 < K) (m : ℕ) : 0 < hydrostaticSupport K m := by
  unfold hydrostaticSupport
  have := stellarPressure_strictAnti hK (Nat.lt_succ_self m)
  linarith

/-- **Discrete hydrostatic equilibrium:** the inner pressure of a shell equals the outer
pressure plus the shell's own weight. -/
theorem hydrostatic_balance (K : ℝ) (m : ℕ) :
    stellarPressure K m = stellarPressure K (m + 1) + hydrostaticSupport K m := by
  unfold hydrostaticSupport; ring

/-! ## Anchoring the star to the now slice -/

/-- With central scale `K = Ω_k·N₆₇`, the stellar pressure profile **is** the now-slice
curvature imprint `Ω_k·δ_E(m)`. -/
theorem stellarPressure_eq_curvatureImprint (s : NowSlice) (m : ℕ) :
    stellarPressure (s.omegaK * curvatureNorm) m = s.curvatureImprint m := by
  unfold stellarPressure NowSlice.curvatureImprint deltaE; ring

/-- A positively-curved now slice gives a positive stellar profile at every shell. -/
theorem curvatureImprint_pos (s : NowSlice) (hΩ : 0 < s.omegaK) (m : ℕ) :
    0 < s.curvatureImprint m :=
  s.curvatureImprint_pos hΩ m

/-- A positively-curved now slice gives an outward-softening star. -/
theorem curvatureImprint_strictAnti (s : NowSlice) (hΩ : 0 < s.omegaK) :
    StrictAnti s.curvatureImprint := by
  intro a b hab
  unfold NowSlice.curvatureImprint
  exact mul_lt_mul_of_pos_left (deltaE_strictAnti hab) hΩ

/-! ## Closure -/

/-- **Stellar-structure discharge bundle.** -/
structure StellarClosure : Prop where
  central_max : ∀ {K : ℝ}, 0 < K → ∀ m : ℕ, stellarPressure K m ≤ stellarPressure K 0
  outward_softening : ∀ {K : ℝ}, 0 < K → StrictAnti (stellarPressure K)
  hydrostatic : ∀ (K : ℝ) (m : ℕ),
    stellarPressure K m = stellarPressure K (m + 1) + hydrostaticSupport K m
  support_positive : ∀ {K : ℝ}, 0 < K → ∀ m : ℕ, 0 < hydrostaticSupport K m
  anchored_to_now_slice : ∀ (s : NowSlice) (m : ℕ),
    stellarPressure (s.omegaK * curvatureNorm) m = s.curvatureImprint m

/-- **The hydrostatic φ-shell star is discharged:** a central-peaked, outward-softening pressure
profile in genuine hydrostatic balance, anchored to the now-slice curvature imprint. -/
theorem stellar_structure_closure : StellarClosure where
  central_max := stellarPressure_le_center
  outward_softening := stellarPressure_strictAnti
  hydrostatic := hydrostatic_balance
  support_positive := hydrostaticSupport_pos
  anchored_to_now_slice := stellarPressure_eq_curvatureImprint

end HqivSpine.Physics.StellarStructure
