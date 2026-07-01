import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Polarizability` — field–displacement response of the binding well

Polarizability is the next observable from the derived geometry: apply a field `E`, the bound
charge `q` displaces against the well's restoring force until balance, and the induced dipole per
field is `α`. For a quadratic well `V(x) = ½ k x²` the balance `k·x = qE` gives `x* = qE/k`, induced
dipole `q·x* = q²E/k`, so `α = q²/k`. Identifying the well curvature with the derived binding —
depth `I` (ionization scale) at radius `r` (`½ k r² = I` ⇒ `k = 2I/r²`) — gives the harmonic floor
`α = q² r² / (2 I)`. Both `I` and `r` are derived (hydrogenic shell), so `α` carries no new constant.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Polarizability

/-- Restoring-force balance: a quadratic well of stiffness `k` displaces to `x* = qE/k`. -/
theorem displacement_balance (k q E : ℝ) (hk : k ≠ 0) :
    k * (q * E / k) = q * E := by
  field_simp

/-- **Response law.** The induced dipole per field of a charge `q` in a well of stiffness `k` is
`α = q²/k`. -/
theorem polarizability_response (k q E : ℝ) (hk : k ≠ 0) (hE : E ≠ 0) :
    (q * (q * E / k)) / E = q ^ 2 / k := by
  field_simp

/-- Curvature of a well of depth `I` at scale `r`: `k = 2I/r²` (from `½ k r² = I`). -/
noncomputable def wellCurvature (I r : ℝ) : ℝ := 2 * I / r ^ 2

theorem well_depth_consistent (I r : ℝ) (hr : r ≠ 0) :
    (1 / 2) * wellCurvature I r * r ^ 2 = I := by
  unfold wellCurvature; field_simp

/-- **Harmonic floor.** Polarizability of a charge `q` in the binding well `= q² r² / (2 I)`. -/
theorem polarizability_floor (I r q : ℝ) (hI : I ≠ 0) (hr : r ≠ 0) :
    q ^ 2 / wellCurvature I r = q ^ 2 * r ^ 2 / (2 * I) := by
  unfold wellCurvature; field_simp

/-- Hydrogenic closed form (atomic units, `q = 1`): with `I = z²/(2n²)` Hartree and `r = n²/z` a₀
the floor is `n⁶/z⁴` a₀³. -/
theorem hydrogenic_floor (n z : ℝ) (hn : n ≠ 0) (hz : z ≠ 0) :
    (1 : ℝ) ^ 2 * (n ^ 2 / z) ^ 2 / (2 * (z ^ 2 / (2 * n ^ 2))) = n ^ 6 / z ^ 4 := by
  field_simp

/-- The exact soft-Coulomb (hydrogenic ground-state) enhancement over the harmonic floor. -/
noncomputable def softCoulombEnhancement : ℝ := 9 / 2

theorem softCoulombEnhancement_pos : (0 : ℝ) < softCoulombEnhancement := by
  unfold softCoulombEnhancement; norm_num

end HqivSpine.Chemistry.Polarizability
