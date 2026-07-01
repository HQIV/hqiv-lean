import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# `HqivSpine.Foundation.ThreeGrowth` — the arithmetic seed

Ground-up, Mathlib-only restatement of the HQIV foundation seed. The *only*
combinatorial input of the whole spine is the transverse spatial dimension
`transverseDim = 3` of the past null light cone. From it we count null-shell
modes (stars-and-bars), record the quadratic-vs-cubic growth hinge, and read off
the curvature-imprint pair `(α, γ) = (3/5, 2/5)` as the `d = 3` row of a closed
rational family.

No octonions, no matrices, no carrier choice here: everything is `ℕ`/`ℚ`
arithmetic. The `8`, the seven imaginary directions, and the Fano incidence are
*derived* downstream, not assumed.
-/

namespace HqivSpine.Foundation

/-- The single combinatorial input: transverse spatial dimension of the null
lattice. The octonion data is forced from this, not the other way around. -/
def transverseDim : ℕ := 3

/-- **Spacetime (base) dimension** `= transverseDim + 1 = 4`: the three transverse
light-cone directions plus the one null/time direction — the `Fin 4` base the gauge
and Lorentz layers are fibered over. -/
def spacetimeDim : ℕ := transverseDim + 1

theorem spacetimeDim_eq_four : spacetimeDim = 4 := rfl

/-- 3D null-shell mode-count numerator: twice the stars-and-bars count
`C(m+2, 2)`, kept as the integer `(m+2)(m+1)` (the `1/2` is implicit). -/
def shellNumer (m : ℕ) : ℕ := (m + 2) * (m + 1)

theorem shellNumer_pos (m : ℕ) : 0 < shellNumer m := by
  unfold shellNumer; positivity

/-- **Quadratic growth hinge.** The per-shell increment is the *linear* `2(m+2)`,
so the shell count is quadratic in `m`; a genuine `3+1` ball-volume law would be
cubic. That gap is what makes "3D causal growth" specific. -/
theorem shellNumer_increment (m : ℕ) :
    shellNumer (m + 1) = shellNumer m + 2 * (m + 2) := by
  simp only [shellNumer]; ring

/-- **Discrete Ricci-flow fixed point on the shell lattice.** The shell mode count
is quadratic, so its discrete curvature — the second difference — is the *constant*
`2`: `shellNumer (m+2) + shellNumer m = 2·shellNumer (m+1) + 2`. The lattice carries
constant discrete curvature, a Ricci-flow fixed point (soliton): curvature cannot
sharpen without bound, so any coupling built on it (e.g. `G_eff`) saturates. -/
theorem shellNumer_second_difference (m : ℕ) :
    shellNumer (m + 2) + shellNumer m = 2 * shellNumer (m + 1) + 2 := by
  simp only [shellNumer]; ring

/-- Cumulative shell count up to shell `n`. -/
def cumShell : ℕ → ℕ
  | 0 => shellNumer 0
  | n + 1 => cumShell n + shellNumer (n + 1)

/-- **Hockey-stick (cubic cumulative law):** `3 · cum n = (n+1)(n+2)(n+3)`. The
factor `3` is the transverse dimension and the source of the numerator in
`α = 3/5`. -/
theorem cumShell_hockey_stick (n : ℕ) :
    3 * cumShell n = (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => simp [cumShell, shellNumer]
  | succ n ih =>
    simp only [cumShell, shellNumer]
    rw [Nat.mul_add 3, ih]; ring

theorem cumShell_pos (n : ℕ) : 0 < cumShell n := by
  induction n with
  | zero => simpa [cumShell] using shellNumer_pos 0
  | succ n ih => rw [cumShell]; exact Nat.add_pos_left ih _

/-! ## Curvature-imprint family `(α_d, γ_d)` -/

/-- **Curvature-imprint exponent** `α_d = d / (2d − 1)`. -/
def alphaRat (d : ℕ) : ℚ := (d : ℚ) / (2 * (d : ℚ) - 1)

/-- **Informational-monogamy complement** `γ_d = (d − 1) / (2d − 1)`. -/
def gammaRat (d : ℕ) : ℚ := ((d : ℚ) - 1) / (2 * (d : ℚ) - 1)

/-- **α = 3/5** at the physical `d = 3` row. -/
theorem alpha_three : alphaRat 3 = 3 / 5 := by unfold alphaRat; norm_num

/-- **γ = 2/5** at the physical `d = 3` row. -/
theorem gamma_three : gammaRat 3 = 2 / 5 := by unfold gammaRat; norm_num

/-- `α` at the lattice's own transverse dimension is `3/5`. -/
theorem alpha_transverseDim : alphaRat transverseDim = 3 / 5 := alpha_three

/-- **Unit split:** `α_d + γ_d = 1` for every `d ≥ 1` (imprint plus monogamy fill
the unit). -/
theorem alpha_add_gamma (d : ℕ) (hd : 1 ≤ d) : alphaRat d + gammaRat d = 1 := by
  unfold alphaRat gammaRat
  have hcast : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hne : 2 * (d : ℚ) - 1 ≠ 0 := by nlinarith
  rw [← add_div, div_eq_one_iff_eq hne]; ring

/-- **Dimension-balance ratio:** `α₃ / γ₃ = 3/2 = d / (d−1)` at `d = 3`. -/
theorem alpha_div_gamma_three : alphaRat 3 / gammaRat 3 = 3 / 2 := by
  rw [alpha_three, gamma_three]; norm_num

end HqivSpine.Foundation
