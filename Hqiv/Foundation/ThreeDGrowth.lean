import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# ThreeDGrowth — the axiom-free 3D null-shell growth backbone

This module is the **earliest foundation file** of the octonion-derivation spine.
It contains **only number theory**: stars-and-bars shell counting for a
three-dimensional transverse null lattice, the cumulative (hockey-stick) law, the
quadratic-versus-cubic dimensional hinge, and the curvature-imprint pair
`(α, γ) = (3/5, 2/5)` as the `d = 3` row of a closed family.

**No octonions, no matrices, no carrier choice appear here.** Everything is proved
over `ℕ`/`ℚ` with `rfl`, `ring`, `norm_num`, and a single `induction`. The octonion
factor `8`, the seven imaginary directions, and the Fano incidence are *derived*
downstream (`CarrierBudget`, `SevenImaginaryIncidence`), not assumed.

The point of the derivation programme: the carrier is the **endpoint** of

`3D growth + monogamy + closure → 8-channel carrier → 7 imaginary directions → octonions`

rather than a starting assumption. This file is the irreducible arithmetic seed.
-/

namespace Hqiv.Foundation

/-- **Transverse spatial dimension** of the HQIV null lattice.

This is the single combinatorial input that the whole spine hangs on: the past
light-cone has a `d = 3` transverse stars-and-bars structure. It is *not* an octonion
input; the octonion data is forced from it downstream. -/
def transverseDim : ℕ := 3

theorem transverseDim_eq : transverseDim = 3 := rfl

/-! ## Null-shell mode counting (stars-and-bars, `d = 3`) -/

/-- **3D null-shell mode-count numerator.**

Twice the stars-and-bars count `C(m+2, 2)` of nonnegative integer solutions of
`x + y + z = m`, kept as the integer numerator `(m+2)(m+1)` (the `1/2` is implicit).
This is the number of new null modes available at shell `m`. -/
def shellNumer (m : ℕ) : ℕ := (m + 2) * (m + 1)

theorem shellNumer_eq (m : ℕ) : shellNumer m = (m + 2) * (m + 1) := rfl

theorem shellNumer_zero : shellNumer 0 = 2 := rfl
theorem shellNumer_one : shellNumer 1 = 6 := rfl
theorem shellNumer_two : shellNumer 2 = 12 := rfl

theorem shellNumer_pos (m : ℕ) : 0 < shellNumer m := by
  rw [shellNumer_eq]; positivity

/-- **The dimensional hinge (quadratic growth).**

The per-shell increment `shellNumer (m+1) − shellNumer m` is the *linear* function
`2(m+2)`, hence the shell count itself is **quadratic** in `m`. A genuine `3+1`
ball-volume law would be **cubic**; that quadratic-versus-cubic gap is exactly what
makes "3D causal growth" specific. (Cf. `cumShell_hockey_stick`, which is the cubic
cumulative.) -/
theorem shellNumer_increment (m : ℕ) :
    shellNumer (m + 1) = shellNumer m + 2 * (m + 2) := by
  simp only [shellNumer_eq]; ring

/-- Cumulative shell count up to shell `n`. -/
def cumShell : ℕ → ℕ
  | 0 => shellNumer 0
  | n + 1 => cumShell n + shellNumer (n + 1)

theorem cumShell_zero : cumShell 0 = shellNumer 0 := rfl

/-- **Hockey-stick (the cubic cumulative law):** `3 · cum n = (n+1)(n+2)(n+3)`.

The cumulative mode budget grows cubically while each shell grows quadratically; the
factor `3` is the transverse dimension and the source of the numerator in `α = 3/5`. -/
theorem cumShell_hockey_stick (n : ℕ) :
    3 * cumShell n = (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => simp [cumShell, shellNumer]
  | succ n ih =>
    simp only [cumShell, shellNumer]
    rw [Nat.mul_add 3, ih]
    ring

theorem cumShell_pos (n : ℕ) : 0 < cumShell n := by
  induction n with
  | zero => simpa [cumShell] using shellNumer_pos 0
  | succ n ih =>
    rw [cumShell]
    exact Nat.add_pos_left ih (shellNumer (n + 1))

/-! ## Curvature-imprint family `(α_d, γ_d)` -/

/-- **Curvature-imprint exponent** for transverse dimension `d`: `α_d = d / (2d − 1)`. -/
def alphaRat (d : ℕ) : ℚ := (d : ℚ) / (2 * (d : ℚ) - 1)

/-- **Informational-monogamy complement:** `γ_d = (d − 1) / (2d − 1)`. -/
def gammaRat (d : ℕ) : ℚ := ((d : ℚ) - 1) / (2 * (d : ℚ) - 1)

/-- **α = 3/5** at the physical `d = 3` row. -/
theorem alpha_three : alphaRat 3 = 3 / 5 := by unfold alphaRat; norm_num

/-- **γ = 2/5** at the physical `d = 3` row. -/
theorem gamma_three : gammaRat 3 = 2 / 5 := by unfold gammaRat; norm_num

/-- `α` evaluated at the lattice's own transverse dimension is `3/5`. -/
theorem alpha_transverseDim : alphaRat transverseDim = 3 / 5 := by
  rw [transverseDim_eq]; exact alpha_three

/-- **Unit split:** `α_d + γ_d = 1` for every `d ≥ 1` (imprint plus monogamy fill the unit). -/
theorem alpha_add_gamma (d : ℕ) (hd : 1 ≤ d) : alphaRat d + gammaRat d = 1 := by
  unfold alphaRat gammaRat
  have hcast : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hne : 2 * (d : ℚ) - 1 ≠ 0 := by nlinarith
  rw [← add_div, div_eq_one_iff_eq hne]
  ring

/-- **Dimension-balance ratio:** `α₃ / γ₃ = 3/2 = d / (d−1)` at `d = 3`. -/
theorem alpha_div_gamma_three : alphaRat 3 / gammaRat 3 = 3 / 2 := by
  rw [alpha_three, gamma_three]; norm_num

end Hqiv.Foundation
