import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Hqiv.Physics.HQIVLSeriesAnalytic

/-!
# Shell index `m+1` ↔ classical ζ / Λ analytic layer (proved hooks only)

This module records **checkable** links between:

1. **The same `(n+1)` shift** appearing in the HQIV Dirichlet scaffold (`hqivDirichletTerm` uses
   `(n+1)^{-s}`) and Mathlib’s convergent Dirichlet form of **`ζ(s)`** on `Re s > 1`
   (`zeta_eq_tsum_one_div_nat_add_one_cpow`).
2. **Completed zeta** `completedRiemannZeta` (Mathlib’s Λ(s), not a separate `Xi` symbol) and its
   **functional-equation symmetry** `s ↦ 1 - s`.
3. **Trivial zeros** of **`ζ`** on the arithmetic progression **`s = -2(n+1)`** — the standard “`-2` chain”
   from the analytic continuation (often narrated as “factors of 2” lining up with sine zeros in the
   symmetric functional equation).
4. **Mod 4:** if the shell index `m` is **even**, then **`m+1` is odd**, hence **`(m+1) % 4 ∈ {1, 3}`** —
   the classical **Gaussian-type split for odd primes** (quadratic reciprocity layer). Lean only proves the
   **integer congruence**, not a tomographic selection rule for HQIV phases.

**Not claimed:** that `effCorrected`, `shell_shape`, or Fano residues are determined by zeros of Λ, or any
identity between discrete HQIV sums and `completedRiemannZeta` off the half-plane `Re s > 1` without
extra hypotheses (`HQIVRHClosureScaffold`, `ThreeSpiralGammaSymmetry`, etc.).
-/

namespace Hqiv.Physics

open Complex
open Hqiv.Geometry
open scoped Topology

noncomputable section

/-- After an even shell `m`, the shifted label `m + 1` is odd. -/
theorem odd_succ_of_even_shell (m : ℕ) (hm : Even m) : Odd (m + 1) :=
  (Nat.odd_add_one).mpr (Nat.not_odd_iff_even.mpr hm)

/-- Odd naturals reduce mod `4` to **`1` or `3`** (the two odd residue classes). -/
theorem odd_mod_four_eq_one_or_three {n : ℕ} (hn : Odd n) : n % 4 = 1 ∨ n % 4 = 3 := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
  omega

/-- Even shell `m` ⇒ `m+1 ≡ 1` or `3` (mod 4): the **1 / 3** mod‑4 axis for odd `m+1`. -/
theorem shell_succ_mod_four_eq_one_or_three_of_even (m : ℕ) (hm : Even m) :
    (m + 1) % 4 = 1 ∨ (m + 1) % 4 = 3 :=
  odd_mod_four_eq_one_or_three (odd_succ_of_even_shell m hm)

/-! ### Mathlib ζ: same `(n+1)` convention as `hqivDirichletTerm` on `Re s > 1` -/

/-- `ζ(s)` as a `ℕ`-indexed sum over **`1 / (n+1)^s`**, avoiding the `0^s` convention issue. -/
theorem riemannZeta_tsum_succ_eq (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_add_one_cpow hs

/-! ### Trivial zeros (“all 2’s” on the negative even axis) -/

/-- `ζ(-2(n+1)) = 0` for every `n` — the trivial zero ladder. -/
theorem riemannZeta_trivial_zero_at_neg_two_mul_succ (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-! ### Completed Λ(s): symmetry `s ↔ 1 - s` -/

theorem completedRiemannZeta_functional_symmetry (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-! ### HQIV coefficients `1` ⇒ literal `ζ` on `Re s > 1` (same `(n+1)` sum as above) -/

theorem hqivDirichletSeries_eq_riemannZeta_of_coeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re)
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = riemannZeta s :=
  hqivDirichletSeries_eq_riemannZeta_of_hqivCoeff_one φ t ω domains c k s hs h

theorem hqivDirichletSeries_eq_tsum_succ_of_coeff_one (φ t : ℝ) (ω : ℕ → ℝ)
    (domains : RapidityClassDomains) (c k : ℕ) (s : ℂ) (hs : 1 < s.re)
    (h : ∀ n : ℕ, hqivCoeff φ t ω domains c k n = 1) :
    hqivDirichletSeries φ t ω domains c k s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  rw [hqivDirichletSeries_eq_riemannZeta_of_coeff_one φ t ω domains c k s hs h,
    riemannZeta_tsum_succ_eq s hs]

end

end Hqiv.Physics
