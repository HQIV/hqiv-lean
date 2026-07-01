/-
  HQIV Algebra: the Fano multiplication table of the Cayley–Dickson octonions
  ===========================================================================

  Bridge between the abstractly-forced carrier and its combinatorial skeleton.
  On the concrete octonions `𝕆 = CayleyDickson³ ℝ` we exhibit the standard basis
  `e₀ = 1, e₁ … e₇`, prove the imaginary units square to `-1`, and compute the
  seven oriented "line" products. We then show these products land **exactly on
  the Fano incidence derived upstream** in `Hqiv.Foundation.SevenImaginaryIncidence`
  (the `PG(2,2)` lines forced by `imaginaryDim = 7`), under the labelling
  `imaginary point p : Fin 7  ↦  e_{p+1}`.

  This connects the two octonion descriptions in the repo: the abstract
  Cayley–Dickson algebra (here) and the Foundation-derived Fano plane — the same
  incidence that the matrix model `Hqiv.Algebra.OctonionBasics` realizes.

  No `sorry`, no new `axiom`, no `native_decide`.
-/

import Hqiv.Algebra.CayleyDickson
import Hqiv.Foundation.SevenImaginaryIncidence

namespace Hqiv.Algebra

namespace CayleyDickson

-- Recurse `ext` through every Cayley–Dickson layer down to the `ℝ` leaves.
attribute [local ext] CayleyDickson.ext

/-! ### The standard octonion basis `e₀ … e₇`

Coordinates run through the three doublings: an element is
`⟨⟨⟨a,b⟩,⟨c,d⟩⟩, ⟨⟨e,f⟩,⟨g,h⟩⟩⟩` with `a … h : ℝ`, and `eₙ` is the unit vector
in slot `n` (in that order). -/

/-- `e₀ = 1`. -/
def e0 : 𝕆 := 1
/-- `e₁`. -/
def e1 : 𝕆 := ⟨⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₂`. -/
def e2 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₃`. -/
def e3 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 1⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₄`. -/
def e4 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨1, 0⟩, ⟨0, 0⟩⟩⟩
/-- `e₅`. -/
def e5 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 1⟩, ⟨0, 0⟩⟩⟩
/-- `e₆`. -/
def e6 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨1, 0⟩⟩⟩
/-- `e₇`. -/
def e7 : 𝕆 := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 1⟩⟩⟩

/-- The seven imaginary units, indexed by the Fano points `Fin 7` (`p ↦ e_{p+1}`). -/
def eImag : Fin 7 → 𝕆
  | 0 => e1
  | 1 => e2
  | 2 => e3
  | 3 => e4
  | 4 => e5
  | 5 => e6
  | 6 => e7

/-- Tactic skeleton: split to the eight real leaves, unfold the basis vectors and
the Cayley–Dickson multiplication, and discharge the arithmetic. -/
local macro "octonion_compute" : tactic =>
  `(tactic|
    (ext <;>
      simp only [e0, e1, e2, e3, e4, e5, e6, e7, mul_fst, mul_snd, star_fst, star_snd,
        star_trivial, add_fst, add_snd, neg_fst, neg_snd, sub_fst, sub_snd, one_fst', one_snd',
        zero_fst, zero_snd] <;>
      ring))

/-! ### Unit and squares -/

theorem e0_mul (x : 𝕆) : e0 * x = x := by rw [e0, one_mul]
theorem mul_e0 (x : 𝕆) : x * e0 = x := by rw [e0, mul_one]

theorem e1_sq : e1 * e1 = -e0 := by octonion_compute
theorem e2_sq : e2 * e2 = -e0 := by octonion_compute
theorem e3_sq : e3 * e3 = -e0 := by octonion_compute
theorem e4_sq : e4 * e4 = -e0 := by octonion_compute
theorem e5_sq : e5 * e5 = -e0 := by octonion_compute
theorem e6_sq : e6 * e6 = -e0 := by octonion_compute
theorem e7_sq : e7 * e7 = -e0 := by octonion_compute

/-! ### The seven oriented Fano-line products -/

theorem e1_mul_e2 : e1 * e2 = e3 := by octonion_compute
theorem e1_mul_e4 : e1 * e4 = e5 := by octonion_compute
theorem e1_mul_e7 : e1 * e7 = e6 := by octonion_compute
theorem e2_mul_e4 : e2 * e4 = e6 := by octonion_compute
theorem e2_mul_e5 : e2 * e5 = e7 := by octonion_compute
theorem e3_mul_e4 : e3 * e4 = e7 := by octonion_compute
theorem e3_mul_e6 : e3 * e6 = e5 := by octonion_compute

/-- Sample anticommutativity: the product reverses sign on swapping factors. -/
theorem e2_mul_e1 : e2 * e1 = -e3 := by octonion_compute

/-! ### Bridge to the Foundation Fano incidence

Each of the seven Foundation lines `Hqiv.Foundation.fanoLine L` (a 3-point set in
`Fin 7`) is realized by an oriented product of the corresponding Cayley–Dickson
imaginary units: there exist `a b c` with `fanoLine L = {a,b,c}` and
`eImag a · eImag b = eImag c`. Hence the CD multiplication is supported exactly on
the abstractly-derived `PG(2,2)` incidence. -/
theorem cd_basis_realizes_fanoLine (L : Fin 7) :
    ∃ a b c : Fin 7, Hqiv.Foundation.fanoLine L = {a, b, c} ∧ eImag a * eImag b = eImag c := by
  fin_cases L
  · exact ⟨0, 1, 2, by decide, e1_mul_e2⟩
  · exact ⟨0, 3, 4, by decide, e1_mul_e4⟩
  · exact ⟨0, 6, 5, by decide, e1_mul_e7⟩
  · exact ⟨1, 3, 5, by decide, e2_mul_e4⟩
  · exact ⟨1, 4, 6, by decide, e2_mul_e5⟩
  · exact ⟨2, 3, 6, by decide, e3_mul_e4⟩
  · exact ⟨2, 5, 4, by decide, e3_mul_e6⟩

/-- Conversely, the three imaginary units on any Foundation line close
multiplicatively: their oriented product is collinear in the sense of
`Hqiv.Foundation.collinearImag`. -/
theorem cd_fano_product_collinear (L : Fin 7) :
    ∃ a b c : Fin 7, Hqiv.Foundation.collinearImag a b c ∧ eImag a * eImag b = eImag c := by
  obtain ⟨a, b, c, hL, hprod⟩ := cd_basis_realizes_fanoLine L
  refine ⟨a, b, c, ⟨L, ?_, ?_, ?_⟩, hprod⟩ <;> rw [hL] <;> simp

end CayleyDickson

end Hqiv.Algebra
