import Hqiv.Geometry.HarmonicMulModPrimeFibreChart
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Cascade-prefix cube fibre charts (`p ∈ {13,…,41}`)

Three-cube triangulation witnesses on `ℤ/pℤ` for the harmonic cascade prefix primes
after the Fano base `7` and first adelic slot `11`.  Used by
`Hqiv.Algebra.MulModBSDEulerFactor` for prime-indexed Euler slots.
-/

namespace Hqiv.Geometry

open ZMod


theorem triangulate_mod13 (r : ZMod 13) :
    ∃ a b c : ZMod 13, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 1, 1, by native_decide⟩
  · exact ⟨0, 2, 2, by native_decide⟩
  · exact ⟨0, 4, 7, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 1, 7, by native_decide⟩
  · exact ⟨0, 2, 4, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 1, 2, by native_decide⟩
  · exact ⟨0, 7, 7, by native_decide⟩
  · exact ⟨0, 4, 4, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩

theorem triangulate_mod17 (r : ZMod 17) :
    ∃ a b c : ZMod 17, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 13, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 14, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 0, 15, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 0, 12, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 16, by native_decide⟩

theorem triangulate_mod19 (r : ZMod 19) :
    ∃ a b c : ZMod 19, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 1, 1, by native_decide⟩
  · exact ⟨0, 5, 5, by native_decide⟩
  · exact ⟨0, 5, 10, by native_decide⟩
  · exact ⟨0, 10, 10, by native_decide⟩
  · exact ⟨0, 4, 8, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 1, 2, by native_decide⟩
  · exact ⟨0, 5, 8, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩
  · exact ⟨0, 1, 10, by native_decide⟩
  · exact ⟨0, 4, 4, by native_decide⟩
  · exact ⟨0, 2, 4, by native_decide⟩
  · exact ⟨0, 2, 2, by native_decide⟩
  · exact ⟨0, 8, 8, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩

theorem triangulate_mod23 (r : ZMod 23) :
    ∃ a b c : ZMod 23, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 16, by native_decide⟩
  · exact ⟨0, 0, 12, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 0, 19, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 0, 14, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩
  · exact ⟨0, 0, 13, by native_decide⟩
  · exact ⟨0, 0, 18, by native_decide⟩
  · exact ⟨0, 0, 17, by native_decide⟩
  · exact ⟨0, 0, 21, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 15, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 20, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 22, by native_decide⟩

theorem triangulate_mod29 (r : ZMod 29) :
    ∃ a b c : ZMod 29, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 26, by native_decide⟩
  · exact ⟨0, 0, 18, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 22, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 16, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 21, by native_decide⟩
  · exact ⟨0, 0, 15, by native_decide⟩
  · exact ⟨0, 0, 17, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩
  · exact ⟨0, 0, 19, by native_decide⟩
  · exact ⟨0, 0, 23, by native_decide⟩
  · exact ⟨0, 0, 12, by native_decide⟩
  · exact ⟨0, 0, 14, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 0, 24, by native_decide⟩
  · exact ⟨0, 0, 27, by native_decide⟩
  · exact ⟨0, 0, 13, by native_decide⟩
  · exact ⟨0, 0, 25, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 20, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 0, 28, by native_decide⟩

theorem triangulate_mod31 (r : ZMod 31) :
    ∃ a b c : ZMod 31, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 1, 4, by native_decide⟩
  · exact ⟨0, 0, 16, by native_decide⟩
  · exact ⟨0, 1, 16, by native_decide⟩
  · exact ⟨0, 2, 11, by native_decide⟩
  · exact ⟨0, 2, 6, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 1, 2, by native_decide⟩
  · exact ⟨0, 2, 4, by native_decide⟩
  · exact ⟨0, 3, 17, by native_decide⟩
  · exact ⟨0, 2, 16, by native_decide⟩
  · exact ⟨0, 11, 17, by native_decide⟩
  · exact ⟨0, 6, 17, by native_decide⟩
  · exact ⟨0, 0, 17, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 1, 8, by native_decide⟩
  · exact ⟨0, 4, 8, by native_decide⟩
  · exact ⟨0, 3, 12, by native_decide⟩
  · exact ⟨0, 8, 16, by native_decide⟩
  · exact ⟨0, 11, 12, by native_decide⟩
  · exact ⟨0, 6, 12, by native_decide⟩
  · exact ⟨0, 0, 12, by native_decide⟩
  · exact ⟨0, 1, 12, by native_decide⟩
  · exact ⟨0, 3, 11, by native_decide⟩
  · exact ⟨0, 3, 6, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 1, 3, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩

theorem triangulate_mod37 (r : ZMod 37) :
    ∃ a b c : ZMod 37, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 1, 1, by native_decide⟩
  · exact ⟨0, 5, 9, by native_decide⟩
  · exact ⟨0, 3, 5, by native_decide⟩
  · exact ⟨0, 6, 21, by native_decide⟩
  · exact ⟨0, 0, 14, by native_decide⟩
  · exact ⟨0, 1, 14, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 1, 2, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 21, by native_decide⟩
  · exact ⟨0, 1, 21, by native_decide⟩
  · exact ⟨0, 3, 18, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 1, 5, by native_decide⟩
  · exact ⟨0, 2, 2, by native_decide⟩
  · exact ⟨0, 3, 3, by native_decide⟩
  · exact ⟨0, 2, 7, by native_decide⟩
  · exact ⟨0, 2, 21, by native_decide⟩
  · exact ⟨0, 5, 14, by native_decide⟩
  · exact ⟨0, 3, 6, by native_decide⟩
  · exact ⟨0, 2, 5, by native_decide⟩
  · exact ⟨0, 0, 18, by native_decide⟩
  · exact ⟨0, 1, 18, by native_decide⟩
  · exact ⟨0, 5, 21, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 1, 3, by native_decide⟩
  · exact ⟨0, 0, 17, by native_decide⟩
  · exact ⟨0, 1, 17, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 1, 6, by native_decide⟩
  · exact ⟨0, 3, 14, by native_decide⟩
  · exact ⟨0, 2, 9, by native_decide⟩
  · exact ⟨0, 2, 3, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩

theorem triangulate_mod41 (r : ZMod 41) :
    ∃ a b c : ZMod 41, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 27, by native_decide⟩
  · exact ⟨0, 0, 25, by native_decide⟩
  · exact ⟨0, 0, 20, by native_decide⟩
  · exact ⟨0, 0, 12, by native_decide⟩
  · exact ⟨0, 0, 24, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 0, 32, by native_decide⟩
  · exact ⟨0, 0, 18, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 0, 19, by native_decide⟩
  · exact ⟨0, 0, 15, by native_decide⟩
  · exact ⟨0, 0, 38, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩
  · exact ⟨0, 0, 28, by native_decide⟩
  · exact ⟨0, 0, 37, by native_decide⟩
  · exact ⟨0, 0, 11, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 0, 33, by native_decide⟩
  · exact ⟨0, 0, 30, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 13, by native_decide⟩
  · exact ⟨0, 0, 31, by native_decide⟩
  · exact ⟨0, 0, 34, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 0, 26, by native_decide⟩
  · exact ⟨0, 0, 22, by native_decide⟩
  · exact ⟨0, 0, 35, by native_decide⟩
  · exact ⟨0, 0, 23, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 39, by native_decide⟩
  · exact ⟨0, 0, 17, by native_decide⟩
  · exact ⟨0, 0, 29, by native_decide⟩
  · exact ⟨0, 0, 21, by native_decide⟩
  · exact ⟨0, 0, 16, by native_decide⟩
  · exact ⟨0, 0, 14, by native_decide⟩
  · exact ⟨0, 0, 36, by native_decide⟩
  · exact ⟨0, 0, 40, by native_decide⟩

end Hqiv.Geometry
