import Hqiv.Geometry.HarmonicMulModCubeTriangulation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Prime-modulus cube fibre charts (generalization template)

Mod `7` is the Fano base for the harmonic obstruction shell.  Mod `11` is the first
prime in the cascade prefix after the raw block `{6,5,11,7}` saturation; proving a
three-cube triangulation on `ℤ/11ℤ` shows the **same simplicial-cover pattern** lifts
to the next adelic slot without changing the obstruction classification spine.
-/

namespace Hqiv.Geometry

open ZMod

/--
**Three-cube triangulation of `ℤ/11ℤ`.**  Witnessed residue-by-residue; this is the
`p = 11` instance of the `PrimeFibreSimplicialChart` template in
`Hqiv.Algebra.MulModBSDEulerFactor` (also re-exported from Story).
-/
theorem triangulate_mod11 (r : ZMod 11) :
    ∃ a b c : ZMod 11, a ^ 3 + b ^ 3 + c ^ 3 = r := by
  fin_cases r
  · exact ⟨0, 0, 0, by native_decide⟩
  · exact ⟨0, 0, 1, by native_decide⟩
  · exact ⟨0, 0, 7, by native_decide⟩
  · exact ⟨0, 0, 9, by native_decide⟩
  · exact ⟨0, 0, 5, by native_decide⟩
  · exact ⟨0, 0, 3, by native_decide⟩
  · exact ⟨0, 0, 8, by native_decide⟩
  · exact ⟨0, 0, 6, by native_decide⟩
  · exact ⟨0, 0, 2, by native_decide⟩
  · exact ⟨0, 0, 4, by native_decide⟩
  · exact ⟨0, 0, 10, by native_decide⟩

theorem triangulate_mod11_of_nat (m : ℕ) :
    ∃ a b c : ℕ, (a ^ 3 + b ^ 3 + c ^ 3 : ZMod 11) = (m : ZMod 11) := by
  obtain ⟨a, b, c, hr⟩ := triangulate_mod11 (m : ZMod 11)
  exact ⟨a.val, b.val, c.val, by simpa using hr⟩

end Hqiv.Geometry
