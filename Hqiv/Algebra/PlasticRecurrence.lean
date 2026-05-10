import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Plastic recurrence anchor

This module provides the first machine-checkable anchor for the plastic-number
route: an explicit cubic transfer matrix whose characteristic polynomial is
`X^3 - X - 1`.

It is intentionally minimal and independent from the heavy SO(8) closure files.
-/

open Matrix
open Polynomial

namespace Hqiv.Algebra

/-- The 3x3 companion-style transfer matrix for the recurrence
`u_{n+3} = u_{n+1} + u_n`. -/
def plasticTransfer : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(0 : ℚ), 1, 0;
     0,       0, 1;
     1,       1, 0]

/-- Cubic polynomial selecting the plastic constant as dominant real root. -/
noncomputable def plasticPoly : Polynomial ℚ := X ^ 3 - X - 1

theorem charpoly_plasticTransfer :
    Matrix.charpoly plasticTransfer = plasticPoly := by
  unfold Matrix.charpoly plasticPoly
  simp [plasticTransfer, Matrix.det_fin_three]
  ring

end Hqiv.Algebra

