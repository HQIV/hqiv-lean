import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

import Hqiv.GeneratorsLieClosureData0
import Hqiv.GeneratorsLieClosureData1
import Hqiv.GeneratorsLieClosureData2
import Hqiv.GeneratorsLieClosureData3
import Hqiv.GeneratorsLieClosureData4
import Hqiv.GeneratorsLieClosureData5
import Hqiv.GeneratorsLieClosureData6
import Hqiv.GeneratorsLieClosureData7
import Hqiv.GeneratorsLieClosureData8
import Hqiv.GeneratorsLieClosureData9
import Hqiv.GeneratorsLieClosureData10
import Hqiv.GeneratorsLieClosureData11
import Hqiv.GeneratorsLieClosureData12
import Hqiv.GeneratorsLieClosureData13
import Hqiv.GeneratorsLieClosureData14
import Hqiv.GeneratorsLieClosureData15
import Hqiv.GeneratorsLieClosureData16
import Hqiv.GeneratorsLieClosureData17
import Hqiv.GeneratorsLieClosureData18
import Hqiv.GeneratorsLieClosureData19
import Hqiv.GeneratorsLieClosureData20
import Hqiv.GeneratorsLieClosureData21
import Hqiv.GeneratorsLieClosureData22
import Hqiv.GeneratorsLieClosureData23
import Hqiv.GeneratorsLieClosureData24
import Hqiv.GeneratorsLieClosureData25
import Hqiv.GeneratorsLieClosureData26
import Hqiv.GeneratorsLieClosureData27

namespace Hqiv

/-- Coefficients for `[so8Generator i, so8Generator j] = ∑ k, lieBracketCoeff i j k • so8Generator k` (chunked).
Each chunk stores exact rationals `ℚ`; we cast to `ℝ` here for the matrix Lie algebra model. -/
private def row0 (j k : Fin 28) : ℝ := (lieBracketCoeffRow0 j k : ℝ)
private def row1 (j k : Fin 28) : ℝ := (lieBracketCoeffRow1 j k : ℝ)
private def row2 (j k : Fin 28) : ℝ := (lieBracketCoeffRow2 j k : ℝ)
private def row3 (j k : Fin 28) : ℝ := (lieBracketCoeffRow3 j k : ℝ)
private def row4 (j k : Fin 28) : ℝ := (lieBracketCoeffRow4 j k : ℝ)
private def row5 (j k : Fin 28) : ℝ := (lieBracketCoeffRow5 j k : ℝ)
private def row6 (j k : Fin 28) : ℝ := (lieBracketCoeffRow6 j k : ℝ)
private def row7 (j k : Fin 28) : ℝ := (lieBracketCoeffRow7 j k : ℝ)
private def row8 (j k : Fin 28) : ℝ := (lieBracketCoeffRow8 j k : ℝ)
private def row9 (j k : Fin 28) : ℝ := (lieBracketCoeffRow9 j k : ℝ)
private def row10 (j k : Fin 28) : ℝ := (lieBracketCoeffRow10 j k : ℝ)
private def row11 (j k : Fin 28) : ℝ := (lieBracketCoeffRow11 j k : ℝ)
private def row12 (j k : Fin 28) : ℝ := (lieBracketCoeffRow12 j k : ℝ)
private def row13 (j k : Fin 28) : ℝ := (lieBracketCoeffRow13 j k : ℝ)
private def row14 (j k : Fin 28) : ℝ := (lieBracketCoeffRow14 j k : ℝ)
private def row15 (j k : Fin 28) : ℝ := (lieBracketCoeffRow15 j k : ℝ)
private def row16 (j k : Fin 28) : ℝ := (lieBracketCoeffRow16 j k : ℝ)
private def row17 (j k : Fin 28) : ℝ := (lieBracketCoeffRow17 j k : ℝ)
private def row18 (j k : Fin 28) : ℝ := (lieBracketCoeffRow18 j k : ℝ)
private def row19 (j k : Fin 28) : ℝ := (lieBracketCoeffRow19 j k : ℝ)
private def row20 (j k : Fin 28) : ℝ := (lieBracketCoeffRow20 j k : ℝ)
private def row21 (j k : Fin 28) : ℝ := (lieBracketCoeffRow21 j k : ℝ)
private def row22 (j k : Fin 28) : ℝ := (lieBracketCoeffRow22 j k : ℝ)
private def row23 (j k : Fin 28) : ℝ := (lieBracketCoeffRow23 j k : ℝ)
private def row24 (j k : Fin 28) : ℝ := (lieBracketCoeffRow24 j k : ℝ)
private def row25 (j k : Fin 28) : ℝ := (lieBracketCoeffRow25 j k : ℝ)
private def row26 (j k : Fin 28) : ℝ := (lieBracketCoeffRow26 j k : ℝ)
private def row27 (j k : Fin 28) : ℝ := (lieBracketCoeffRow27 j k : ℝ)
private def rows : Array (Fin 28 → Fin 28 → ℝ) := #[
  row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27
]

def lieBracketCoeff (i j : Fin 28) : Fin 28 → ℝ := fun k => rows[i.val]! j k

end Hqiv
