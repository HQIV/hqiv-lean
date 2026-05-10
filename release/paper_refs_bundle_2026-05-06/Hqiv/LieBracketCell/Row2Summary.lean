import Hqiv.LieBracketCell.R2C0
import Hqiv.LieBracketCell.R2C1
import Hqiv.LieBracketCell.R2C2
import Hqiv.LieBracketCell.R2C3
import Hqiv.LieBracketCell.R2C4
import Hqiv.LieBracketCell.R2C5
import Hqiv.LieBracketCell.R2C6
import Hqiv.LieBracketCell.R2C7
import Hqiv.LieBracketCell.R2C8
import Hqiv.LieBracketCell.R2C9
import Hqiv.LieBracketCell.R2C10
import Hqiv.LieBracketCell.R2C11
import Hqiv.LieBracketCell.R2C12
import Hqiv.LieBracketCell.R2C13
import Hqiv.LieBracketCell.R2C14
import Hqiv.LieBracketCell.R2C15
import Hqiv.LieBracketCell.R2C16
import Hqiv.LieBracketCell.R2C17
import Hqiv.LieBracketCell.R2C18
import Hqiv.LieBracketCell.R2C19
import Hqiv.LieBracketCell.R2C20
import Hqiv.LieBracketCell.R2C21
import Hqiv.LieBracketCell.R2C22
import Hqiv.LieBracketCell.R2C23
import Hqiv.LieBracketCell.R2C24
import Hqiv.LieBracketCell.R2C25
import Hqiv.LieBracketCell.R2C26
import Hqiv.LieBracketCell.R2C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 2 (imports parallel cell modules). -/
theorem lieBracket_in_span_row2 (j : Fin 28) :
    lieBracket (so8Generator ⟨2, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨2, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r2_c0
  · exact lieBracket_in_span_r2_c1
  · exact lieBracket_in_span_r2_c2
  · exact lieBracket_in_span_r2_c3
  · exact lieBracket_in_span_r2_c4
  · exact lieBracket_in_span_r2_c5
  · exact lieBracket_in_span_r2_c6
  · exact lieBracket_in_span_r2_c7
  · exact lieBracket_in_span_r2_c8
  · exact lieBracket_in_span_r2_c9
  · exact lieBracket_in_span_r2_c10
  · exact lieBracket_in_span_r2_c11
  · exact lieBracket_in_span_r2_c12
  · exact lieBracket_in_span_r2_c13
  · exact lieBracket_in_span_r2_c14
  · exact lieBracket_in_span_r2_c15
  · exact lieBracket_in_span_r2_c16
  · exact lieBracket_in_span_r2_c17
  · exact lieBracket_in_span_r2_c18
  · exact lieBracket_in_span_r2_c19
  · exact lieBracket_in_span_r2_c20
  · exact lieBracket_in_span_r2_c21
  · exact lieBracket_in_span_r2_c22
  · exact lieBracket_in_span_r2_c23
  · exact lieBracket_in_span_r2_c24
  · exact lieBracket_in_span_r2_c25
  · exact lieBracket_in_span_r2_c26
  · exact lieBracket_in_span_r2_c27

end Hqiv
