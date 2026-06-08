import Hqiv.LieBracketCell.R5C0
import Hqiv.LieBracketCell.R5C1
import Hqiv.LieBracketCell.R5C2
import Hqiv.LieBracketCell.R5C3
import Hqiv.LieBracketCell.R5C4
import Hqiv.LieBracketCell.R5C5
import Hqiv.LieBracketCell.R5C6
import Hqiv.LieBracketCell.R5C7
import Hqiv.LieBracketCell.R5C8
import Hqiv.LieBracketCell.R5C9
import Hqiv.LieBracketCell.R5C10
import Hqiv.LieBracketCell.R5C11
import Hqiv.LieBracketCell.R5C12
import Hqiv.LieBracketCell.R5C13
import Hqiv.LieBracketCell.R5C14
import Hqiv.LieBracketCell.R5C15
import Hqiv.LieBracketCell.R5C16
import Hqiv.LieBracketCell.R5C17
import Hqiv.LieBracketCell.R5C18
import Hqiv.LieBracketCell.R5C19
import Hqiv.LieBracketCell.R5C20
import Hqiv.LieBracketCell.R5C21
import Hqiv.LieBracketCell.R5C22
import Hqiv.LieBracketCell.R5C23
import Hqiv.LieBracketCell.R5C24
import Hqiv.LieBracketCell.R5C25
import Hqiv.LieBracketCell.R5C26
import Hqiv.LieBracketCell.R5C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 5 (imports parallel cell modules). -/
theorem lieBracket_in_span_row5 (j : Fin 28) :
    lieBracket (so8Generator ⟨5, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨5, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r5_c0
  · exact lieBracket_in_span_r5_c1
  · exact lieBracket_in_span_r5_c2
  · exact lieBracket_in_span_r5_c3
  · exact lieBracket_in_span_r5_c4
  · exact lieBracket_in_span_r5_c5
  · exact lieBracket_in_span_r5_c6
  · exact lieBracket_in_span_r5_c7
  · exact lieBracket_in_span_r5_c8
  · exact lieBracket_in_span_r5_c9
  · exact lieBracket_in_span_r5_c10
  · exact lieBracket_in_span_r5_c11
  · exact lieBracket_in_span_r5_c12
  · exact lieBracket_in_span_r5_c13
  · exact lieBracket_in_span_r5_c14
  · exact lieBracket_in_span_r5_c15
  · exact lieBracket_in_span_r5_c16
  · exact lieBracket_in_span_r5_c17
  · exact lieBracket_in_span_r5_c18
  · exact lieBracket_in_span_r5_c19
  · exact lieBracket_in_span_r5_c20
  · exact lieBracket_in_span_r5_c21
  · exact lieBracket_in_span_r5_c22
  · exact lieBracket_in_span_r5_c23
  · exact lieBracket_in_span_r5_c24
  · exact lieBracket_in_span_r5_c25
  · exact lieBracket_in_span_r5_c26
  · exact lieBracket_in_span_r5_c27

end Hqiv
