import Hqiv.LieBracketCell.R7C0
import Hqiv.LieBracketCell.R7C1
import Hqiv.LieBracketCell.R7C2
import Hqiv.LieBracketCell.R7C3
import Hqiv.LieBracketCell.R7C4
import Hqiv.LieBracketCell.R7C5
import Hqiv.LieBracketCell.R7C6
import Hqiv.LieBracketCell.R7C7
import Hqiv.LieBracketCell.R7C8
import Hqiv.LieBracketCell.R7C9
import Hqiv.LieBracketCell.R7C10
import Hqiv.LieBracketCell.R7C11
import Hqiv.LieBracketCell.R7C12
import Hqiv.LieBracketCell.R7C13
import Hqiv.LieBracketCell.R7C14
import Hqiv.LieBracketCell.R7C15
import Hqiv.LieBracketCell.R7C16
import Hqiv.LieBracketCell.R7C17
import Hqiv.LieBracketCell.R7C18
import Hqiv.LieBracketCell.R7C19
import Hqiv.LieBracketCell.R7C20
import Hqiv.LieBracketCell.R7C21
import Hqiv.LieBracketCell.R7C22
import Hqiv.LieBracketCell.R7C23
import Hqiv.LieBracketCell.R7C24
import Hqiv.LieBracketCell.R7C25
import Hqiv.LieBracketCell.R7C26
import Hqiv.LieBracketCell.R7C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 7 (imports parallel cell modules). -/
theorem lieBracket_in_span_row7 (j : Fin 28) :
    lieBracket (so8Generator ⟨7, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨7, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r7_c0
  · exact lieBracket_in_span_r7_c1
  · exact lieBracket_in_span_r7_c2
  · exact lieBracket_in_span_r7_c3
  · exact lieBracket_in_span_r7_c4
  · exact lieBracket_in_span_r7_c5
  · exact lieBracket_in_span_r7_c6
  · exact lieBracket_in_span_r7_c7
  · exact lieBracket_in_span_r7_c8
  · exact lieBracket_in_span_r7_c9
  · exact lieBracket_in_span_r7_c10
  · exact lieBracket_in_span_r7_c11
  · exact lieBracket_in_span_r7_c12
  · exact lieBracket_in_span_r7_c13
  · exact lieBracket_in_span_r7_c14
  · exact lieBracket_in_span_r7_c15
  · exact lieBracket_in_span_r7_c16
  · exact lieBracket_in_span_r7_c17
  · exact lieBracket_in_span_r7_c18
  · exact lieBracket_in_span_r7_c19
  · exact lieBracket_in_span_r7_c20
  · exact lieBracket_in_span_r7_c21
  · exact lieBracket_in_span_r7_c22
  · exact lieBracket_in_span_r7_c23
  · exact lieBracket_in_span_r7_c24
  · exact lieBracket_in_span_r7_c25
  · exact lieBracket_in_span_r7_c26
  · exact lieBracket_in_span_r7_c27

end Hqiv
