import Hqiv.LieBracketCell.R6C0
import Hqiv.LieBracketCell.R6C1
import Hqiv.LieBracketCell.R6C2
import Hqiv.LieBracketCell.R6C3
import Hqiv.LieBracketCell.R6C4
import Hqiv.LieBracketCell.R6C5
import Hqiv.LieBracketCell.R6C6
import Hqiv.LieBracketCell.R6C7
import Hqiv.LieBracketCell.R6C8
import Hqiv.LieBracketCell.R6C9
import Hqiv.LieBracketCell.R6C10
import Hqiv.LieBracketCell.R6C11
import Hqiv.LieBracketCell.R6C12
import Hqiv.LieBracketCell.R6C13
import Hqiv.LieBracketCell.R6C14
import Hqiv.LieBracketCell.R6C15
import Hqiv.LieBracketCell.R6C16
import Hqiv.LieBracketCell.R6C17
import Hqiv.LieBracketCell.R6C18
import Hqiv.LieBracketCell.R6C19
import Hqiv.LieBracketCell.R6C20
import Hqiv.LieBracketCell.R6C21
import Hqiv.LieBracketCell.R6C22
import Hqiv.LieBracketCell.R6C23
import Hqiv.LieBracketCell.R6C24
import Hqiv.LieBracketCell.R6C25
import Hqiv.LieBracketCell.R6C26
import Hqiv.LieBracketCell.R6C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 6 (imports parallel cell modules). -/
theorem lieBracket_in_span_row6 (j : Fin 28) :
    lieBracket (so8Generator ⟨6, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨6, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r6_c0
  · exact lieBracket_in_span_r6_c1
  · exact lieBracket_in_span_r6_c2
  · exact lieBracket_in_span_r6_c3
  · exact lieBracket_in_span_r6_c4
  · exact lieBracket_in_span_r6_c5
  · exact lieBracket_in_span_r6_c6
  · exact lieBracket_in_span_r6_c7
  · exact lieBracket_in_span_r6_c8
  · exact lieBracket_in_span_r6_c9
  · exact lieBracket_in_span_r6_c10
  · exact lieBracket_in_span_r6_c11
  · exact lieBracket_in_span_r6_c12
  · exact lieBracket_in_span_r6_c13
  · exact lieBracket_in_span_r6_c14
  · exact lieBracket_in_span_r6_c15
  · exact lieBracket_in_span_r6_c16
  · exact lieBracket_in_span_r6_c17
  · exact lieBracket_in_span_r6_c18
  · exact lieBracket_in_span_r6_c19
  · exact lieBracket_in_span_r6_c20
  · exact lieBracket_in_span_r6_c21
  · exact lieBracket_in_span_r6_c22
  · exact lieBracket_in_span_r6_c23
  · exact lieBracket_in_span_r6_c24
  · exact lieBracket_in_span_r6_c25
  · exact lieBracket_in_span_r6_c26
  · exact lieBracket_in_span_r6_c27

end Hqiv
