import Hqiv.LieBracketCell.R19C0
import Hqiv.LieBracketCell.R19C1
import Hqiv.LieBracketCell.R19C2
import Hqiv.LieBracketCell.R19C3
import Hqiv.LieBracketCell.R19C4
import Hqiv.LieBracketCell.R19C5
import Hqiv.LieBracketCell.R19C6
import Hqiv.LieBracketCell.R19C7
import Hqiv.LieBracketCell.R19C8
import Hqiv.LieBracketCell.R19C9
import Hqiv.LieBracketCell.R19C10
import Hqiv.LieBracketCell.R19C11
import Hqiv.LieBracketCell.R19C12
import Hqiv.LieBracketCell.R19C13
import Hqiv.LieBracketCell.R19C14
import Hqiv.LieBracketCell.R19C15
import Hqiv.LieBracketCell.R19C16
import Hqiv.LieBracketCell.R19C17
import Hqiv.LieBracketCell.R19C18
import Hqiv.LieBracketCell.R19C19
import Hqiv.LieBracketCell.R19C20
import Hqiv.LieBracketCell.R19C21
import Hqiv.LieBracketCell.R19C22
import Hqiv.LieBracketCell.R19C23
import Hqiv.LieBracketCell.R19C24
import Hqiv.LieBracketCell.R19C25
import Hqiv.LieBracketCell.R19C26
import Hqiv.LieBracketCell.R19C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 19 (imports parallel cell modules). -/
theorem lieBracket_in_span_row19 (j : Fin 28) :
    lieBracket (so8Generator ⟨19, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨19, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r19_c0
  · exact lieBracket_in_span_r19_c1
  · exact lieBracket_in_span_r19_c2
  · exact lieBracket_in_span_r19_c3
  · exact lieBracket_in_span_r19_c4
  · exact lieBracket_in_span_r19_c5
  · exact lieBracket_in_span_r19_c6
  · exact lieBracket_in_span_r19_c7
  · exact lieBracket_in_span_r19_c8
  · exact lieBracket_in_span_r19_c9
  · exact lieBracket_in_span_r19_c10
  · exact lieBracket_in_span_r19_c11
  · exact lieBracket_in_span_r19_c12
  · exact lieBracket_in_span_r19_c13
  · exact lieBracket_in_span_r19_c14
  · exact lieBracket_in_span_r19_c15
  · exact lieBracket_in_span_r19_c16
  · exact lieBracket_in_span_r19_c17
  · exact lieBracket_in_span_r19_c18
  · exact lieBracket_in_span_r19_c19
  · exact lieBracket_in_span_r19_c20
  · exact lieBracket_in_span_r19_c21
  · exact lieBracket_in_span_r19_c22
  · exact lieBracket_in_span_r19_c23
  · exact lieBracket_in_span_r19_c24
  · exact lieBracket_in_span_r19_c25
  · exact lieBracket_in_span_r19_c26
  · exact lieBracket_in_span_r19_c27

end Hqiv
