import Hqiv.LieBracketCell.R13C0
import Hqiv.LieBracketCell.R13C1
import Hqiv.LieBracketCell.R13C2
import Hqiv.LieBracketCell.R13C3
import Hqiv.LieBracketCell.R13C4
import Hqiv.LieBracketCell.R13C5
import Hqiv.LieBracketCell.R13C6
import Hqiv.LieBracketCell.R13C7
import Hqiv.LieBracketCell.R13C8
import Hqiv.LieBracketCell.R13C9
import Hqiv.LieBracketCell.R13C10
import Hqiv.LieBracketCell.R13C11
import Hqiv.LieBracketCell.R13C12
import Hqiv.LieBracketCell.R13C13
import Hqiv.LieBracketCell.R13C14
import Hqiv.LieBracketCell.R13C15
import Hqiv.LieBracketCell.R13C16
import Hqiv.LieBracketCell.R13C17
import Hqiv.LieBracketCell.R13C18
import Hqiv.LieBracketCell.R13C19
import Hqiv.LieBracketCell.R13C20
import Hqiv.LieBracketCell.R13C21
import Hqiv.LieBracketCell.R13C22
import Hqiv.LieBracketCell.R13C23
import Hqiv.LieBracketCell.R13C24
import Hqiv.LieBracketCell.R13C25
import Hqiv.LieBracketCell.R13C26
import Hqiv.LieBracketCell.R13C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 13 (imports parallel cell modules). -/
theorem lieBracket_in_span_row13 (j : Fin 28) :
    lieBracket (so8Generator ⟨13, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨13, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r13_c0
  · exact lieBracket_in_span_r13_c1
  · exact lieBracket_in_span_r13_c2
  · exact lieBracket_in_span_r13_c3
  · exact lieBracket_in_span_r13_c4
  · exact lieBracket_in_span_r13_c5
  · exact lieBracket_in_span_r13_c6
  · exact lieBracket_in_span_r13_c7
  · exact lieBracket_in_span_r13_c8
  · exact lieBracket_in_span_r13_c9
  · exact lieBracket_in_span_r13_c10
  · exact lieBracket_in_span_r13_c11
  · exact lieBracket_in_span_r13_c12
  · exact lieBracket_in_span_r13_c13
  · exact lieBracket_in_span_r13_c14
  · exact lieBracket_in_span_r13_c15
  · exact lieBracket_in_span_r13_c16
  · exact lieBracket_in_span_r13_c17
  · exact lieBracket_in_span_r13_c18
  · exact lieBracket_in_span_r13_c19
  · exact lieBracket_in_span_r13_c20
  · exact lieBracket_in_span_r13_c21
  · exact lieBracket_in_span_r13_c22
  · exact lieBracket_in_span_r13_c23
  · exact lieBracket_in_span_r13_c24
  · exact lieBracket_in_span_r13_c25
  · exact lieBracket_in_span_r13_c26
  · exact lieBracket_in_span_r13_c27

end Hqiv
