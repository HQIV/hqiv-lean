import Hqiv.LieBracketCell.R25C0
import Hqiv.LieBracketCell.R25C1
import Hqiv.LieBracketCell.R25C2
import Hqiv.LieBracketCell.R25C3
import Hqiv.LieBracketCell.R25C4
import Hqiv.LieBracketCell.R25C5
import Hqiv.LieBracketCell.R25C6
import Hqiv.LieBracketCell.R25C7
import Hqiv.LieBracketCell.R25C8
import Hqiv.LieBracketCell.R25C9
import Hqiv.LieBracketCell.R25C10
import Hqiv.LieBracketCell.R25C11
import Hqiv.LieBracketCell.R25C12
import Hqiv.LieBracketCell.R25C13
import Hqiv.LieBracketCell.R25C14
import Hqiv.LieBracketCell.R25C15
import Hqiv.LieBracketCell.R25C16
import Hqiv.LieBracketCell.R25C17
import Hqiv.LieBracketCell.R25C18
import Hqiv.LieBracketCell.R25C19
import Hqiv.LieBracketCell.R25C20
import Hqiv.LieBracketCell.R25C21
import Hqiv.LieBracketCell.R25C22
import Hqiv.LieBracketCell.R25C23
import Hqiv.LieBracketCell.R25C24
import Hqiv.LieBracketCell.R25C25
import Hqiv.LieBracketCell.R25C26
import Hqiv.LieBracketCell.R25C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 25 (imports parallel cell modules). -/
theorem lieBracket_in_span_row25 (j : Fin 28) :
    lieBracket (so8Generator ⟨25, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨25, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r25_c0
  · exact lieBracket_in_span_r25_c1
  · exact lieBracket_in_span_r25_c2
  · exact lieBracket_in_span_r25_c3
  · exact lieBracket_in_span_r25_c4
  · exact lieBracket_in_span_r25_c5
  · exact lieBracket_in_span_r25_c6
  · exact lieBracket_in_span_r25_c7
  · exact lieBracket_in_span_r25_c8
  · exact lieBracket_in_span_r25_c9
  · exact lieBracket_in_span_r25_c10
  · exact lieBracket_in_span_r25_c11
  · exact lieBracket_in_span_r25_c12
  · exact lieBracket_in_span_r25_c13
  · exact lieBracket_in_span_r25_c14
  · exact lieBracket_in_span_r25_c15
  · exact lieBracket_in_span_r25_c16
  · exact lieBracket_in_span_r25_c17
  · exact lieBracket_in_span_r25_c18
  · exact lieBracket_in_span_r25_c19
  · exact lieBracket_in_span_r25_c20
  · exact lieBracket_in_span_r25_c21
  · exact lieBracket_in_span_r25_c22
  · exact lieBracket_in_span_r25_c23
  · exact lieBracket_in_span_r25_c24
  · exact lieBracket_in_span_r25_c25
  · exact lieBracket_in_span_r25_c26
  · exact lieBracket_in_span_r25_c27

end Hqiv
