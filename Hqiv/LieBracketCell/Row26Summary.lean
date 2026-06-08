import Hqiv.LieBracketCell.R26C0
import Hqiv.LieBracketCell.R26C1
import Hqiv.LieBracketCell.R26C2
import Hqiv.LieBracketCell.R26C3
import Hqiv.LieBracketCell.R26C4
import Hqiv.LieBracketCell.R26C5
import Hqiv.LieBracketCell.R26C6
import Hqiv.LieBracketCell.R26C7
import Hqiv.LieBracketCell.R26C8
import Hqiv.LieBracketCell.R26C9
import Hqiv.LieBracketCell.R26C10
import Hqiv.LieBracketCell.R26C11
import Hqiv.LieBracketCell.R26C12
import Hqiv.LieBracketCell.R26C13
import Hqiv.LieBracketCell.R26C14
import Hqiv.LieBracketCell.R26C15
import Hqiv.LieBracketCell.R26C16
import Hqiv.LieBracketCell.R26C17
import Hqiv.LieBracketCell.R26C18
import Hqiv.LieBracketCell.R26C19
import Hqiv.LieBracketCell.R26C20
import Hqiv.LieBracketCell.R26C21
import Hqiv.LieBracketCell.R26C22
import Hqiv.LieBracketCell.R26C23
import Hqiv.LieBracketCell.R26C24
import Hqiv.LieBracketCell.R26C25
import Hqiv.LieBracketCell.R26C26
import Hqiv.LieBracketCell.R26C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 26 (imports parallel cell modules). -/
theorem lieBracket_in_span_row26 (j : Fin 28) :
    lieBracket (so8Generator ⟨26, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨26, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r26_c0
  · exact lieBracket_in_span_r26_c1
  · exact lieBracket_in_span_r26_c2
  · exact lieBracket_in_span_r26_c3
  · exact lieBracket_in_span_r26_c4
  · exact lieBracket_in_span_r26_c5
  · exact lieBracket_in_span_r26_c6
  · exact lieBracket_in_span_r26_c7
  · exact lieBracket_in_span_r26_c8
  · exact lieBracket_in_span_r26_c9
  · exact lieBracket_in_span_r26_c10
  · exact lieBracket_in_span_r26_c11
  · exact lieBracket_in_span_r26_c12
  · exact lieBracket_in_span_r26_c13
  · exact lieBracket_in_span_r26_c14
  · exact lieBracket_in_span_r26_c15
  · exact lieBracket_in_span_r26_c16
  · exact lieBracket_in_span_r26_c17
  · exact lieBracket_in_span_r26_c18
  · exact lieBracket_in_span_r26_c19
  · exact lieBracket_in_span_r26_c20
  · exact lieBracket_in_span_r26_c21
  · exact lieBracket_in_span_r26_c22
  · exact lieBracket_in_span_r26_c23
  · exact lieBracket_in_span_r26_c24
  · exact lieBracket_in_span_r26_c25
  · exact lieBracket_in_span_r26_c26
  · exact lieBracket_in_span_r26_c27

end Hqiv
