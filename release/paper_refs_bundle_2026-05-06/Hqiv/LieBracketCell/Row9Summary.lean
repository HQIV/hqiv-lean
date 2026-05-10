import Hqiv.LieBracketCell.R9C0
import Hqiv.LieBracketCell.R9C1
import Hqiv.LieBracketCell.R9C2
import Hqiv.LieBracketCell.R9C3
import Hqiv.LieBracketCell.R9C4
import Hqiv.LieBracketCell.R9C5
import Hqiv.LieBracketCell.R9C6
import Hqiv.LieBracketCell.R9C7
import Hqiv.LieBracketCell.R9C8
import Hqiv.LieBracketCell.R9C9
import Hqiv.LieBracketCell.R9C10
import Hqiv.LieBracketCell.R9C11
import Hqiv.LieBracketCell.R9C12
import Hqiv.LieBracketCell.R9C13
import Hqiv.LieBracketCell.R9C14
import Hqiv.LieBracketCell.R9C15
import Hqiv.LieBracketCell.R9C16
import Hqiv.LieBracketCell.R9C17
import Hqiv.LieBracketCell.R9C18
import Hqiv.LieBracketCell.R9C19
import Hqiv.LieBracketCell.R9C20
import Hqiv.LieBracketCell.R9C21
import Hqiv.LieBracketCell.R9C22
import Hqiv.LieBracketCell.R9C23
import Hqiv.LieBracketCell.R9C24
import Hqiv.LieBracketCell.R9C25
import Hqiv.LieBracketCell.R9C26
import Hqiv.LieBracketCell.R9C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 9 (imports parallel cell modules). -/
theorem lieBracket_in_span_row9 (j : Fin 28) :
    lieBracket (so8Generator ⟨9, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨9, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r9_c0
  · exact lieBracket_in_span_r9_c1
  · exact lieBracket_in_span_r9_c2
  · exact lieBracket_in_span_r9_c3
  · exact lieBracket_in_span_r9_c4
  · exact lieBracket_in_span_r9_c5
  · exact lieBracket_in_span_r9_c6
  · exact lieBracket_in_span_r9_c7
  · exact lieBracket_in_span_r9_c8
  · exact lieBracket_in_span_r9_c9
  · exact lieBracket_in_span_r9_c10
  · exact lieBracket_in_span_r9_c11
  · exact lieBracket_in_span_r9_c12
  · exact lieBracket_in_span_r9_c13
  · exact lieBracket_in_span_r9_c14
  · exact lieBracket_in_span_r9_c15
  · exact lieBracket_in_span_r9_c16
  · exact lieBracket_in_span_r9_c17
  · exact lieBracket_in_span_r9_c18
  · exact lieBracket_in_span_r9_c19
  · exact lieBracket_in_span_r9_c20
  · exact lieBracket_in_span_r9_c21
  · exact lieBracket_in_span_r9_c22
  · exact lieBracket_in_span_r9_c23
  · exact lieBracket_in_span_r9_c24
  · exact lieBracket_in_span_r9_c25
  · exact lieBracket_in_span_r9_c26
  · exact lieBracket_in_span_r9_c27

end Hqiv
