import Hqiv.LieBracketCell.R18C0
import Hqiv.LieBracketCell.R18C1
import Hqiv.LieBracketCell.R18C2
import Hqiv.LieBracketCell.R18C3
import Hqiv.LieBracketCell.R18C4
import Hqiv.LieBracketCell.R18C5
import Hqiv.LieBracketCell.R18C6
import Hqiv.LieBracketCell.R18C7
import Hqiv.LieBracketCell.R18C8
import Hqiv.LieBracketCell.R18C9
import Hqiv.LieBracketCell.R18C10
import Hqiv.LieBracketCell.R18C11
import Hqiv.LieBracketCell.R18C12
import Hqiv.LieBracketCell.R18C13
import Hqiv.LieBracketCell.R18C14
import Hqiv.LieBracketCell.R18C15
import Hqiv.LieBracketCell.R18C16
import Hqiv.LieBracketCell.R18C17
import Hqiv.LieBracketCell.R18C18
import Hqiv.LieBracketCell.R18C19
import Hqiv.LieBracketCell.R18C20
import Hqiv.LieBracketCell.R18C21
import Hqiv.LieBracketCell.R18C22
import Hqiv.LieBracketCell.R18C23
import Hqiv.LieBracketCell.R18C24
import Hqiv.LieBracketCell.R18C25
import Hqiv.LieBracketCell.R18C26
import Hqiv.LieBracketCell.R18C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 18 (imports parallel cell modules). -/
theorem lieBracket_in_span_row18 (j : Fin 28) :
    lieBracket (so8Generator ⟨18, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨18, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r18_c0
  · exact lieBracket_in_span_r18_c1
  · exact lieBracket_in_span_r18_c2
  · exact lieBracket_in_span_r18_c3
  · exact lieBracket_in_span_r18_c4
  · exact lieBracket_in_span_r18_c5
  · exact lieBracket_in_span_r18_c6
  · exact lieBracket_in_span_r18_c7
  · exact lieBracket_in_span_r18_c8
  · exact lieBracket_in_span_r18_c9
  · exact lieBracket_in_span_r18_c10
  · exact lieBracket_in_span_r18_c11
  · exact lieBracket_in_span_r18_c12
  · exact lieBracket_in_span_r18_c13
  · exact lieBracket_in_span_r18_c14
  · exact lieBracket_in_span_r18_c15
  · exact lieBracket_in_span_r18_c16
  · exact lieBracket_in_span_r18_c17
  · exact lieBracket_in_span_r18_c18
  · exact lieBracket_in_span_r18_c19
  · exact lieBracket_in_span_r18_c20
  · exact lieBracket_in_span_r18_c21
  · exact lieBracket_in_span_r18_c22
  · exact lieBracket_in_span_r18_c23
  · exact lieBracket_in_span_r18_c24
  · exact lieBracket_in_span_r18_c25
  · exact lieBracket_in_span_r18_c26
  · exact lieBracket_in_span_r18_c27

end Hqiv
