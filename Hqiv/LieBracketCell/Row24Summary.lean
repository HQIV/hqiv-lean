import Hqiv.LieBracketCell.R24C0
import Hqiv.LieBracketCell.R24C1
import Hqiv.LieBracketCell.R24C2
import Hqiv.LieBracketCell.R24C3
import Hqiv.LieBracketCell.R24C4
import Hqiv.LieBracketCell.R24C5
import Hqiv.LieBracketCell.R24C6
import Hqiv.LieBracketCell.R24C7
import Hqiv.LieBracketCell.R24C8
import Hqiv.LieBracketCell.R24C9
import Hqiv.LieBracketCell.R24C10
import Hqiv.LieBracketCell.R24C11
import Hqiv.LieBracketCell.R24C12
import Hqiv.LieBracketCell.R24C13
import Hqiv.LieBracketCell.R24C14
import Hqiv.LieBracketCell.R24C15
import Hqiv.LieBracketCell.R24C16
import Hqiv.LieBracketCell.R24C17
import Hqiv.LieBracketCell.R24C18
import Hqiv.LieBracketCell.R24C19
import Hqiv.LieBracketCell.R24C20
import Hqiv.LieBracketCell.R24C21
import Hqiv.LieBracketCell.R24C22
import Hqiv.LieBracketCell.R24C23
import Hqiv.LieBracketCell.R24C24
import Hqiv.LieBracketCell.R24C25
import Hqiv.LieBracketCell.R24C26
import Hqiv.LieBracketCell.R24C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 24 (imports parallel cell modules). -/
theorem lieBracket_in_span_row24 (j : Fin 28) :
    lieBracket (so8Generator ⟨24, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨24, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r24_c0
  · exact lieBracket_in_span_r24_c1
  · exact lieBracket_in_span_r24_c2
  · exact lieBracket_in_span_r24_c3
  · exact lieBracket_in_span_r24_c4
  · exact lieBracket_in_span_r24_c5
  · exact lieBracket_in_span_r24_c6
  · exact lieBracket_in_span_r24_c7
  · exact lieBracket_in_span_r24_c8
  · exact lieBracket_in_span_r24_c9
  · exact lieBracket_in_span_r24_c10
  · exact lieBracket_in_span_r24_c11
  · exact lieBracket_in_span_r24_c12
  · exact lieBracket_in_span_r24_c13
  · exact lieBracket_in_span_r24_c14
  · exact lieBracket_in_span_r24_c15
  · exact lieBracket_in_span_r24_c16
  · exact lieBracket_in_span_r24_c17
  · exact lieBracket_in_span_r24_c18
  · exact lieBracket_in_span_r24_c19
  · exact lieBracket_in_span_r24_c20
  · exact lieBracket_in_span_r24_c21
  · exact lieBracket_in_span_r24_c22
  · exact lieBracket_in_span_r24_c23
  · exact lieBracket_in_span_r24_c24
  · exact lieBracket_in_span_r24_c25
  · exact lieBracket_in_span_r24_c26
  · exact lieBracket_in_span_r24_c27

end Hqiv
