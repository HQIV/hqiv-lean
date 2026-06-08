import Hqiv.LieBracketCell.R4C0
import Hqiv.LieBracketCell.R4C1
import Hqiv.LieBracketCell.R4C2
import Hqiv.LieBracketCell.R4C3
import Hqiv.LieBracketCell.R4C4
import Hqiv.LieBracketCell.R4C5
import Hqiv.LieBracketCell.R4C6
import Hqiv.LieBracketCell.R4C7
import Hqiv.LieBracketCell.R4C8
import Hqiv.LieBracketCell.R4C9
import Hqiv.LieBracketCell.R4C10
import Hqiv.LieBracketCell.R4C11
import Hqiv.LieBracketCell.R4C12
import Hqiv.LieBracketCell.R4C13
import Hqiv.LieBracketCell.R4C14
import Hqiv.LieBracketCell.R4C15
import Hqiv.LieBracketCell.R4C16
import Hqiv.LieBracketCell.R4C17
import Hqiv.LieBracketCell.R4C18
import Hqiv.LieBracketCell.R4C19
import Hqiv.LieBracketCell.R4C20
import Hqiv.LieBracketCell.R4C21
import Hqiv.LieBracketCell.R4C22
import Hqiv.LieBracketCell.R4C23
import Hqiv.LieBracketCell.R4C24
import Hqiv.LieBracketCell.R4C25
import Hqiv.LieBracketCell.R4C26
import Hqiv.LieBracketCell.R4C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 4 (imports parallel cell modules). -/
theorem lieBracket_in_span_row4 (j : Fin 28) :
    lieBracket (so8Generator ⟨4, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨4, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r4_c0
  · exact lieBracket_in_span_r4_c1
  · exact lieBracket_in_span_r4_c2
  · exact lieBracket_in_span_r4_c3
  · exact lieBracket_in_span_r4_c4
  · exact lieBracket_in_span_r4_c5
  · exact lieBracket_in_span_r4_c6
  · exact lieBracket_in_span_r4_c7
  · exact lieBracket_in_span_r4_c8
  · exact lieBracket_in_span_r4_c9
  · exact lieBracket_in_span_r4_c10
  · exact lieBracket_in_span_r4_c11
  · exact lieBracket_in_span_r4_c12
  · exact lieBracket_in_span_r4_c13
  · exact lieBracket_in_span_r4_c14
  · exact lieBracket_in_span_r4_c15
  · exact lieBracket_in_span_r4_c16
  · exact lieBracket_in_span_r4_c17
  · exact lieBracket_in_span_r4_c18
  · exact lieBracket_in_span_r4_c19
  · exact lieBracket_in_span_r4_c20
  · exact lieBracket_in_span_r4_c21
  · exact lieBracket_in_span_r4_c22
  · exact lieBracket_in_span_r4_c23
  · exact lieBracket_in_span_r4_c24
  · exact lieBracket_in_span_r4_c25
  · exact lieBracket_in_span_r4_c26
  · exact lieBracket_in_span_r4_c27

end Hqiv
