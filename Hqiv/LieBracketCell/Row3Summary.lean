import Hqiv.LieBracketCell.R3C0
import Hqiv.LieBracketCell.R3C1
import Hqiv.LieBracketCell.R3C2
import Hqiv.LieBracketCell.R3C3
import Hqiv.LieBracketCell.R3C4
import Hqiv.LieBracketCell.R3C5
import Hqiv.LieBracketCell.R3C6
import Hqiv.LieBracketCell.R3C7
import Hqiv.LieBracketCell.R3C8
import Hqiv.LieBracketCell.R3C9
import Hqiv.LieBracketCell.R3C10
import Hqiv.LieBracketCell.R3C11
import Hqiv.LieBracketCell.R3C12
import Hqiv.LieBracketCell.R3C13
import Hqiv.LieBracketCell.R3C14
import Hqiv.LieBracketCell.R3C15
import Hqiv.LieBracketCell.R3C16
import Hqiv.LieBracketCell.R3C17
import Hqiv.LieBracketCell.R3C18
import Hqiv.LieBracketCell.R3C19
import Hqiv.LieBracketCell.R3C20
import Hqiv.LieBracketCell.R3C21
import Hqiv.LieBracketCell.R3C22
import Hqiv.LieBracketCell.R3C23
import Hqiv.LieBracketCell.R3C24
import Hqiv.LieBracketCell.R3C25
import Hqiv.LieBracketCell.R3C26
import Hqiv.LieBracketCell.R3C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 3 (imports parallel cell modules). -/
theorem lieBracket_in_span_row3 (j : Fin 28) :
    lieBracket (so8Generator ⟨3, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨3, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r3_c0
  · exact lieBracket_in_span_r3_c1
  · exact lieBracket_in_span_r3_c2
  · exact lieBracket_in_span_r3_c3
  · exact lieBracket_in_span_r3_c4
  · exact lieBracket_in_span_r3_c5
  · exact lieBracket_in_span_r3_c6
  · exact lieBracket_in_span_r3_c7
  · exact lieBracket_in_span_r3_c8
  · exact lieBracket_in_span_r3_c9
  · exact lieBracket_in_span_r3_c10
  · exact lieBracket_in_span_r3_c11
  · exact lieBracket_in_span_r3_c12
  · exact lieBracket_in_span_r3_c13
  · exact lieBracket_in_span_r3_c14
  · exact lieBracket_in_span_r3_c15
  · exact lieBracket_in_span_r3_c16
  · exact lieBracket_in_span_r3_c17
  · exact lieBracket_in_span_r3_c18
  · exact lieBracket_in_span_r3_c19
  · exact lieBracket_in_span_r3_c20
  · exact lieBracket_in_span_r3_c21
  · exact lieBracket_in_span_r3_c22
  · exact lieBracket_in_span_r3_c23
  · exact lieBracket_in_span_r3_c24
  · exact lieBracket_in_span_r3_c25
  · exact lieBracket_in_span_r3_c26
  · exact lieBracket_in_span_r3_c27

end Hqiv
