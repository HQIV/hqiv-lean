import Hqiv.LieBracketCell.R1C0
import Hqiv.LieBracketCell.R1C1
import Hqiv.LieBracketCell.R1C2
import Hqiv.LieBracketCell.R1C3
import Hqiv.LieBracketCell.R1C4
import Hqiv.LieBracketCell.R1C5
import Hqiv.LieBracketCell.R1C6
import Hqiv.LieBracketCell.R1C7
import Hqiv.LieBracketCell.R1C8
import Hqiv.LieBracketCell.R1C9
import Hqiv.LieBracketCell.R1C10
import Hqiv.LieBracketCell.R1C11
import Hqiv.LieBracketCell.R1C12
import Hqiv.LieBracketCell.R1C13
import Hqiv.LieBracketCell.R1C14
import Hqiv.LieBracketCell.R1C15
import Hqiv.LieBracketCell.R1C16
import Hqiv.LieBracketCell.R1C17
import Hqiv.LieBracketCell.R1C18
import Hqiv.LieBracketCell.R1C19
import Hqiv.LieBracketCell.R1C20
import Hqiv.LieBracketCell.R1C21
import Hqiv.LieBracketCell.R1C22
import Hqiv.LieBracketCell.R1C23
import Hqiv.LieBracketCell.R1C24
import Hqiv.LieBracketCell.R1C25
import Hqiv.LieBracketCell.R1C26
import Hqiv.LieBracketCell.R1C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 1 (imports parallel cell modules). -/
theorem lieBracket_in_span_row1 (j : Fin 28) :
    lieBracket (so8Generator ⟨1, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨1, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r1_c0
  · exact lieBracket_in_span_r1_c1
  · exact lieBracket_in_span_r1_c2
  · exact lieBracket_in_span_r1_c3
  · exact lieBracket_in_span_r1_c4
  · exact lieBracket_in_span_r1_c5
  · exact lieBracket_in_span_r1_c6
  · exact lieBracket_in_span_r1_c7
  · exact lieBracket_in_span_r1_c8
  · exact lieBracket_in_span_r1_c9
  · exact lieBracket_in_span_r1_c10
  · exact lieBracket_in_span_r1_c11
  · exact lieBracket_in_span_r1_c12
  · exact lieBracket_in_span_r1_c13
  · exact lieBracket_in_span_r1_c14
  · exact lieBracket_in_span_r1_c15
  · exact lieBracket_in_span_r1_c16
  · exact lieBracket_in_span_r1_c17
  · exact lieBracket_in_span_r1_c18
  · exact lieBracket_in_span_r1_c19
  · exact lieBracket_in_span_r1_c20
  · exact lieBracket_in_span_r1_c21
  · exact lieBracket_in_span_r1_c22
  · exact lieBracket_in_span_r1_c23
  · exact lieBracket_in_span_r1_c24
  · exact lieBracket_in_span_r1_c25
  · exact lieBracket_in_span_r1_c26
  · exact lieBracket_in_span_r1_c27

end Hqiv
