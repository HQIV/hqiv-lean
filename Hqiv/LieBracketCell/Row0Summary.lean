import Hqiv.LieBracketCell.R0C0
import Hqiv.LieBracketCell.R0C1
import Hqiv.LieBracketCell.R0C2
import Hqiv.LieBracketCell.R0C3
import Hqiv.LieBracketCell.R0C4
import Hqiv.LieBracketCell.R0C5
import Hqiv.LieBracketCell.R0C6
import Hqiv.LieBracketCell.R0C7
import Hqiv.LieBracketCell.R0C8
import Hqiv.LieBracketCell.R0C9
import Hqiv.LieBracketCell.R0C10
import Hqiv.LieBracketCell.R0C11
import Hqiv.LieBracketCell.R0C12
import Hqiv.LieBracketCell.R0C13
import Hqiv.LieBracketCell.R0C14
import Hqiv.LieBracketCell.R0C15
import Hqiv.LieBracketCell.R0C16
import Hqiv.LieBracketCell.R0C17
import Hqiv.LieBracketCell.R0C18
import Hqiv.LieBracketCell.R0C19
import Hqiv.LieBracketCell.R0C20
import Hqiv.LieBracketCell.R0C21
import Hqiv.LieBracketCell.R0C22
import Hqiv.LieBracketCell.R0C23
import Hqiv.LieBracketCell.R0C24
import Hqiv.LieBracketCell.R0C25
import Hqiv.LieBracketCell.R0C26
import Hqiv.LieBracketCell.R0C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 0 (imports parallel cell modules). -/
theorem lieBracket_in_span_row0 (j : Fin 28) :
    lieBracket (so8Generator ⟨0, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨0, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r0_c0
  · exact lieBracket_in_span_r0_c1
  · exact lieBracket_in_span_r0_c2
  · exact lieBracket_in_span_r0_c3
  · exact lieBracket_in_span_r0_c4
  · exact lieBracket_in_span_r0_c5
  · exact lieBracket_in_span_r0_c6
  · exact lieBracket_in_span_r0_c7
  · exact lieBracket_in_span_r0_c8
  · exact lieBracket_in_span_r0_c9
  · exact lieBracket_in_span_r0_c10
  · exact lieBracket_in_span_r0_c11
  · exact lieBracket_in_span_r0_c12
  · exact lieBracket_in_span_r0_c13
  · exact lieBracket_in_span_r0_c14
  · exact lieBracket_in_span_r0_c15
  · exact lieBracket_in_span_r0_c16
  · exact lieBracket_in_span_r0_c17
  · exact lieBracket_in_span_r0_c18
  · exact lieBracket_in_span_r0_c19
  · exact lieBracket_in_span_r0_c20
  · exact lieBracket_in_span_r0_c21
  · exact lieBracket_in_span_r0_c22
  · exact lieBracket_in_span_r0_c23
  · exact lieBracket_in_span_r0_c24
  · exact lieBracket_in_span_r0_c25
  · exact lieBracket_in_span_r0_c26
  · exact lieBracket_in_span_r0_c27

end Hqiv
