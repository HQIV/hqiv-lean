import Hqiv.LieBracketCell.R16C0
import Hqiv.LieBracketCell.R16C1
import Hqiv.LieBracketCell.R16C2
import Hqiv.LieBracketCell.R16C3
import Hqiv.LieBracketCell.R16C4
import Hqiv.LieBracketCell.R16C5
import Hqiv.LieBracketCell.R16C6
import Hqiv.LieBracketCell.R16C7
import Hqiv.LieBracketCell.R16C8
import Hqiv.LieBracketCell.R16C9
import Hqiv.LieBracketCell.R16C10
import Hqiv.LieBracketCell.R16C11
import Hqiv.LieBracketCell.R16C12
import Hqiv.LieBracketCell.R16C13
import Hqiv.LieBracketCell.R16C14
import Hqiv.LieBracketCell.R16C15
import Hqiv.LieBracketCell.R16C16
import Hqiv.LieBracketCell.R16C17
import Hqiv.LieBracketCell.R16C18
import Hqiv.LieBracketCell.R16C19
import Hqiv.LieBracketCell.R16C20
import Hqiv.LieBracketCell.R16C21
import Hqiv.LieBracketCell.R16C22
import Hqiv.LieBracketCell.R16C23
import Hqiv.LieBracketCell.R16C24
import Hqiv.LieBracketCell.R16C25
import Hqiv.LieBracketCell.R16C26
import Hqiv.LieBracketCell.R16C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 16 (imports parallel cell modules). -/
theorem lieBracket_in_span_row16 (j : Fin 28) :
    lieBracket (so8Generator ⟨16, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨16, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r16_c0
  · exact lieBracket_in_span_r16_c1
  · exact lieBracket_in_span_r16_c2
  · exact lieBracket_in_span_r16_c3
  · exact lieBracket_in_span_r16_c4
  · exact lieBracket_in_span_r16_c5
  · exact lieBracket_in_span_r16_c6
  · exact lieBracket_in_span_r16_c7
  · exact lieBracket_in_span_r16_c8
  · exact lieBracket_in_span_r16_c9
  · exact lieBracket_in_span_r16_c10
  · exact lieBracket_in_span_r16_c11
  · exact lieBracket_in_span_r16_c12
  · exact lieBracket_in_span_r16_c13
  · exact lieBracket_in_span_r16_c14
  · exact lieBracket_in_span_r16_c15
  · exact lieBracket_in_span_r16_c16
  · exact lieBracket_in_span_r16_c17
  · exact lieBracket_in_span_r16_c18
  · exact lieBracket_in_span_r16_c19
  · exact lieBracket_in_span_r16_c20
  · exact lieBracket_in_span_r16_c21
  · exact lieBracket_in_span_r16_c22
  · exact lieBracket_in_span_r16_c23
  · exact lieBracket_in_span_r16_c24
  · exact lieBracket_in_span_r16_c25
  · exact lieBracket_in_span_r16_c26
  · exact lieBracket_in_span_r16_c27

end Hqiv
