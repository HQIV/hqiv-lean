import Hqiv.LieBracketCell.R8C0
import Hqiv.LieBracketCell.R8C1
import Hqiv.LieBracketCell.R8C2
import Hqiv.LieBracketCell.R8C3
import Hqiv.LieBracketCell.R8C4
import Hqiv.LieBracketCell.R8C5
import Hqiv.LieBracketCell.R8C6
import Hqiv.LieBracketCell.R8C7
import Hqiv.LieBracketCell.R8C8
import Hqiv.LieBracketCell.R8C9
import Hqiv.LieBracketCell.R8C10
import Hqiv.LieBracketCell.R8C11
import Hqiv.LieBracketCell.R8C12
import Hqiv.LieBracketCell.R8C13
import Hqiv.LieBracketCell.R8C14
import Hqiv.LieBracketCell.R8C15
import Hqiv.LieBracketCell.R8C16
import Hqiv.LieBracketCell.R8C17
import Hqiv.LieBracketCell.R8C18
import Hqiv.LieBracketCell.R8C19
import Hqiv.LieBracketCell.R8C20
import Hqiv.LieBracketCell.R8C21
import Hqiv.LieBracketCell.R8C22
import Hqiv.LieBracketCell.R8C23
import Hqiv.LieBracketCell.R8C24
import Hqiv.LieBracketCell.R8C25
import Hqiv.LieBracketCell.R8C26
import Hqiv.LieBracketCell.R8C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 8 (imports parallel cell modules). -/
theorem lieBracket_in_span_row8 (j : Fin 28) :
    lieBracket (so8Generator ⟨8, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨8, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r8_c0
  · exact lieBracket_in_span_r8_c1
  · exact lieBracket_in_span_r8_c2
  · exact lieBracket_in_span_r8_c3
  · exact lieBracket_in_span_r8_c4
  · exact lieBracket_in_span_r8_c5
  · exact lieBracket_in_span_r8_c6
  · exact lieBracket_in_span_r8_c7
  · exact lieBracket_in_span_r8_c8
  · exact lieBracket_in_span_r8_c9
  · exact lieBracket_in_span_r8_c10
  · exact lieBracket_in_span_r8_c11
  · exact lieBracket_in_span_r8_c12
  · exact lieBracket_in_span_r8_c13
  · exact lieBracket_in_span_r8_c14
  · exact lieBracket_in_span_r8_c15
  · exact lieBracket_in_span_r8_c16
  · exact lieBracket_in_span_r8_c17
  · exact lieBracket_in_span_r8_c18
  · exact lieBracket_in_span_r8_c19
  · exact lieBracket_in_span_r8_c20
  · exact lieBracket_in_span_r8_c21
  · exact lieBracket_in_span_r8_c22
  · exact lieBracket_in_span_r8_c23
  · exact lieBracket_in_span_r8_c24
  · exact lieBracket_in_span_r8_c25
  · exact lieBracket_in_span_r8_c26
  · exact lieBracket_in_span_r8_c27

end Hqiv
