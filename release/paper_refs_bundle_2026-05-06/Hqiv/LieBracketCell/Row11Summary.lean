import Hqiv.LieBracketCell.R11C0
import Hqiv.LieBracketCell.R11C1
import Hqiv.LieBracketCell.R11C2
import Hqiv.LieBracketCell.R11C3
import Hqiv.LieBracketCell.R11C4
import Hqiv.LieBracketCell.R11C5
import Hqiv.LieBracketCell.R11C6
import Hqiv.LieBracketCell.R11C7
import Hqiv.LieBracketCell.R11C8
import Hqiv.LieBracketCell.R11C9
import Hqiv.LieBracketCell.R11C10
import Hqiv.LieBracketCell.R11C11
import Hqiv.LieBracketCell.R11C12
import Hqiv.LieBracketCell.R11C13
import Hqiv.LieBracketCell.R11C14
import Hqiv.LieBracketCell.R11C15
import Hqiv.LieBracketCell.R11C16
import Hqiv.LieBracketCell.R11C17
import Hqiv.LieBracketCell.R11C18
import Hqiv.LieBracketCell.R11C19
import Hqiv.LieBracketCell.R11C20
import Hqiv.LieBracketCell.R11C21
import Hqiv.LieBracketCell.R11C22
import Hqiv.LieBracketCell.R11C23
import Hqiv.LieBracketCell.R11C24
import Hqiv.LieBracketCell.R11C25
import Hqiv.LieBracketCell.R11C26
import Hqiv.LieBracketCell.R11C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 11 (imports parallel cell modules). -/
theorem lieBracket_in_span_row11 (j : Fin 28) :
    lieBracket (so8Generator ⟨11, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨11, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r11_c0
  · exact lieBracket_in_span_r11_c1
  · exact lieBracket_in_span_r11_c2
  · exact lieBracket_in_span_r11_c3
  · exact lieBracket_in_span_r11_c4
  · exact lieBracket_in_span_r11_c5
  · exact lieBracket_in_span_r11_c6
  · exact lieBracket_in_span_r11_c7
  · exact lieBracket_in_span_r11_c8
  · exact lieBracket_in_span_r11_c9
  · exact lieBracket_in_span_r11_c10
  · exact lieBracket_in_span_r11_c11
  · exact lieBracket_in_span_r11_c12
  · exact lieBracket_in_span_r11_c13
  · exact lieBracket_in_span_r11_c14
  · exact lieBracket_in_span_r11_c15
  · exact lieBracket_in_span_r11_c16
  · exact lieBracket_in_span_r11_c17
  · exact lieBracket_in_span_r11_c18
  · exact lieBracket_in_span_r11_c19
  · exact lieBracket_in_span_r11_c20
  · exact lieBracket_in_span_r11_c21
  · exact lieBracket_in_span_r11_c22
  · exact lieBracket_in_span_r11_c23
  · exact lieBracket_in_span_r11_c24
  · exact lieBracket_in_span_r11_c25
  · exact lieBracket_in_span_r11_c26
  · exact lieBracket_in_span_r11_c27

end Hqiv
