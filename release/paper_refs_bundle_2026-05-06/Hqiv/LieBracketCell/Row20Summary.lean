import Hqiv.LieBracketCell.R20C0
import Hqiv.LieBracketCell.R20C1
import Hqiv.LieBracketCell.R20C2
import Hqiv.LieBracketCell.R20C3
import Hqiv.LieBracketCell.R20C4
import Hqiv.LieBracketCell.R20C5
import Hqiv.LieBracketCell.R20C6
import Hqiv.LieBracketCell.R20C7
import Hqiv.LieBracketCell.R20C8
import Hqiv.LieBracketCell.R20C9
import Hqiv.LieBracketCell.R20C10
import Hqiv.LieBracketCell.R20C11
import Hqiv.LieBracketCell.R20C12
import Hqiv.LieBracketCell.R20C13
import Hqiv.LieBracketCell.R20C14
import Hqiv.LieBracketCell.R20C15
import Hqiv.LieBracketCell.R20C16
import Hqiv.LieBracketCell.R20C17
import Hqiv.LieBracketCell.R20C18
import Hqiv.LieBracketCell.R20C19
import Hqiv.LieBracketCell.R20C20
import Hqiv.LieBracketCell.R20C21
import Hqiv.LieBracketCell.R20C22
import Hqiv.LieBracketCell.R20C23
import Hqiv.LieBracketCell.R20C24
import Hqiv.LieBracketCell.R20C25
import Hqiv.LieBracketCell.R20C26
import Hqiv.LieBracketCell.R20C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 20 (imports parallel cell modules). -/
theorem lieBracket_in_span_row20 (j : Fin 28) :
    lieBracket (so8Generator ⟨20, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨20, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r20_c0
  · exact lieBracket_in_span_r20_c1
  · exact lieBracket_in_span_r20_c2
  · exact lieBracket_in_span_r20_c3
  · exact lieBracket_in_span_r20_c4
  · exact lieBracket_in_span_r20_c5
  · exact lieBracket_in_span_r20_c6
  · exact lieBracket_in_span_r20_c7
  · exact lieBracket_in_span_r20_c8
  · exact lieBracket_in_span_r20_c9
  · exact lieBracket_in_span_r20_c10
  · exact lieBracket_in_span_r20_c11
  · exact lieBracket_in_span_r20_c12
  · exact lieBracket_in_span_r20_c13
  · exact lieBracket_in_span_r20_c14
  · exact lieBracket_in_span_r20_c15
  · exact lieBracket_in_span_r20_c16
  · exact lieBracket_in_span_r20_c17
  · exact lieBracket_in_span_r20_c18
  · exact lieBracket_in_span_r20_c19
  · exact lieBracket_in_span_r20_c20
  · exact lieBracket_in_span_r20_c21
  · exact lieBracket_in_span_r20_c22
  · exact lieBracket_in_span_r20_c23
  · exact lieBracket_in_span_r20_c24
  · exact lieBracket_in_span_r20_c25
  · exact lieBracket_in_span_r20_c26
  · exact lieBracket_in_span_r20_c27

end Hqiv
