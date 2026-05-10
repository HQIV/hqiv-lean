import Hqiv.LieBracketCell.R22C0
import Hqiv.LieBracketCell.R22C1
import Hqiv.LieBracketCell.R22C2
import Hqiv.LieBracketCell.R22C3
import Hqiv.LieBracketCell.R22C4
import Hqiv.LieBracketCell.R22C5
import Hqiv.LieBracketCell.R22C6
import Hqiv.LieBracketCell.R22C7
import Hqiv.LieBracketCell.R22C8
import Hqiv.LieBracketCell.R22C9
import Hqiv.LieBracketCell.R22C10
import Hqiv.LieBracketCell.R22C11
import Hqiv.LieBracketCell.R22C12
import Hqiv.LieBracketCell.R22C13
import Hqiv.LieBracketCell.R22C14
import Hqiv.LieBracketCell.R22C15
import Hqiv.LieBracketCell.R22C16
import Hqiv.LieBracketCell.R22C17
import Hqiv.LieBracketCell.R22C18
import Hqiv.LieBracketCell.R22C19
import Hqiv.LieBracketCell.R22C20
import Hqiv.LieBracketCell.R22C21
import Hqiv.LieBracketCell.R22C22
import Hqiv.LieBracketCell.R22C23
import Hqiv.LieBracketCell.R22C24
import Hqiv.LieBracketCell.R22C25
import Hqiv.LieBracketCell.R22C26
import Hqiv.LieBracketCell.R22C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 22 (imports parallel cell modules). -/
theorem lieBracket_in_span_row22 (j : Fin 28) :
    lieBracket (so8Generator ⟨22, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨22, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r22_c0
  · exact lieBracket_in_span_r22_c1
  · exact lieBracket_in_span_r22_c2
  · exact lieBracket_in_span_r22_c3
  · exact lieBracket_in_span_r22_c4
  · exact lieBracket_in_span_r22_c5
  · exact lieBracket_in_span_r22_c6
  · exact lieBracket_in_span_r22_c7
  · exact lieBracket_in_span_r22_c8
  · exact lieBracket_in_span_r22_c9
  · exact lieBracket_in_span_r22_c10
  · exact lieBracket_in_span_r22_c11
  · exact lieBracket_in_span_r22_c12
  · exact lieBracket_in_span_r22_c13
  · exact lieBracket_in_span_r22_c14
  · exact lieBracket_in_span_r22_c15
  · exact lieBracket_in_span_r22_c16
  · exact lieBracket_in_span_r22_c17
  · exact lieBracket_in_span_r22_c18
  · exact lieBracket_in_span_r22_c19
  · exact lieBracket_in_span_r22_c20
  · exact lieBracket_in_span_r22_c21
  · exact lieBracket_in_span_r22_c22
  · exact lieBracket_in_span_r22_c23
  · exact lieBracket_in_span_r22_c24
  · exact lieBracket_in_span_r22_c25
  · exact lieBracket_in_span_r22_c26
  · exact lieBracket_in_span_r22_c27

end Hqiv
