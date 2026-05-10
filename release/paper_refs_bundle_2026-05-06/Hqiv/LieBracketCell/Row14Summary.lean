import Hqiv.LieBracketCell.R14C0
import Hqiv.LieBracketCell.R14C1
import Hqiv.LieBracketCell.R14C2
import Hqiv.LieBracketCell.R14C3
import Hqiv.LieBracketCell.R14C4
import Hqiv.LieBracketCell.R14C5
import Hqiv.LieBracketCell.R14C6
import Hqiv.LieBracketCell.R14C7
import Hqiv.LieBracketCell.R14C8
import Hqiv.LieBracketCell.R14C9
import Hqiv.LieBracketCell.R14C10
import Hqiv.LieBracketCell.R14C11
import Hqiv.LieBracketCell.R14C12
import Hqiv.LieBracketCell.R14C13
import Hqiv.LieBracketCell.R14C14
import Hqiv.LieBracketCell.R14C15
import Hqiv.LieBracketCell.R14C16
import Hqiv.LieBracketCell.R14C17
import Hqiv.LieBracketCell.R14C18
import Hqiv.LieBracketCell.R14C19
import Hqiv.LieBracketCell.R14C20
import Hqiv.LieBracketCell.R14C21
import Hqiv.LieBracketCell.R14C22
import Hqiv.LieBracketCell.R14C23
import Hqiv.LieBracketCell.R14C24
import Hqiv.LieBracketCell.R14C25
import Hqiv.LieBracketCell.R14C26
import Hqiv.LieBracketCell.R14C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 14 (imports parallel cell modules). -/
theorem lieBracket_in_span_row14 (j : Fin 28) :
    lieBracket (so8Generator ⟨14, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨14, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r14_c0
  · exact lieBracket_in_span_r14_c1
  · exact lieBracket_in_span_r14_c2
  · exact lieBracket_in_span_r14_c3
  · exact lieBracket_in_span_r14_c4
  · exact lieBracket_in_span_r14_c5
  · exact lieBracket_in_span_r14_c6
  · exact lieBracket_in_span_r14_c7
  · exact lieBracket_in_span_r14_c8
  · exact lieBracket_in_span_r14_c9
  · exact lieBracket_in_span_r14_c10
  · exact lieBracket_in_span_r14_c11
  · exact lieBracket_in_span_r14_c12
  · exact lieBracket_in_span_r14_c13
  · exact lieBracket_in_span_r14_c14
  · exact lieBracket_in_span_r14_c15
  · exact lieBracket_in_span_r14_c16
  · exact lieBracket_in_span_r14_c17
  · exact lieBracket_in_span_r14_c18
  · exact lieBracket_in_span_r14_c19
  · exact lieBracket_in_span_r14_c20
  · exact lieBracket_in_span_r14_c21
  · exact lieBracket_in_span_r14_c22
  · exact lieBracket_in_span_r14_c23
  · exact lieBracket_in_span_r14_c24
  · exact lieBracket_in_span_r14_c25
  · exact lieBracket_in_span_r14_c26
  · exact lieBracket_in_span_r14_c27

end Hqiv
