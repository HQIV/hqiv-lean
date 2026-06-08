import Hqiv.LieBracketCell.R10C0
import Hqiv.LieBracketCell.R10C1
import Hqiv.LieBracketCell.R10C2
import Hqiv.LieBracketCell.R10C3
import Hqiv.LieBracketCell.R10C4
import Hqiv.LieBracketCell.R10C5
import Hqiv.LieBracketCell.R10C6
import Hqiv.LieBracketCell.R10C7
import Hqiv.LieBracketCell.R10C8
import Hqiv.LieBracketCell.R10C9
import Hqiv.LieBracketCell.R10C10
import Hqiv.LieBracketCell.R10C11
import Hqiv.LieBracketCell.R10C12
import Hqiv.LieBracketCell.R10C13
import Hqiv.LieBracketCell.R10C14
import Hqiv.LieBracketCell.R10C15
import Hqiv.LieBracketCell.R10C16
import Hqiv.LieBracketCell.R10C17
import Hqiv.LieBracketCell.R10C18
import Hqiv.LieBracketCell.R10C19
import Hqiv.LieBracketCell.R10C20
import Hqiv.LieBracketCell.R10C21
import Hqiv.LieBracketCell.R10C22
import Hqiv.LieBracketCell.R10C23
import Hqiv.LieBracketCell.R10C24
import Hqiv.LieBracketCell.R10C25
import Hqiv.LieBracketCell.R10C26
import Hqiv.LieBracketCell.R10C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 10 (imports parallel cell modules). -/
theorem lieBracket_in_span_row10 (j : Fin 28) :
    lieBracket (so8Generator ⟨10, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨10, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r10_c0
  · exact lieBracket_in_span_r10_c1
  · exact lieBracket_in_span_r10_c2
  · exact lieBracket_in_span_r10_c3
  · exact lieBracket_in_span_r10_c4
  · exact lieBracket_in_span_r10_c5
  · exact lieBracket_in_span_r10_c6
  · exact lieBracket_in_span_r10_c7
  · exact lieBracket_in_span_r10_c8
  · exact lieBracket_in_span_r10_c9
  · exact lieBracket_in_span_r10_c10
  · exact lieBracket_in_span_r10_c11
  · exact lieBracket_in_span_r10_c12
  · exact lieBracket_in_span_r10_c13
  · exact lieBracket_in_span_r10_c14
  · exact lieBracket_in_span_r10_c15
  · exact lieBracket_in_span_r10_c16
  · exact lieBracket_in_span_r10_c17
  · exact lieBracket_in_span_r10_c18
  · exact lieBracket_in_span_r10_c19
  · exact lieBracket_in_span_r10_c20
  · exact lieBracket_in_span_r10_c21
  · exact lieBracket_in_span_r10_c22
  · exact lieBracket_in_span_r10_c23
  · exact lieBracket_in_span_r10_c24
  · exact lieBracket_in_span_r10_c25
  · exact lieBracket_in_span_r10_c26
  · exact lieBracket_in_span_r10_c27

end Hqiv
