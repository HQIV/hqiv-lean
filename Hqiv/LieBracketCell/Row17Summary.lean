import Hqiv.LieBracketCell.R17C0
import Hqiv.LieBracketCell.R17C1
import Hqiv.LieBracketCell.R17C2
import Hqiv.LieBracketCell.R17C3
import Hqiv.LieBracketCell.R17C4
import Hqiv.LieBracketCell.R17C5
import Hqiv.LieBracketCell.R17C6
import Hqiv.LieBracketCell.R17C7
import Hqiv.LieBracketCell.R17C8
import Hqiv.LieBracketCell.R17C9
import Hqiv.LieBracketCell.R17C10
import Hqiv.LieBracketCell.R17C11
import Hqiv.LieBracketCell.R17C12
import Hqiv.LieBracketCell.R17C13
import Hqiv.LieBracketCell.R17C14
import Hqiv.LieBracketCell.R17C15
import Hqiv.LieBracketCell.R17C16
import Hqiv.LieBracketCell.R17C17
import Hqiv.LieBracketCell.R17C18
import Hqiv.LieBracketCell.R17C19
import Hqiv.LieBracketCell.R17C20
import Hqiv.LieBracketCell.R17C21
import Hqiv.LieBracketCell.R17C22
import Hqiv.LieBracketCell.R17C23
import Hqiv.LieBracketCell.R17C24
import Hqiv.LieBracketCell.R17C25
import Hqiv.LieBracketCell.R17C26
import Hqiv.LieBracketCell.R17C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 17 (imports parallel cell modules). -/
theorem lieBracket_in_span_row17 (j : Fin 28) :
    lieBracket (so8Generator ⟨17, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨17, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r17_c0
  · exact lieBracket_in_span_r17_c1
  · exact lieBracket_in_span_r17_c2
  · exact lieBracket_in_span_r17_c3
  · exact lieBracket_in_span_r17_c4
  · exact lieBracket_in_span_r17_c5
  · exact lieBracket_in_span_r17_c6
  · exact lieBracket_in_span_r17_c7
  · exact lieBracket_in_span_r17_c8
  · exact lieBracket_in_span_r17_c9
  · exact lieBracket_in_span_r17_c10
  · exact lieBracket_in_span_r17_c11
  · exact lieBracket_in_span_r17_c12
  · exact lieBracket_in_span_r17_c13
  · exact lieBracket_in_span_r17_c14
  · exact lieBracket_in_span_r17_c15
  · exact lieBracket_in_span_r17_c16
  · exact lieBracket_in_span_r17_c17
  · exact lieBracket_in_span_r17_c18
  · exact lieBracket_in_span_r17_c19
  · exact lieBracket_in_span_r17_c20
  · exact lieBracket_in_span_r17_c21
  · exact lieBracket_in_span_r17_c22
  · exact lieBracket_in_span_r17_c23
  · exact lieBracket_in_span_r17_c24
  · exact lieBracket_in_span_r17_c25
  · exact lieBracket_in_span_r17_c26
  · exact lieBracket_in_span_r17_c27

end Hqiv
