import Hqiv.LieBracketCell.R15C0
import Hqiv.LieBracketCell.R15C1
import Hqiv.LieBracketCell.R15C2
import Hqiv.LieBracketCell.R15C3
import Hqiv.LieBracketCell.R15C4
import Hqiv.LieBracketCell.R15C5
import Hqiv.LieBracketCell.R15C6
import Hqiv.LieBracketCell.R15C7
import Hqiv.LieBracketCell.R15C8
import Hqiv.LieBracketCell.R15C9
import Hqiv.LieBracketCell.R15C10
import Hqiv.LieBracketCell.R15C11
import Hqiv.LieBracketCell.R15C12
import Hqiv.LieBracketCell.R15C13
import Hqiv.LieBracketCell.R15C14
import Hqiv.LieBracketCell.R15C15
import Hqiv.LieBracketCell.R15C16
import Hqiv.LieBracketCell.R15C17
import Hqiv.LieBracketCell.R15C18
import Hqiv.LieBracketCell.R15C19
import Hqiv.LieBracketCell.R15C20
import Hqiv.LieBracketCell.R15C21
import Hqiv.LieBracketCell.R15C22
import Hqiv.LieBracketCell.R15C23
import Hqiv.LieBracketCell.R15C24
import Hqiv.LieBracketCell.R15C25
import Hqiv.LieBracketCell.R15C26
import Hqiv.LieBracketCell.R15C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 15 (imports parallel cell modules). -/
theorem lieBracket_in_span_row15 (j : Fin 28) :
    lieBracket (so8Generator ⟨15, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨15, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r15_c0
  · exact lieBracket_in_span_r15_c1
  · exact lieBracket_in_span_r15_c2
  · exact lieBracket_in_span_r15_c3
  · exact lieBracket_in_span_r15_c4
  · exact lieBracket_in_span_r15_c5
  · exact lieBracket_in_span_r15_c6
  · exact lieBracket_in_span_r15_c7
  · exact lieBracket_in_span_r15_c8
  · exact lieBracket_in_span_r15_c9
  · exact lieBracket_in_span_r15_c10
  · exact lieBracket_in_span_r15_c11
  · exact lieBracket_in_span_r15_c12
  · exact lieBracket_in_span_r15_c13
  · exact lieBracket_in_span_r15_c14
  · exact lieBracket_in_span_r15_c15
  · exact lieBracket_in_span_r15_c16
  · exact lieBracket_in_span_r15_c17
  · exact lieBracket_in_span_r15_c18
  · exact lieBracket_in_span_r15_c19
  · exact lieBracket_in_span_r15_c20
  · exact lieBracket_in_span_r15_c21
  · exact lieBracket_in_span_r15_c22
  · exact lieBracket_in_span_r15_c23
  · exact lieBracket_in_span_r15_c24
  · exact lieBracket_in_span_r15_c25
  · exact lieBracket_in_span_r15_c26
  · exact lieBracket_in_span_r15_c27

end Hqiv
