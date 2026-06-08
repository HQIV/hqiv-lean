import Hqiv.LieBracketCell.R12C0
import Hqiv.LieBracketCell.R12C1
import Hqiv.LieBracketCell.R12C2
import Hqiv.LieBracketCell.R12C3
import Hqiv.LieBracketCell.R12C4
import Hqiv.LieBracketCell.R12C5
import Hqiv.LieBracketCell.R12C6
import Hqiv.LieBracketCell.R12C7
import Hqiv.LieBracketCell.R12C8
import Hqiv.LieBracketCell.R12C9
import Hqiv.LieBracketCell.R12C10
import Hqiv.LieBracketCell.R12C11
import Hqiv.LieBracketCell.R12C12
import Hqiv.LieBracketCell.R12C13
import Hqiv.LieBracketCell.R12C14
import Hqiv.LieBracketCell.R12C15
import Hqiv.LieBracketCell.R12C16
import Hqiv.LieBracketCell.R12C17
import Hqiv.LieBracketCell.R12C18
import Hqiv.LieBracketCell.R12C19
import Hqiv.LieBracketCell.R12C20
import Hqiv.LieBracketCell.R12C21
import Hqiv.LieBracketCell.R12C22
import Hqiv.LieBracketCell.R12C23
import Hqiv.LieBracketCell.R12C24
import Hqiv.LieBracketCell.R12C25
import Hqiv.LieBracketCell.R12C26
import Hqiv.LieBracketCell.R12C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 12 (imports parallel cell modules). -/
theorem lieBracket_in_span_row12 (j : Fin 28) :
    lieBracket (so8Generator ⟨12, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨12, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r12_c0
  · exact lieBracket_in_span_r12_c1
  · exact lieBracket_in_span_r12_c2
  · exact lieBracket_in_span_r12_c3
  · exact lieBracket_in_span_r12_c4
  · exact lieBracket_in_span_r12_c5
  · exact lieBracket_in_span_r12_c6
  · exact lieBracket_in_span_r12_c7
  · exact lieBracket_in_span_r12_c8
  · exact lieBracket_in_span_r12_c9
  · exact lieBracket_in_span_r12_c10
  · exact lieBracket_in_span_r12_c11
  · exact lieBracket_in_span_r12_c12
  · exact lieBracket_in_span_r12_c13
  · exact lieBracket_in_span_r12_c14
  · exact lieBracket_in_span_r12_c15
  · exact lieBracket_in_span_r12_c16
  · exact lieBracket_in_span_r12_c17
  · exact lieBracket_in_span_r12_c18
  · exact lieBracket_in_span_r12_c19
  · exact lieBracket_in_span_r12_c20
  · exact lieBracket_in_span_r12_c21
  · exact lieBracket_in_span_r12_c22
  · exact lieBracket_in_span_r12_c23
  · exact lieBracket_in_span_r12_c24
  · exact lieBracket_in_span_r12_c25
  · exact lieBracket_in_span_r12_c26
  · exact lieBracket_in_span_r12_c27

end Hqiv
