import Hqiv.LieBracketCell.R21C0
import Hqiv.LieBracketCell.R21C1
import Hqiv.LieBracketCell.R21C2
import Hqiv.LieBracketCell.R21C3
import Hqiv.LieBracketCell.R21C4
import Hqiv.LieBracketCell.R21C5
import Hqiv.LieBracketCell.R21C6
import Hqiv.LieBracketCell.R21C7
import Hqiv.LieBracketCell.R21C8
import Hqiv.LieBracketCell.R21C9
import Hqiv.LieBracketCell.R21C10
import Hqiv.LieBracketCell.R21C11
import Hqiv.LieBracketCell.R21C12
import Hqiv.LieBracketCell.R21C13
import Hqiv.LieBracketCell.R21C14
import Hqiv.LieBracketCell.R21C15
import Hqiv.LieBracketCell.R21C16
import Hqiv.LieBracketCell.R21C17
import Hqiv.LieBracketCell.R21C18
import Hqiv.LieBracketCell.R21C19
import Hqiv.LieBracketCell.R21C20
import Hqiv.LieBracketCell.R21C21
import Hqiv.LieBracketCell.R21C22
import Hqiv.LieBracketCell.R21C23
import Hqiv.LieBracketCell.R21C24
import Hqiv.LieBracketCell.R21C25
import Hqiv.LieBracketCell.R21C26
import Hqiv.LieBracketCell.R21C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 21 (imports parallel cell modules). -/
theorem lieBracket_in_span_row21 (j : Fin 28) :
    lieBracket (so8Generator ⟨21, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨21, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r21_c0
  · exact lieBracket_in_span_r21_c1
  · exact lieBracket_in_span_r21_c2
  · exact lieBracket_in_span_r21_c3
  · exact lieBracket_in_span_r21_c4
  · exact lieBracket_in_span_r21_c5
  · exact lieBracket_in_span_r21_c6
  · exact lieBracket_in_span_r21_c7
  · exact lieBracket_in_span_r21_c8
  · exact lieBracket_in_span_r21_c9
  · exact lieBracket_in_span_r21_c10
  · exact lieBracket_in_span_r21_c11
  · exact lieBracket_in_span_r21_c12
  · exact lieBracket_in_span_r21_c13
  · exact lieBracket_in_span_r21_c14
  · exact lieBracket_in_span_r21_c15
  · exact lieBracket_in_span_r21_c16
  · exact lieBracket_in_span_r21_c17
  · exact lieBracket_in_span_r21_c18
  · exact lieBracket_in_span_r21_c19
  · exact lieBracket_in_span_r21_c20
  · exact lieBracket_in_span_r21_c21
  · exact lieBracket_in_span_r21_c22
  · exact lieBracket_in_span_r21_c23
  · exact lieBracket_in_span_r21_c24
  · exact lieBracket_in_span_r21_c25
  · exact lieBracket_in_span_r21_c26
  · exact lieBracket_in_span_r21_c27

end Hqiv
