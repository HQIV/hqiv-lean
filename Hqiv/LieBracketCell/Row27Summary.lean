import Hqiv.LieBracketCell.R27C0
import Hqiv.LieBracketCell.R27C1
import Hqiv.LieBracketCell.R27C2
import Hqiv.LieBracketCell.R27C3
import Hqiv.LieBracketCell.R27C4
import Hqiv.LieBracketCell.R27C5
import Hqiv.LieBracketCell.R27C6
import Hqiv.LieBracketCell.R27C7
import Hqiv.LieBracketCell.R27C8
import Hqiv.LieBracketCell.R27C9
import Hqiv.LieBracketCell.R27C10
import Hqiv.LieBracketCell.R27C11
import Hqiv.LieBracketCell.R27C12
import Hqiv.LieBracketCell.R27C13
import Hqiv.LieBracketCell.R27C14
import Hqiv.LieBracketCell.R27C15
import Hqiv.LieBracketCell.R27C16
import Hqiv.LieBracketCell.R27C17
import Hqiv.LieBracketCell.R27C18
import Hqiv.LieBracketCell.R27C19
import Hqiv.LieBracketCell.R27C20
import Hqiv.LieBracketCell.R27C21
import Hqiv.LieBracketCell.R27C22
import Hqiv.LieBracketCell.R27C23
import Hqiv.LieBracketCell.R27C24
import Hqiv.LieBracketCell.R27C25
import Hqiv.LieBracketCell.R27C26
import Hqiv.LieBracketCell.R27C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 27 (imports parallel cell modules). -/
theorem lieBracket_in_span_row27 (j : Fin 28) :
    lieBracket (so8Generator ⟨27, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨27, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r27_c0
  · exact lieBracket_in_span_r27_c1
  · exact lieBracket_in_span_r27_c2
  · exact lieBracket_in_span_r27_c3
  · exact lieBracket_in_span_r27_c4
  · exact lieBracket_in_span_r27_c5
  · exact lieBracket_in_span_r27_c6
  · exact lieBracket_in_span_r27_c7
  · exact lieBracket_in_span_r27_c8
  · exact lieBracket_in_span_r27_c9
  · exact lieBracket_in_span_r27_c10
  · exact lieBracket_in_span_r27_c11
  · exact lieBracket_in_span_r27_c12
  · exact lieBracket_in_span_r27_c13
  · exact lieBracket_in_span_r27_c14
  · exact lieBracket_in_span_r27_c15
  · exact lieBracket_in_span_r27_c16
  · exact lieBracket_in_span_r27_c17
  · exact lieBracket_in_span_r27_c18
  · exact lieBracket_in_span_r27_c19
  · exact lieBracket_in_span_r27_c20
  · exact lieBracket_in_span_r27_c21
  · exact lieBracket_in_span_r27_c22
  · exact lieBracket_in_span_r27_c23
  · exact lieBracket_in_span_r27_c24
  · exact lieBracket_in_span_r27_c25
  · exact lieBracket_in_span_r27_c26
  · exact lieBracket_in_span_r27_c27

end Hqiv
