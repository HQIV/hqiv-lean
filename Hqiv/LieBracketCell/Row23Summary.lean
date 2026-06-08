import Hqiv.LieBracketCell.R23C0
import Hqiv.LieBracketCell.R23C1
import Hqiv.LieBracketCell.R23C2
import Hqiv.LieBracketCell.R23C3
import Hqiv.LieBracketCell.R23C4
import Hqiv.LieBracketCell.R23C5
import Hqiv.LieBracketCell.R23C6
import Hqiv.LieBracketCell.R23C7
import Hqiv.LieBracketCell.R23C8
import Hqiv.LieBracketCell.R23C9
import Hqiv.LieBracketCell.R23C10
import Hqiv.LieBracketCell.R23C11
import Hqiv.LieBracketCell.R23C12
import Hqiv.LieBracketCell.R23C13
import Hqiv.LieBracketCell.R23C14
import Hqiv.LieBracketCell.R23C15
import Hqiv.LieBracketCell.R23C16
import Hqiv.LieBracketCell.R23C17
import Hqiv.LieBracketCell.R23C18
import Hqiv.LieBracketCell.R23C19
import Hqiv.LieBracketCell.R23C20
import Hqiv.LieBracketCell.R23C21
import Hqiv.LieBracketCell.R23C22
import Hqiv.LieBracketCell.R23C23
import Hqiv.LieBracketCell.R23C24
import Hqiv.LieBracketCell.R23C25
import Hqiv.LieBracketCell.R23C26
import Hqiv.LieBracketCell.R23C27

open Matrix BigOperators

namespace Hqiv

/-- Aggregate row 23 (imports parallel cell modules). -/
theorem lieBracket_in_span_row23 (j : Fin 28) :
    lieBracket (so8Generator ⟨23, by decide⟩) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff ⟨23, by decide⟩ j k • so8Generator k := by
  fin_cases j
  · exact lieBracket_in_span_r23_c0
  · exact lieBracket_in_span_r23_c1
  · exact lieBracket_in_span_r23_c2
  · exact lieBracket_in_span_r23_c3
  · exact lieBracket_in_span_r23_c4
  · exact lieBracket_in_span_r23_c5
  · exact lieBracket_in_span_r23_c6
  · exact lieBracket_in_span_r23_c7
  · exact lieBracket_in_span_r23_c8
  · exact lieBracket_in_span_r23_c9
  · exact lieBracket_in_span_r23_c10
  · exact lieBracket_in_span_r23_c11
  · exact lieBracket_in_span_r23_c12
  · exact lieBracket_in_span_r23_c13
  · exact lieBracket_in_span_r23_c14
  · exact lieBracket_in_span_r23_c15
  · exact lieBracket_in_span_r23_c16
  · exact lieBracket_in_span_r23_c17
  · exact lieBracket_in_span_r23_c18
  · exact lieBracket_in_span_r23_c19
  · exact lieBracket_in_span_r23_c20
  · exact lieBracket_in_span_r23_c21
  · exact lieBracket_in_span_r23_c22
  · exact lieBracket_in_span_r23_c23
  · exact lieBracket_in_span_r23_c24
  · exact lieBracket_in_span_r23_c25
  · exact lieBracket_in_span_r23_c26
  · exact lieBracket_in_span_r23_c27

end Hqiv
