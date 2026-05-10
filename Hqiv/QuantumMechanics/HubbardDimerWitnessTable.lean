import Hqiv.Geometry.AuxiliaryField

namespace Hqiv.QM

/-- Tiny Lean-side witness row for the shell sweep alignment. -/
structure HubbardShellRow where
  m : Nat
  phi_num : Nat
  lambda_ratio_num : Nat
  lambda_ratio_den : Nat
deriving Repr, DecidableEq

/-- `phi_of_shell(m) = 2(m+1)` encoded as a natural numerator. -/
def phiNum (m : Nat) : Nat :=
  2 * (m + 1)

/-- `lambda_shell / (lambda0*coherence) = (m+1)/5` numerator. -/
def lambdaRatioNum (m : Nat) : Nat :=
  m + 1

/-- Common denominator for the normalized shell-ratio witness. -/
def lambdaRatioDen : Nat := 5

/-- Computed witness rows (used by `#eval` and compile-time equality checks). -/
def computedHubbardShellRows : List HubbardShellRow :=
  (List.range 7).map (fun k =>
    let m := k + 2
    { m := m
      phi_num := phiNum m
      lambda_ratio_num := lambdaRatioNum m
      lambda_ratio_den := lambdaRatioDen })

/-- Frozen expected rows for `m = 2..8`. -/
def expectedHubbardShellRows : List HubbardShellRow :=
  [ { m := 2, phi_num := 6,  lambda_ratio_num := 3, lambda_ratio_den := 5 }
  , { m := 3, phi_num := 8,  lambda_ratio_num := 4, lambda_ratio_den := 5 }
  , { m := 4, phi_num := 10, lambda_ratio_num := 5, lambda_ratio_den := 5 }
  , { m := 5, phi_num := 12, lambda_ratio_num := 6, lambda_ratio_den := 5 }
  , { m := 6, phi_num := 14, lambda_ratio_num := 7, lambda_ratio_den := 5 }
  , { m := 7, phi_num := 16, lambda_ratio_num := 8, lambda_ratio_den := 5 }
  , { m := 8, phi_num := 18, lambda_ratio_num := 9, lambda_ratio_den := 5 }
  ]

/-- Shell indices carried by the frozen witness table (`m = 2..8`). -/
def witnessShellMs : List Nat :=
  expectedHubbardShellRows.map HubbardShellRow.m

theorem witnessShellMs_eq : witnessShellMs = [2, 3, 4, 5, 6, 7, 8] := rfl

/-- Compile-time drift guard for the witness table itself. -/
theorem computedHubbardShellRows_eq_expected :
    computedHubbardShellRows = expectedHubbardShellRows := by
  native_decide

example : phiNum 4 = 10 := by
  decide

#eval computedHubbardShellRows

end Hqiv.QM
