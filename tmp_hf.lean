import Hqiv.Physics.StrongColorSu3LieCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

open scoped BigOperators
open Complex Matrix Finset
open Hqiv.Algebra Hqiv.Physics

example : colorSu3fStructure (0 : Fin 8) (1 : Fin 8) (7 : Fin 8) = 0 := by
  simp [colorSu3fStructure, colorSu3PermSign, min3, mid3, max3, colorSu3fSorted]
