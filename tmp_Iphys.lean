import Hqiv.Physics.StrongColorSu3LieCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators
open Complex Matrix Finset
open Hqiv.Algebra Hqiv.Physics

example : (-1 / 2 : ℂ) = I ^ 2 * (1 / 2 : ℂ) := by
  rw [Complex.I_sq]
  ring
