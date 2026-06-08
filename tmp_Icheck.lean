import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

open Complex

example : (-1 / 2 : ℂ) = I ^ 2 * (1 / 2 : ℂ) := by
  rw [Complex.I_sq]
  ring

example : (-1 / 2 : ℂ) = Complex.I ^ 2 * (1 / 2 : ℂ) := by
  rw [Complex.I_sq]
  ring
