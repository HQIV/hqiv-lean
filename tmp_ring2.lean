import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

open Complex

example : (2⁻¹ : ℂ) * ((2⁻¹ : ℂ) * I) + (2⁻¹ : ℂ) * I * (2⁻¹ : ℂ) = I * (2⁻¹ : ℂ) := by
  ring_nf

example : (2⁻¹ : ℂ) * ((2⁻¹ : ℂ) * I) + (2⁻¹ : ℂ) * I * (2⁻¹ : ℂ) = I * (2⁻¹ : ℂ) := by
  ring
