import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

open scoped InnerProductSpace
open Complex EuclideanSpace Matrix PiLp WithLp

abbrev H := EuclideanSpace ℂ (Fin 2)

noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
noncomputable def linX : H →ₗ[ℂ] H := Matrix.toEuclideanLin pauliX
noncomputable def linZ : H →ₗ[ℂ] H := Matrix.toEuclideanLin pauliZ
noncomputable def expect (A : H →ₗ[ℂ] H) (ψ : H) : ℂ := inner ℂ ψ (A ψ)
noncomputable def fluct (A : H →ₗ[ℂ] H) (ψ : H) : H := A ψ - expect A ψ • ψ

theorem im_test (ψ : H) (a b c d : ℝ) (h0 : ψ 0 = a + I * b) (h1 : ψ 1 = c + I * d) :
    (inner ℂ (fluct linX ψ) (fluct linZ ψ)).im = -(2 * (a * d - b * c)) := by
  sorry
