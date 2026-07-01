import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.VonNeumann` — observables, the Born rule, and density matrices

The **measurement** layer of the spine's quantum mechanics, complementing
`Physics.SpinStatistics` (spin & statistics) and `Physics.Uncertainty` (Robertson bound).
von Neumann's identification **observable ↔ self-adjoint operator** is implemented in the
finite-dimensional case: bounded operators are matrices, self-adjointness is
`Matrix.IsHermitian`, and states are unit vectors (pure) or density matrices
(Hermitian, unit trace).

Main results (Mathlib core only, no new physics axioms):

* `Observable n`, `expectQ`, `PureState` — observables and expectation `⟨O⟩_ψ = ⟪ψ, Oψ⟫`;
* **Born rule** `bornProbCompBasis ψ i = ‖ψ i‖²` with the normalisation
  `∑ᵢ bornProb = ‖ψ‖²` (`sum_bornProbCompBasis_eq_norm_sq`), so on a pure state the
  outcome probabilities sum to `1` (`sum_bornProbCompBasis_pure`);
* `rankOne ψ = |ψ⟩⟨ψ|` is Hermitian with trace `‖ψ‖²`, giving the pure-state density matrix
  `DensityMatrix.fromPure` (Hermitian, unit trace).

This is the standard finite-dim QM₂ linear algebra on `EuclideanSpace ℂ (Fin n)`; positivity
(`PosSemidef`) and the Borel functional calculus are the usual Mathlib upgrade paths, not
needed for the Born normalisation proved here.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.VonNeumann

open scoped InnerProductSpace BigOperators Matrix Complex ComplexConjugate PiLp
open Matrix Complex Fintype

/-- Finite complex Hilbert space `ℂⁿ` with the standard `L²` inner product. -/
abbrev HilbertFin (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable section

/-- Self-adjoint observable: a Hermitian matrix, hence a bounded operator on `HilbertFin n`. -/
structure Observable (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℂ
  isHerm : A.IsHermitian

/-- Underlying `ℂ`-linear operator on Hilbert space. -/
def Observable.toLin {n : ℕ} (O : Observable n) : HilbertFin n →ₗ[ℂ] HilbertFin n :=
  Matrix.toEuclideanLin O.A

/-- Quantum expectation `⟨O⟩_ψ = ⟪ψ, O ψ⟫`. -/
def expectQ {n : ℕ} (O : Observable n) (ψ : HilbertFin n) : ℂ :=
  inner ℂ ψ (O.toLin ψ)

/-- Unit-norm vector = pure state (Schrödinger picture). -/
def PureState (n : ℕ) := { ψ : HilbertFin n // ‖ψ‖ = 1 }

/-- Born probability for outcome `i` in the computational basis: `|⟨eᵢ,ψ⟩|² = ‖ψᵢ‖²`. -/
def bornProbCompBasis {n : ℕ} (ψ : HilbertFin n) (i : Fin n) : ℝ :=
  ‖ψ i‖ ^ 2

/-- Rank-one operator `|ψ⟩⟨ψ|` (matrix `ψᵢ conj ψⱼ`). -/
def rankOne {n : ℕ} (ψ : HilbertFin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ψ i * star (ψ j)

theorem rankOne_isHermitian {n : ℕ} (ψ : HilbertFin n) : (rankOne ψ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext i j
  simp [rankOne, map_mul, mul_comm]

theorem trace_rankOne {n : ℕ} (ψ : HilbertFin n) :
    (rankOne ψ).trace = ∑ k : Fin n, ψ k * star (ψ k) := by
  simp [Matrix.trace, rankOne, Matrix.diag_apply]

/-- Hermitian density matrix with unit trace (von Neumann statistical operator).

Borel functional calculus and complete positivity are not developed here. For mixed states
one should additionally require `Matrix.PosSemidef ρ` when convex geometry matters; pure
`rankOne` projectors are PSD automatically in the spectral sense. -/
structure DensityMatrix (n : ℕ) where
  ρ : Matrix (Fin n) (Fin n) ℂ
  herm : ρ.IsHermitian
  trace_one : ρ.trace = 1

/-- Pure state as density matrix `ρ = |ψ⟩⟨ψ|`. -/
def DensityMatrix.fromPure {n : ℕ} (ψ : HilbertFin n) (hψ : ‖ψ‖ = 1) : DensityMatrix n where
  ρ := rankOne ψ
  herm := rankOne_isHermitian ψ
  trace_one := by
    have htr := trace_rankOne ψ
    have hsq : (∑ k : Fin n, ‖ψ k‖ ^ 2 : ℝ) = 1 := by
      rw [← EuclideanSpace.norm_sq_eq ψ, hψ, one_pow]
    have hsum : (∑ k : Fin n, ψ k * star (ψ k) : ℂ) = 1 := by
      have hterm (k : Fin n) : ψ k * star (ψ k) = Complex.ofReal (‖ψ k‖ ^ 2) := by
        rw [star_def, mul_conj, Complex.normSq_eq_norm_sq]
      calc
        (∑ k : Fin n, ψ k * star (ψ k) : ℂ) = ∑ k : Fin n, Complex.ofReal (‖ψ k‖ ^ 2) :=
          Finset.sum_congr rfl fun k _ => hterm k
        _ = Complex.ofReal (∑ k : Fin n, ‖ψ k‖ ^ 2) := (Complex.ofReal_sum ..).symm
        _ = 1 := by rw [hsq, Complex.ofReal_one]
    rw [hsum] at htr
    simp [htr]

/-- Pauli `σₓ` on `ℂ²` as a registered observable. -/
def pauliX_obs : Observable 2 where
  A := !![(0 : ℂ), 1; 1, 0]
  isHerm := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply]

/-- **Born normalisation:** the computational-basis outcome probabilities sum to `‖ψ‖²`. -/
theorem sum_bornProbCompBasis_eq_norm_sq {n : ℕ} (ψ : HilbertFin n) :
    (∑ i : Fin n, bornProbCompBasis ψ i) = ‖ψ‖ ^ 2 := by
  simp [bornProbCompBasis, PiLp.norm_sq_eq_of_L2]

/-- **Born rule (pure state):** the outcome probabilities of a measurement sum to `1`. -/
theorem sum_bornProbCompBasis_pure {n : ℕ} (S : PureState n) :
    (∑ i : Fin n, bornProbCompBasis S.val i) = 1 := by
  rcases S with ⟨ψ, hψ⟩
  simpa [hψ] using sum_bornProbCompBasis_eq_norm_sq ψ

end

end HqivSpine.Physics.VonNeumann
