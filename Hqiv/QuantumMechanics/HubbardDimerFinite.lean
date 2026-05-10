import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Hqiv.Geometry.AuxiliaryField
import Hqiv.QuantumMechanics.FiniteDimVonNeumann
import Hqiv.QuantumMechanics.FiniteManyBodyTensorScaffold

/-!
# Hubbard dimer (finite 4D spin sector)

Minimal two-site, spin-1/2 toy in a finite four-state sector. This is intended as
the first interacting numerical bridge on top of
`FiniteManyBodyTensorScaffold`:

* non-interacting part from a Kronecker sum (`H₁ ⊗ I + I ⊗ H₂`);
* interaction slot `+ λ V` with `V = σ_z ⊗ σ_z`.

The coupling hook `lambdaShell` ties `λ` to the HQIV shell ladder via
`phi_of_shell` (normalized at shell `m = 4`).
-/

namespace Hqiv.QM

open scoped Kronecker
open Matrix Complex

/-- Two-level local Hilbert dimension as a positive natural. -/
abbrev twoDim : ℕ+ := 2

/-- Composite dimer dimension (`2 * 2 = 4`). -/
abbrev dimerDim : ℕ+ := twoDim * twoDim

/-- Pauli `σx`. -/
def sigmaX : Matrix (Fin twoDim.1) (Fin twoDim.1) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

/-- Pauli `σz`. -/
def sigmaZ : Matrix (Fin twoDim.1) (Fin twoDim.1) ℂ :=
  !![(1 : ℂ), 0; 0, (-1 : ℂ)]

theorem sigmaX_isHermitian : sigmaX.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.of_apply]

theorem sigmaZ_isHermitian : sigmaZ.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.of_apply]

/-- Non-interacting dimer part `-t (σx ⊗ I + I ⊗ σx)` on `Fin 4`. -/
noncomputable def hoppingXX (t : ℝ) : Matrix (Fin dimerDim.1) (Fin dimerDim.1) ℂ :=
  (-(t : ℂ)) • tensorKroneckerSumMatrix twoDim twoDim sigmaX sigmaX

/-- Interaction slot `V = σz ⊗ σz`, reindexed onto `Fin 4`. -/
noncomputable def interactionZZ : Matrix (Fin dimerDim.1) (Fin dimerDim.1) ℂ :=
  ((sigmaZ ⊗ₖ sigmaZ).submatrix (finTensorIndexEquiv twoDim twoDim).symm
    (finTensorIndexEquiv twoDim twoDim).symm)

/-- Shell-coupled interaction strength, normalized at shell `m = 4`. -/
noncomputable def lambdaShell (m : ℕ) (lambda0 coherence : ℝ := 1) : ℝ :=
  lambda0 * coherence * (Hqiv.phi_of_shell m / Hqiv.phi_of_shell 4)

/-- Full finite Hubbard-dimer toy Hamiltonian with explicit interaction slot. -/
noncomputable def hubbardDimerMatrix (t lambda : ℝ) :
    Matrix (Fin dimerDim.1) (Fin dimerDim.1) ℂ :=
  hoppingXX t + (lambda : ℂ) • interactionZZ

/-- Shell-driven variant: `lambda = lambdaShell m ...`. -/
noncomputable def hubbardDimerShellMatrix (m : ℕ) (t lambda0 coherence : ℝ) :
    Matrix (Fin dimerDim.1) (Fin dimerDim.1) ℂ :=
  hubbardDimerMatrix t (lambdaShell m lambda0 coherence)

theorem interactionZZ_isHermitian : interactionZZ.IsHermitian := by
  have hprod : (sigmaZ ⊗ₖ sigmaZ).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_kronecker]
    have hσ : sigmaZᴴ = sigmaZ := sigmaZ_isHermitian
    simp [hσ]
  exact hprod.submatrix (finTensorIndexEquiv twoDim twoDim).symm

theorem hoppingXX_isHermitian (t : ℝ) : (hoppingXX t).IsHermitian := by
  have h0 :
      (tensorKroneckerSumMatrix twoDim twoDim sigmaX sigmaX).IsHermitian :=
    tensorKroneckerSumMatrix_isHermitian twoDim twoDim sigmaX sigmaX
      sigmaX_isHermitian sigmaX_isHermitian
  rw [hoppingXX, Matrix.IsHermitian, Matrix.conjTranspose_smul, h0]
  simp

theorem hubbardDimerMatrix_isHermitian (t lambda : ℝ) :
    (hubbardDimerMatrix t lambda).IsHermitian := by
  refine (hoppingXX_isHermitian t).add ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, interactionZZ_isHermitian]
  simp

/-- Observable package for the finite dimer toy. -/
noncomputable def hubbardDimerObservable (t lambda : ℝ) : Observable dimerDim.1 where
  A := hubbardDimerMatrix t lambda
  isHerm := hubbardDimerMatrix_isHermitian t lambda

end Hqiv.QM
