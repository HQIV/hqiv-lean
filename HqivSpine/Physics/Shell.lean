import HqivSpine.Foundation.Carrier
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `HqivSpine.Physics.Shell` — the shell ladder and its couplings

Dimensionless shell machinery built directly on the foundation constants:

* the lock-in shell `referenceM = 4` (the proton anchor index);
* the mode-count `φ(m) = 2(m+1)` and the lattice simplex count
  `(m+2)(m+1) = shellNumer m` (reusing the foundation seed);
* the bare inverse coupling `1/α_GUT = 42 = 6·7` (`7 = imaginaryDim`), the
  curvature-imprint exponent `α = 3/5` (the `d = 3` row), and the shell-running
  effective coupling.

No MeV, no PDG: this layer is pure ratios and a `log` running form.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **Lock-in shell** = proton anchor index. -/
def referenceM : ℕ := 4

/-- Null-shell mode count `φ(m) = 2(m+1)`. -/
def phi (m : ℕ) : ℕ := 2 * (m + 1)

/-- Lattice simplex count at shell `m`, identical to the foundation seed
`shellNumer m = (m+2)(m+1)`. -/
def latticeSimplexCount (m : ℕ) : ℕ := shellNumer m

theorem latticeSimplexCount_eq_shellNumer (m : ℕ) :
    latticeSimplexCount m = shellNumer m := rfl

theorem latticeSimplexCount_pos (m : ℕ) : 0 < latticeSimplexCount m :=
  shellNumer_pos m

/-- **Curvature-imprint / EM exponent** `α = 3/5`, the `d = 3` row of the
foundation family `alphaRat`. -/
noncomputable def alphaEM : ℝ := (alphaRat transverseDim : ℝ)

theorem alphaEM_eq : alphaEM = 3 / 5 := by
  unfold alphaEM; rw [alpha_transverseDim]; norm_num

/-- **Informational-monogamy complement** `γ = 2/5`, the `d = 3` row of the foundation
family and the partner of `α = 3/5` under the unit split `α + γ = 1`. -/
noncomputable def gammaHQIV : ℝ := (gammaRat transverseDim : ℝ)

theorem gammaHQIV_eq : gammaHQIV = 2 / 5 := by
  unfold gammaHQIV
  rw [show gammaRat transverseDim = 2 / 5 from gamma_three]; norm_num

/-- **Bare inverse coupling** `1/α_GUT = 42`. -/
def oneOverAlphaBare : ℝ := 42

/-- `42 = 6 · 7 = 6 · imaginaryDim`: the bare coupling is set by the seven
imaginary directions. -/
theorem oneOverAlphaBare_eq_six_mul_imaginaryDim :
    oneOverAlphaBare = 6 * (imaginaryDim : ℝ) := by
  rw [imaginaryDim_eq_seven]; norm_num [oneOverAlphaBare]

/-- **Effective inverse coupling on the shell ladder** (one-loop `log` running). -/
noncomputable def oneOverAlphaEffAtShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  oneOverAlphaBare * (1 + c * alphaEM * Real.log ((phi m : ℝ) + 1))

/-- **Effective coupling at shell `m`.** -/
noncomputable def alphaEffAtShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  (oneOverAlphaEffAtShell m c)⁻¹

end HqivSpine.Physics
