import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quaternion Maxwell on `S³` and O-Maxwell shell on `S⁴`

This module packages **standard** scalar Laplace–Beltrami data on the unit spheres
`S³ ⊂ ℝ⁴` and `S⁴ ⊂ ℝ⁵`, parallel to `Hqiv.Geometry.S7MetahorizonCasimir`.

**Classic quaternion / H-sector (`S³`).** The unit quaternions form `S³` inside
`ℝ⁴ ≅ ℍ`. That sphere is the natural compact phase manifold for the **four-component**
electromagnetic / quaternionic block used in `Hqiv.Physics.ModifiedMaxwell` (restriction
from octonions to `Fin 4` indices `0..3` in `Hqiv.Physics.OMaxwellAlgebraSeed`). Scalar
spherical harmonics on `S³` have eigenvalues `λ_ℓ = ℓ(ℓ+2)` (intrinsic dimension `3`).

**O-Maxwell extension (`S⁴`).** Viewing the octonion split as “quaternions plus one
extra Cayley–Dickson direction”, the next compact homogeneous counterpart is `S⁴ ⊂ ℝ⁵`
(one real dimension beyond the `ℝ⁴` quaternion carrier). Scalar harmonics on `S⁴`
have `λ_ℓ = ℓ(ℓ+3)`. This is **spectral geometry only**—not a claim that full O-Maxwell
dynamics reduces to a scalar Laplacian on `S⁴`.

**Dimension formula** (same convention as `S7MetahorizonCasimir`): for unit `Sᵈ` with
intrinsic dimension `d`,
`dim ℋ_ℓ = (2ℓ + d − 1) · binom(ℓ + d − 2, d − 2) / (d − 1)`.

The file is independent of the discrete null-lattice axiom stack; it is pure spectral
geometry + small sanity lemmas.
-/

namespace Hqiv.Geometry

open Nat

/-! ## `S³`: quaternion / classic Maxwell carrier -/

/-- Scalar Laplace–Beltrami eigenvalue on unit `S³`, degree `ℓ`: `λ_ℓ = ℓ(ℓ+2)`. -/
def laplaceBeltramiEigenvalueS3 (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + 2)

/-- Same eigenvalue as a natural number (for exact arithmetic in small lemmas). -/
def laplaceBeltramiEigenvalueS3Nat (ℓ : ℕ) : ℕ :=
  ℓ * (ℓ + 2)

theorem laplaceBeltramiEigenvalueS3Nat_cast (ℓ : ℕ) :
    (laplaceBeltramiEigenvalueS3Nat ℓ : ℝ) = laplaceBeltramiEigenvalueS3 ℓ := by
  simp [laplaceBeltramiEigenvalueS3Nat, laplaceBeltramiEigenvalueS3, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]

/--
Dimension of degree-`ℓ` spherical harmonics on `S³`:
`(2ℓ+2) · binom(ℓ+1,1) / 2` (= `(ℓ+1)²`).
-/
def sphericalHarmonicDimS3 (ℓ : ℕ) : ℕ :=
  (2 * ℓ + 2) * choose (ℓ + 1) 1 / 2

theorem sphericalHarmonicDimS3_eq_succ_sq (ℓ : ℕ) : sphericalHarmonicDimS3 ℓ = (ℓ + 1) ^ 2 := by
  unfold sphericalHarmonicDimS3
  rw [Nat.choose_one_right, show 2 * ℓ + 2 = 2 * (ℓ + 1) by omega]
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left ((ℓ + 1) * (ℓ + 1)) (by decide : 0 < 2)]
  simp [Nat.pow_two]

theorem sphericalHarmonicDimS3_zero : sphericalHarmonicDimS3 0 = 1 := by
  rw [sphericalHarmonicDimS3_eq_succ_sq]; rfl

theorem sphericalHarmonicDimS3_one : sphericalHarmonicDimS3 1 = 4 := by
  rw [sphericalHarmonicDimS3_eq_succ_sq]; rfl

theorem sphericalHarmonicDimS3_two : sphericalHarmonicDimS3 2 = 9 := by
  rw [sphericalHarmonicDimS3_eq_succ_sq]; rfl

private lemma two_le_sphericalHarmonicNumerS3 (ℓ : ℕ) :
    2 ≤ (2 * ℓ + 2) * choose (ℓ + 1) 1 := by
  have hone : 1 ≤ choose (ℓ + 1) 1 := by
    rw [Nat.choose_one_right]
    exact Nat.succ_le_succ (Nat.zero_le ℓ)
  calc
    2 ≤ 2 * ℓ + 2 := by omega
    _ = (2 * ℓ + 2) * 1 := by rw [Nat.mul_one]
    _ ≤ (2 * ℓ + 2) * choose (ℓ + 1) 1 := Nat.mul_le_mul_left _ hone

theorem sphericalHarmonicDimS3_pos (ℓ : ℕ) : 0 < sphericalHarmonicDimS3 ℓ := by
  unfold sphericalHarmonicDimS3
  refine Nat.div_pos (two_le_sphericalHarmonicNumerS3 ℓ) (by decide : 0 < 2)

/-! ## `S⁴`: O-Maxwell extension shell -/

/-- Scalar Laplace–Beltrami eigenvalue on unit `S⁴`, degree `ℓ`: `λ_ℓ = ℓ(ℓ+3)`. -/
def laplaceBeltramiEigenvalueS4 (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + 3)

def laplaceBeltramiEigenvalueS4Nat (ℓ : ℕ) : ℕ :=
  ℓ * (ℓ + 3)

theorem laplaceBeltramiEigenvalueS4Nat_cast (ℓ : ℕ) :
    (laplaceBeltramiEigenvalueS4Nat ℓ : ℝ) = laplaceBeltramiEigenvalueS4 ℓ := by
  simp [laplaceBeltramiEigenvalueS4Nat, laplaceBeltramiEigenvalueS4, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]

/--
Dimension of degree-`ℓ` spherical harmonics on `S⁴`:
`(2ℓ+3) · binom(ℓ+2,2) / 3`.
-/
def sphericalHarmonicDimS4 (ℓ : ℕ) : ℕ :=
  (2 * ℓ + 3) * choose (ℓ + 2) 2 / 3

theorem sphericalHarmonicDimS4_zero : sphericalHarmonicDimS4 0 = 1 := by
  rfl

theorem sphericalHarmonicDimS4_one : sphericalHarmonicDimS4 1 = 5 := by
  rfl

theorem sphericalHarmonicDimS4_two : sphericalHarmonicDimS4 2 = 14 := by
  rfl

private lemma three_le_sphericalHarmonicNumerS4 (ℓ : ℕ) :
    3 ≤ (2 * ℓ + 3) * choose (ℓ + 2) 2 := by
  have hchoose : 1 ≤ choose (ℓ + 2) 2 :=
    Nat.succ_le_iff.mpr (Nat.choose_pos (by omega : 2 ≤ ℓ + 2))
  calc
    3 ≤ 2 * ℓ + 3 := by omega
    _ = (2 * ℓ + 3) * 1 := by rw [Nat.mul_one]
    _ ≤ (2 * ℓ + 3) * choose (ℓ + 2) 2 := Nat.mul_le_mul_left _ hchoose

theorem sphericalHarmonicDimS4_pos (ℓ : ℕ) : 0 < sphericalHarmonicDimS4 ℓ := by
  unfold sphericalHarmonicDimS4
  refine Nat.div_pos (three_le_sphericalHarmonicNumerS4 ℓ) (by decide : 0 < 3)

end Hqiv.Geometry
