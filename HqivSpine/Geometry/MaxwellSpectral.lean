import HqivSpine.Foundation.ThreeGrowth
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Geometry.MaxwellSpectral` — Maxwell carrier spectra on `S³` and `S⁴`

The four-component electromagnetic / quaternionic block (the `Fin 4` restriction of the octonion
carrier) lives on its compact phase manifold: the **unit quaternions `S³ ⊂ ℝ⁴ ≅ ℍ`**. Scalar
spherical harmonics on `S³` have Laplace–Beltrami eigenvalues `λ_ℓ = ℓ(ℓ+2)` and degeneracy
`(ℓ+1)²` — the *same* `(ℓ+1)²` square that the spine's `S²` mode count (`Geometry.SphericalHarmonics`)
runs against. Viewing the octonion split as "quaternions plus one Cayley–Dickson direction" gives the
O-Maxwell extension on **`S⁴ ⊂ ℝ⁵`**, with `λ_ℓ = ℓ(ℓ+3)`.

This is spectral geometry only (not a claim that O-Maxwell dynamics reduce to a scalar Laplacian).
The general degeneracy for unit `Sᵈ` is `dim ℋ_ℓ = (2ℓ+d−1)·C(ℓ+d−2, d−2)/(d−1)`.

Mathlib + foundation only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Geometry.MaxwellSpectral

open Nat HqivSpine.Foundation

/-! ## `S³`: the quaternion / classic-Maxwell carrier (intrinsic dim `3 = transverseDim`) -/

/-- The `S³` carrier has intrinsic dimension `transverseDim = 3`. -/
theorem s3_intrinsic_dim : transverseDim = 3 := rfl

/-- Scalar Laplace–Beltrami eigenvalue on unit `S³`, degree `ℓ`: `λ_ℓ = ℓ(ℓ+2)`. -/
def eigenvalueS3 (ℓ : ℕ) : ℝ := (ℓ : ℝ) * ((ℓ : ℝ) + 2)

/-- Same eigenvalue as a natural number (exact arithmetic). -/
def eigenvalueS3Nat (ℓ : ℕ) : ℕ := ℓ * (ℓ + 2)

theorem eigenvalueS3Nat_cast (ℓ : ℕ) : (eigenvalueS3Nat ℓ : ℝ) = eigenvalueS3 ℓ := by
  simp [eigenvalueS3Nat, eigenvalueS3, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]

/-- Degree-`ℓ` harmonic degeneracy on `S³`: `(2ℓ+2)·C(ℓ+1,1)/2 = (ℓ+1)²`. -/
def harmonicDimS3 (ℓ : ℕ) : ℕ := (2 * ℓ + 2) * choose (ℓ + 1) 1 / 2

theorem harmonicDimS3_eq_succ_sq (ℓ : ℕ) : harmonicDimS3 ℓ = (ℓ + 1) ^ 2 := by
  unfold harmonicDimS3
  rw [Nat.choose_one_right, show 2 * ℓ + 2 = 2 * (ℓ + 1) by omega,
    Nat.mul_assoc, Nat.mul_div_cancel_left ((ℓ + 1) * (ℓ + 1)) (by decide : 0 < 2)]
  simp [Nat.pow_two]

theorem harmonicDimS3_zero : harmonicDimS3 0 = 1 := by rw [harmonicDimS3_eq_succ_sq]; rfl
theorem harmonicDimS3_one : harmonicDimS3 1 = 4 := by rw [harmonicDimS3_eq_succ_sq]; rfl
theorem harmonicDimS3_two : harmonicDimS3 2 = 9 := by rw [harmonicDimS3_eq_succ_sq]; rfl

theorem harmonicDimS3_pos (ℓ : ℕ) : 0 < harmonicDimS3 ℓ := by
  rw [harmonicDimS3_eq_succ_sq]; positivity

/-! ## `S⁴`: the O-Maxwell extension shell -/

/-- Scalar Laplace–Beltrami eigenvalue on unit `S⁴`, degree `ℓ`: `λ_ℓ = ℓ(ℓ+3)`. -/
def eigenvalueS4 (ℓ : ℕ) : ℝ := (ℓ : ℝ) * ((ℓ : ℝ) + 3)

def eigenvalueS4Nat (ℓ : ℕ) : ℕ := ℓ * (ℓ + 3)

theorem eigenvalueS4Nat_cast (ℓ : ℕ) : (eigenvalueS4Nat ℓ : ℝ) = eigenvalueS4 ℓ := by
  simp [eigenvalueS4Nat, eigenvalueS4, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]

/-- Degree-`ℓ` harmonic degeneracy on `S⁴`: `(2ℓ+3)·C(ℓ+2,2)/3`. -/
def harmonicDimS4 (ℓ : ℕ) : ℕ := (2 * ℓ + 3) * choose (ℓ + 2) 2 / 3

theorem harmonicDimS4_zero : harmonicDimS4 0 = 1 := rfl
theorem harmonicDimS4_one : harmonicDimS4 1 = 5 := rfl
theorem harmonicDimS4_two : harmonicDimS4 2 = 14 := rfl

private lemma three_le_numerS4 (ℓ : ℕ) : 3 ≤ (2 * ℓ + 3) * choose (ℓ + 2) 2 := by
  have hchoose : 1 ≤ choose (ℓ + 2) 2 :=
    Nat.succ_le_iff.mpr (Nat.choose_pos (by omega : 2 ≤ ℓ + 2))
  calc 3 ≤ 2 * ℓ + 3 := by omega
    _ = (2 * ℓ + 3) * 1 := (Nat.mul_one _).symm
    _ ≤ (2 * ℓ + 3) * choose (ℓ + 2) 2 := Nat.mul_le_mul_left _ hchoose

theorem harmonicDimS4_pos (ℓ : ℕ) : 0 < harmonicDimS4 ℓ :=
  Nat.div_pos (three_le_numerS4 ℓ) (by decide : 0 < 3)

end HqivSpine.Geometry.MaxwellSpectral
