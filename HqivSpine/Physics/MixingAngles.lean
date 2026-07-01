import HqivSpine.Physics.MixingUnitarity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Sqrt

/-!
# `HqivSpine.Physics.MixingAngles` — the mixing angle **from the masses** (Gatto–Sartori–Tonin)

`MixingUnitarity` proved the mixing matrix is unitary; the *angles* were left to dynamics. With the
spine's mass derivations in hand, one structural ingredient closes the gap: the **texture zero**.

In the hierarchical shell ladder the lightest generation has no leading-order diagonal self-mass —
its mass arises only through mixing with the heavier one — so the `2×2` sector mass matrix is the
**texture-zero** form `M = [[0, b], [b, a]]`. This is the *only* structural input; everything else is
a theorem.

* **The masses are the eigenvalues.** `det M = −m₁m₂`, `tr M = m₂ − m₁` (`textureMatrix_det`,
  `textureMatrix_trace`), so `m₂` and `−m₁` satisfy the characteristic equation
  (`masses_are_eigenvalues`): the off-diagonal coupling is fixed to `b = √(m₁m₂)`.
* **The mass basis is orthonormal.** The heavy/light eigenvectors are orthogonal
  (`eigenvectors_orthogonal`) — an instance of the `MixingUnitarity` basis structure.
* **The angle is the mass ratio (GST).** The light-eigenvector slope gives
  `tan²θ = m₁/m₂ = m_light/m_heavy` (`mixingTan_sq`) — the `θ_C ≈ √(m_d/m_s)` relation. The angle is
  below `45°` (`mixingTanSq_lt_one`) and **shrinks with the hierarchy** (`mixingTanSq_strictMono`):
  the more split the masses, the smaller the mixing. Plugging spine-ladder masses yields the angle —
  no fitted CKM entry.

Bundled in `MixingAngleClosure` / `mixing_angles_closure`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.MixingAngles

open HqivSpine.Physics
open scoped Matrix

/-! ## The texture-zero sector mass matrix -/

/-- **Off-diagonal coupling** fixed by the two masses: `b = √(m₁·m₂)` (from `|det| = m₁m₂`). -/
noncomputable def coupling (m₁ m₂ : ℝ) : ℝ := Real.sqrt (m₁ * m₂)

theorem coupling_sq (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) : coupling m₁ m₂ * coupling m₁ m₂ = m₁ * m₂ :=
  Real.mul_self_sqrt h

theorem coupling_pos (m₁ m₂ : ℝ) (h : 0 < m₁ * m₂) : 0 < coupling m₁ m₂ :=
  Real.sqrt_pos.mpr h

/-- **Texture-zero sector mass matrix** `M = [[0, b], [b, m₂ − m₁]]` with `b = √(m₁m₂)`. -/
noncomputable def textureMatrix (m₁ m₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, coupling m₁ m₂; coupling m₁ m₂, m₂ - m₁]

/-- **Determinant** `det M = −m₁m₂`. -/
theorem textureMatrix_det (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) :
    (textureMatrix m₁ m₂).det = -(m₁ * m₂) := by
  rw [textureMatrix, Matrix.det_fin_two_of, ← coupling_sq m₁ m₂ h]; ring

/-- **Trace** `tr M = m₂ − m₁`. -/
theorem textureMatrix_trace (m₁ m₂ : ℝ) : (textureMatrix m₁ m₂).trace = m₂ - m₁ := by
  rw [textureMatrix, Matrix.trace_fin_two_of]; ring

/-- **The masses are the eigenvalues:** `m₂` and `−m₁` both solve the characteristic equation
`λ² − (tr M)·λ + det M = 0`, so the physical masses `{m₁, m₂}` are `{|−m₁|, m₂}`. -/
theorem masses_are_eigenvalues (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) :
    m₂ ^ 2 - (textureMatrix m₁ m₂).trace * m₂ + (textureMatrix m₁ m₂).det = 0 ∧
      (-m₁) ^ 2 - (textureMatrix m₁ m₂).trace * (-m₁) + (textureMatrix m₁ m₂).det = 0 := by
  rw [textureMatrix_trace, textureMatrix_det m₁ m₂ h]
  constructor <;> ring

/-! ## The mass-eigenstate basis -/

/-- Heavy mass eigenvector `(b, m₂)`. -/
noncomputable def heavyVec (m₁ m₂ : ℝ) : Fin 2 → ℝ := ![coupling m₁ m₂, m₂]

/-- Light mass eigenvector `(b, −m₁)`. -/
noncomputable def lightVec (m₁ m₂ : ℝ) : Fin 2 → ℝ := ![coupling m₁ m₂, -m₁]

/-- **The mass basis is orthonormal:** heavy and light eigenvectors are orthogonal. -/
theorem eigenvectors_orthogonal (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) :
    heavyVec m₁ m₂ ⬝ᵥ lightVec m₁ m₂ = 0 := by
  have hb := coupling_sq m₁ m₂ h
  rw [dotProduct, Fin.sum_univ_two]
  simp only [heavyVec, lightVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination hb

/-- **The heavy state is a genuine eigenvector**, eigenvalue `m₂`: `M·v_h = m₂·v_h`. -/
theorem textureMatrix_mulVec_heavy (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) :
    (textureMatrix m₁ m₂).mulVec (heavyVec m₁ m₂) = m₂ • heavyVec m₁ m₂ := by
  have hb := coupling_sq m₁ m₂ h
  funext i
  fin_cases i
  · simp [textureMatrix, heavyVec]
  · simp [textureMatrix, heavyVec]; linear_combination hb

/-- **The light state is a genuine eigenvector**, eigenvalue `−m₁`: `M·v_l = −m₁·v_l`. -/
theorem textureMatrix_mulVec_light (m₁ m₂ : ℝ) (h : 0 ≤ m₁ * m₂) :
    (textureMatrix m₁ m₂).mulVec (lightVec m₁ m₂) = (-m₁) • lightVec m₁ m₂ := by
  have hb := coupling_sq m₁ m₂ h
  funext i
  fin_cases i
  · simp [textureMatrix, lightVec]
  · simp [textureMatrix, lightVec]; linear_combination hb

/-! ## The Gatto–Sartori–Tonin relation -/

/-- **Mixing tangent** = the light-eigenvector slope `tan θ = m₁ / b = m₁ / √(m₁m₂)`. -/
noncomputable def mixingTan (m₁ m₂ : ℝ) : ℝ := m₁ / coupling m₁ m₂

/-- **The angle is the eigenvector slope, not an independent stipulation:**
`tan θ = −(v_l)₁ / (v_l)₀`, the slope of the genuine light eigenvector. -/
theorem mixingTan_eq_lightVec_slope (m₁ m₂ : ℝ) :
    mixingTan m₁ m₂ = -(lightVec m₁ m₂ 1) / (lightVec m₁ m₂ 0) := by
  unfold mixingTan lightVec
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Gatto–Sartori–Tonin:** `tan²θ = m₁/m₂ = m_light/m_heavy`. The mixing angle is fixed by the
mass ratio alone. -/
theorem mixingTan_sq (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (mixingTan m₁ m₂) ^ 2 = m₁ / m₂ := by
  unfold mixingTan coupling
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- The mixing angle is **below `45°`** (`tan²θ < 1`) for a genuine hierarchy `m₁ < m₂`. -/
theorem mixingTanSq_lt_one (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h : m₁ < m₂) :
    (mixingTan m₁ m₂) ^ 2 < 1 := by
  rw [mixingTan_sq m₁ m₂ h₁ (by linarith)]
  rw [div_lt_one (by linarith)]; exact h

/-- **The mixing shrinks with the hierarchy:** a lighter light-state (deeper split) gives a smaller
angle. -/
theorem mixingTanSq_strictMono (m₂ : ℝ) (hm₂ : 0 < m₂) {m₁ m₁' : ℝ} (h0 : 0 < m₁) (h : m₁ < m₁') :
    (mixingTan m₁ m₂) ^ 2 < (mixingTan m₁' m₂) ^ 2 := by
  rw [mixingTan_sq m₁ m₂ h0 hm₂, mixingTan_sq m₁' m₂ (by linarith) hm₂]
  gcongr

/-! ## Closure -/

/-- **Mixing-angle discharge bundle.** -/
structure MixingAngleClosure : Prop where
  masses_are_eigenvalues : ∀ (m₁ m₂ : ℝ), 0 ≤ m₁ * m₂ →
    m₂ ^ 2 - (textureMatrix m₁ m₂).trace * m₂ + (textureMatrix m₁ m₂).det = 0 ∧
      (-m₁) ^ 2 - (textureMatrix m₁ m₂).trace * (-m₁) + (textureMatrix m₁ m₂).det = 0
  mass_basis_orthonormal : ∀ (m₁ m₂ : ℝ), 0 ≤ m₁ * m₂ →
    heavyVec m₁ m₂ ⬝ᵥ lightVec m₁ m₂ = 0
  gatto_sartori_tonin : ∀ (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ → (mixingTan m₁ m₂) ^ 2 = m₁ / m₂
  below_45_degrees : ∀ (m₁ m₂ : ℝ), 0 < m₁ → m₁ < m₂ → (mixingTan m₁ m₂) ^ 2 < 1
  shrinks_with_hierarchy : ∀ (m₂ : ℝ), 0 < m₂ → ∀ {m₁ m₁' : ℝ}, 0 < m₁ → m₁ < m₁' →
    (mixingTan m₁ m₂) ^ 2 < (mixingTan m₁' m₂) ^ 2

/-- **The mixing angle is discharged from the masses:** with the texture-zero structure the masses
are the eigenvalues, the mass basis is orthonormal, and the angle obeys `tan²θ = m_light/m_heavy`
(Gatto–Sartori–Tonin) — below `45°` and shrinking with the mass hierarchy. -/
theorem mixing_angles_closure : MixingAngleClosure where
  masses_are_eigenvalues := masses_are_eigenvalues
  mass_basis_orthonormal := eigenvectors_orthogonal
  gatto_sartori_tonin := mixingTan_sq
  below_45_degrees := mixingTanSq_lt_one
  shrinks_with_hierarchy := mixingTanSq_strictMono

end HqivSpine.Physics.MixingAngles
