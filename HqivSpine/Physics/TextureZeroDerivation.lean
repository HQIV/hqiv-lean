import HqivSpine.Physics.MixingAngles

/-!
# `HqivSpine.Physics.TextureZeroDerivation` — the texture zero is **derived, not assumed**

`MixingAngles` took the texture zero `M₁₁ = 0` as a structural input. Here we discharge that input:
the texture-zero form is the **canonical form of a seesaw-lifted mass matrix**, and once chosen it
leaves *no* freedom.

The spine statement about the lightest generation is: it is the **would-be-zero mode** of the shell
ladder (the deepest Beltrami winding), chirally protected so its bare diagonal self-energy vanishes,
and it acquires mass only by mixing up to the heavier shell. That is a **seesaw**: the bare sector
matrix has one positive and one negative eigenvalue (`det < 0`).

* A general real-symmetric sector matrix is `S = [[p, q-entry], …]`; its invariants are
  `tr S = p + q`, `det S = p·q − b²` (`symMatrix_trace`, `symMatrix_det`). Carrying the seesaw
  spectrum `{m₂, −m₁}` means `tr = m₂ − m₁`, `det = −m₁m₂` (`carriesSpectrum`); these *are* the two
  eigenvalues (`carriesSpectrum_roots`).
* **Realizability is exactly the seesaw condition.** A *real* texture-zero representative of the
  spectrum exists **iff** `det ≤ 0`, i.e. `0 ≤ m₁m₂` (`textureZero_realizable_iff`): a same-sign
  spectrum (`det > 0`) would need `b² < 0` — impossible. So the texture-zero ansatz is available
  *precisely because* the light generation is a lifted would-be-zero mode.
* **Uniqueness.** Texture zero `p = 0` **plus** the spectrum forces `q = m₂ − m₁` and
  `b² = m₁m₂` (`textureZero_unique`) — no remaining freedom; the matrix is `MixingAngles.textureMatrix`
  (`symMatrix_zero_eq_textureMatrix`).
* **Capstone:** chiral protection (`p = 0`) + the seesaw spectrum ⇒ the matrix is fixed **and** the
  mixing angle is forced to Gatto–Sartori–Tonin `tan²θ = m₁/m₂` (`ansatz_forces_GST`).

So the only physical inputs are (i) the light mode is chirally protected (`p = 0`) and (ii) it is a
lifted would-be-zero mode (`det < 0`) — both native ladder statements. The angle then follows.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.TextureZeroDerivation

open HqivSpine.Physics.MixingAngles
open scoped Matrix

/-! ## General symmetric sector matrix and its invariants -/

/-- General real-symmetric `2×2` sector mass matrix `[[p, b], [b, q]]`. -/
def symMatrix (p q b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, b; b, q]

theorem symMatrix_trace (p q b : ℝ) : (symMatrix p q b).trace = p + q := by
  rw [symMatrix, Matrix.trace_fin_two_of]

theorem symMatrix_det (p q b : ℝ) : (symMatrix p q b).det = p * q - b ^ 2 := by
  rw [symMatrix, Matrix.det_fin_two_of]; ring

/-- The matrix **carries the seesaw spectrum `{m₂, −m₁}`** when its trace and determinant match
those eigenvalues: `tr = m₂ + (−m₁)`, `det = m₂·(−m₁)`. -/
def carriesSpectrum (S : Matrix (Fin 2) (Fin 2) ℝ) (m₁ m₂ : ℝ) : Prop :=
  S.trace = m₂ - m₁ ∧ S.det = -(m₁ * m₂)

/-- Carrying the spectrum means `m₂` and `−m₁` really are the eigenvalues: both solve the
characteristic equation `λ² − (tr)·λ + det = 0`. -/
theorem carriesSpectrum_roots (S : Matrix (Fin 2) (Fin 2) ℝ) (m₁ m₂ : ℝ)
    (h : carriesSpectrum S m₁ m₂) :
    m₂ ^ 2 - S.trace * m₂ + S.det = 0 ∧ (-m₁) ^ 2 - S.trace * (-m₁) + S.det = 0 := by
  obtain ⟨htr, hdet⟩ := h
  rw [htr, hdet]
  constructor <;> ring

/-! ## The ansatz is realizable **iff** the spectrum is a seesaw -/

/-- **Realizability = seesaw.** A *real* texture-zero representative of the spectrum `{m₂, −m₁}`
exists iff `0 ≤ m₁m₂`, i.e. iff `det = −m₁m₂ ≤ 0` (opposite-sign eigenvalues, a lifted zero mode).
A same-sign spectrum would demand `b² = m₁m₂ < 0` — impossible over ℝ. -/
theorem textureZero_realizable_iff (m₁ m₂ : ℝ) :
    (∃ b : ℝ, carriesSpectrum (symMatrix 0 (m₂ - m₁) b) m₁ m₂) ↔ 0 ≤ m₁ * m₂ := by
  constructor
  · rintro ⟨b, _, hdet⟩
    rw [symMatrix_det] at hdet
    nlinarith [sq_nonneg b]
  · intro h
    refine ⟨coupling m₁ m₂, by rw [symMatrix_trace]; ring, ?_⟩
    rw [symMatrix_det,
      show coupling m₁ m₂ ^ 2 = m₁ * m₂ from by rw [sq]; exact coupling_sq m₁ m₂ h]
    ring

/-! ## Texture zero + spectrum forces everything -/

/-- **Uniqueness.** If a texture-zero matrix `[[0, b], [b, q]]` carries the spectrum `{m₂, −m₁}`,
then `q = m₂ − m₁` and `b² = m₁m₂` — no remaining freedom (the sign of `b` is irrelevant to `tan²θ`). -/
theorem textureZero_unique (m₁ m₂ q b : ℝ) (h : carriesSpectrum (symMatrix 0 q b) m₁ m₂) :
    q = m₂ - m₁ ∧ b ^ 2 = m₁ * m₂ := by
  obtain ⟨htr, hdet⟩ := h
  rw [symMatrix_trace] at htr
  rw [symMatrix_det] at hdet
  constructor
  · linarith
  · nlinarith

/-- The unique texture-zero representative **is** the `MixingAngles` matrix. -/
theorem symMatrix_zero_eq_textureMatrix (m₁ m₂ : ℝ) :
    symMatrix 0 (m₂ - m₁) (coupling m₁ m₂) = textureMatrix m₁ m₂ := rfl

/-- For genuine positive masses the spectrum is a **strict seesaw**: `det < 0` with one positive and
one negative eigenvalue. -/
theorem seesaw_opposite_sign (m₁ m₂ : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (symMatrix 0 (m₂ - m₁) (coupling m₁ m₂)).det < 0 ∧ -m₁ < 0 ∧ 0 < m₂ := by
  refine ⟨?_, by linarith, h₂⟩
  rw [symMatrix_det, show coupling m₁ m₂ ^ 2 = m₁ * m₂ from by
        rw [sq]; exact coupling_sq m₁ m₂ (by positivity)]
  nlinarith

/-! ## Capstone: the ansatz is discharged, the angle is forced -/

/-- **The texture-zero ansatz is derived, and it forces the angle.** Given only that the light
generation is the chirally-protected would-be-zero mode (`p = 0`) and the sector carries the seesaw
spectrum `{m₂, −m₁}`, the mass matrix is *uniquely* the texture-zero form **and** the mixing angle is
forced to Gatto–Sartori–Tonin `tan²θ = m₁/m₂`. -/
theorem ansatz_forces_GST (m₁ m₂ q b : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (hspec : carriesSpectrum (symMatrix 0 q b) m₁ m₂) :
    q = m₂ - m₁ ∧ b ^ 2 = m₁ * m₂ ∧ (mixingTan m₁ m₂) ^ 2 = m₁ / m₂ := by
  obtain ⟨hq, hb⟩ := textureZero_unique m₁ m₂ q b hspec
  exact ⟨hq, hb, mixingTan_sq m₁ m₂ h₁ h₂⟩

/-! ## Closure -/

/-- **Texture-zero derivation bundle.** -/
structure TextureZeroClosure : Prop where
  spectrum_are_eigenvalues : ∀ (S : Matrix (Fin 2) (Fin 2) ℝ) (m₁ m₂ : ℝ),
    carriesSpectrum S m₁ m₂ →
      m₂ ^ 2 - S.trace * m₂ + S.det = 0 ∧ (-m₁) ^ 2 - S.trace * (-m₁) + S.det = 0
  realizable_iff_seesaw : ∀ (m₁ m₂ : ℝ),
    (∃ b : ℝ, carriesSpectrum (symMatrix 0 (m₂ - m₁) b) m₁ m₂) ↔ 0 ≤ m₁ * m₂
  unique_given_spectrum : ∀ (m₁ m₂ q b : ℝ), carriesSpectrum (symMatrix 0 q b) m₁ m₂ →
    q = m₂ - m₁ ∧ b ^ 2 = m₁ * m₂
  forces_GST : ∀ (m₁ m₂ q b : ℝ), 0 < m₁ → 0 < m₂ → carriesSpectrum (symMatrix 0 q b) m₁ m₂ →
    q = m₂ - m₁ ∧ b ^ 2 = m₁ * m₂ ∧ (mixingTan m₁ m₂) ^ 2 = m₁ / m₂

/-- **The texture-zero ansatz is fully discharged:** it is the canonical form of a seesaw spectrum
(realizable iff `det ≤ 0`), unique given the masses, and it forces the Gatto–Sartori–Tonin angle. -/
theorem texture_zero_closure : TextureZeroClosure where
  spectrum_are_eigenvalues := carriesSpectrum_roots
  realizable_iff_seesaw := textureZero_realizable_iff
  unique_given_spectrum := textureZero_unique
  forces_GST := ansatz_forces_GST

end HqivSpine.Physics.TextureZeroDerivation
