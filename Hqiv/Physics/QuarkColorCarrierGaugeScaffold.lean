import Hqiv.Algebra.WeakInComplexStructure
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# Color triplet: complex carrier projection + minimal gauge algebra (scaffold)

This parallels the electroweak **projected complex carrier** story in
`Hqiv.Algebra.WeakInComplexStructure` / `Hqiv.Physics.WeakDoubletCarrierGaugeQuadratic`:

* **Carrier:** the same `WeakComplexOctonionCarrier` (`EuclideanSpace ℂ (Fin 8)`), with an explicit
  inclusion `Fin 3 → ℂ → ℂ⁸` supported on three octonion indices (here `2,3,4` — disjoint from the
  `0,1` chart used for the weak doublet inclusion in `weakDoubletInclCoeff`, so the two pictures do
  not fight over basis slots in this scaffold).
* **Inner product:** slotwise Hermitian sum on `Fin 3 → ℂ`, identified with `weakCarrierCinner` after
  inclusion (`colorTriplet_inner_eq_weakCarrierCinner`).
* **Color gauge (local closure):** the first three Gell–Mann matrices `λ₁,λ₂,λ₃` (Hermitian), scaled to
  `T^a = λ^a/2`, satisfy the same **commutator identity** as an `su(2)` triple:
  `[T¹,T²] = I * T³` (`colorHalfGellMann_comm_12`).
  This is **not** the full eight-generator `su(3)` closure (that belongs with the `G₂` / `so(8)`
  matrix backbone in `Hqiv.Algebra.SMEmbedding` and the heavy Lie-closure targets); it is the
  honest minimal analogue of “prove a generator algebra on the active chart”. The eight-generator
  chart layer (`colorHalfGellMannFull`, `colorSu3fStructure`, `colorTripletCovariantTermFull`) is in
  `Hqiv.Physics.StrongColorSu3ChartClosure`.

Downstream mass scaffolding that uses the outer gauge vev but **not** this inclusion lives in
`Hqiv.Physics.QuarkSectorFromEWGauge`.

**Rindler / φ fiber (strong sector push):** `Hqiv.Physics.StrongColorRapidityFiberBridge` reuses the same
`rindlerDetuningShared` and `phi_of_shell` shell readouts to dress the schematic color covariant slot,
aligning with the “rapidity fiber across DOF” research hook (see that module doc).

**EW-style carrier closure:** `Hqiv.Physics.StrongColorCarrierClosure` defines `colorTripletB` / `colorGellMannEmbed`
(`8 × 8` conjugation) and lifts the chart commutator `colorHalfGellMann_comm_12` to the carrier via
`colorGellMannEmbed_lieBracket` — the same structural pattern as `weakDoubletB` / `weakPauliEmbed`.
-/

open scoped BigOperators InnerProductSpace
open Complex Finset Matrix EuclideanSpace PiLp WithLp
open Hqiv.Algebra

namespace Hqiv.Physics

noncomputable section

/-- Hermitian inner product on the abstract color triplet chart `Fin 3 → ℂ`. -/
def colorTripletHermitianInner (ψ χ : Fin 3 → ℂ) : ℂ :=
  star (ψ 0) * χ 0 + star (ψ 1) * χ 1 + star (ψ 2) * χ 2

/-- Octonion slots carrying the triplet chart in `Fin 8` (disjoint from indices `0,1` in `weakDoubletInclCoeff`). -/
def colorTripletOctonionSlot : Fin 3 → Fin 8
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨4, by decide⟩

/-- Coefficient inclusion `ℂ³ → (Fin 8 → ℂ)` used for `toLp 2` (slots `2,3,4` only; matches `colorTripletOctonionSlot`). -/
noncomputable def colorTripletInclCoeff (ψ : Fin 3 → ℂ) : Fin 8 → ℂ
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => 0
  | ⟨2, _⟩ => ψ 0
  | ⟨3, _⟩ => ψ 1
  | ⟨4, _⟩ => ψ 2

/-- Embedded triplet field in the same `L²(ℂ⁸)` carrier as the electroweak layer. -/
noncomputable def colorTripletToCarrier (ψ : Fin 3 → ℂ) : WeakComplexOctonionCarrier :=
  toLp 2 (colorTripletInclCoeff ψ)

theorem colorTriplet_inner_eq_weakCarrierCinner (ψ χ : Fin 3 → ℂ) :
    weakCarrierCinner (colorTripletToCarrier ψ) (colorTripletToCarrier χ) =
      colorTripletHermitianInner ψ χ := by
  rw [weakCarrierCinner_eq_inner]
  dsimp only [colorTripletToCarrier]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct]
  rw [Fin.sum_univ_eight]
  simp [colorTripletInclCoeff, mul_zero, zero_add, add_zero, colorTripletHermitianInner, mul_comm]

/-! ### Gell–Mann `λ₁,λ₂,λ₃` at half-height (minimal `su(2)` closure inside `su(3)`) -/

/-- `λ₁` (Hermitian). -/
def colorGellMannLambda1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- `λ₂` (Hermitian). -/
def colorGellMannLambda2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -I, 0; I, 0, 0; 0, 0, 0]

/-- `λ₃` (Hermitian). -/
def colorGellMannLambda3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- Matrix commutator on the color triplet chart (`3 × 3`). -/
def lieBracketMat₃ (A B : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  A * B - B * A

/-- Half Gell–Mann generators `T^a = λ^a / 2` on the active `Fin 3` chart. -/
def colorHalfGellMann (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  match a with
  | 0 => ((1 : ℂ) / 2) • colorGellMannLambda1
  | 1 => ((1 : ℂ) / 2) • colorGellMannLambda2
  | 2 => ((1 : ℂ) / 2) • colorGellMannLambda3

/-- Schematic covariant kinetic slot `-i g ∑_a G_a T^a ψ` (one static term, same packaging as `weakDoubletCovariantTerm`). -/
def colorTripletCovariantTerm (g : ℝ) (G : Fin 3 → ℂ) (ψ : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ∑ a : Fin 3, (-I * (g : ℂ) * G a) • (colorHalfGellMann a).mulVec ψ

/-- Same commutator law as the Pauli half-spin `su(2)` normalisation, specialised to the `(λ₁,λ₂,λ₃)` triple. -/
theorem colorHalfGellMann_comm_12 :
    lieBracketMat₃ (colorHalfGellMann 0) (colorHalfGellMann 1) = I • colorHalfGellMann 2 := by
  unfold lieBracketMat₃
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [colorHalfGellMann, colorGellMannLambda1, colorGellMannLambda2, colorGellMannLambda3,
      Matrix.of_apply]; try ring)

end -- noncomputable section

end Hqiv.Physics
