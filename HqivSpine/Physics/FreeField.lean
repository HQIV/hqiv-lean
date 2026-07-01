import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.FreeField` — smeared field operators on a finite Cauchy slice

The Hilbert-space-grounded companion to `Physics.PatchObstruction`: a fixed-time Cauchy slice is
modelled by `Fin n` sites with Hilbert space `LatticeHilbert n = EuclideanSpace ℂ (Fin n)` (the
standard `L²` inner product), and a **diagonal smeared field** `Φ(w) = toEuclideanLin (diagonal w)`
acts site-wise by `Φ(w)ψ i = wᵢ ψ i`.

Results:

* `smearedField_comp` — composition multiplies the site weights (`Φ(f)∘Φ(g) = Φ(f·g)`), so the
  smeared algebra is **abelian** (`smearedField_comm`);
* `opCommutator` — the operator commutator `[A,B] = A∘B − B∘A` on `LatticeHilbert n`, **bilinear**
  in both factors (`opCommutator_sum_univ_first/second`), and vanishing on smeared fields
  (`smearedField_opCommutator_eq_zero`) — operator-level microcausality on the slice;
* `smearedField_comp_eq_zero_of_disjoint` — fields with **disjoint sampling supports** annihilate
  (`Φ(f)∘Φ(g) = 0`), the lattice shadow of spacelike separation;
* `microcausality_in_domain_free_lattice_holds` — unconditional commutativity packaged as a
  reusable microcausality slot.

This is honest free-field scaffolding — it isolates smeared linear operators and their algebra
*before* canonical pairs or dynamics (and `Physics.CCR` already shows no exact `[A,B]=I` exists on
a fixed `Matₙ`). Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.FreeField

open scoped InnerProductSpace
open Matrix

/-- One complex amplitude per lattice site, with the `L²` inner product. -/
abbrev LatticeHilbert (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable section

/-- Diagonal matrix with real site weights `(w i : ℂ)`. -/
noncomputable def smearedMat {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (w i : ℂ))

/-- Smeared field operator `Φ(w)` on `LatticeHilbert n`. -/
noncomputable def smearedField {n : ℕ} (w : Fin n → ℝ) :
    LatticeHilbert n →ₗ[ℂ] LatticeHilbert n :=
  Matrix.toEuclideanLin (smearedMat w)

@[simp]
theorem smearedField_apply {n : ℕ} (w : Fin n → ℝ) (ψ : LatticeHilbert n) (i : Fin n) :
    smearedField w ψ i = (w i : ℂ) * ψ i := by
  simp [smearedField, smearedMat, Matrix.toLpLin_apply, mulVec_diagonal]

theorem smearedField_ext {n : ℕ} {w v : Fin n → ℝ} (h : ∀ i, w i = v i) :
    smearedField w = smearedField v := by
  refine LinearMap.ext fun ψ => PiLp.ext fun i => ?_
  simp [smearedField_apply, h i]

/-- Composition of smeared fields multiplies their site weights. -/
theorem smearedField_comp {n : ℕ} (f g : Fin n → ℝ) :
    smearedField f ∘ₗ smearedField g = smearedField (fun i => f i * g i) := by
  refine LinearMap.ext fun ψ => PiLp.ext fun i => ?_
  simp only [LinearMap.comp_apply, smearedField_apply]
  push_cast
  ring

/-- The diagonal smeared algebra is **abelian**. -/
theorem smearedField_comm {n : ℕ} (f g : Fin n → ℝ) :
    smearedField f ∘ₗ smearedField g = smearedField g ∘ₗ smearedField f := by
  rw [smearedField_comp, smearedField_comp]
  exact smearedField_ext fun i => mul_comm _ _

/-- Operator commutator `[A,B] = A∘B − B∘A` on `LatticeHilbert n`. -/
noncomputable def opCommutator {n : ℕ} (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    LatticeHilbert n →ₗ[ℂ] LatticeHilbert n :=
  A ∘ₗ B - B ∘ₗ A

@[simp]
theorem opCommutator_apply {n : ℕ} (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)
    (ψ : LatticeHilbert n) : opCommutator A B ψ = A (B ψ) - B (A ψ) := rfl

theorem opCommutator_zero_left {n : ℕ} (B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (0 : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) B = 0 := by
  unfold opCommutator; simp

theorem opCommutator_smul_left {n : ℕ} (r : ℂ) (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (r • A) B = r • opCommutator A B := by
  unfold opCommutator
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

theorem opCommutator_add_left {n : ℕ} (A₁ A₂ B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (A₁ + A₂) B = opCommutator A₁ B + opCommutator A₂ B := by
  unfold opCommutator
  rw [LinearMap.add_comp, LinearMap.comp_add, sub_add_sub_comm]

/-- **Linearity of the commutator in the first factor.** -/
theorem opCommutator_sum_univ_first {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (A : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n))
    (B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (∑ i, c i • A i) B = ∑ i, c i • opCommutator (A i) B := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simp [opCommutator_zero_left]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opCommutator_add_left, ih,
      opCommutator_smul_left]

theorem opCommutator_zero_right {n : ℕ} (A : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (0 : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) = 0 := by
  unfold opCommutator; simp

theorem opCommutator_smul_right {n : ℕ} (r : ℂ) (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (r • B) = r • opCommutator A B := by
  unfold opCommutator
  rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_sub]

theorem opCommutator_add_right {n : ℕ} (A B₁ B₂ : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (B₁ + B₂) = opCommutator A B₁ + opCommutator A B₂ := by
  unfold opCommutator
  rw [LinearMap.comp_add, LinearMap.add_comp, sub_add_sub_comm]

/-- **Linearity of the commutator in the second factor.** -/
theorem opCommutator_sum_univ_second {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (A : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)
    (B : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)) :
    opCommutator A (∑ i, c i • B i) = ∑ i, c i • opCommutator A (B i) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · simp [opCommutator_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opCommutator_add_right, ih,
      opCommutator_smul_right]

/-- **Operator microcausality:** diagonal smeared fields commute, so their commutator vanishes. -/
theorem smearedField_opCommutator_eq_zero {n : ℕ} (f g : Fin n → ℝ) :
    opCommutator (smearedField f) (smearedField g) = 0 := by
  unfold opCommutator
  rw [smearedField_comm, sub_self]

/-- Pointwise disjoint supports: at each site at least one weight vanishes. -/
def DisjointSamplingSupport {n : ℕ} (f g : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, f i = 0 ∨ g i = 0

theorem smearedField_zero {n : ℕ} : smearedField (fun _ : Fin n => (0 : ℝ)) = 0 := by
  refine LinearMap.ext fun ψ => PiLp.ext fun i => ?_
  simp [smearedField_apply]

/-- **Disjoint supports annihilate:** spacelike-separated lattice fields compose to `0`. -/
theorem smearedField_comp_eq_zero_of_disjoint {n : ℕ} {f g : Fin n → ℝ}
    (h : DisjointSamplingSupport f g) : smearedField f ∘ₗ smearedField g = 0 := by
  rw [smearedField_comp]
  have hfg : (fun i : Fin n => f i * g i) = fun _ : Fin n => (0 : ℝ) := by
    funext i
    rcases h i with hf | hg
    · simp [hf]
    · simp [hg]
  rw [hfg]; exact smearedField_zero

/-- Unconditional commutativity of all smeared lattice fields (abelian microcausality slot). -/
def microcausality_in_domain_free_lattice : Prop :=
  ∀ (n : ℕ) (f g : Fin n → ℝ),
    smearedField f ∘ₗ smearedField g = smearedField g ∘ₗ smearedField f

theorem microcausality_in_domain_free_lattice_holds : microcausality_in_domain_free_lattice :=
  fun _ _ _ => smearedField_comm _ _

end

end HqivSpine.Physics.FreeField
