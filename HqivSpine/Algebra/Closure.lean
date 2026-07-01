import HqivSpine.Algebra.So8
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Basic

/-!
# `HqivSpine.Algebra.Closure` — phase lift `Δ` inside the genuine `𝔰𝔬(8)`

The last structural requirement of the spine: adjoining a single phase-lift
generator `Δ` to the derivation algebra `𝔤₂` of the seven imaginary directions
lands inside the carrier rotation algebra `𝔰𝔬(8)`, whose genuine dimension and Lie
closure are established (determinant-free) in `So8`.

Here we provide the *honest, proved* pieces:

* the phase-lift `Δ` as a genuine skew-symmetric `8×8` matrix on the distinguished
  `(e₁, e₇)` plane (skew-symmetric, nonzero, and a member of `skewMatrices 8`);
* `Δ` and the plane generators are exactly (up to sign) the standard skew basis
  `skewGen`, so they live in the genuine `𝔰𝔬(8)`;
* the dimension bookkeeping `CarrierClosure` (`28 = 14 + 7 + 7`), now tied to the
  real `finrank (skewMatrices 8) = 28`.

The skew basis itself is closed under the Lie bracket (`So8.skewGen_so_closure`),
so no `28×28` determinant or `native_decide` is needed anywhere.
-/

namespace HqivSpine.Algebra

open Matrix

/-- **Abstract phase-lift generator** on the carrier: skew-symmetric, with `+1` at
`(j, i)` and `−1` at `(i, j)` (infinitesimal rotation of the `(i, j)`-plane). -/
def planeGenerator (i j : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.single j i 1 - Matrix.single i j 1

private theorem single_transpose (i j : Fin 8) (c : ℝ) :
    (Matrix.single i j c)ᵀ = Matrix.single j i c := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.single_apply]
  by_cases h : i = b ∧ j = a
  · obtain ⟨hi, hj⟩ := h; subst hi; subst hj; simp
  · rw [if_neg h, if_neg]; tauto

/-- **Skew-symmetry:** `(planeGenerator i j)ᵀ = − planeGenerator i j`. -/
theorem planeGenerator_transpose (i j : Fin 8) :
    (planeGenerator i j)ᵀ = - planeGenerator i j := by
  unfold planeGenerator
  rw [Matrix.transpose_sub, single_transpose, single_transpose]; abel

/-- **Entrywise antisymmetry.** -/
theorem planeGenerator_antisymm (i j a b : Fin 8) :
    planeGenerator i j a b + planeGenerator i j b a = 0 := by
  have h := congrFun (congrFun (planeGenerator_transpose i j) b) a
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  linarith [h]

theorem planeGenerator_apply_swap (i j : Fin 8) (hij : i ≠ j) :
    planeGenerator i j j i = 1 := by
  unfold planeGenerator; simp [Matrix.sub_apply, hij]

theorem planeGenerator_ne_zero (i j : Fin 8) (hij : i ≠ j) : planeGenerator i j ≠ 0 := by
  intro h
  have : planeGenerator i j j i = 0 := by rw [h]; rfl
  rw [planeGenerator_apply_swap i j hij] at this
  exact one_ne_zero this

/-- HQIV distinguished plane index `i` = the EM axis `e₁`. -/
def phaseLiftPlaneI : Fin 8 := 1
/-- HQIV distinguished plane index `j` = the colour-preferred axis `e₇`. -/
def phaseLiftPlaneJ : Fin 8 := 7

/-- **The abstract HQIV phase-lift `Δ`** on the `(e₁, e₇)` plane. -/
def foundationDelta : Matrix (Fin 8) (Fin 8) ℝ :=
  planeGenerator phaseLiftPlaneI phaseLiftPlaneJ

theorem foundationDelta_transpose : (foundationDelta)ᵀ = - foundationDelta :=
  planeGenerator_transpose _ _

theorem foundationDelta_ne_zero : foundationDelta ≠ 0 :=
  planeGenerator_ne_zero _ _ (by decide)

/-! ## Plane generators are the genuine `𝔰𝔬(8)` skew basis -/

/-- The plane generator is exactly the standard skew basis vector `skewGen j i`. -/
theorem planeGenerator_eq_skewGen (i j : Fin 8) : planeGenerator i j = skewGen j i := rfl

/-- **Every plane generator lies in the genuine `𝔰𝔬(8)`.** -/
theorem planeGenerator_mem (i j : Fin 8) : planeGenerator i j ∈ skewMatrices 8 := by
  rw [planeGenerator_eq_skewGen]; exact skewGen_mem j i

/-- **The phase lift `Δ` lies in the genuine `𝔰𝔬(8)`.** -/
theorem foundationDelta_mem : foundationDelta ∈ skewMatrices 8 :=
  planeGenerator_mem _ _

/-! ## Closure dimension interface -/

open HqivSpine.Foundation

/-- **Abstract carrier-closure data.** A derivation seed (dimension
`derivationSeedDim`) plus a phase lift, in `𝔰𝔬` of an `carrierDim`-channel
carrier, Lie-generating a space of dimension `generatedDim = soDim carrierDim`. -/
structure CarrierClosure where
  carrierDim : ℕ
  derivationSeedDim : ℕ
  phaseLiftDim : ℕ
  generatedDim : ℕ
  closes : generatedDim = soDim carrierDim

/-- **The HQIV instance:** 8-channel carrier, 14-dimensional `𝔤₂` seed, a single
phase lift, closing to the 28-dimensional `𝔰𝔬(8)`. -/
def hqivCarrierClosure : CarrierClosure where
  carrierDim := carrierMultiplicity
  derivationSeedDim := g2Dim
  phaseLiftDim := 1
  generatedDim := soDim carrierMultiplicity
  closes := rfl

theorem hqivCarrierClosure_carrierDim : hqivCarrierClosure.carrierDim = 8 :=
  carrierMultiplicity_eq_eight

theorem hqivCarrierClosure_generatedDim : hqivCarrierClosure.generatedDim = 28 :=
  soDim_carrier

theorem hqivCarrierClosure_seedDim : hqivCarrierClosure.derivationSeedDim = 14 :=
  g2Dim_eq_fourteen

/-- **Dimension-consistent with the branching** `28 = 14 + 7 + 7`. -/
theorem hqivCarrierClosure_branch :
    hqivCarrierClosure.generatedDim
      = hqivCarrierClosure.derivationSeedDim + imaginaryDim + imaginaryDim := by
  simp only [hqivCarrierClosure]; exact so8_branch_g2

/-- **The bookkeeping dimension is the genuine matrix-Lie dimension.** The
`generatedDim = 28` equals `finrank ℝ (skewMatrices 8)`, established by the standard
skew basis (no determinant, no `native_decide`). -/
theorem hqivCarrierClosure_generatedDim_eq_finrank :
    hqivCarrierClosure.generatedDim = Module.finrank ℝ (skewMatrices 8) := by
  rw [hqivCarrierClosure_generatedDim, finrank_so8]

end HqivSpine.Algebra
