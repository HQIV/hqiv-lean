import Hqiv.Story.MillenniumBridgePatchPoincareWightman
import Hqiv.GeneratorsFromAxioms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.ENNReal.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# First non-abelian smeared field on the patch carrier

`PatchHilbert = ℓ²(ℂ⁴)` (real dimension `8`) already hosts the abelian / jet
`patchDerivOVD` layer. This file adds a **genuinely non-abelian** smearing using the
proved HQIV matrix generators `Hqiv.so8Generator k : Matrix (Fin 8) (Fin 8) ℝ` on the
**same** real `8`-dimensional model.

For each `k : Fin 28` we transport the `8×8` endomorphism
`Matrix.toEuclideanLin (Hqiv.so8Generator k)` on `Euclidean ℝ (Fin 8)` along the
standard `ℝ`-linear isometry
`ℂ⁴ = Euclidean ℂ (Fin 4) ≃ₗᵢ[ℝ] Euclidean ℝ (Fin 8)`: in chart coordinates, each
`z : ℂ` is sent to `(z.re, z.im) ∈ ℝ²`, and the four `ℝ²` blocks are concatenated in
`x₀…x₃` / `x₄…x₇` order (re block then im block) so the inner product is preserved.
The resulting `ℝ`-linear endomorphism on the **complex** `PatchHilbert` is then
turned into a `ContinuousLinearMap` (finite dimension).

A **smeared** operator is a *finite* linear combination, with coefficients at the origin
taken to be (complex) linear functionals of `PatchSchwartzSpace` in each chart direction
`i : Fin 4` and each Lie direction `k : Fin 28`. Concretely we use the existing jet
coefficients `patchLineDerivℂAtZero` as the "realized" C-linear maps `PatchSchwartzSpace →L[ℂ] ℂ`
coming from a chosen family `coeff : Fin 4 → Fin 28 → PatchSchwartzSpace →L[ℂ] ℂ`.

This is a **Story-native** first step toward non-abelian YM: it is not the full
`QuantumYangMillsTheory G` `field_operators` / `localOperators` constructor yet, but
it is a *defined* OVD on `PatchHilbert` whose smearing is indexed by a `28` dimensional
(Lie) direction slot.

See `Hqiv.Story.HQIVQFTLieAlgebraFeed` (skew adjointness of the same generators) for the
Lie DOF link.

**Restriction / normalization (motivation, not wired here yet).** If this patch OVD is
to be matched to the **same** HQIV continuum cutout used for modified Maxwell / GR
(`0 < x < Θ_local` in `Hqiv.Physics.SM_GR_Unification`, from the informational-energy
layer in `Hqiv.Geometry.AuxiliaryField`), or to the **quarter-turn phase window**
`0 < x < θ` with `θ = π/2` in `Hqiv.Physics.ComptonIRWindow`, that is the natural place
to **restrict tests** `f` or **rescale smearing coefficients** so the smeared operator
tracks the auxiliary-field / phase domain rather than raw jets at `0` alone. The
definitions below stay minimal (origin jets + fixed `so8Generator` matrices); any
such bridge should be an explicit downstream layer, not a silent change of meaning.
-/

namespace Hqiv.Story

open scoped BigOperators
open Finset
open Hqiv.QM
open MillenniumYangMillsDefs
open InnerProductSpace
open ContinuousLinearMap
open Module

open EuclideanSpace
open Equiv

/-- `PatchHilbert = ℂ⁴` (PiLp) identified with `ℝ⁸` by 4 independent `(re,im)` blocks;
`Fin 2 × Fin 4` indices packed with `finProdFinEquiv` (re block: `0..3`, im block: `4..7`). -/
noncomputable def patchHilbertToEuclidean8 : PatchHilbert ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8) :=
  let p2 : ENNReal := 2
  let chartToBlocks :=
    (LinearIsometryEquiv.piLpCurry (𝕜 := ℝ) (p := p2)
        (α := fun (_i : Fin 4) (_j : Fin 2) => ℝ)).symm
  let σTo8 :=
    (Equiv.sigmaEquivProd (Fin 4) (Fin 2)).trans (Equiv.prodComm (Fin 4) (Fin 2) |>.trans
      finProdFinEquiv)
  let reindex8 := LinearIsometryEquiv.piLpCongrLeft p2 ℝ ℝ σTo8
  (LinearIsometryEquiv.piLpCongrRight p2
    (fun _i : Fin 4 => Complex.orthonormalBasisOneI.repr)).trans chartToBlocks |>.trans reindex8

noncomputable section

open SchwartzMap

/-- SO(8) Lie image of `Hqiv.so8Generator k` on the real `8` underlying `PatchHilbert`
(via `patchHilbertToEuclidean8` and `Matrix.toEuclideanLin`). -/
noncomputable def patchSo8GeneratorOp (k : Fin 28) : PatchHilbert →L[ℝ] PatchHilbert :=
  let e := patchHilbertToEuclidean8
  let A : EuclideanSpace ℝ (Fin 8) →ₗ[ℝ] EuclideanSpace ℝ (Fin 8) :=
    Matrix.toEuclideanLin (Hqiv.so8Generator k)
  LinearMap.toContinuousLinearMap
    (e.symm.toLinearMap.comp (A.comp e.toLinearMap))

/-- Non-abelian patch OVD: linear combination of the `28` `so8Generator` directions, with weights
`w i k` multiplying the **directional jet** at the origin in the standard `eᵢ` directions.

Smeared operator:
`Φ(f) = ∑_k∑_i  Re( w(i,k) · ∂ᵢ f(0) ) · T_k  +  ∑_k∑_i  Im( … ) · T_k`
for `T_k` the `ℝ`-linear SO(8) action on the patch carrier. -/
noncomputable def nonabelianSO8SmearedPatchOVD (w : Fin 4 → Fin 28 → ℂ) :
    PatchOperatorValuedDistribution PatchHilbert := fun f =>
  ∑ k : Fin 28, (∑ i : Fin 4, ((w i k) * patchLineDerivℂAtZero (spacetimeBasis i) f).re •
    patchSo8GeneratorOp k) +
  ∑ k : Fin 28, (∑ i : Fin 4, ((w i k) * patchLineDerivℂAtZero (spacetimeBasis i) f).im •
    patchSo8GeneratorOp k)

end

end Hqiv.Story
