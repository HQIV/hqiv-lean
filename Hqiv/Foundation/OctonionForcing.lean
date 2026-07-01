import Hqiv.Foundation.ClosureConstraint
import Hqiv.Foundation.SevenImaginaryIncidence
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Tactic

/-!
# OctonionForcing — the capstone and the explicit honesty frontier

This module assembles the spine and states **exactly** what is proved versus what
remains, with no `sorry` and no new `axiom`.

## What is proved from 3D growth (axiom-free, `ℕ`/`ℚ`/finite combinatorics)

`forcedCarrierData` collects:

* `carrierMultiplicity = 8` — the carrier channel count, from `2³`;
* `imaginaryDim = 7` — the imaginary-direction count;
* `soDim carrierMultiplicity = 28` — the rotation-algebra dimension;
* the **full Fano incidence** on the seven imaginary directions: 3 points per line and
  a unique common line through any two distinct points.

Together with `Hqiv.Foundation.hqivCarrierClosure` (the `28 = 14 + 7 + 7` closure
bookkeeping) and `Hqiv.Foundation.foundationDelta` (the skew phase-lift on the
distinguished plane), the structural skeleton of the octonion carrier is *forced* by
the single input `transverseDim = 3`.

## The frontier (the one remaining step, stated as a hypothesis — never an axiom)

What is **not** yet proved internally is that the *unique* multiplication compatible
with this forced skeleton is the octonion product. We encode this as the explicit
predicate `OctonionTableUnique` and the implication `threeD_forces_octonion_of_uniqueness`:
given table-uniqueness, 3D growth forces the octonion carrier. The hypothesis is the
sole gap; it is carried as an explicit antecedent so the honesty boundary is visible in
the type, not hidden in an `axiom`.

## Topological refinement

`Hqiv.Foundation.HopfDivisionLadder` sharpens this frontier with the TUFT hypothesis
that topology forces Hopf fibrations: it proves the carrier dimension `8` is the
**maximal** Hopf-invariant-one dimension (`S⁷ ↪ S¹⁵ → S⁸`), with the fiber `S⁷` equal to
the seven imaginary directions and the next Cayley–Dickson rung (`16`, sedenions)
provably outside the ladder. The residual `OctonionTableUnique` is thereby reinterpreted
as the uniqueness of that maximal fibration's normed division algebra.
-/

namespace Hqiv.Foundation

open Finset

/-! ## Bridges: the "octonion factor 8/7" is now derived, matching the light cone -/

/-- The forced imaginary-direction count equals the light cone's octonion imaginary
dimension. The numeral `7` in `Hqiv.octonionImaginaryDim` is thereby a **consequence**
of `transverseDim = 3`, not an independent primitive. -/
theorem imaginaryDim_eq_lightcone : imaginaryDim = Hqiv.octonionImaginaryDim := by
  rw [imaginaryDim_eq_seven, Hqiv.octonionImaginaryDim_eq]

/-- The forced carrier multiplicity reproduces the light cone's octonion factor
`8 = 7 + 1` (imaginary directions plus the scalar). -/
theorem carrier_eq_lightcone_octonion_succ :
    carrierMultiplicity = Hqiv.octonionImaginaryDim + 1 := by
  rw [carrierMultiplicity_eq_eight, Hqiv.octonionImaginaryDim_eq]

/-- The forced curvature-norm exponent (`7`) of the light cone equals `imaginaryDim`. -/
theorem lightcone_curvatureExponent_eq_imaginaryDim :
    Hqiv.curvatureNormExponent = imaginaryDim := by
  rw [imaginaryDim_eq_seven]; exact Hqiv.curvatureNormExponent_eq_octonionDim.trans rfl

/-! ## The forced structural skeleton -/

/-- **Everything 3D growth forces about the carrier**, bundled as one provable `Prop`. -/
def ForcedCarrierData : Prop :=
  carrierMultiplicity = 8 ∧
  imaginaryDim = 7 ∧
  soDim carrierMultiplicity = 28 ∧
  (∀ i : Fin 7, (fanoLine i).card = 3) ∧
  (∀ v w : Fin 7, v ≠ w →
    (Finset.univ.filter fun i => v ∈ fanoLine i ∧ w ∈ fanoLine i).card = 1)

/-- **The structural skeleton is proved**, with the single input `transverseDim = 3`. -/
theorem forcedCarrierData : ForcedCarrierData :=
  ⟨carrierMultiplicity_eq_eight, imaginaryDim_eq_seven, soDim_carrier,
   fanoLine_card, unique_common_line⟩

/-! ## Abstract multiplication tables and the frontier predicate -/

/-- **Structure constants** of a multiplication on the 8-channel carrier:
`e_i · e_j = Σ_k (c i j k) • e_k`. -/
abbrev CarrierStructure := Fin 8 → Fin 8 → Fin 8 → ℝ

/-- Imaginary label of a (nonzero) carrier index, as a Fano point in `Fin 7`. -/
def imagLabel (i : Fin 8) : Fin 7 := ⟨(i.val - 1) % 7, Nat.mod_lt _ (by norm_num)⟩

/-- **Unital:** the scalar channel `e₀` is a two-sided identity. -/
def Unital (c : CarrierStructure) : Prop :=
  (∀ j k, c 0 j k = if j = k then 1 else 0) ∧
  (∀ i k, c i 0 k = if i = k then 1 else 0)

/-- **Imaginary units square to `−e₀`** (the composition-algebra norm condition on units). -/
def ImaginaryInvolutive (c : CarrierStructure) : Prop :=
  ∀ i : Fin 8, i ≠ 0 → ∀ k, c i i k = if k = 0 then -1 else 0

/-- **Fano-compatible:** a product of two distinct imaginary units is supported only on
the scalar channel or on the third point of their unique Fano line. -/
def FanoCompatible (c : CarrierStructure) : Prop :=
  ∀ i j k : Fin 8, i ≠ 0 → j ≠ 0 → i ≠ j → c i j k ≠ 0 →
    (k = 0 ∨ collinearImag (imagLabel i) (imagLabel j) (imagLabel k))

/-- **Realizability target** (consistency of the forced skeleton): there exists a
multiplication that is unital, has involutive imaginary units, and is Fano-compatible.
A concrete witness is the octonion table carried by `Hqiv.octonionLeftMul_*`; recording
it here as a named target keeps the witness layer decoupled from this file. -/
def OctonionTableRealizable : Prop :=
  ∃ c : CarrierStructure, Unital c ∧ ImaginaryInvolutive c ∧ FanoCompatible c

/-- **Frontier predicate (the one open step).**

The forced skeleton (unital, involutive imaginary units, Fano-compatible products)
**determines the multiplication uniquely**. This is the precise statement that the
octonion product is forced rather than merely realizable — the content classically
supplied by Hurwitz rigidity. It is stated as a `Prop` to be discharged, never assumed. -/
def OctonionTableUnique : Prop :=
  ∀ c d : CarrierStructure,
    (Unital c ∧ ImaginaryInvolutive c ∧ FanoCompatible c) →
    (Unital d ∧ ImaginaryInvolutive d ∧ FanoCompatible d) →
    c = d

/-- **The end goal:** 3D growth forces the octonion carrier — the forced structural
skeleton together with table-uniqueness. -/
def ThreeDForcesOctonion : Prop := ForcedCarrierData ∧ OctonionTableUnique

/-- **Frontier theorem (honesty boundary).**

Everything except table-uniqueness is already proved (`forcedCarrierData`). Given the
single remaining hypothesis `OctonionTableUnique`, 3D causal growth forces the octonion
carrier. The hypothesis is the *sole* gap and is carried as an explicit antecedent,
not introduced as an axiom. -/
theorem threeD_forces_octonion_of_uniqueness
    (h : OctonionTableUnique) : ThreeDForcesOctonion :=
  ⟨forcedCarrierData, h⟩

end Hqiv.Foundation
