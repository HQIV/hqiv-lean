import Hqiv.Algebra.CliffordCl06SixSpinorGammaMonomialLinearIndependent
import Hqiv.Algebra.CliffordCl06SixSpinorMonomialMatrixData
import Hqiv.Algebra.CliffordCl06SixStandardSpinorMatLiftSurjective
import Hqiv.Algebra.OctonionSpinorCarrier
import Hqiv.Algebra.SMEmbedding
import Hqiv.Algebra.Triality
import Hqiv.Geometry.AlphaGammaForcedByLattice

/-!
# Furey ↔ HQIV ontology bridge scaffold

**Status (roadmap verdict):** Stage 2–3 are **partial** — `Cl(1)` minimal ideal plus
1D hypercharge / `Δ` slot refinement are proved (`CliffordMinimalIdeal`,
`CliffordHQIVSlotRefinement`, `RapidityIdealPurposeBridge`); **`Cl(0,6)` on six
imaginary octonion directions** is now scaffolded in `CliffordSixImaginaryScaffold`
with abstract `ι` relations and matrix `L(e_k)² = -1` lemmas (`OctonionLeftMulSquare`);
a **full** `Cl(6)`-scale / complexified **equivariant** minimal-ideal ↔ spinor bridge
remains **open** (the unconditional `Mat₈(ℝ)` generation chain from ordered `γ` monomials is in
`Hqiv.Algebra.CliffordCl06SixStandardSpinorMatLiftSurjective`, with linear independence proved in
`Hqiv.Algebra.CliffordCl06SixSpinorGammaMonomialLinearIndependent`).

**Spinor Mat₈ / Gram (May 2026):** `spinorMonomialGramColumns` is the **closed-form** normalized
Frobenius Gram `W` built from `spinorGammaMonomialMatZ` (`CliffordCl06SixSpinorMonomialMatrixData`).
The mod-`101` certificate is the axiom `spinorMonomialGramColumnsZMod101_det` (script
`scripts/spinor_monomial_gram_det_mod101.py`), yielding `spinorMonomialGramColumns_det_ne_zero`.
`spinorGammaMonomialMatZ_map` identifies `spinorGammaMonomialMat` with `Matrix.map (algebraMap ℤ ℝ)` of
that integral layer. The theorem `Hqiv.Algebra.spinorGammaMonomialMat_linearIndependent` packages the
`ℝ^64` Gram / coordinate-matrix argument; use `hqivSpinorGammaMonomialLinearIndependent` below and then
`hqiv_cl06_standard_spinor_mat_lift_surjective_of_gamma_li`.

This module records the foundation-first interface for combining Furey-style
octonionic/Clifford classification with HQIV.  It does **not** formalize `Cl(6)`
or Furey's number operator.  A **first** Clifford/minimal-ideal layer — proving the
slot-level pattern on Mathlib’s `Cl(1) ≅ ℂ` model and packaging it with the HQIV
`Δ` matrix line — lives in `Hqiv.Algebra.CliffordMinimalIdeal` and
`Hqiv.Algebra.CliffordHQIVSlotRefinement`.  The stronger `Cl(6)` / spinor-8 bridge
and ontology refinement obligations remain here as explicit `Prop` fields below.

HQIV remains primary here: the discrete light-cone / monogamy constants, the
octonion spinor carrier, the current SM bookkeeping, and triality count are the
accepted anchor.  Furey-style machinery is represented as a candidate derivation
layer that may refine that anchor only through theorem-backed obligations.
-/

namespace Hqiv.Physics

/-- The current HQIV foundation-first algebra/ontology anchor.

These are the facts that remain primary when comparing to Furey-style
classification.  The record is intentionally small and imports only the stable
SM/triality/light-cone constant surface, not the heavy closure-data target.
-/
structure HQIVFoundationFirstAnchor where
  spinorCarrierDim : Fintype.card (Fin 8) = 8
  oneGenerationQuantumNumbers :
    Hqiv.Algebra.smChiralGenerationDim = 16 ∧
      Hqiv.Algebra.octonionSpinorDim = 8 ∧
      Hqiv.Algebra.hyperchargeEigenvalue 7 = 0 ∧
      Fintype.card Hqiv.Algebra.So8RepIndex = 3
  trialityRepCount : Fintype.card Hqiv.Algebra.So8RepIndex = 3
  alphaGammaForced :
    Hqiv.alpha = (3 / 5 : ℝ) ∧
      Hqiv.gamma_HQIV = (2 / 5 : ℝ) ∧
      Hqiv.alpha + Hqiv.gamma_HQIV = 1

/-- Canonical current HQIV anchor for Furey comparison work. -/
def hqivFoundationFirstAnchor : HQIVFoundationFirstAnchor where
  spinorCarrierDim := Hqiv.Algebra.octonionSpinorCarrier_dim
  oneGenerationQuantumNumbers := Hqiv.Algebra.sm_quantum_numbers_one_generation
  trialityRepCount := Hqiv.Algebra.three_generations_from_triality_reps
  alphaGammaForced := Hqiv.alpha_gamma_forced_pair

/-- The HQIV foundation-first anchor exists without any Furey/Clifford assumptions. -/
theorem hqivFoundationFirstAnchor_exists : Nonempty HQIVFoundationFirstAnchor :=
  ⟨hqivFoundationFirstAnchor⟩

/-!
## Three-generation embedding from HQIV foundations

This is the theorem-backed part that can be used today: HQIV supplies the
triality generation index, one octonion-spinor carrier per index, and the
one-generation SM bookkeeping on each copy.  This is the right landing zone for
Furey's three-generation embedding.  The stronger claim that Furey's minimal
left ideals are equivalent to these copies remains a bridge obligation below.
-/

/-- The three generation labels are the three Spin(8) triality representation labels. -/
abbrev HQIVFureyGenerationIndex := Hqiv.Algebra.So8RepIndex

/-- One HQIV octonion-spinor carrier for each Furey/HQIV generation label. -/
abbrev HQIVFureyThreeGenerationCarrier :=
  HQIVFureyGenerationIndex → Hqiv.Algebra.OctonionSpinorCarrier

/-- The finite slot index for the three real 8s carriers. -/
abbrev HQIVFureyGenerationSlot := HQIVFureyGenerationIndex × Fin 8

/-- The finite slot index for three full 16-component chiral generations. -/
abbrev HQIVFureyChiralSlot :=
  HQIVFureyGenerationIndex × Fin Hqiv.Algebra.smChiralGenerationDim

/-- HQIV supplies exactly three generation labels for the Furey embedding target. -/
theorem hqivFurey_generation_count_eq_three :
    Fintype.card HQIVFureyGenerationIndex = 3 :=
  Hqiv.Algebra.three_generations_from_triality_reps

/-- Three triality labels times the real 8s carrier gives 24 carrier slots. -/
theorem hqivFurey_generationSlot_count_eq_twenty_four :
    Fintype.card HQIVFureyGenerationSlot = 24 := by
  simp [HQIVFureyGenerationSlot, HQIVFureyGenerationIndex, Hqiv.Algebra.So8RepIndex]

/-- Three full 16-component chiral generations give 48 chiral Weyl bookkeeping slots. -/
theorem hqivFurey_chiralSlot_count_eq_forty_eight :
    Fintype.card HQIVFureyChiralSlot = 48 := by
  simp [HQIVFureyChiralSlot, HQIVFureyGenerationIndex, Hqiv.Algebra.So8RepIndex,
    Hqiv.Algebra.smChiralGenerationDim]

/-- Concrete HQIV-side certificate for the three-generation Furey landing zone. -/
structure FureyThreeGenerationEmbeddingFromHQIV where
  foundation : HQIVFoundationFirstAnchor
  generationCount : Fintype.card HQIVFureyGenerationIndex = 3
  oneGenerationQuantumNumbers :
    Hqiv.Algebra.smChiralGenerationDim = 16 ∧
      Hqiv.Algebra.octonionSpinorDim = 8 ∧
      Hqiv.Algebra.hyperchargeEigenvalue 7 = 0 ∧
      Fintype.card Hqiv.Algebra.So8RepIndex = 3
  generationCycleOrder :
    ∀ r : HQIVFureyGenerationIndex,
      Hqiv.Algebra.trialityCycle
        (Hqiv.Algebra.trialityCycle (Hqiv.Algebra.trialityCycle r)) = r
  carrierSlotCount : Fintype.card HQIVFureyGenerationSlot = 24
  chiralSlotCount : Fintype.card HQIVFureyChiralSlot = 48

/-- The canonical HQIV-derived three-generation embedding target for Furey alignment. -/
def hqivFureyThreeGenerationEmbedding : FureyThreeGenerationEmbeddingFromHQIV where
  foundation := hqivFoundationFirstAnchor
  generationCount := hqivFurey_generation_count_eq_three
  oneGenerationQuantumNumbers := Hqiv.Algebra.sm_quantum_numbers_one_generation
  generationCycleOrder := Hqiv.Algebra.triality_cycle_order_3
  carrierSlotCount := hqivFurey_generationSlot_count_eq_twenty_four
  chiralSlotCount := hqivFurey_chiralSlot_count_eq_forty_eight

/-- HQIV foundations already provide the three-generation embedding target. -/
theorem hqivFureyThreeGenerationEmbedding_exists :
    Nonempty FureyThreeGenerationEmbeddingFromHQIV :=
  ⟨hqivFureyThreeGenerationEmbedding⟩

/-- Projection: the HQIV-derived Furey landing zone has exactly three generations. -/
theorem hqivFureyThreeGenerationEmbedding_count :
    hqivFureyThreeGenerationEmbedding.generationCount =
      hqivFurey_generation_count_eq_three := rfl

/-- Projection: the HQIV-derived Furey landing zone has 48 chiral generation slots. -/
theorem hqivFureyThreeGenerationEmbedding_chiral_slots :
    hqivFureyThreeGenerationEmbedding.chiralSlotCount =
      hqivFurey_chiralSlot_count_eq_forty_eight := rfl

/-!
## Furey's shape as an HQIV-derived theorem

The next layer abstracts the part of Furey's program we can use without importing
minimal left ideals: a Furey-shaped generation space is any finite label space
identified with the HQIV triality labels.  Once that shape equivalence is given,
the generation count and the 48 chiral bookkeeping slots are theorems from the
HQIV foundation.
-/

/-- A Furey-shaped generation label space, anchored by an equivalence to HQIV triality labels. -/
structure FureyGenerationShape where
  Generation : Type
  generationFintype : Fintype Generation
  generationEquivHQIV : Generation ≃ HQIVFureyGenerationIndex

attribute [instance] FureyGenerationShape.generationFintype

/-- The carrier determined by a Furey-shaped generation label space. -/
abbrev FureyShapeCarrier (s : FureyGenerationShape) :=
  s.Generation → Hqiv.Algebra.OctonionSpinorCarrier

/-- The full chiral slot space determined by a Furey-shaped generation label space. -/
abbrev FureyShapeChiralSlot (s : FureyGenerationShape) :=
  s.Generation × Fin Hqiv.Algebra.smChiralGenerationDim

/-- Any Furey-shaped generation space equivalent to HQIV triality has exactly three labels. -/
theorem fureyShape_generation_count_eq_three
    (foundation : HQIVFoundationFirstAnchor) (s : FureyGenerationShape) :
    @Fintype.card s.Generation s.generationFintype = 3 := by
  have hcard :
      @Fintype.card s.Generation s.generationFintype =
        Fintype.card HQIVFureyGenerationIndex :=
    Fintype.card_congr s.generationEquivHQIV
  rw [hcard]
  exact foundation.trialityRepCount

/-- A Furey-shaped three-generation space gives 48 full chiral Weyl bookkeeping slots. -/
theorem fureyShape_chiralSlot_count_eq_forty_eight
    (foundation : HQIVFoundationFirstAnchor) (s : FureyGenerationShape) :
    Fintype.card (FureyShapeChiralSlot s) = 48 := by
  rw [Fintype.card_prod, fureyShape_generation_count_eq_three foundation s]
  simp [Hqiv.Algebra.smChiralGenerationDim]

/-- Certificate that Furey's generation shape has been embedded into the HQIV foundation. -/
structure FureyShapeThreeGenerationsFromHQIV where
  shape : FureyGenerationShape
  foundation : HQIVFoundationFirstAnchor
  generationCount : @Fintype.card shape.Generation shape.generationFintype = 3
  chiralSlotCount :
    Fintype.card (FureyShapeChiralSlot shape) = 48
  shapeEquivHQIV : shape.Generation ≃ HQIVFureyGenerationIndex

/-- Build the three-generation certificate from a Furey-shaped generation space. -/
def fureyShapeThreeGenerationsFromHQIV (s : FureyGenerationShape) :
    FureyShapeThreeGenerationsFromHQIV where
  shape := s
  foundation := hqivFoundationFirstAnchor
  generationCount := fureyShape_generation_count_eq_three hqivFoundationFirstAnchor s
  chiralSlotCount := fureyShape_chiralSlot_count_eq_forty_eight hqivFoundationFirstAnchor s
  shapeEquivHQIV := s.generationEquivHQIV

/-- Furey's three-generation shape is a theorem once its labels are matched to HQIV triality. -/
theorem furey_shape_three_generations_from_HQIV
    (s : FureyGenerationShape) :
    (fureyShapeThreeGenerationsFromHQIV s).generationCount =
      fureyShape_generation_count_eq_three hqivFoundationFirstAnchor s := rfl

/-- Canonical Furey shape obtained directly from the HQIV triality label space. -/
def canonicalFureyGenerationShape : FureyGenerationShape where
  Generation := HQIVFureyGenerationIndex
  generationFintype := inferInstance
  generationEquivHQIV := Equiv.refl HQIVFureyGenerationIndex

/-- The canonical HQIV/Furey generation shape has exactly three generations. -/
theorem canonicalFureyGenerationShape_count_eq_three :
    @Fintype.card canonicalFureyGenerationShape.Generation
      canonicalFureyGenerationShape.generationFintype = 3 :=
  fureyShape_generation_count_eq_three hqivFoundationFirstAnchor canonicalFureyGenerationShape

/-- Future Furey-side proof obligations.

Each field is a proposition because this scaffold should not invent the missing
Clifford/minimal-ideal machinery.  A concrete future Furey formalization should
instantiate these propositions with real theorem statements and then prove the
refinement certificate below.
-/
structure FureyCandidateDerivation where
  complexifiedCarrierBridge : Prop
  minimalLeftIdealOneGenerationBridge : Prop
  chargeNumberOperatorMatchesHQIV : Prop
  threeGenerationSplitMatchesTriality : Prop
  carrierOntologyRefinesHQIV : Prop
  chargeOntologyRefinesHQIV : Prop
  generationOntologyRefinesHQIV : Prop
  shellSupportSelectionBridge : Prop

/-!
### Spinor `Mat₈(ℝ)` generation certificate (hooked to `CliffordCl06SixStandardSpinorMatLiftSurjective`)

The **linear independence** of the `64` ordered `γ` monomials implies `ρ_mat` is surjective onto
`Mat₈(ℝ)`; see `Hqiv.Algebra.cl06StandardSpinorMatLift_surjective_of_linearIndependent`.

#### Integral Gram layer (`CliffordCl06SixSpinorMonomialMatrixData`)

`spinorMonomialGramColumns` is the normalized Frobenius Gram `W` over `ℤ` (see module doc there).

* `Hqiv.Algebra.spinorMonomialGramColumns_det_ne_zero` — from the mod-`101` axiom
  `spinorMonomialGramColumnsZMod101_det` in the same module (script
  `scripts/spinor_monomial_gram_det_mod101.py`).

* `Hqiv.Algebra.spinorGammaMonomialMat_linearIndependent` — `ℝ^64` row-major Gram / `mulVec`
  argument in `CliffordCl06SixSpinorGammaMonomialLinearIndependent`.
-/

/-- Nonsingular integral Gram matrix for the spinor monomial certificate. -/
abbrev HQIVSpinorMonomialGramDetNonsingular : Prop :=
  Hqiv.Algebra.spinorMonomialGramColumns.det ≠ 0

/-- Hypothesis-style packaging for the `γ` monomial linear-independence target. -/
abbrev HQIVSpinorGammaMonomialLinearIndependent : Prop :=
  LinearIndependent ℝ Hqiv.Algebra.spinorGammaMonomialMat

/-- The `γ` monomial matrices are `ℝ`-linearly independent (Gram / coordinate proof). -/
theorem hqivSpinorGammaMonomialLinearIndependent : HQIVSpinorGammaMonomialLinearIndependent :=
  Hqiv.Algebra.spinorGammaMonomialMat_linearIndependent

theorem hqiv_cl06_standard_spinor_mat_lift_surjective_of_gamma_li
    (h : HQIVSpinorGammaMonomialLinearIndependent) :
    Function.Surjective Hqiv.Algebra.cl06StandardSpinorMatLift :=
  Hqiv.Algebra.cl06StandardSpinorMatLift_surjective_of_linearIndependent h

/-- Bijectivity packaging (surjectivity + equal `64`/`64` `finrank`). -/
theorem hqiv_cl06_standard_spinor_mat_lift_bijective_of_gamma_li
    (h : HQIVSpinorGammaMonomialLinearIndependent) :
    Function.Bijective Hqiv.Algebra.cl06StandardSpinorMatLift :=
  Hqiv.Algebra.cl06StandardSpinorMatLift_bijective_of_linearIndependent h

/-- Furey-aligned packaging: the `Mat₈(ℝ)` matrix lift is fixed once monomial matrices are `ℝ`-LI. -/
structure FureySpinorMatLiftFromMonomialLI where
  /-- HQIV-side linear independence of the ordered `γ` monomial matrices (now unconditional). -/
  gammaMonomialLI : HQIVSpinorGammaMonomialLinearIndependent

/-- Construct the Furey-shaped spinor lift certificate from a linear-independence proof. -/
noncomputable def fureySpinorMatLiftFromMonomialLI
    (h : HQIVSpinorGammaMonomialLinearIndependent) : FureySpinorMatLiftFromMonomialLI where
  gammaMonomialLI := h

/-- Default certificate using `hqivSpinorGammaMonomialLinearIndependent`. -/
noncomputable abbrev fureySpinorMatLiftFromMonomialCanonical : FureySpinorMatLiftFromMonomialLI :=
  fureySpinorMatLiftFromMonomialLI hqivSpinorGammaMonomialLinearIndependent

theorem fureySpinorMatLiftFromMonomialLI_surjective (c : FureySpinorMatLiftFromMonomialLI) :
    Function.Surjective Hqiv.Algebra.cl06StandardSpinorMatLift :=
  hqiv_cl06_standard_spinor_mat_lift_surjective_of_gamma_li c.gammaMonomialLI

theorem fureySpinorMatLiftFromMonomialLI_bijective (c : FureySpinorMatLiftFromMonomialLI) :
    Function.Bijective Hqiv.Algebra.cl06StandardSpinorMatLift :=
  hqiv_cl06_standard_spinor_mat_lift_bijective_of_gamma_li c.gammaMonomialLI

/-- A Furey candidate may refine HQIV only after all bridge obligations are proved. -/
structure FureyMayRefineHQIV (d : FureyCandidateDerivation) : Prop where
  complexifiedCarrierBridge : d.complexifiedCarrierBridge
  minimalLeftIdealOneGenerationBridge : d.minimalLeftIdealOneGenerationBridge
  chargeNumberOperatorMatchesHQIV : d.chargeNumberOperatorMatchesHQIV
  threeGenerationSplitMatchesTriality : d.threeGenerationSplitMatchesTriality
  carrierOntologyRefinesHQIV : d.carrierOntologyRefinesHQIV
  chargeOntologyRefinesHQIV : d.chargeOntologyRefinesHQIV
  generationOntologyRefinesHQIV : d.generationOntologyRefinesHQIV
  shellSupportSelectionBridge : d.shellSupportSelectionBridge

/-- Carrier ontology refinement requires both the complex carrier and ideal bridges. -/
theorem furey_refinement_requires_carrier_bridge
    {d : FureyCandidateDerivation} (h : FureyMayRefineHQIV d) :
    d.complexifiedCarrierBridge ∧
      d.minimalLeftIdealOneGenerationBridge ∧
      d.carrierOntologyRefinesHQIV := by
  exact ⟨h.complexifiedCarrierBridge, h.minimalLeftIdealOneGenerationBridge,
    h.carrierOntologyRefinesHQIV⟩

/-- Charge ontology refinement requires matching the Furey number-operator charge to HQIV. -/
theorem furey_refinement_requires_charge_bridge
    {d : FureyCandidateDerivation} (h : FureyMayRefineHQIV d) :
    d.chargeNumberOperatorMatchesHQIV ∧ d.chargeOntologyRefinesHQIV := by
  exact ⟨h.chargeNumberOperatorMatchesHQIV, h.chargeOntologyRefinesHQIV⟩

/-- Generation ontology refinement requires the Furey split to match HQIV triality labels. -/
theorem furey_refinement_requires_generation_bridge
    {d : FureyCandidateDerivation} (h : FureyMayRefineHQIV d) :
    d.threeGenerationSplitMatchesTriality ∧ d.generationOntologyRefinesHQIV := by
  exact ⟨h.threeGenerationSplitMatchesTriality, h.generationOntologyRefinesHQIV⟩

/-- Shell/support ontology remains HQIV-first until Furey proves this explicit bridge. -/
theorem furey_refinement_requires_shell_support_bridge
    {d : FureyCandidateDerivation} (h : FureyMayRefineHQIV d) :
    d.shellSupportSelectionBridge := by
  exact h.shellSupportSelectionBridge

end Hqiv.Physics
