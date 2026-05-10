import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.LinearMap
import Problems.YangMills.Quantum

/-!
# Trivial Poincaré unitary representation + 1D Wightman scaffold

**Poincaré scaffold:** `MillenniumPoincareGroup := Unit` with `millenniumPoincareTrivialUnitaryRep`
(trivial `H ≃ₗᵢ[ℝ] H`) and `millenniumPoincareTrivialTestAction` (identity on `SchwartzSpace`).

**Wightman / field (1D toy):** `WightmanToyHilbert = EuclideanSpace ℝ (Fin 1)`, scalar field
`wightmanToyScalarField f = (SchwartzMap.evalCLM … 0 f) • id`, Hamiltonian `0`, trivial spatial
translations, vacuum `EuclideanSpace.single 0 (1 : ℝ)`. Locality and covariance are proved.

Cyclicity uses `schwartzMap_real_eqAt_zero` (Schwartz surjectivity at a point: a `ContDiffBump`
at the origin, `HasCompactSupport.toSchwartzMap`, and scalar action in `𝓢(ℝ⁴, ℝ)`).

For **`PatchHilbert`** / ladder Hamiltonian packaging, see `MillenniumBridgePatchPoincareWightman`.

**Dojo YM *shape* (interface only):** the same carrier + field is wrapped as
`MillenniumYangMillsDefs.QuantumYangMillsTheory` in
`Hqiv.Story.QuantumYangMillsFromPatchHQIV` / `QuantumYangMillsFromPoincareToy` (those modules `import` this one).
-/

namespace Hqiv.Story

open Metric
open MillenniumYangMillsDefs
open scoped InnerProductSpace SchwartzMap ContDiff

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Terminal “Poincaré” group used for covariance bookkeeping in this scaffold. -/
abbrev MillenniumPoincareGroup : Type :=
  Unit

instance millenniumPoincareGroup_instGroup : Group MillenniumPoincareGroup :=
  inferInstanceAs (Group Unit)

/-- Trivial unitary representation on `H`. -/
noncomputable def millenniumPoincareTrivialUnitaryRep : MillenniumPoincareGroup →* (H ≃ₗᵢ[ℝ] H) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp only [one_mul]

@[simp]
theorem millenniumPoincareTrivialUnitaryRep_apply (g : MillenniumPoincareGroup) :
    millenniumPoincareTrivialUnitaryRep g = (1 : H ≃ₗᵢ[ℝ] H) :=
  rfl

/-- Trivial action on Schwartz test functions. -/
@[simp]
noncomputable def millenniumPoincareTrivialTestAction (g : MillenniumPoincareGroup)
    (f : SchwartzSpace) : SchwartzSpace :=
  f

@[simp]
theorem millenniumPoincareTrivialTestAction_one (f : SchwartzSpace) :
    millenniumPoincareTrivialTestAction (1 : MillenniumPoincareGroup) f = f :=
  rfl

theorem millenniumPoincareTrivialTestAction_mul (g₁ g₂ : MillenniumPoincareGroup)
    (f : SchwartzSpace) :
    millenniumPoincareTrivialTestAction (g₁ * g₂) f =
      millenniumPoincareTrivialTestAction g₁ (millenniumPoincareTrivialTestAction g₂ f) := by
  rfl

/-- Trivial unitary representation of spatial translations. -/
abbrev millenniumSpatialTranslationTrivial (_x : Space) : H ≃ₗᵢ[ℝ] H :=
  1

@[simp]
theorem millenniumSpatialTranslationTrivial_zero :
    millenniumSpatialTranslationTrivial (0 : Space) = (1 : H ≃ₗᵢ[ℝ] H) :=
  rfl

/-! ### One-dimensional Hilbert carrier (no extra `InnerProductSpace` instance) -/

/-- Real one-dimensional Hilbert space. -/
abbrev WightmanToyHilbert : Type :=
  EuclideanSpace ℝ (Fin 1)

instance wightmanToyHilbert_nontrivial : Nontrivial WightmanToyHilbert := by
  refine ⟨⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), EuclideanSpace.single (0 : Fin 1) (2 : ℝ), ?_⟩⟩
  intro he
  have := congr_arg (fun v : WightmanToyHilbert => v 0) he
  simp [EuclideanSpace.single_apply] at this

instance : CompleteSpace WightmanToyHilbert := by
  simpa [WightmanToyHilbert] using inferInstanceAs (CompleteSpace (PiLp 2 fun _ : Fin 1 => ℝ))

/-- Trivial spatial translation action on the concrete toy carrier. -/
abbrev wightmanToySpatialTranslation (_ : Space) : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert :=
  1

@[simp]
theorem wightmanToySpatialTranslation_zero :
    wightmanToySpatialTranslation (0 : Space) = (1 : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert) :=
  rfl

theorem wightmanToySpatialTranslation_add (x y : Space) :
    wightmanToySpatialTranslation (x + y) =
      wightmanToySpatialTranslation x * wightmanToySpatialTranslation y :=
  rfl

instance wightmanToyEnd_nontrivial : Nontrivial (WightmanToyHilbert →L[ℝ] WightmanToyHilbert) := by
  refine ⟨⟨(1 : WightmanToyHilbert →L[ℝ] WightmanToyHilbert), 0, ?_⟩⟩
  intro rid
  have := congr_arg (fun f : WightmanToyHilbert →L[ℝ] WightmanToyHilbert => ‖f‖) rid
  simp at this

noncomputable def wightmanToyVacuum : WightmanToyHilbert :=
  EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

theorem wightmanToyVacuum_norm : ‖wightmanToyVacuum‖ = 1 := by
  simp [wightmanToyVacuum, EuclideanSpace.norm_single]

/-- Scalar field `Φ(f) = f(0) • id` (point evaluation at the spacetime origin).

We use the underlying `toFun` accessor (public on `SchwartzMap`) for evaluation at a point. -/
noncomputable def wightmanToyScalarField : OperatorValuedDistribution WightmanToyHilbert :=
  fun f => (f.toFun (0 : Spacetime) : ℝ) • ContinuousLinearMap.id ℝ WightmanToyHilbert

theorem wightmanToyScalarField_apply (f : SchwartzSpace) (ψ : WightmanToyHilbert) :
    wightmanToyScalarField f ψ = f.toFun (0 : Spacetime) • ψ :=
  rfl

theorem wightmanToy_covariance (g : MillenniumPoincareGroup) (f : SchwartzSpace) :
    wightmanToyScalarField (millenniumPoincareTrivialTestAction g f) =
      conjugateOperator (millenniumPoincareTrivialUnitaryRep g) (wightmanToyScalarField f) := by
  simp only [millenniumPoincareTrivialTestAction]
  rw [millenniumPoincareTrivialUnitaryRep_apply g]
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1symm :
      (1 : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert).symm =
        (1 : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert) := by
    rw [← LinearIsometryEquiv.inv_def, inv_one]
  have h1clm :
      (1 : WightmanToyHilbert ≃ₗᵢ[ℝ] WightmanToyHilbert).toContinuousLinearEquiv =
        ContinuousLinearEquiv.refl ℝ WightmanToyHilbert := by
    rw [LinearIsometryEquiv.one_def, LinearIsometryEquiv.toContinuousLinearEquiv_refl]
  simp only [conjugateOperator, ContinuousLinearMap.comp_apply, wightmanToyScalarField,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, h1symm, h1clm,
    ContinuousLinearEquiv.coe_refl]

theorem wightmanToy_locality (f g : SchwartzMap Spacetime ℝ)
    (_h : ∀ (x y : Spacetime), (MinkowskiMetric (x - y) (x - y) < 0) → f x = 0 ∨ g y = 0) :
    wightmanToyScalarField f ∘L wightmanToyScalarField g =
      wightmanToyScalarField g ∘L wightmanToyScalarField f := by
  ext ψ
  simp [wightmanToyScalarField, ContinuousLinearMap.comp_apply, smul_smul, mul_comm]

noncomputable def wightmanToyHamiltonian : LinearOperator WightmanToyHilbert :=
  0

theorem wightmanToy_hamiltonian_selfAdjoint : IsSelfAdjoint wightmanToyHamiltonian :=
  ContinuousLinearMap.isPositive_zero.isSelfAdjoint

theorem wightmanToy_hamiltonian_positive : wightmanToyHamiltonian.IsPositive :=
  ContinuousLinearMap.isPositive_zero

theorem wightmanToy_not_isUnit_zeroHamiltonian : ¬IsUnit wightmanToyHamiltonian := by
  simpa [wightmanToyHamiltonian] using
    (not_isUnit_zero (M₀ := WightmanToyHilbert →L[ℝ] WightmanToyHilbert))

theorem wightmanToy_mem_spectrum_hamiltonian (E : ℝ) :
    E ∈ spectrum ℝ wightmanToyHamiltonian ↔ E = 0 := by
  classical
  rw [spectrum.mem_iff]
  simp only [wightmanToyHamiltonian, map_zero, sub_zero, Algebra.algebraMap_eq_smul_one]
  constructor
  · intro hE
    by_contra hE0
    apply hE
    exact IsUnit.smul (Units.mk0 E hE0) (isUnit_one : IsUnit (1 : WightmanToyHilbert →L[ℝ] WightmanToyHilbert))
  · rintro rfl
    simpa using wightmanToy_not_isUnit_zeroHamiltonian

theorem wightmanToy_spectrum_nonneg (E : ℝ) (hE : E ∈ spectrum ℝ wightmanToyHamiltonian) : 0 ≤ E := by
  simpa [(wightmanToy_mem_spectrum_hamiltonian E).mp hE] using le_rfl

theorem wightmanToy_vacuum_energy_zero : (0 : ℝ) ∈ spectrum ℝ wightmanToyHamiltonian :=
  (wightmanToy_mem_spectrum_hamiltonian 0).2 rfl

theorem wightmanToy_isVacuum : IsVacuum wightmanToyVacuum wightmanToyHamiltonian := by
  simp [IsVacuum, wightmanToyHamiltonian]

theorem wightmanToy_vacuum_poincare_invariant (g : MillenniumPoincareGroup) :
    millenniumPoincareTrivialUnitaryRep g wightmanToyVacuum = wightmanToyVacuum :=
  rfl

theorem wightmanToy_vacuum_spatial_invariant (x : Space) :
    wightmanToySpatialTranslation x wightmanToyVacuum = wightmanToyVacuum :=
  rfl

/-!
### Schwartz surjectivity at a point

From a smooth `ContDiffBump` at `0 : Spacetime = ℝ⁴` (Euclidean) we obtain a compactly supported
`C^∞` map, converted to a `SchwartzMap` via
`HasCompactSupport.toSchwartzMap` (`SchwartzSpace/Basic.lean`), then scaled in `𝓢(ℝ⁴, ℝ)`.
-/

lemma schwartzMap_real_eqAt_zero (c : ℝ) :
    ∃ f : SchwartzSpace, f.toFun (0 : Spacetime) = c := by
  classical
  haveI : HasContDiffBump (Spacetime) := by
    simpa [Spacetime] using (inferInstance : HasContDiffBump (EuclideanSpace ℝ (Fin 4)))
  let b : ContDiffBump (0 : Spacetime) := Inhabited.default
  have hmem : (0 : Spacetime) ∈ closedBall 0 b.rIn := by
    simp [mem_closedBall, dist_eq_norm, sub_zero]
    exact b.rIn_pos.le
  have hb1 : b 0 = 1 := ContDiffBump.one_of_mem_closedBall b hmem
  have hcont : ContDiff ℝ ∞ b := b.contDiff
  have hsupp : HasCompactSupport b := ContDiffBump.hasCompactSupport b
  let f0 : SchwartzSpace := hsupp.toSchwartzMap hcont
  have hf0 : f0.toFun 0 = 1 := by
    -- `toSchwartzMap` keeps the underlying `toFun` (`SchwartzSpace/Basic` `@[simps]`)
    simpa [HasCompactSupport.toSchwartzMap, hb1]
  -- `Quantum.SchwartzSpace` is a `def` over `SchwartzMap`; `•` is synthesised for `SchwartzMap` only.
  let f0S : SchwartzMap Spacetime ℝ := f0
  let f1S : SchwartzMap Spacetime ℝ := c • f0S
  have hf1 : f1S.toFun (0 : Spacetime) = c := by
    -- `SchwartzMap.instSMul` is pointwise: `(c•f).toFun = c • f.toFun`
    have : f1S.toFun 0 = (c • f0S.toFun) 0 := rfl
    rw [this, Pi.smul_apply, show f0S.toFun 0 = 1 from by simpa [f0S] using hf0]
    simp [smul_eq_mul, mul_one]
  exact ⟨f1S, hf1⟩

theorem wightmanToy_field_span_eq_top :
    fieldGeneratedSubmodule wightmanToyScalarField wightmanToyVacuum = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun v => ?_
  have hv : ∃ c : ℝ, c • wightmanToyVacuum = v := by
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [wightmanToyVacuum, EuclideanSpace.single_apply]
  rcases hv with ⟨c, rfl⟩
  rcases schwartzMap_real_eqAt_zero c with ⟨f, hf⟩
  refine Submodule.subset_span ?_
  refine ⟨f, ?_⟩
  simp [wightmanToyScalarField, wightmanToyVacuum, hf]

theorem wightmanToy_vacuum_cyclic :
    Dense (fieldGeneratedSubmodule wightmanToyScalarField wightmanToyVacuum : Set WightmanToyHilbert) := by
  rw [wightmanToy_field_span_eq_top]
  simp

/-- Wightman axioms for the scalar toy on `ℝ¹` (using `schwartzMap_real_eqAt_zero`). -/
noncomputable def wightmanToyWightmanAxioms : WightmanAxioms WightmanToyHilbert wightmanToyScalarField where
  poincare_group := MillenniumPoincareGroup
  poincare_structure := by infer_instance
  unitary_rep := millenniumPoincareTrivialUnitaryRep
  action_on_tests := millenniumPoincareTrivialTestAction
  action_on_tests_one := millenniumPoincareTrivialTestAction_one
  action_on_tests_mul := millenniumPoincareTrivialTestAction_mul
  covariance := wightmanToy_covariance
  hamiltonian := wightmanToyHamiltonian
  is_hamiltonian_self_adjoint := wightmanToy_hamiltonian_selfAdjoint
  is_hamiltonian_positive := wightmanToy_hamiltonian_positive
  spaceTranslation := wightmanToySpatialTranslation
  spaceTranslation_zero := wightmanToySpatialTranslation_zero
  spaceTranslation_add := wightmanToySpatialTranslation_add
  spectrum_nonneg := wightmanToy_spectrum_nonneg
  vacuum_energy_zero := wightmanToy_vacuum_energy_zero
  vacuum := wightmanToyVacuum
  is_vacuum := wightmanToy_isVacuum
  vacuum_invariant := wightmanToy_vacuum_poincare_invariant
  vacuum_spatial_invariant := wightmanToy_vacuum_spatial_invariant
  vacuum_cyclic := wightmanToy_vacuum_cyclic
  locality := wightmanToy_locality

end

end Hqiv.Story
