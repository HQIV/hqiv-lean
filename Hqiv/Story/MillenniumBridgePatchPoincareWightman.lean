import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold
import Hqiv.Story.MillenniumBridgePatchSchwartzJets
import Hqiv.Story.MillenniumBridgePatchVacuum
import Hqiv.Story.LadderGapCandidateWell
import Mathlib.Tactic.FinCases
import Problems.YangMills.Quantum

/-!
# Patch Hilbert Wightman layer + ladder-scaled Hamiltonian

Carrier: **`PatchHilbert = LatticeHilbert 4`** with `InnerProductSpace ℝ` via `complexToReal`.

Field: **directional derivatives at the origin** (standard `ℝ⁴` basis of `Spacetime`) paired with
coordinate embeddings on `PatchHilbert`.

Poincaré bookkeeping: the group is **`Multiplicative Space ≅ (ℝ³,+)`** (spatial translations only).
The unitary representation and test action remain **trivial**, and **`patchSpatialTranslation`**
remains **identity**, because `patchLineDerivℂAtZero` freezes jets at the origin: a genuine
Schwartz pullback along `x ↦ x - patchEmbedSpatial v` would not match `lineDerivOpCLM` at `0`
without re-centring the derivative (see `Mathlib`’s `lineDerivOp_compCLMOfContinuousLinearEquiv`
for the **linear** chart-change case). The upgrade records the **spatial translation group type**
expected by `PatchWightmanAxioms` while keeping the present jet scaffold consistent.

Hamiltonian: **`ladderGapCandidate • (I − rankOne Ω Ω)`** with `Ω` normalized and entrywise nonzero.

**Patch smearing (`Option 2`).** The field uses **`PatchSchwartzSpace = 𝓢(ℝ⁴, ℂ)`** and first jets
`∂_{eᵢ} f (0) ∈ ℂ`, packaged as `patchSlotLin c i` (one complex slot coefficient per direction). This
matches **`finrank ℝ PatchHilbert = 8`** (four complex chart directions). **W4** is reduced to a
single Schwartz **jet surjectivity** placeholder `schwartzMap_complex_directionalJets_at_zero` (same
role as `schwartzMap_real_eqAt_zero` in the toy line).

Abelian patch sandwich: `patchHilbertPatchBridge.patchOpAsLinearOperator (smearedField 0) = 0`.
-/

namespace Hqiv.Story

open Hqiv.QM
open MillenniumYangMillsDefs
open InnerProductSpace
open ContinuousLinearMap
open Module
open Finset
open scoped SchwartzMap

noncomputable section

open EuclideanSpace SchwartzMap LineDeriv

/-- Real inner product on the `ℂ⁴` patch carrier used by Dojo-style `InnerProductSpace ℝ H`. -/
noncomputable instance patchHilbertInnerReal : InnerProductSpace ℝ PatchHilbert :=
  InnerProductSpace.complexToReal

instance patchHilbert_complete : CompleteSpace PatchHilbert := by
  simpa [PatchHilbert] using inferInstanceAs (CompleteSpace (PiLp 2 fun _ : Fin 4 => ℂ))

instance patchHilbert_nontrivial : Nontrivial PatchHilbert := by
  refine ⟨⟨EuclideanSpace.single (0 : Fin 4) (1 : ℂ), EuclideanSpace.single (0 : Fin 4) (2 : ℂ), ?_⟩⟩
  intro he
  have := congr_arg (fun v : PatchHilbert => v 0) he
  simp [EuclideanSpace.single_apply] at this

instance patchHilbert_end_nontrivial : Nontrivial (PatchHilbert →L[ℝ] PatchHilbert) := by
  refine ⟨⟨(1 : PatchHilbert →L[ℝ] PatchHilbert), 0, ?_⟩⟩
  intro rid
  have := congr_arg (fun f : PatchHilbert →L[ℝ] PatchHilbert => ‖f‖) rid
  simp at this

/-- Wightman vacuum vector on the patch carrier (same as `patchVacuum`). -/
noncomputable def patchWightmanOmega : PatchHilbert :=
  patchVacuum

theorem patchWightmanOmega_norm : ‖patchWightmanOmega‖ = 1 := by
  simpa [patchWightmanOmega] using patchVacuum_norm

theorem patchWightmanOmega_inner_self : inner ℝ patchWightmanOmega patchWightmanOmega = 1 := by
  rw [patchWightmanOmega, real_inner_eq_re_inner, patchVacuum_inner_self]
  simp

/-- Standard basis vectors in `Spacetime = ℝ⁴`. -/
noncomputable def spacetimeBasis (i : Fin 4) : Spacetime :=
  EuclideanSpace.single i (1 : ℝ)

/-- Point evaluation `f ↦ f 0` on complex Schwartz space (continuous `ℂ`-linear). -/
noncomputable def patchSchwartzEvalAtZero : PatchSchwartzSpace →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f : PatchSchwartzSpace => f (0 : Spacetime))
    (fun f g => rfl)
    (fun a f => rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      simp only [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      exact SchwartzMap.norm_le_seminorm ℂ f (0 : Spacetime)⟩

@[simp]
theorem patchSchwartzEvalAtZero_apply (f : PatchSchwartzSpace) :
    patchSchwartzEvalAtZero f = f (0 : Spacetime) :=
  rfl

/-- Complex directional derivative at the origin: `f ↦ ∂_m f (0)` (ℂ-linear). -/
noncomputable def patchLineDerivℂAtZero (m : Spacetime) : PatchSchwartzSpace →L[ℂ] ℂ :=
  patchSchwartzEvalAtZero ∘L lineDerivOpCLM ℂ PatchSchwartzSpace m

/-- Embed `ψ i` back along chart index `i` (ℂ-linear, then restricted to `ℝ`). -/
noncomputable def patchEmbedCoordℂ (i : Fin 4) : PatchHilbert →L[ℂ] PatchHilbert :=
  ContinuousLinearMap.smulRight (EuclideanSpace.proj i) (EuclideanSpace.single i (1 : ℂ))

noncomputable def patchEmbedCoord (i : Fin 4) : PatchHilbert →L[ℝ] PatchHilbert :=
  (patchEmbedCoordℂ i).restrictScalars ℝ

/-- Scale the slot-`i` chart coordinate by `c` (ℂ-linear, then restricted to `ℝ`). -/
noncomputable def patchSlotLinℂ (c : ℂ) (i : Fin 4) : PatchHilbert →L[ℂ] PatchHilbert :=
  (c • ContinuousLinearMap.id ℂ PatchHilbert).comp (patchEmbedCoordℂ i)

noncomputable def patchSlotLin (c : ℂ) (i : Fin 4) : PatchHilbert →L[ℝ] PatchHilbert :=
  (patchSlotLinℂ c i).restrictScalars ℝ

/-- Smeared field: first complex jets at the origin, one slot per direction. -/
noncomputable def patchDerivOVD : PatchOperatorValuedDistribution PatchHilbert := fun f =>
  Finset.univ.sum fun i : Fin 4 =>
    patchSlotLin (patchLineDerivℂAtZero (spacetimeBasis i) f) i

theorem patchDerivOVD_apply (f : PatchSchwartzSpace) (ψ : PatchHilbert) :
    patchDerivOVD f ψ =
      Finset.univ.sum fun i : Fin 4 =>
        patchSlotLin (patchLineDerivℂAtZero (spacetimeBasis i) f) i ψ := by
  simp [patchDerivOVD, Finset.sum_apply]

theorem patchEmbedCoordℂ_comp_comm (i j : Fin 4) :
    (patchEmbedCoordℂ i).comp (patchEmbedCoordℂ j) = (patchEmbedCoordℂ j).comp (patchEmbedCoordℂ i) := by
  simp only [patchEmbedCoordℂ, smulRight_comp_smulRight]
  refine ContinuousLinearMap.ext fun v => ?_
  rcases eq_or_ne i j with rfl | hij
  · ext k
    simp only [smulRight_apply, PiLp.proj_apply, EuclideanSpace.single_apply, smul_smul]
  · ext k
    simp [hij, Ne.symm hij, smulRight_apply, PiLp.proj_apply, EuclideanSpace.single_apply, smul_zero,
      PiLp.zero_apply]

theorem patchEmbedCoord_comp_comm (i j : Fin 4) :
    (patchEmbedCoord i).comp (patchEmbedCoord j) = (patchEmbedCoord j).comp (patchEmbedCoord i) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hℂ :=
    congrArg (fun T : PatchHilbert →L[ℂ] PatchHilbert => T v) (patchEmbedCoordℂ_comp_comm i j)
  simpa [patchEmbedCoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using hℂ

theorem patchSlotLinℂ_comp_comm (i j : Fin 4) (c d : ℂ) :
    (patchSlotLinℂ c i).comp (patchSlotLinℂ d j) = (patchSlotLinℂ d j).comp (patchSlotLinℂ c i) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [patchSlotLinℂ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rcases eq_or_ne i j with rfl | hij
  · ext k
    simp only [patchEmbedCoordℂ, smulRight_apply, PiLp.proj_apply, EuclideanSpace.single_apply,
      smul_smul]
    rcases eq_or_ne k i with rfl | hki
    · simp [mul_assoc, mul_comm, mul_left_comm]
    · simp [hki, Ne.symm hki]
  · ext k
    simp [hij, Ne.symm hij, patchEmbedCoordℂ, smulRight_apply, PiLp.proj_apply,
      EuclideanSpace.single_apply, smul_zero, PiLp.zero_apply]

theorem patchSlotLin_comp_comm (i j : Fin 4) (c d : ℂ) :
    (patchSlotLin c i).comp (patchSlotLin d j) = (patchSlotLin d j).comp (patchSlotLin c i) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simpa [patchSlotLin, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using
    congrArg (fun T : PatchHilbert →L[ℂ] PatchHilbert => T v) (patchSlotLinℂ_comp_comm i j c d)

/-! ### Spatial translation group + trivial jet-level representation -/

/-- Spatial translation group `(ℝ³,+)` in multiplicative notation (Clay `spaceTranslation` carrier). -/
abbrev PatchMillenniumPoincareGroup : Type :=
  Multiplicative Space

/-- Embed `a ∈ ℝ³` into `Spacetime = ℝ⁴` as `(0, a₀, a₁, a₂)` (time index `0 : Fin 4`). -/
noncomputable def patchEmbedSpatial (a : Space) : Spacetime :=
  Finset.univ.sum fun j : Fin 3 => EuclideanSpace.single (Fin.succ j) (a j)

@[simp]
theorem patchEmbedSpatial_zero : patchEmbedSpatial (0 : Space) = (0 : Spacetime) := by
  classical
  ext i
  fin_cases i <;> (
    simp [patchEmbedSpatial, Finset.sum_apply, EuclideanSpace.single_apply, Fin.sum_univ_succ,
      Fin.succ_ne_zero])

noncomputable def patchMillenniumPoincareTrivialUnitaryRep :
    PatchMillenniumPoincareGroup →* (PatchHilbert ≃ₗᵢ[ℝ] PatchHilbert) where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp only [one_mul]

@[simp]
theorem patchMillenniumPoincareTrivialUnitaryRep_apply (g : PatchMillenniumPoincareGroup) :
    patchMillenniumPoincareTrivialUnitaryRep g = (1 : PatchHilbert ≃ₗᵢ[ℝ] PatchHilbert) :=
  rfl

@[simp]
noncomputable def patchMillenniumPoincareTrivialTestAction (_g : PatchMillenniumPoincareGroup)
    (f : PatchSchwartzSpace) : PatchSchwartzSpace :=
  f

@[simp]
theorem patchMillenniumPoincareTrivialTestAction_one (f : PatchSchwartzSpace) :
    patchMillenniumPoincareTrivialTestAction (1 : PatchMillenniumPoincareGroup) f = f :=
  rfl

theorem patchMillenniumPoincareTrivialTestAction_mul (g₁ g₂ : PatchMillenniumPoincareGroup)
    (f : PatchSchwartzSpace) :
    patchMillenniumPoincareTrivialTestAction (g₁ * g₂) f =
      patchMillenniumPoincareTrivialTestAction g₁ (patchMillenniumPoincareTrivialTestAction g₂ f) :=
  rfl

lemma conjugateOperator_one_eq {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : LinearOperator H) :
    conjugateOperator (1 : H ≃ₗᵢ[ℝ] H) A = A := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have h1symm : (1 : H ≃ₗᵢ[ℝ] H).symm = 1 := by rw [← LinearIsometryEquiv.inv_def, inv_one]
  have h1clm :
      (1 : H ≃ₗᵢ[ℝ] H).toContinuousLinearEquiv = ContinuousLinearEquiv.refl ℝ H := by
    rw [LinearIsometryEquiv.one_def, LinearIsometryEquiv.toContinuousLinearEquiv_refl]
  simp only [conjugateOperator, ContinuousLinearMap.comp_apply, h1symm, h1clm,
    ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]

theorem patchDeriv_covariance (g : PatchMillenniumPoincareGroup) (f : PatchSchwartzSpace) :
    patchDerivOVD (patchMillenniumPoincareTrivialTestAction g f) =
      conjugateOperator (patchMillenniumPoincareTrivialUnitaryRep g) (patchDerivOVD f) := by
  simp only [patchMillenniumPoincareTrivialTestAction]
  rw [patchMillenniumPoincareTrivialUnitaryRep_apply g]
  refine ContinuousLinearMap.ext fun ψ => ?_
  simp only [patchDerivOVD, Finset.sum_apply]
  rw [conjugateOperator_one_eq]

theorem patchDeriv_locality (f g : PatchSchwartzSpace)
    (_h : ∀ (x y : Spacetime),
      (MinkowskiMetric (x - y) (x - y) < 0) → (f : Spacetime → ℂ) x = 0 ∨ (g : Spacetime → ℂ) y = 0) :
    patchDerivOVD f ∘L patchDerivOVD g = patchDerivOVD g ∘L patchDerivOVD f := by
  classical
  let P (i : Fin 4) : PatchHilbert →L[ℝ] PatchHilbert :=
    patchSlotLin (patchLineDerivℂAtZero (spacetimeBasis i) f) i
  let Q (j : Fin 4) : PatchHilbert →L[ℝ] PatchHilbert :=
    patchSlotLin (patchLineDerivℂAtZero (spacetimeBasis j) g) j
  have hf : patchDerivOVD f = Finset.univ.sum (fun i : Fin 4 => P i) := by
    dsimp [patchDerivOVD, P]
  have hg : patchDerivOVD g = Finset.univ.sum (fun j : Fin 4 => Q j) := by
    dsimp [patchDerivOVD, Q]
  rw [hf, hg, ContinuousLinearMap.finset_sum_comp]
  rw [Finset.sum_congr rfl fun i _ => ContinuousLinearMap.comp_finset_sum (P i) Q]
  dsimp [P, Q]
  rw [Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => patchSlotLin_comp_comm i j _ _]
  rw [Finset.sum_comm]
  rw [← Finset.sum_congr rfl fun j _ => ContinuousLinearMap.comp_finset_sum (Q j) P]
  rw [← ContinuousLinearMap.finset_sum_comp]

/-! ### Spatial translations on `PatchHilbert` (identity; see module comment) -/

abbrev patchSpatialTranslation (_ : Space) : PatchHilbert ≃ₗᵢ[ℝ] PatchHilbert :=
  1

@[simp]
theorem patchSpatialTranslation_zero :
    patchSpatialTranslation (0 : Space) = (1 : PatchHilbert ≃ₗᵢ[ℝ] PatchHilbert) :=
  rfl

theorem patchSpatialTranslation_add (x y : Space) :
    patchSpatialTranslation (x + y) = patchSpatialTranslation x * patchSpatialTranslation y :=
  rfl

/-! ### Hamiltonian -/

noncomputable def patchRankOneOmega : PatchHilbert →L[ℝ] PatchHilbert :=
  rankOne ℝ patchWightmanOmega patchWightmanOmega

/-- Orthogonal complement projector `I − |Ω⟩⟨Ω|` onto `({Ω}ᗮ)` with `‖Ω‖ = 1`. -/
noncomputable def patchComplementProjector : PatchHilbert →L[ℝ] PatchHilbert :=
  ContinuousLinearMap.id ℝ PatchHilbert - patchRankOneOmega

noncomputable def patchHamiltonian : LinearOperator PatchHilbert :=
  ladderGapCandidate • patchComplementProjector

theorem patchRankOneOmega_selfAdjoint : IsSelfAdjoint patchRankOneOmega := by
  simpa [patchRankOneOmega] using
    LinearMap.IsSymmetric.isSelfAdjoint (InnerProductSpace.isSymmetric_rankOne_self
      (E := PatchHilbert) (𝕜 := ℝ) patchWightmanOmega)

theorem patchRankOneOmega_sq :
    patchRankOneOmega.comp patchRankOneOmega = patchRankOneOmega := by
  simp [patchRankOneOmega, rankOne_comp_rankOne, patchWightmanOmega_norm, one_smul]

theorem patchComplementProjector_sq :
    patchComplementProjector.comp patchComplementProjector = patchComplementProjector := by
  simp only [patchComplementProjector, sub_comp, comp_sub, id_comp, comp_id, patchRankOneOmega_sq,
    sub_self, sub_zero]

theorem patchHamiltonian_eq_smul_complement :
    patchHamiltonian = ladderGapCandidate • patchComplementProjector := rfl

theorem patchHamiltonian_isSelfAdjoint : IsSelfAdjoint patchHamiltonian := by
  rw [patchHamiltonian_eq_smul_complement]
  have hQ : IsSelfAdjoint patchComplementProjector :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr (by
      simpa [patchComplementProjector] using
        LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.id
          (InnerProductSpace.isSymmetric_rankOne_self patchWightmanOmega))
  exact IsSelfAdjoint.smul (IsSelfAdjoint.all ladderGapCandidate) hQ

theorem patchComplementProjector_isPositive : patchComplementProjector.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff patchComplementProjector).mpr ⟨?_, ?_⟩
  · simpa [patchComplementProjector] using
      LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.id
        (InnerProductSpace.isSymmetric_rankOne_self patchWightmanOmega)
  · intro ψ
    simp only [patchComplementProjector, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, patchRankOneOmega, rankOne_apply]
    rw [inner_sub_left, inner_smul_left_eq_smul (𝕜 := ℝ)]
    simp_rw [smul_eq_mul]
    rw [real_inner_self_eq_norm_sq ψ]
    have habs : |⟪patchWightmanOmega, ψ⟫_ℝ| ≤ ‖ψ‖ := by
      simpa [patchWightmanOmega_norm, one_mul] using abs_real_inner_le_norm patchWightmanOmega ψ
    have hsq : ⟪patchWightmanOmega, ψ⟫_ℝ ^ 2 ≤ ‖ψ‖ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr habs
    nlinarith [hsq]

theorem patchHamiltonian_isPositive : patchHamiltonian.IsPositive := by
  unfold patchHamiltonian
  exact IsPositive.smul_of_nonneg patchComplementProjector_isPositive
    (le_of_lt ladderGapCandidate_pos)

theorem patch_isVacuum : IsVacuum patchWightmanOmega patchHamiltonian := by
  simp only [IsVacuum, patchHamiltonian, patchComplementProjector, patchRankOneOmega,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    rankOne_apply, patchWightmanOmega_inner_self, one_smul, sub_self, smul_zero]

theorem patch_vacuum_poincare_invariant (g : PatchMillenniumPoincareGroup) :
    patchMillenniumPoincareTrivialUnitaryRep g patchWightmanOmega = patchWightmanOmega :=
  rfl

theorem patch_vacuum_spatial_invariant (x : Space) :
    patchSpatialTranslation x patchWightmanOmega = patchWightmanOmega :=
  rfl

def PatchWightmanMassGapOnSpectrum (Δ : ℝ) : Prop :=
  Δ > 0 ∧ Disjoint (spectrum ℝ patchHamiltonian) (Set.Ioo 0 Δ)

theorem patchWightman_massGapOnSpectrum :
    PatchWightmanMassGapOnSpectrum (ladderGapCandidate / 2) := by
  refine ⟨div_pos ladderGapCandidate_pos (show (0 : ℝ) < 2 by norm_num), ?_⟩
  rw [Set.disjoint_left]
  intro x hx ⟨hxlo, hxhi⟩
  have hx0 : x ≠ 0 := ne_of_gt hxlo
  have hxc : x ≠ ladderGapCandidate := by
    intro rid
    subst rid
    linarith [hxhi, half_pos ladderGapCandidate_pos]
  have hres :
      IsUnit (algebraMap ℝ (PatchHilbert →L[ℝ] PatchHilbert) x - patchHamiltonian) := by
    let P := patchRankOneOmega
    let Q := patchComplementProjector
    let c := ladderGapCandidate
    have hH : patchHamiltonian = c • Q := patchHamiltonian_eq_smul_complement
    have hPQ : P + Q = ContinuousLinearMap.id ℝ PatchHilbert := by
      ext v
      simp [P, Q, patchComplementProjector, add_sub_cancel]
    have hQP : Q.comp P = 0 := by
      simpa [Q, patchComplementProjector] using
        (show (ContinuousLinearMap.id ℝ PatchHilbert - patchRankOneOmega).comp patchRankOneOmega = 0 by
          rw [sub_comp, id_comp, patchRankOneOmega_sq, sub_self])
    have hPQ0 : P.comp Q = 0 := by
      simpa [Q, patchComplementProjector] using
        (show patchRankOneOmega.comp (ContinuousLinearMap.id ℝ PatchHilbert - patchRankOneOmega) = 0 by
          rw [comp_sub, comp_id, patchRankOneOmega_sq, sub_self])
    have hQQ : Q.comp Q = Q := patchComplementProjector_sq
    let R : PatchHilbert →L[ℝ] PatchHilbert := x⁻¹ • P + (x - c)⁻¹ • Q
    have hxsub : x - c ≠ 0 := sub_ne_zero.mpr hxc
    have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    have hxcinv : (x - c) * (x - c)⁻¹ = 1 := mul_inv_cancel₀ hxsub
    have hmul : (algebraMap ℝ (PatchHilbert →L[ℝ] PatchHilbert) x - patchHamiltonian) * R = 1 := by
      rw [ContinuousLinearMap.mul_def, Algebra.algebraMap_eq_smul_one, hH, ContinuousLinearMap.one_def]
      dsimp [R]
      rw [sub_comp, comp_add (x • ContinuousLinearMap.id ℝ PatchHilbert),
        comp_add (c • Q)]
      rw [smul_comp, comp_smul, id_comp, smul_comp, comp_smul, id_comp]
      rw [smul_comp, comp_smul, hQP]
      rw [smul_comp, comp_smul, hQQ, smul_smul]
      rw [smul_smul, hxinv, one_smul, smul_smul]
      have htail :
          (c * x⁻¹) • (0 : PatchHilbert →L[ℝ] PatchHilbert) + c • (x - c)⁻¹ • Q =
            (c * (x - c)⁻¹) • Q := by
        have hz : (c * x⁻¹) • (0 : PatchHilbert →L[ℝ] PatchHilbert) = 0 := by
          ext v
          simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply]
        rw [hz, zero_add, ← smul_smul]
      rw [htail, add_sub_assoc, (sub_smul (x * (x - c)⁻¹) (c * (x - c)⁻¹) Q).symm,
        ← sub_mul x c (x - c)⁻¹, hxcinv, one_smul, hPQ]
    have hmul' : R * (algebraMap ℝ (PatchHilbert →L[ℝ] PatchHilbert) x - patchHamiltonian) = 1 := by
      rw [ContinuousLinearMap.mul_def, Algebra.algebraMap_eq_smul_one, hH, ContinuousLinearMap.one_def]
      dsimp [R]
      rw [comp_sub]
      rw [add_comp (x⁻¹ • P) ((x - c)⁻¹ • Q) (x • ContinuousLinearMap.id ℝ PatchHilbert)]
      rw [add_comp (x⁻¹ • P) ((x - c)⁻¹ • Q) (c • Q)]
      rw [← sub_sub]
      have ha1 : (x⁻¹ • P).comp (x • ContinuousLinearMap.id ℝ PatchHilbert) = P := by
        rw [smul_comp, comp_smul, comp_id, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      have ha2 : ((x - c)⁻¹ • Q).comp (x • ContinuousLinearMap.id ℝ PatchHilbert) =
          (x * (x - c)⁻¹) • Q := by
        rw [smul_comp, comp_smul, comp_id, smul_smul, mul_comm x]
      have hb1 : (x⁻¹ • P).comp (c • Q) = 0 := by
        rw [smul_comp, comp_smul, hPQ0]
        ext v
        simp [ContinuousLinearMap.smul_apply, smul_zero]
      have hb2 : ((x - c)⁻¹ • Q).comp (c • Q) = (c * (x - c)⁻¹) • Q := by
        rw [smul_comp, comp_smul, hQQ, smul_smul, mul_comm (x - c)⁻¹]
      rw [ha1, ha2, hb1, hb2, sub_zero, add_sub_assoc, (sub_smul (x * (x - c)⁻¹) (c * (x - c)⁻¹) Q).symm,
        ← sub_mul x c (x - c)⁻¹, hxcinv, one_smul, hPQ]
    exact isUnit_iff_exists.mpr ⟨R, hmul, hmul'⟩
  exact absurd hx (spectrum.notMem_iff.mpr hres)

theorem patch_spectrum_nonneg (E : ℝ) (hE : E ∈ spectrum ℝ patchHamiltonian) : 0 ≤ E := by
  classical
  exact spectrum_nonneg_of_nonneg
    ((ContinuousLinearMap.le_def 0 patchHamiltonian).2 (by simpa using patchHamiltonian_isPositive))
      hE

theorem patch_vacuum_energy_zero : (0 : ℝ) ∈ spectrum ℝ patchHamiltonian := by
  classical
  rw [spectrum.zero_mem_iff]
  intro hunit
  rw [isUnit_iff_bijective] at hunit
  have hn0 : patchWightmanOmega ≠ 0 :=
    (norm_ne_zero_iff (E := PatchHilbert)).1 (by rw [patchWightmanOmega_norm]; norm_num)
  refine hn0 ?_
  exact hunit.1 (patch_isVacuum.trans (map_zero patchHamiltonian).symm)

/-! ### Wightman W4 (vacuum cyclicity) for complex patch smearing -/

theorem patchHilbert_finrank_real : Module.finrank ℝ PatchHilbert = 8 := by
  have hℂ : Module.finrank ℂ PatchHilbert = 4 := by
    simp only [PatchHilbert, LatticeHilbert, finrank_euclideanSpace_fin]
  calc
    Module.finrank ℝ PatchHilbert = 2 * Module.finrank ℂ PatchHilbert :=
      finrank_real_of_complex (E := PatchHilbert)
    _ = 2 * 4 := by rw [hℂ]
    _ = 8 := by norm_num

theorem patchWightmanOmega_coord_eq (j : Fin 4) : patchWightmanOmega j = (2 : ℂ)⁻¹ :=
  Eq.trans (congrArg (fun v : PatchHilbert => v j) (show patchWightmanOmega = patchVacuum from rfl))
    (patchVacuum_apply j)

theorem patchWightmanOmega_coord_ne_zero (j : Fin 4) : patchWightmanOmega j ≠ 0 := by
  rw [patchWightmanOmega_coord_eq]
  exact inv_ne_zero (by norm_num : (2 : ℂ) ≠ 0)

theorem patchSlotLinℂ_apply_omega (c : ℂ) (i j : Fin 4) :
    patchSlotLinℂ c i patchWightmanOmega j = if i = j then c * patchWightmanOmega j else 0 := by
  fin_cases j <;> fin_cases i <;> simp [patchSlotLinℂ, patchEmbedCoordℂ, patchWightmanOmega,
    patchVacuum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smulRight_apply, PiLp.proj_apply, EuclideanSpace.single_apply,
    smul_eq_mul, mul_zero, mul_one, zero_mul, add_zero]

theorem patchSlotLin_apply_omega (c : ℂ) (i j : Fin 4) :
    patchSlotLin c i patchWightmanOmega j = if i = j then c * patchWightmanOmega j else 0 := by
  simpa [patchSlotLin, ContinuousLinearMap.coe_restrictScalars'] using
    patchSlotLinℂ_apply_omega c i j

theorem patchDerivOVD_apply_omega (f : PatchSchwartzSpace) (j : Fin 4) :
    patchDerivOVD f patchWightmanOmega j =
      (patchLineDerivℂAtZero (spacetimeBasis j) f) * patchWightmanOmega j := by
  classical
  have hsum :=
    congrArg (fun v : PatchHilbert => v j) (patchDerivOVD_apply f patchWightmanOmega)
  simp_rw [WithLp.ofLp_sum, Finset.sum_apply] at hsum
  rw [Fintype.sum_eq_single j (fun i hi => by rw [patchSlotLin_apply_omega, if_neg hi])] at hsum
  simpa [patchSlotLin_apply_omega, mul_comm] using hsum

/-!
Schwartz jet surjectivity at the origin (four independent complex directional derivatives).

See `Hqiv.Story.schwartzMap_complex_directionalJets_at_zero_single` for the bump × linear form
construction on `Spacetime`.
-/
lemma schwartzMap_complex_directionalJets_at_zero (w : Fin 4 → ℂ) :
    ∃ f : PatchSchwartzSpace, ∀ i : Fin 4, patchLineDerivℂAtZero (spacetimeBasis i) f = w i := by
  classical
  rcases schwartzMap_complex_directionalJets_at_zero_single w with ⟨f, hf⟩
  refine ⟨f, fun i => ?_⟩
  simp [spacetimeBasis, patchLineDerivℂAtZero, ContinuousLinearMap.comp_apply,
    patchSchwartzEvalAtZero_apply, SchwartzMap.lineDerivOp_apply, hf i]

theorem patchFieldGeneratedSubmodule_patchDeriv_eq_top :
    patchFieldGeneratedSubmodule patchDerivOVD patchWightmanOmega = ⊤ := by
  classical
  refine (Submodule.eq_top_iff').2 fun v => ?_
  rcases schwartzMap_complex_directionalJets_at_zero (fun i => (2 : ℂ) * v i) with ⟨f, hfJet⟩
  let S := Set.range fun g : PatchSchwartzSpace => patchDerivOVD g patchWightmanOmega
  have hmem : v ∈ S := by
    refine ⟨f, ?_⟩
    ext j
    rw [patchDerivOVD_apply_omega, hfJet j, patchWightmanOmega_coord_eq]
    ring
  rw [patchFieldGeneratedSubmodule]
  change v ∈ Submodule.span ℝ S
  exact Submodule.mem_span_of_mem hmem

theorem patch_vacuum_cyclic :
    Dense (patchFieldGeneratedSubmodule patchDerivOVD patchWightmanOmega : Set PatchHilbert) := by
  rw [patchFieldGeneratedSubmodule_patchDeriv_eq_top]
  simp

theorem patchHilbertPatchBridge_smearedField_zero_eq_zeroOperator :
    patchHilbertPatchBridge.patchOpAsLinearOperator (smearedField (fun _ : Fin 4 => (0 : ℝ))) =
      (0 : PatchHilbert →L[ℝ] PatchHilbert) := by
  have hsf : smearedField (fun _ : Fin 4 => (0 : ℝ)) = (0 : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) := by
    ext ψ i
    simp [smearedField_apply]
  simp [hsf, HilbertPatchBridge.patchOpAsLinearOperator_zero]

noncomputable def patchMillenniumPatchWightmanAxioms : PatchWightmanAxioms PatchHilbert patchDerivOVD where
  poincare_group := PatchMillenniumPoincareGroup
  poincare_structure := Multiplicative.group (α := Space)
  unitary_rep := patchMillenniumPoincareTrivialUnitaryRep
  action_on_tests := patchMillenniumPoincareTrivialTestAction
  action_on_tests_one := patchMillenniumPoincareTrivialTestAction_one
  action_on_tests_mul := patchMillenniumPoincareTrivialTestAction_mul
  covariance := patchDeriv_covariance
  hamiltonian := patchHamiltonian
  is_hamiltonian_self_adjoint := patchHamiltonian_isSelfAdjoint
  is_hamiltonian_positive := patchHamiltonian_isPositive
  spaceTranslation := patchSpatialTranslation
  spaceTranslation_zero := patchSpatialTranslation_zero
  spaceTranslation_add := patchSpatialTranslation_add
  spectrum_nonneg := patch_spectrum_nonneg
  vacuum_energy_zero := patch_vacuum_energy_zero
  vacuum := patchWightmanOmega
  is_vacuum := patch_isVacuum
  vacuum_invariant := patch_vacuum_poincare_invariant
  vacuum_spatial_invariant := patch_vacuum_spatial_invariant
  vacuum_cyclic := patch_vacuum_cyclic
  locality := patchDeriv_locality

end

end Hqiv.Story
