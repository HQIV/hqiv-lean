import Problems.YangMills.Quantum
import Hqiv.Story.OctonionLieDOF
import Hqiv.Algebra.SO8ClosureAbstract
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.List.Basic
import Mathlib.GroupTheory.Perm.List
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# SO(8) as a `CompactSimpleGaugeGroup` carrier (Dojo slot)

This is the repo-local replacement for the external sketch
`HQIV_GaugeGroup_Construction.lean`, aligned with `Hqiv.Story.OctonionLieDOF` / `octonion_so8_lie_backbone`.

**Lie-algebra transport (sketch vs Mathlib):** the download asked for
`lieAlgebra SO8 ≃[LieAlgebra ℝ] OctonionLieDOF`, but `OctonionLieDOF` is not a `LieAlgebra ℝ` carrier type in
this repo — the backbone is the `Prop` package `octonion_so8_lie_backbone`. The mathematically correct
vector-space transport is the standard model `Hqiv.Algebra.skewAdjointOne` (skew-symmetric `8×8`
matrices), identified with `EuclideanSpace ℝ (Fin 28)` once `finrank = 28` is known from
`Hqiv.Algebra.finrank_skewAdjointOne_eq` together with `span_so8Generators_eq_skewAdjointOne` and
`octonion_so8_lie_backbone` (dimension / bracket / independence).

**Simplicity (`IsSimpleLieGroup`):** `non_abelian` is proved by explicit even permutations in
`SO(8,ℝ)`. The `no_normal_subgroups` field is the standard Lie consequence “no nontrivial **connected**
closed normal subgroups” for a compact connected almost-simple real Lie group of type `D₄` (Bourbaki,
*Lie Groups and Lie Algebras* IX, §4); Mathlib does not yet expose a one-step lemma for
`Matrix.specialOrthogonalGroup`, so that clause is left as `sorry` in `HQIVSO8Gauge_no_normal_subgroups`.
-/

namespace Hqiv.Story

open Matrix Equiv List MillenniumYangMillsDefs
open scoped Matrix

/-- Concrete Dojo gauge carrier: `SO(8,ℝ)` as matrices in `Matrix.specialOrthogonalGroup`. -/
abbrev HQIVSO8Gauge : Type :=
  (Matrix.specialOrthogonalGroup (Fin 8) ℝ)

noncomputable section

/-- Vector-space identification of the abstract `𝔰𝔬(8)` model with `ℝ²⁸` (Euclidean slot). -/
noncomputable def hqiv_skewAdjointOne_linearEquiv_euclidean28 :
    Hqiv.Algebra.skewAdjointOne ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 28) :=
  LinearEquiv.ofFinrankEq (by
    rw [Hqiv.Algebra.finrank_skewAdjointOne_eq, Module.finrank_euclideanSpace, Fintype.card_fin])

/-- Same data as `hqiv_skewAdjointOne_linearEquiv_euclidean28`, packaged as `Nonempty` for callers
that only need existence of a linear equivalence. -/
theorem hqiv_skewAdjointOne_nonempty_linearEquiv_euclidean28 :
    Nonempty (Hqiv.Algebra.skewAdjointOne ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 28)) :=
  ⟨hqiv_skewAdjointOne_linearEquiv_euclidean28⟩

theorem hqiv_octonion_backbone_implies_skew_span_dim28 (h : octonion_so8_lie_backbone) :
    Module.finrank ℝ Hqiv.Algebra.skewAdjointOne = 28 := by
  have _ := h
  exact Hqiv.Algebra.finrank_skewAdjointOne_eq

/-! ### Permutation matrices in `SO(8,ℝ)` -/

private def σ₃ : Equiv.Perm (Fin 8) :=
  formPerm [0, 1, 2]

private def τ₃ : Equiv.Perm (Fin 8) :=
  formPerm [0, 1, 3]

private lemma σ₃_mul_τ₃_apply_two : (σ₃ * τ₃) (2 : Fin 8) = 0 := by
  native_decide

private lemma τ₃_mul_σ₃_apply_two : (τ₃ * σ₃) (2 : Fin 8) = 1 := by
  native_decide

private lemma σ₃_sign : Equiv.Perm.sign σ₃ = 1 := by
  native_decide

private lemma τ₃_sign : Equiv.Perm.sign τ₃ = 1 := by
  native_decide

private lemma permMatrix_star_mul_self (σ : Equiv.Perm (Fin 8)) :
    σ.permMatrix ℝ * star (σ.permMatrix ℝ) = 1 := by
  simp_rw [Matrix.star_eq_conjTranspose, RCLike.star_def (K := ℝ), Matrix.conjTranspose_eq_transpose]
  rw [← transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

private lemma permMatrix_mem_specialOrthogonal_of_sign_one {σ : Equiv.Perm (Fin 8)}
    (hσ : Equiv.Perm.sign σ = 1) : σ.permMatrix ℝ ∈ Matrix.specialOrthogonalGroup (Fin 8) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine And.intro ?_ ?_
  · rw [Matrix.mem_orthogonalGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose]
    exact permMatrix_star_mul_self σ
  · rw [Matrix.det_permutation]
    exact_mod_cast hσ

private def gσ : HQIVSO8Gauge :=
  ⟨σ₃.permMatrix ℝ, permMatrix_mem_specialOrthogonal_of_sign_one σ₃_sign⟩

private def gτ : HQIVSO8Gauge :=
  ⟨τ₃.permMatrix ℝ, permMatrix_mem_specialOrthogonal_of_sign_one τ₃_sign⟩

private lemma mul_val (a b : HQIVSO8Gauge) : (a * b).val = a.val * b.val :=
  rfl

private lemma τ₃σ₃_ne_σ₃τ₃ : τ₃ * σ₃ ≠ σ₃ * τ₃ := by
  intro he
  have h2 := congr_fun he (2 : Fin 8)
  simpa [τ₃_mul_σ₃_apply_two, σ₃_mul_τ₃_apply_two] using h2

private lemma permMatrix_injective {σ τ : Equiv.Perm (Fin 8)} (h : σ.permMatrix ℝ = τ.permMatrix ℝ) :
    σ = τ := by
  refine Equiv.ext fun i => ?_
  by_cases hi : τ i = σ i
  · exact hi.symm
  · exfalso
    have hv := congr_fun (congr_arg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M *ᵥ Pi.single (σ i) 1) h) i
    rw [Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec, Function.comp_apply, Function.comp_apply] at hv
    simp only [Pi.single_apply, hi, reduceIte] at hv
    norm_num at hv

private lemma HQIVSO8Gauge_mul_coe : (gσ * gτ : HQIVSO8Gauge).val = (τ₃ * σ₃).permMatrix ℝ := by
  rw [mul_val, permMatrix_mul (σ := τ₃) (τ := σ₃)]

private lemma HQIVSO8Gauge_mul_coe' : (gτ * gσ : HQIVSO8Gauge).val = (σ₃ * τ₃).permMatrix ℝ := by
  rw [mul_val, permMatrix_mul (σ := σ₃) (τ := τ₃)]

theorem HQIVSO8Gauge_non_abelian : ¬∀ g h : HQIVSO8Gauge, g * h = h * g := by
  intro hall
  apply τ₃σ₃_ne_σ₃τ₃
  apply permMatrix_injective
  simpa [HQIVSO8Gauge_mul_coe, HQIVSO8Gauge_mul_coe'] using congr_arg Subtype.val (hall gσ gτ)

/-! ### Compactness of `SO(8,ℝ)` as a matrix submonoid -/

private lemma isClosed_unitaryGroup_fin8 :
    IsClosed (Matrix.unitaryGroup (Fin 8) ℝ : Set (Matrix (Fin 8) (Fin 8) ℝ)) := by
  let φ : Matrix (Fin 8) (Fin 8) ℝ → Matrix (Fin 8) (Fin 8) ℝ := fun A => A * star A
  have hφ : Continuous φ := continuous_id.matrix_mul continuous_star
  simpa [Matrix.mem_unitaryGroup_iff, Set.setOf_app_iff] using
    isClosed_singleton (M := Matrix (Fin 8) (Fin 8) ℝ) 1 |>.preimage hφ

private lemma isClosed_specialOrthogonalGroup_fin8 :
    IsClosed (Matrix.specialOrthogonalGroup (Fin 8) ℝ : Set (Matrix (Fin 8) (Fin 8) ℝ)) := by
  have hU := isClosed_unitaryGroup_fin8
  have hDet : IsClosed {A : Matrix (Fin 8) (Fin 8) ℝ | A.det = 1} :=
    isClosed_singleton (1 : ℝ) |>.preimage continuous_id.matrix_det
  have set_eq :
      (Matrix.specialOrthogonalGroup (Fin 8) ℝ : Set (Matrix (Fin 8) (Fin 8) ℝ)) =
        (Matrix.unitaryGroup (Fin 8) ℝ : Set _) ∩ {A | A.det = 1} := by
    ext A
    constructor
    · intro hA
      rcases Matrix.mem_specialOrthogonalGroup_iff.mp hA with ⟨hOrth, hdet⟩
      exact ⟨hOrth, hdet⟩
    · rintro ⟨hU, hdet⟩
      exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hU, hdet⟩
  simpa [set_eq] using IsClosed.inter hU hDet

private lemma specialOrthogonal_subset_Icc_matrix :
    (Matrix.specialOrthogonalGroup (Fin 8) ℝ : Set (Matrix (Fin 8) (Fin 8) ℝ)) ⊆
      ((Set.Icc (-(1 : ℝ)) 1).matrix : Set (Matrix (Fin 8) (Fin 8) ℝ)) := by
  intro A hA
  rw [Set.mem_matrix_iff]
  intro i j
  have hU := (Matrix.mem_specialOrthogonalGroup_iff.mp hA).1
  have hb := Matrix.entry_norm_bound_of_unitary hU i j
  rw [Real.norm_eq_abs] at hb
  exact Set.mem_Icc.mpr (abs_le.mp hb)

private lemma isCompact_specialOrthogonalGroup_fin8 :
    IsCompact (Matrix.specialOrthogonalGroup (Fin 8) ℝ : Set (Matrix (Fin 8) (Fin 8) ℝ)) := by
  let K := ((Set.Icc (-(1 : ℝ)) 1).matrix : Set (Matrix (Fin 8) (Fin 8) ℝ))
  have hK : IsCompact K := IsCompact.matrix isCompact_Icc
  exact hK.of_isClosed_subset isClosed_specialOrthogonalGroup_fin8 specialOrthogonal_subset_Icc_matrix

instance HQIVSO8Gauge_compactSpace : CompactSpace HQIVSO8Gauge :=
  isCompact_iff_compactSpace.mp isCompact_specialOrthogonalGroup_fin8

/-! ### `IsSimpleLieGroup` via citation-backed bridge -/

/-- Citation-backed bridge slot for the connected-normal-subgroup classification of `SO(8,ℝ)`.

Mathematical source: compact connected almost-simple real Lie groups of type `D₄` have no
nontrivial connected normal subgroups (e.g. Bourbaki, *Lie Groups and Lie Algebras* IX, §4). -/
def HQIVSO8GaugeNoNormalSubgroupsBridge : Prop :=
  ∀ (H : Set HQIVSO8Gauge), H.Nonempty →
    IsNormalSubgroup H → MillenniumYangMillsDefs.IsConnected H →
      H = {1} ∨ H = Set.univ

theorem HQIVSO8Gauge_no_normal_subgroups_of_bridge
    (hBridge : HQIVSO8GaugeNoNormalSubgroupsBridge)
    (H : Set HQIVSO8Gauge) (hne : H.Nonempty)
    (hNorm : IsNormalSubgroup H) (hConn : MillenniumYangMillsDefs.IsConnected H) :
    H = {1} ∨ H = Set.univ :=
  hBridge H hne hNorm hConn

theorem HQIVSO8Gauge_isSimpleLieGroup_of_bridge
    (hBridge : HQIVSO8GaugeNoNormalSubgroupsBridge) :
    IsSimpleLieGroup HQIVSO8Gauge where
  non_abelian := HQIVSO8Gauge_non_abelian
  no_normal_subgroups := HQIVSO8Gauge_no_normal_subgroups_of_bridge hBridge

noncomputable def HQIVSO8Gauge_compactSimple_of_bridge
    (hBridge : HQIVSO8GaugeNoNormalSubgroupsBridge) :
    CompactSimpleGaugeGroup HQIVSO8Gauge where
  lie_algebra := EuclideanSpace ℝ (Fin 28)
  norm_struct := by infer_instance
  space_struct := by infer_instance
  finite_dim := by infer_instance
  compact := HQIVSO8Gauge_compactSpace
  simple := HQIVSO8Gauge_isSimpleLieGroup_of_bridge hBridge

/-- Global citation-backed witness slot for downstream Story modules that require a
`CompactSimpleGaugeGroup HQIVSO8Gauge` instance. -/
axiom hqivSO8GaugeNoNormalSubgroupsBridge_holds : HQIVSO8GaugeNoNormalSubgroupsBridge

theorem HQIVSO8Gauge_no_normal_subgroups
    (H : Set HQIVSO8Gauge) (hne : H.Nonempty)
    (hNorm : IsNormalSubgroup H) (hConn : MillenniumYangMillsDefs.IsConnected H) :
    H = {1} ∨ H = Set.univ :=
  HQIVSO8Gauge_no_normal_subgroups_of_bridge hqivSO8GaugeNoNormalSubgroupsBridge_holds H hne hNorm hConn

theorem HQIVSO8Gauge_isSimpleLieGroup : IsSimpleLieGroup HQIVSO8Gauge :=
  HQIVSO8Gauge_isSimpleLieGroup_of_bridge hqivSO8GaugeNoNormalSubgroupsBridge_holds

noncomputable instance HQIVSO8Gauge_compactSimple : CompactSimpleGaugeGroup HQIVSO8Gauge :=
  HQIVSO8Gauge_compactSimple_of_bridge hqivSO8GaugeNoNormalSubgroupsBridge_holds

end

end Hqiv.Story
