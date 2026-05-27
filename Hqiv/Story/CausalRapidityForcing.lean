import Mathlib.Topology.Basic
import Hqiv.Geometry.SharedManifoldRapidity
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Generators

/-!
# Causal rapidity forcing package theorems

This module packages existing results into a single machine-checkable statement:
causal shared-manifold rapidity transport + forced curvature divergence +
the octonionic (`G₂ + Δ`) closure witness.

**Narrative aliases:** `causal_set_growth_forces_spin8` is definitionally the same
theorem as `causal_rapidity_forces_octonion` (the So8 span witness is still an
explicit hypothesis). `causal_shell_growth_law` records the HQIV discrete shell
increment matching \(A(m+1)-A(m)=8(m+2)\). `rapidity_from_causal_poset` is the
common-rapidity transport lemma for a `SATSharedManifoldSmoothBridge`.
-/

namespace Hqiv.Story

open scoped Topology

/-- Discrete shell increment for `Hqiv.available_modes` (paper \(A(m)=4(m+1)(m+2)\)):
`available_modes (m+1) - available_modes m = 8(m+2)`. -/
theorem causal_shell_growth_law (m : ℕ) :
    Hqiv.available_modes (m + 1) - Hqiv.available_modes m = 8 * (m + 2 : ℝ) := by
  simpa [Hqiv.new_modes, Nat.succ_ne_zero] using (Hqiv.new_modes_succ m)

/-- Common rapidity observable induced from a shared SAT manifold bridge
(`B.rapidity` already satisfies the profile equalities). -/
theorem rapidity_from_causal_poset {M : Type*} [TopologicalSpace M]
    (B : Hqiv.Geometry.SATSharedManifoldSmoothBridge M) :
    ∃ ρ : Hqiv.Geometry.SharedRapidityObservable M,
      Hqiv.Geometry.variableRapidityProfile B.shared ρ =
        Hqiv.Geometry.variableRapidityProfile B.shared B.rapidity ∧
      Hqiv.Geometry.clauseRapidityProfile B.shared ρ =
        Hqiv.Geometry.clauseRapidityProfile B.shared B.rapidity :=
  Hqiv.Geometry.shared_manifold_induces_common_rapidity B

/-- Machine-checkable packaged theorem for the causal-rapidity forcing route. -/
theorem causal_rapidity_forces_octonion
    {M : Type*} [TopologicalSpace M]
    (B : Hqiv.Geometry.SATSharedManifoldSmoothBridge M)
    (hSo8Closure :
      (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
       Module.finrank ℝ spanSo8 = 28 ∧
       (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8))) :
    (∃ ρ : Hqiv.Geometry.SharedRapidityObservable M,
      Hqiv.Geometry.variableRapidityProfile B.shared ρ =
        Hqiv.Geometry.variableRapidityProfile B.shared B.rapidity ∧
      Hqiv.Geometry.clauseRapidityProfile B.shared ρ =
        Hqiv.Geometry.clauseRapidityProfile B.shared B.rapidity) ∧
    (0 < Hqiv.curvature_integral Hqiv.referenceM) ∧
    Filter.Tendsto Hqiv.curvature_integral Filter.atTop Filter.atTop ∧
    (Hqiv.omega_k_partial Hqiv.referenceM = 1) ∧
    (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
     Module.finrank ℝ spanSo8 = 28 ∧
     (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Hqiv.Geometry.shared_manifold_induces_common_rapidity B
  · exact Hqiv.curvature_integral_ref_pos
  · exact Hqiv.curvature_integral_tends_to_atTop
  · exact Hqiv.omega_k_partial_at_reference Hqiv.curvature_integral_ref_pos
  · exact hSo8Closure

/-- Same conjunction as `causal_rapidity_forces_octonion` (paper / causal-set narrative name). -/
theorem causal_set_growth_forces_spin8
    {M : Type*} [TopologicalSpace M]
    (B : Hqiv.Geometry.SATSharedManifoldSmoothBridge M)
    (hSo8Closure :
      (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
       Module.finrank ℝ spanSo8 = 28 ∧
       (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8))) :
    (∃ ρ : Hqiv.Geometry.SharedRapidityObservable M,
      Hqiv.Geometry.variableRapidityProfile B.shared ρ =
        Hqiv.Geometry.variableRapidityProfile B.shared B.rapidity ∧
      Hqiv.Geometry.clauseRapidityProfile B.shared ρ =
        Hqiv.Geometry.clauseRapidityProfile B.shared B.rapidity) ∧
    (0 < Hqiv.curvature_integral Hqiv.referenceM) ∧
    Filter.Tendsto Hqiv.curvature_integral Filter.atTop Filter.atTop ∧
    (Hqiv.omega_k_partial Hqiv.referenceM = 1) ∧
    (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
     Module.finrank ℝ spanSo8 = 28 ∧
     (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8)) :=
  causal_rapidity_forces_octonion B hSo8Closure

/-- Equivalent packaged form emphasizing the "real/imaginary layer" wording.
In this repository, the real layer is represented by the scalar causal-growth /
curvature / rapidity channel, while the imaginary layer is represented by the
imported octonionic closure witness.
-/
theorem causal_growth_forces_real_imaginary_layers_d3
    {M : Type*} [TopologicalSpace M]
    (B : Hqiv.Geometry.SATSharedManifoldSmoothBridge M)
    (hSo8Closure :
      (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
       Module.finrank ℝ spanSo8 = 28 ∧
       (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8))) :
    (∃ ρ : Hqiv.Geometry.SharedRapidityObservable M,
      Hqiv.Geometry.variableRapidityProfile B.shared ρ =
        Hqiv.Geometry.variableRapidityProfile B.shared B.rapidity ∧
      Hqiv.Geometry.clauseRapidityProfile B.shared ρ =
        Hqiv.Geometry.clauseRapidityProfile B.shared B.rapidity) ∧
    (0 < Hqiv.curvature_integral Hqiv.referenceM) ∧
    Filter.Tendsto Hqiv.curvature_integral Filter.atTop Filter.atTop ∧
    (Hqiv.omega_k_partial Hqiv.referenceM = 1) ∧
    (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
     Module.finrank ℝ spanSo8 = 28 ∧
     (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8)) :=
  causal_rapidity_forces_octonion B hSo8Closure

/-- Interface theorem for the stacked 1D/2D/3D spin-channel interpretation.

This theorem keeps the proved geometric/algebraic package explicit, while
treating "mild associativity breaking in the 3D layer" and its observational
readout ("superposition form") as additional interface hypotheses.
-/
theorem stacked_spin_channel_forcing_d3_with_superposition_interface
    {M : Type*} [TopologicalSpace M]
    (B : Hqiv.Geometry.SATSharedManifoldSmoothBridge M)
    (hSo8Closure :
      (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
       Module.finrank ℝ spanSo8 = 28 ∧
       (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8)))
    (hMildAssociativityBreaking3D : Prop)
    (hSuperpositionObservable : Prop)
    (hSuperpositionOfMildBreak :
      hMildAssociativityBreaking3D → hSuperpositionObservable) :
    (∃ ρ : Hqiv.Geometry.SharedRapidityObservable M,
      Hqiv.Geometry.variableRapidityProfile B.shared ρ =
        Hqiv.Geometry.variableRapidityProfile B.shared B.rapidity ∧
      Hqiv.Geometry.clauseRapidityProfile B.shared ρ =
        Hqiv.Geometry.clauseRapidityProfile B.shared B.rapidity) ∧
    (0 < Hqiv.curvature_integral Hqiv.referenceM) ∧
    Filter.Tendsto Hqiv.curvature_integral Filter.atTop Filter.atTop ∧
    (Hqiv.omega_k_partial Hqiv.referenceM = 1) ∧
    (let spanSo8 := Submodule.span ℝ (Set.range Hqiv.so8Generator)
     Module.finrank ℝ spanSo8 = 28 ∧
     (∀ k : Fin 28, Hqiv.so8Generator k ∈ spanSo8)) ∧
    (hMildAssociativityBreaking3D → hSuperpositionObservable) := by
  rcases causal_rapidity_forces_octonion B hSo8Closure with
    ⟨hCommonRapidity, hCurvPos, hCurvTendsto, hOmegaRef, hSo8⟩
  exact ⟨hCommonRapidity, hCurvPos, hCurvTendsto, hOmegaRef, hSo8, hSuperpositionOfMildBreak⟩

end Hqiv.Story

