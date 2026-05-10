import Hqiv.Geometry.HQVMetric
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold

/-!
# HQVM causal interval on the `Fin 4` chart (diagonal synchronous metric)

Defines the quadratic invariant `∑_{μ,ν} g_{μν} Δ^μ Δ^ν` for the HQVM metric tensor
(`HQVMetric`) and relates it to the Minkowski chart polynomial `minkowskiIntervalSq` from
`ContinuumManyBodyQFTScaffold`.

**Sign convention:** with `g₀₀ = -N²` and `gᵢᵢ = s = a²(1-2Φ) > 0`, a vector is **spacelike**
iff `g(v,v) > 0` (standard Lorentzian `(-,+,+,+)`). In the Minkowski-limit chart,
`hqvmIntervalSq 1 1 0 Δ = -minkowskiIntervalSq Δ`, so `hqvmSpacelikeSep` (defined from
`hqvmIntervalSq Δ > 0`) matches `minkowskiSpacelikeSep` (defined from `minkowskiIntervalSq < 0`).

**Conformal layer:** rescaling the Minkowski polynomial by `Ω²` with `Ω ≠ 0` preserves strict
inequality signs — the usual causal classification for a conformally flat metric.
-/

namespace Hqiv.Geometry

open scoped BigOperators
open Hqiv.QM

noncomputable section

/-- Full quadratic invariant `g_{μν} z^μ z^ν` for diagonal synchronous HQVM (sum over all `μ,ν`). -/
noncomputable def hqvmIntervalSq (N a Φ : ℝ) (z : SpacetimeChart) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, HQVM_metric N a Φ μ ν * z μ * z ν

/-- Closed diagonal form (no off-diagonal metric entries). -/
theorem hqvmIntervalSq_eq (N a Φ : ℝ) (z : SpacetimeChart) :
    hqvmIntervalSq N a Φ z =
      HQVM_g_tt N * z 0 ^ 2 +
        HQVM_spatial_coeff a Φ * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
  unfold hqvmIntervalSq
  simp [Fin.sum_univ_four, HQVM_metric, HQVM_g_tt, HQVM_spatial_coeff, mul_assoc, mul_comm, mul_left_comm]
  ring

/-- Minkowski background: `g(v,v) = -(v⁰² - ‖v‖²)` vs `minkowskiIntervalSq = v⁰² - ‖v‖²`. -/
theorem hqvmIntervalSq_Minkowski_eq_neg_minkowski (z : SpacetimeChart) :
    hqvmIntervalSq 1 1 0 z = -minkowskiIntervalSq z := by
  simp [hqvmIntervalSq_eq, HQVM_g_tt, HQVM_spatial_coeff, minkowskiIntervalSq]
  ring

theorem minkowskiIntervalSq_smul (ε : ℝ) (z : SpacetimeChart) :
    minkowskiIntervalSq (fun k => ε * z k) = ε ^ 2 * minkowskiIntervalSq z := by
  simp [minkowskiIntervalSq]
  ring

theorem hqvmIntervalSq_smul (N a Φ : ℝ) (ε : ℝ) (z : SpacetimeChart) :
    hqvmIntervalSq N a Φ (fun k => ε * z k) = ε ^ 2 * hqvmIntervalSq N a Φ z := by
  simp only [hqvmIntervalSq_eq]
  ring

/-- Separation between chart points in the HQVM quadratic. -/
noncomputable def hqvmIntervalSq_sep (N a Φ : ℝ) (x y : SpacetimeChart) : ℝ :=
  hqvmIntervalSq N a Φ (minkowskiSep x y)

/-- Strict **spacelike** separation: positive Lorentzian squared interval `g(Δ,Δ) > 0`. -/
def hqvmSpacelikeSep (N a Φ : ℝ) (x y : SpacetimeChart) : Prop :=
  0 < hqvmIntervalSq_sep N a Φ x y

theorem hqvmSpacelikeSep_minkowski_iff (x y : SpacetimeChart) :
    hqvmSpacelikeSep 1 1 0 x y ↔ minkowskiSpacelikeSep x y := by
  dsimp [hqvmSpacelikeSep, hqvmIntervalSq_sep, minkowskiSpacelikeSep]
  rw [hqvmIntervalSq_Minkowski_eq_neg_minkowski]
  constructor <;> intro h <;> linarith

/-- Same-time spatial separation: Minkowski spacelike implies HQVM spacelike once `s = a²(1-2Φ) > 0`. -/
theorem hqvmSpacelike_of_minkowski_spacelike_same_time (N a Φ : ℝ) {x y : SpacetimeChart}
    (ht : x 0 = y 0) (hs : 0 < HQVM_spatial_coeff a Φ)
    (hm : minkowskiSpacelikeSep x y) : hqvmSpacelikeSep N a Φ x y := by
  have hspatial : 0 < (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 + (x 3 - y 3) ^ 2 := by
    have hmk : minkowskiIntervalSq (minkowskiSep x y) < 0 := hm
    dsimp [minkowskiIntervalSq, minkowskiSep] at hmk
    rw [sub_eq_zero.mpr ht] at hmk
    nlinarith [hmk]
  dsimp [hqvmSpacelikeSep, hqvmIntervalSq_sep]
  rw [hqvmIntervalSq_eq]
  simp [minkowskiSep, ht, HQVM_g_tt]
  nlinarith [hs, hspatial]

/-!
### Conformal rescaling of the Minkowski polynomial
-/

theorem minkowskiIntervalSq_conformal_mul_pos_iff {Ω : ℝ} (hΩ : Ω ≠ 0) (z : SpacetimeChart) :
    (Ω ^ 2 * minkowskiIntervalSq z < 0 ↔ minkowskiIntervalSq z < 0) ∧
      (0 < Ω ^ 2 * minkowskiIntervalSq z ↔ 0 < minkowskiIntervalSq z) ∧
      (Ω ^ 2 * minkowskiIntervalSq z = 0 ↔ minkowskiIntervalSq z = 0) := by
  have hΩ2 : 0 < Ω ^ 2 := sq_pos_of_ne_zero hΩ
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intro h
    · nlinarith [hΩ2]
    · nlinarith [hΩ2]
  · constructor <;> intro h
    · nlinarith [hΩ2]
    · nlinarith [hΩ2]
  · constructor <;> intro h
    · rcases mul_eq_zero.mp h with hΩsq | hm
      · rw [sq_eq_zero_iff] at hΩsq
        exact absurd hΩsq hΩ
      · exact hm
    · simp [h]

/-!
### Microcausality schema (scalar zero commutator) pulled back along an event chart
-/

/-- Spacelike relation from HQVM interval on chart-labeled events. -/
def spacelikeRelationHQVM (N a Φ : ℝ) (chart : EventChart) : SpacelikeRelation :=
  fun x y => hqvmSpacelikeSep N a Φ (chart x) (chart y)

theorem microcausality_zero_comm_hqvmChart (N a Φ : ℝ) (chart : EventChart) :
    MicrocausalityStatement commutatorKernelZero (spacelikeRelationHQVM N a Φ chart) :=
  fun _ _ _ => rfl

def microcausality_in_domain_hqvm_scaffold (N a Φ : ℝ) : Prop :=
  ∀ chart : EventChart, MicrocausalityStatement commutatorKernelZero (spacelikeRelationHQVM N a Φ chart)

theorem microcausality_in_domain_hqvm_scaffold_holds (N a Φ : ℝ) :
    microcausality_in_domain_hqvm_scaffold N a Φ :=
  fun chart => microcausality_zero_comm_hqvmChart N a Φ chart

end

end Hqiv.Geometry
