import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold
import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold
import Hqiv.QuantumMechanics.LocalAlgebraNetScaffold
import Hqiv.Geometry.HQVMCausalChart

/-!
# Patch QFT bridge (support-restricted net + spatial Minkowski chart)

Builds on `LocalAlgebraNetScaffold` by restricting smeared weights to **regions** `R : Finset (Fin 4)`
(the same discrete chart indices as the trivial net).  **Isotony** is genuine: larger regions allow
more weights.  Operators remain **abelian** (`smearedField`), so commutators vanish as before; the
progress is **geometric packaging** for simulations and future operator kernels.

**Minkowski embedding:** `patchChartPoint i` places each chart index at a unit corner of Minkowski
`ℝ^{1,3}` (time index `0` on the time axis; `1…3` at fixed `t = 0`).  Distinct **spatial** indices are
**strictly spacelike** — suitable for pairing with `spacelikeRelationMinkowski` in continuum scaffolds.

**Event chart (`EventLabel → SpacetimeChart`):** `patchEventChartFour` maps `n < 4` to the same corners
and sends `n ≥ 4` to the zero four-vector (unused in the `Fin 4` patch net).  Disjoint spatial regions
then imply `spacelikeRelationMinkowski patchEventChartFour` on the corresponding **ℕ** labels
(`spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions`).  Together with
`microcausality_zero_comm_minkowskiChart patchEventChartFour` and `patchAlgebraAt_opCommutator_zero`,
this is the **operator + chart + microcausality** patch story at the scaffold level.

See also `Hqiv.Physics.LightConeMaxwellQFTBridge` for shell/mode budget and time-angle hooks.
Smeared interval–max Pauli lifts on `Fin 4 × Fin 4` (`smearedOpIntervalMax`, spacelike support vanishing):
`Hqiv.QuantumMechanics.PatchIntervalMaxSmeared`.

**Metric scaling / HQVM:** `patchChartPointScaled` rescales corner coordinates by `ε` (cell size).
`Hqiv.Geometry.HQVMCausalChart` supplies `minkowskiIntervalSq_smul` / `hqvmIntervalSq_smul` and
`regions_disjoint_spatial_spacelike_hqvm` (same-time spatial corners, `s > 0`).
-/

namespace Hqiv.QM

open scoped InnerProductSpace
open Matrix

noncomputable section

/-- Weights supported on `R`: any nonzero entry lies in the region. -/
def WeightSupportInRegion (R : SpacetimeRegion) (w : Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 4, w i ≠ 0 → i ∈ R

theorem WeightSupportInRegion.mono {R S : SpacetimeRegion} {w : Fin 4 → ℝ}
    (hRS : R ⊆ S) (h : WeightSupportInRegion R w) : WeightSupportInRegion S w := by
  intro i hi
  exact hRS (h i hi)

/-- Smeared operators whose diagonal weights are supported in `R`. -/
noncomputable def patchAlgebraAt (R : SpacetimeRegion) :
    Set (LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) :=
  { A | ∃ w : Fin 4 → ℝ, WeightSupportInRegion R w ∧ A = smearedField w }

theorem mem_patchAlgebraAt_iff (R : SpacetimeRegion)
    (A : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4) :
    A ∈ patchAlgebraAt R ↔ ∃ w : Fin 4 → ℝ, WeightSupportInRegion R w ∧ A = smearedField w :=
  Iff.rfl

theorem patchAlgebraAt_isotony {R S : SpacetimeRegion} (hRS : R ⊆ S) :
    patchAlgebraAt R ⊆ patchAlgebraAt S := by
  rintro A ⟨w, hw, rfl⟩
  exact ⟨w, WeightSupportInRegion.mono hRS hw, rfl⟩

theorem patchAlgebraAt_opCommutator_zero {R S : SpacetimeRegion}
    (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4)
    (hA : A ∈ patchAlgebraAt R) (hB : B ∈ patchAlgebraAt S) :
    opCommutator A B = 0 := by
  rcases hA with ⟨w, _, rfl⟩
  rcases hB with ⟨v, _, rfl⟩
  exact smearedField_opCommutator_eq_zero w v

/-!
### Discrete corners in Minkowski chart (for spacelike region pairs)
-/

/-- Unit corners: index `0` → time axis; `1…3` → purely spatial at `t = 0`. -/
noncomputable def patchChartPoint (i : Fin 4) : SpacetimeChart :=
  match i with
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, 1, 0, 0]
  | 2 => ![0, 0, 1, 0]
  | 3 => ![0, 0, 0, 1]

theorem minkowski_spacelike_patchChartPoint_spatial {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) : minkowskiSpacelikeSep (patchChartPoint i) (patchChartPoint j) := by
  fin_cases i <;> fin_cases j
    <;> simp [patchChartPoint, minkowskiSpacelikeSep, minkowskiIntervalSq, minkowskiSep,
      cons_val_zero, cons_val_one] at hi hj hij ⊢

/-- Spatial unit corners share `t = 0` in the patch chart. -/
theorem patchChartPoint_time_eq_of_ne_zero {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) :
    patchChartPoint i 0 = patchChartPoint j 0 := by
  fin_cases i <;> fin_cases j <;> first | contradiction | simp [patchChartPoint, cons_val_zero]

/-- If regions lie in `Finset.erase univ 0` and are disjoint, corners are pairwise spacelike. -/
theorem regions_disjoint_spatial_spacelike {R S : SpacetimeRegion}
    (hR : R ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hS : S ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0) (hdisj : Disjoint R S) {i j : Fin 4}
    (hi : i ∈ R) (hj : j ∈ S) : minkowskiSpacelikeSep (patchChartPoint i) (patchChartPoint j) := by
  have hi0 : i ≠ 0 := (Finset.mem_erase.mp (hR hi)).1
  have hj0 : j ≠ 0 := (Finset.mem_erase.mp (hS hj)).1
  have hij : i ≠ j := by
    intro heq
    have hiS : i ∈ S := heq ▸ hj
    have hiRS : i ∈ R ∩ S := Finset.mem_inter.mpr ⟨hi, hiS⟩
    have hcap : R ∩ S = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    rw [hcap] at hiRS
    exact absurd hiRS (Finset.notMem_empty i)
  exact minkowski_spacelike_patchChartPoint_spatial hi0 hj0 hij

/-- Rescale every chart coordinate by `ε` (uniform lattice spacing). -/
noncomputable def patchChartPointScaled (ε : ℝ) (i : Fin 4) : SpacetimeChart :=
  fun j => ε * patchChartPoint i j

theorem minkowskiIntervalSq_patchChartPointScaled (ε : ℝ) (i : Fin 4) :
    minkowskiIntervalSq (patchChartPointScaled ε i) = ε ^ 2 * minkowskiIntervalSq (patchChartPoint i) := by
  simpa [patchChartPointScaled] using Hqiv.Geometry.minkowskiIntervalSq_smul ε (patchChartPoint i)

theorem hqvmIntervalSq_patchChartPointScaled (N a Φ : ℝ) (ε : ℝ) (i : Fin 4) :
    Hqiv.Geometry.hqvmIntervalSq N a Φ (patchChartPointScaled ε i) =
      ε ^ 2 * Hqiv.Geometry.hqvmIntervalSq N a Φ (patchChartPoint i) := by
  simpa [patchChartPointScaled] using Hqiv.Geometry.hqvmIntervalSq_smul N a Φ ε (patchChartPoint i)

/-- Disjoint spatial regions ⇒ HQVM spacelike separation between corners when `s = a²(1-2Φ) > 0`. -/
theorem regions_disjoint_spatial_spacelike_hqvm (N a Φ : ℝ) (hs : 0 < Hqiv.HQVM_spatial_coeff a Φ)
    {R S : SpacetimeRegion} (hR : R ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hS : S ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0) (hdisj : Disjoint R S) {i j : Fin 4}
    (hi : i ∈ R) (hj : j ∈ S) :
    Hqiv.Geometry.hqvmSpacelikeSep N a Φ (patchChartPoint i) (patchChartPoint j) := by
  have hi0 : i ≠ 0 := (Finset.mem_erase.mp (hR hi)).1
  have hj0 : j ≠ 0 := (Finset.mem_erase.mp (hS hj)).1
  refine
    Hqiv.Geometry.hqvmSpacelike_of_minkowski_spacelike_same_time N a Φ ?_ hs
      (regions_disjoint_spatial_spacelike hR hS hdisj hi hj)
  exact patchChartPoint_time_eq_of_ne_zero hi0 hj0

/-!
### `EventChart` wiring (`ℕ` labels) ↔ patch net regions

`ContinuumManyBodyQFTScaffold.EventChart` is `ℕ → SpacetimeChart`.  The patch uses the first four
labels as the discrete corner indices; labels `≥ 4` are parked at **0** (not used by `WeightSupportInRegion`
on `Fin 4` weights).
-/

/-- Patch corners as an **event chart**: `n < 4` agrees with `patchChartPoint ⟨n,⋯⟩`; otherwise **0**. -/
noncomputable def patchEventChartFour : EventChart :=
  fun n =>
    if h : n < 4 then patchChartPoint ⟨n, h⟩ else (0 : SpacetimeChart)

theorem patchEventChartFour_lt_four (n : ℕ) (hn : n < 4) : patchEventChartFour n = patchChartPoint ⟨n, hn⟩ := by
  simp [patchEventChartFour, hn]

/-- `spacelikeRelationMinkowski patchEventChartFour` for ℕ labels coming from disjoint spatial regions. -/
theorem spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions {i j : ℕ}
    (hi : i < 4) (hj : j < 4) {R S : SpacetimeRegion}
    (hR : R ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hS : S ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0) (hdisj : Disjoint R S)
    (hiR : ⟨i, hi⟩ ∈ R) (hjS : ⟨j, hj⟩ ∈ S) :
    spacelikeRelationMinkowski patchEventChartFour i j := by
  dsimp [spacelikeRelationMinkowski]
  rw [patchEventChartFour_lt_four i hi, patchEventChartFour_lt_four j hj]
  exact regions_disjoint_spatial_spacelike hR hS hdisj hiR hjS

/-- Scalar microcausality with the patch chart (commutator surrogate still identically `0`). -/
theorem microcausality_zero_comm_patchEventChartFour :
    MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski patchEventChartFour) :=
  microcausality_zero_comm_minkowskiChart patchEventChartFour

/-- Patch observables commute; if the chosen labels lie in disjoint spatial regions, they are
η-spacelike in `patchEventChartFour` (geometry matches `spacelikeRelationMinkowski`). -/
theorem patchAlgebra_opComm_zero_and_events_spacelike_in_patchChart {R S : SpacetimeRegion}
    (hR : R ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hS : S ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0) (hdisj : Disjoint R S)
    (A B : LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4)
    (hA : A ∈ patchAlgebraAt R) (hB : B ∈ patchAlgebraAt S) {i j : ℕ} (hi : i < 4) (hj : j < 4)
    (hiR : ⟨i, hi⟩ ∈ R) (hjS : ⟨j, hj⟩ ∈ S) :
    opCommutator A B = 0 ∧
      spacelikeRelationMinkowski patchEventChartFour i j :=
  ⟨patchAlgebraAt_opCommutator_zero A B hA hB,
    spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions hi hj hR hS hdisj hiR hjS⟩

/-!
### Interval-max commutator surrogate (`max 0 η`) — nonzero on a **timelike** pair

Among labels `{0,1,2,3}` only, corner separations are null or spacelike; pairing label `0` (time corner)
with a **parked** label `≥ 4` (origin in Minkowski) yields **η = 1**, hence `commutatorKernelIntervalMax = 1`.
So the interval-max surrogate is **not** identically zero on `patchEventChartFour` (it is nonzero in the
timelike / η > 0 **domain**).
-/

theorem patchEventChartFour_four : patchEventChartFour 4 = (0 : SpacetimeChart) := by
  simp [patchEventChartFour]

theorem commutatorKernelIntervalMax_patchEventChartFour_0_4_eq_one :
    commutatorKernelIntervalMax patchEventChartFour 0 4 = 1 := by
  unfold commutatorKernelIntervalMax
  rw [patchEventChartFour_lt_four 0 (by decide : (0 : ℕ) < 4), patchEventChartFour_four]
  simp [minkowskiSep, minkowskiIntervalSq, patchChartPoint, cons_val_zero, cons_val_one]

theorem commutatorKernelIntervalMax_patchEventChartFour_0_4_ne_zero :
    commutatorKernelIntervalMax patchEventChartFour 0 4 ≠ 0 := by
  rw [commutatorKernelIntervalMax_patchEventChartFour_0_4_eq_one]
  norm_num

/-- Interval-max microcausality holds on `patchEventChartFour`, **and** the surrogate is nonzero somewhere. -/
theorem microcausality_intervalMax_patchEventChartFour_holds :
    MicrocausalityStatement (commutatorKernelIntervalMax patchEventChartFour)
      (spacelikeRelationMinkowski patchEventChartFour) :=
  microcausality_intervalMax_minkowski patchEventChartFour

theorem microcausality_patchEventChartFour_intervalMax_and_nonzero :
    MicrocausalityStatement (commutatorKernelIntervalMax patchEventChartFour)
        (spacelikeRelationMinkowski patchEventChartFour) ∧
      commutatorKernelIntervalMax patchEventChartFour 0 4 ≠ 0 :=
  ⟨microcausality_intervalMax_patchEventChartFour_holds,
    commutatorKernelIntervalMax_patchEventChartFour_0_4_ne_zero⟩

end

end Hqiv.QM
