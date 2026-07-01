import HqivSpine.Foundation.Fano
import HqivSpine.Physics.CKMMixingMatrix

/-!
# `HqivSpine.Physics.FanoMixingWeights` — mixing weights from Fano incidence (not mass ratios)

`CKMMixingMatrix` proved the assembled `3×3` matrix is unitary, but its mixing angles were *inputs*
(mass-ratio Gatto–Sartori–Tonin angles + a free phase). This module shores up the **overlap-weight**
caveat (checklist step 1 of `CKM_PMNS_FANO_OVERLAP`): it replaces the phenomenological overlap with a
**graph-theoretic count** on the Fano incidence already proved in `Foundation.Fano`.

* **Overlap weight = shared Fano lines.** `overlap v w` counts the lines through both imaginary
  directions. By the incidence theorems this is **forced**: `overlap v w = 1` for distinct
  directions (`overlap_distinct`, from `unique_common_line`) and `overlap v v = 3`
  (`overlap_self`, from `linesThrough_card`). No fitted sine.
* **The mixing fraction is the graph ratio `1/3`.** `sin²θ = overlap(v,w)/overlap(v,v) = 1/3` for any
  distinct pair (`fano_sinSq_eq_overlap`), a single rational forced by `PG(2,2)` — every pair of
  generations shares one of its three incidences.
* **A Fano-weighted CKM matrix.** Feeding this graph-forced angle into all three planes gives
  `ckmFano`, which is **unitary** (`ckmFano_unitary`) and **CP-violating** when the holonomy phase is
  genuine (`ckmFano_cp_violation`) — now with the *angle* pinned by incidence counts, not masses.

**Honest scope.** The Fano count fixes the **democratic overlap baseline** `sin²θ = 1/3` (maximal,
generation-symmetric mixing) — the combinatorial skeleton of *which* directions mix and *how
strongly at leading incidence order*. It is **not** the measured hierarchical CKM angles; the
hierarchy is the mass-ratio refinement of `MixingAngles` layered on top. This removes the "free
overlap weight" caveat (the weight is now a proved graph invariant) but does not yet fix the physical
angle magnitudes or the phase value `δ`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.FanoMixingWeights

open HqivSpine.Foundation
open HqivSpine.Physics.CKMMixingMatrix
open HqivSpine.Physics.CPHolonomyPhase
open Finset

/-! ## Overlap weight from Fano incidence -/

/-- Lines incident to **both** imaginary directions `v` and `w`. -/
def sharedLines (v w : ImagPoint) : Finset (Fin 7) :=
  Finset.univ.filter fun i => v ∈ fanoLine i ∧ w ∈ fanoLine i

/-- **Overlap weight:** the number of Fano lines through both directions. -/
def overlap (v w : ImagPoint) : ℕ := (sharedLines v w).card

/-- **Distinct directions share exactly one line** — the incidence weight is forced to `1`. -/
theorem overlap_distinct (v w : ImagPoint) (h : v ≠ w) : overlap v w = 1 :=
  unique_common_line v w h

/-- **A direction shares all three of its lines with itself** — the self-weight is `3`. -/
theorem overlap_self (v : ImagPoint) : overlap v v = 3 := by
  unfold overlap sharedLines
  simp only [and_self]
  exact linesThrough_card v

/-! ## The graph-forced mixing fraction `1/3` -/

/-- Sine of the **Fano mixing angle**: `sin θ = √(1/3)` (the democratic overlap baseline). -/
noncomputable def sinθFano : ℝ := Real.sqrt (1 / 3)

/-- Cosine of the **Fano mixing angle**: `cos θ = √(2/3)`. -/
noncomputable def cosθFano : ℝ := Real.sqrt (2 / 3)

theorem sinθFano_pos : 0 < sinθFano := Real.sqrt_pos.mpr (by norm_num)
theorem cosθFano_pos : 0 < cosθFano := Real.sqrt_pos.mpr (by norm_num)

theorem sinθFano_sq : sinθFano ^ 2 = 1 / 3 := by
  rw [sinθFano, Real.sq_sqrt (by norm_num)]

theorem cosθFano_sq : cosθFano ^ 2 = 2 / 3 := by
  rw [cosθFano, Real.sq_sqrt (by norm_num)]

/-- **Pythagoras** for the Fano angle. -/
theorem fano_pyth : cosθFano ^ 2 + sinθFano ^ 2 = 1 := by
  rw [cosθFano_sq, sinθFano_sq]; norm_num

/-- **The mixing fraction is the Fano overlap ratio.** For any two distinct generations the leading
mixing probability `sin²θ` equals the graph-theoretic ratio of shared to total incident lines —
forced to `1/3` by `PG(2,2)`, with no fitted parameter. -/
theorem fano_sinSq_eq_overlap (v w : ImagPoint) (h : v ≠ w) :
    sinθFano ^ 2 = (overlap v w : ℝ) / (overlap v v : ℝ) := by
  rw [sinθFano_sq, overlap_distinct v w h, overlap_self v]; norm_num

/-! ## The Fano-weighted CKM matrix -/

/-- **CKM matrix with all three angles set to the Fano overlap angle** and a holonomy phase `δ`. -/
noncomputable def ckmFano (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ckm cosθFano sinθFano cosθFano sinθFano cosθFano sinθFano δ

/-- **The Fano-weighted CKM matrix is unitary.** -/
theorem ckmFano_unitary (δ : ℝ) : ckmFano δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  ckm_unitary fano_pyth fano_pyth fano_pyth

/-- **Unitarity certificate:** `VᴴV = 1`. -/
theorem ckmFano_unitary_apply (δ : ℝ) : star (ckmFano δ) * ckmFano δ = 1 :=
  (ckmFano_unitary δ).1

/-- **CP violation from a graph-weighted matrix:** the Jarlskog invariant is non-zero exactly when
the holonomy phase is genuine — the mixing magnitudes are now fixed by Fano incidence. -/
theorem ckmFano_cp_violation (δ : ℝ) (hδ : Real.sin δ ≠ 0) :
    jarlskog (ckmFano δ 0 1) (ckmFano δ 1 2) (ckmFano δ 0 2) (ckmFano δ 1 1) ≠ 0 := by
  rw [ckmFano, ckm_jarlskog]
  have hc := cosθFano_pos
  have hs := sinθFano_pos
  have hprod : cosθFano * cosθFano ^ 2 * cosθFano * sinθFano * sinθFano * sinθFano ≠ 0 := by
    positivity
  exact mul_ne_zero hprod hδ

/-! ## Closure -/

/-- **Fano-overlap mixing-weight discharge bundle.** -/
structure FanoMixingDischarged : Prop where
  overlap_off_diagonal : ∀ v w : ImagPoint, v ≠ w → overlap v w = 1
  overlap_diagonal : ∀ v : ImagPoint, overlap v v = 3
  mixing_fraction : ∀ v w : ImagPoint, v ≠ w → sinθFano ^ 2 = (overlap v w : ℝ) / (overlap v v : ℝ)
  ckm_unitary : ∀ δ : ℝ, star (ckmFano δ) * ckmFano δ = 1
  cp_violation : ∀ δ : ℝ, Real.sin δ ≠ 0 →
    jarlskog (ckmFano δ 0 1) (ckmFano δ 1 2) (ckmFano δ 0 2) (ckmFano δ 1 1) ≠ 0

/-- **The mixing weights are discharged from Fano incidence:** the overlap is the forced graph count
(`1` off-diagonal, `3` diagonal), the leading mixing fraction is the resulting ratio `1/3`, and the
Fano-weighted CKM matrix is unitary and CP-violating — the overlap weight is no longer a free input. -/
theorem fanoMixingDischarged_holds : FanoMixingDischarged where
  overlap_off_diagonal := overlap_distinct
  overlap_diagonal := overlap_self
  mixing_fraction := fano_sinSq_eq_overlap
  ckm_unitary := ckmFano_unitary_apply
  cp_violation := ckmFano_cp_violation

end HqivSpine.Physics.FanoMixingWeights
