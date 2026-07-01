import HqivSpine.Physics.Binding
import HqivSpine.Physics.MassLadder
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.ContentClassCompositeTrace` — 8×8 traces from fermion content class

Mined from `NucleonLadder` (three-carrier nucleon / two-carrier meson) and
`ConservedContentMassBridge` (ν:1, charged-ℓ:2, quark:3 Fano triples) into the clean spine.

**Derivation.** Each `FermionContentClass` must close `conservedTripleCount c` independent
Fano triples on the octonion carrier. On the composite-trace diagonal this activates the
first `l` carrier slots on generator family `k = 0` (the same pattern as the nucleon and
meson traces in `NucleonLadder`):

* neutrino (`l = 1`): one slot;
* charged lepton (`l = 2`): two slots — matches the meson two-carrier trace;
* quark (`l = 3`): three slots — matches the nucleon three-valence trace.

The network weight sum is therefore `l`, and binding closes to
`E_bind = l · latticeSimplexCount(m) · α_eff(m)`.

The cross-sector **readout** ratio `(l_q / l_ℓ)² = 9/4` is the squared trace-count ratio,
which equals `intrinsicWaveComplexity` and `C_A / C_F` (`ColorCasimir`).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.ContentClassCompositeTrace

open HqivSpine.Physics
open scoped BigOperators

/-! ## Trace diagonal from conserved triple count -/

/-- **Content-class composite-trace diagonal:** unit weight on generator `0` and the first
`conservedTripleCount c` carrier slots. -/
def contentClassTraceDiagonal (c : FermionContentClass) : So8TraceDiagonal :=
  fun k i => if k = 0 ∧ (i : ℕ) < conservedTripleCount c then 1 else 0

/-- **Uniform carrier state** (all slots active at unit amplitude). -/
def contentClassTraceState : OctonionState := fun _ => 1

/-- **Network weight** induced by the content-class composite trace. -/
noncomputable def contentClassWeight (c : FermionContentClass) : NetworkWeight :=
  networkWeightFromCompositeTrace (contentClassTraceDiagonal c) contentClassTraceState

theorem contentClassWeight_zero (c : FermionContentClass) :
    contentClassWeight c 0 = (conservedTripleCount c : ℝ) := by
  unfold contentClassWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    contentClassTraceDiagonal contentClassTraceState
  rw [Fin.sum_univ_eight]
  rcases c with _ | _ | _ <;> simp [conservedTripleCount] <;> norm_num

theorem contentClassWeight_of_ne {c : FermionContentClass} {k : So8Index} (hk : k ≠ 0) :
    contentClassWeight c k = 0 := by
  unfold contentClassWeight networkWeightFromCompositeTrace compositeTraceAtGenerator
    contentClassTraceDiagonal contentClassTraceState
  apply Finset.sum_eq_zero
  intro i _
  have : ¬ (k = 0 ∧ (i : ℕ) < conservedTripleCount c) := fun h => hk h.1
  simp [this]

/-- **The content-class weights sum to `conservedTripleCount c`.** -/
theorem contentClassWeight_sum (c : FermionContentClass) :
    ∑ k : So8Index, contentClassWeight c k = conservedTripleCount c := by
  rw [Finset.sum_eq_single (0 : So8Index)
    (fun b _ hb => contentClassWeight_of_ne (c := c) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  exact_mod_cast contentClassWeight_zero c

theorem contentClassWeight_neutrino_sum :
    ∑ k : So8Index, contentClassWeight .neutrino k = 1 := by
  simpa [conservedTripleCount] using contentClassWeight_sum .neutrino

theorem contentClassWeight_chargedLepton_sum :
    ∑ k : So8Index, contentClassWeight .chargedLepton k = 2 := by
  simpa [conservedTripleCount] using contentClassWeight_sum .chargedLepton

theorem contentClassWeight_quark_sum :
    ∑ k : So8Index, contentClassWeight .quark k = 3 := by
  simpa [conservedTripleCount] using contentClassWeight_sum .quark

/-! ## Binding closed form -/

theorem log_phi_nonneg (m : ℕ) : 0 ≤ Real.log ((phi m : ℝ) + 1) := by
  apply Real.log_nonneg
  have : (2 : ℝ) ≤ (phi m : ℝ) := by
    have : (2 : ℕ) ≤ phi m := by unfold phi; omega
    exact_mod_cast this
  linarith

theorem oneOverAlphaEffAtShell_one_pos (m : ℕ) : 0 < oneOverAlphaEffAtShell m 1 := by
  unfold oneOverAlphaEffAtShell oneOverAlphaBare
  rw [alphaEM_eq]
  nlinarith [log_phi_nonneg m]

theorem alphaEffAtShell_one_pos (m : ℕ) : 0 < alphaEffAtShell m 1 := by
  unfold alphaEffAtShell
  exact inv_pos.mpr (oneOverAlphaEffAtShell_one_pos m)

/-- **Content-class binding** at shell `m`. -/
theorem E_bind_contentClass (c : FermionContentClass) (m : ℕ) (coupling : ℝ) :
    E_bind_from_network m (contentClassWeight c) coupling =
      (conservedTripleCount c : ℝ) * (latticeSimplexCount m : ℝ) * alphaEffAtShell m coupling := by
  unfold E_bind_from_network bindingCouplingAtShell
  rw [← Finset.sum_mul, contentClassWeight_sum c]
  ring

theorem E_bind_contentClass_pos (c : FermionContentClass) (m : ℕ) :
    0 < E_bind_from_network m (contentClassWeight c) 1 := by
  rw [E_bind_contentClass]
  have hcount : (0 : ℝ) < (latticeSimplexCount m : ℝ) := by exact_mod_cast latticeSimplexCount_pos m
  have hα := alphaEffAtShell_one_pos m
  rcases c with _ | _ | _ <;> simp [conservedTripleCount] <;> positivity

/-! ## Cross-sector ratios -/

/-- **Binding ratio** at fixed shell = trace-count ratio `l_q / l_ℓ = 3/2`. -/
theorem E_bind_quark_over_chargedLepton (m : ℕ) :
    E_bind_from_network m (contentClassWeight .quark) 1 /
      E_bind_from_network m (contentClassWeight .chargedLepton) 1 = (3 : ℝ) / 2 := by
  rw [E_bind_contentClass, E_bind_contentClass]
  have hcount : (0 : ℝ) < (latticeSimplexCount m : ℝ) := by exact_mod_cast latticeSimplexCount_pos m
  have hα := alphaEffAtShell_one_pos m
  simp only [conservedTripleCount]
  field_simp [ne_of_gt hcount, ne_of_gt hα]
  ring

theorem E_bind_neutrino_over_chargedLepton (m : ℕ) :
    E_bind_from_network m (contentClassWeight .neutrino) 1 /
      E_bind_from_network m (contentClassWeight .chargedLepton) 1 = (1 : ℝ) / 2 := by
  rw [E_bind_contentClass, E_bind_contentClass]
  have hcount : (0 : ℝ) < (latticeSimplexCount m : ℝ) := by exact_mod_cast latticeSimplexCount_pos m
  have hα := alphaEffAtShell_one_pos m
  simp only [conservedTripleCount]
  field_simp [ne_of_gt hcount, ne_of_gt hα]
  ring

/-- **Squared trace-count ratio** = intrinsic wave complexity ratio = `9/4`. -/
theorem traceCount_squared_eq_intrinsicWaveComplexity_ratio :
    ((conservedTripleCount .quark : ℝ) / conservedTripleCount .chargedLepton) ^ 2 =
      intrinsicWaveComplexity .quark / intrinsicWaveComplexity .chargedLepton := by
  simp [conservedTripleCount, intrinsicWaveComplexity]; norm_num

/-! ## Unified sector ground factor (Beltrami × complexity) -/

/-- Reference Beltrami winding for normalizing sector ground factors (`λ_min(1) = 2`). -/
def referenceBeltramiWinding : ℕ := 1

theorem referenceBeltramiWinding_eq_one : referenceBeltramiWinding = 1 := rfl

/-- **Sector ground factor** at Hopf winding `n`:
`l² · λ_min(n) / λ_min(1)²`. -/
noncomputable def contentClassGroundFactor (c : FermionContentClass) (n : ℕ) : ℝ :=
  intrinsicWaveComplexity c * beltramiMinEigenvalue n /
    (beltramiMinEigenvalue referenceBeltramiWinding) ^ 2

theorem contentClassGroundFactor_eq (c : FermionContentClass) (n : ℕ) :
    contentClassGroundFactor c n =
      intrinsicWaveComplexity c * ((n : ℝ) + 1) / 4 := by
  unfold contentClassGroundFactor
  rw [beltramiMinEigenvalue_eq_succ, beltramiMinEigenvalue_eq_succ, referenceBeltramiWinding_eq_one]
  rcases c with _ | _ | _ <;> simp [intrinsicWaveComplexity, conservedTripleCount] <;> ring

theorem contentClassGroundFactor_chargedLepton (n : ℕ) :
    contentClassGroundFactor .chargedLepton n = (n : ℝ) + 1 := by
  rw [contentClassGroundFactor_eq .chargedLepton n]
  norm_num [intrinsicWaveComplexity, conservedTripleCount]

theorem contentClassGroundFactor_quark (n : ℕ) :
    contentClassGroundFactor .quark n = 9 * ((n : ℝ) + 1) / 4 := by
  rw [contentClassGroundFactor_eq .quark n]
  norm_num [intrinsicWaveComplexity, conservedTripleCount]

theorem contentClassGroundFactor_quark_over_chargedLepton (n : ℕ) :
    contentClassGroundFactor .quark n / contentClassGroundFactor .chargedLepton n = (9 : ℝ) / 4 := by
  rw [contentClassGroundFactor_quark, contentClassGroundFactor_chargedLepton]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp [ne_of_gt hn]

theorem contentClassGroundFactor_neutrino (n : ℕ) :
    contentClassGroundFactor .neutrino n = ((n : ℝ) + 1) / 4 := by
  rw [contentClassGroundFactor_eq .neutrino n]
  simp [intrinsicWaveComplexity, conservedTripleCount]

theorem contentClassGroundFactor_chargedLepton_over_neutrino (n : ℕ) :
    contentClassGroundFactor .chargedLepton n / contentClassGroundFactor .neutrino n = 4 := by
  rw [contentClassGroundFactor_chargedLepton, contentClassGroundFactor_neutrino]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  field_simp [ne_of_gt hn]

/-- Cross-sector ground-factor ratio equals squared trace-count ratio. -/
theorem contentClassGroundFactor_ratio_eq_traceCount_squared (n : ℕ) :
    contentClassGroundFactor .quark n / contentClassGroundFactor .chargedLepton n =
      ((conservedTripleCount .quark : ℝ) / conservedTripleCount .chargedLepton) ^ 2 := by
  rw [contentClassGroundFactor_quark_over_chargedLepton]
  simp [conservedTripleCount]; norm_num

/-! ## Capstone -/

structure ContentClassCompositeTraceClosure where
  /-- Weight sum = conserved triple count. -/
  weight_sum : ∀ c, ∑ k : So8Index, contentClassWeight c k = conservedTripleCount c
  /-- Binding closes to `l · count · α_eff`. -/
  binding_closed : ∀ c m coupling,
    E_bind_from_network m (contentClassWeight c) coupling =
      (conservedTripleCount c : ℝ) * (latticeSimplexCount m : ℝ) * alphaEffAtShell m coupling
  /-- Charged lepton / quark trace counts `2 / 3`. -/
  charged_lepton_quark_counts :
    (∑ k : So8Index, contentClassWeight .chargedLepton k = 2) ∧
      (∑ k : So8Index, contentClassWeight .quark k = 3)
  /-- Cross-sector ground factor `9/4` from `l²` ratio. -/
  cross_sector_ground :
    ∀ (n : ℕ), 0 < (n : ℝ) + 1 →
      contentClassGroundFactor .quark n / contentClassGroundFactor .chargedLepton n = (9 : ℝ) / 4

def contentClassCompositeTraceClosure : ContentClassCompositeTraceClosure where
  weight_sum := fun c => contentClassWeight_sum c
  binding_closed := fun c m coupling => E_bind_contentClass c m coupling
  charged_lepton_quark_counts := ⟨contentClassWeight_chargedLepton_sum, contentClassWeight_quark_sum⟩
  cross_sector_ground := fun n _ => contentClassGroundFactor_quark_over_chargedLepton n

end HqivSpine.Physics.ContentClassCompositeTrace
