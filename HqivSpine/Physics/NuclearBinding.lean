import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.Curvature

/-!
# `HqivSpine.Physics.NuclearBinding` — bound states from the curvature network

Nuclear binding as a **theorem about the sign and shape** of the `Physics.Binding` so(8) network and
the `Physics.Curvature` imprint — constituent masses only, no PDG / MeV literal.

* **The shell coupling is positive.** For a forward (`c ≥ 0`) running, the per-generator coupling
  `latticeSimplexCount(m)·α_eff(m)` is strictly positive (`bindingCouplingAtShell_pos`), so a
  nonnegative network weight gives nonnegative binding and a single positive weight gives strictly
  positive binding (`E_bind_from_network_pos`).
* **Mass defect = binding ⇒ bound state.** The defect `A·M_nucleon − M_nucleus` equals the network
  binding (`networkMassDefect_eq`), so a nucleus sits **below** its constituents exactly when the
  binding is positive (`nucleus_bound_iff_binding_pos`), which the positive-weight hypothesis
  delivers (`nucleus_bound_of_positive_weight`).
* **Curvature-driven depth: saturation + inward deepening.** Modelling the per-nucleon binding by the
  curvature imprint `δ_E(m)` gives binding `A·δ_E(m)`: the binding **per nucleon is independent of
  `A`** (`bindingPerNucleon_saturates` — the saturation of the nuclear force) and **strictly deeper on
  inner shells** (`bindingPerNucleon_deeper_inside`, from `deltaE_strictAnti`). The resulting nucleus is
  always bound (`nucleus_always_bound`).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.NuclearBinding

open HqivSpine.Physics HqivSpine.Foundation
open scoped BigOperators

/-! ## Positivity of the running coupling -/

/-- The bare-times-running inverse coupling is positive for a forward (`c ≥ 0`) running. -/
theorem oneOverAlphaEffAtShell_pos (m : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    0 < oneOverAlphaEffAtShell m c := by
  unfold oneOverAlphaEffAtShell
  have hlog : 0 ≤ Real.log ((phi m : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ (phi m : ℝ) := Nat.cast_nonneg _; linarith)
  have hα : (0 : ℝ) ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  have hterm : 0 ≤ c * alphaEM * Real.log ((phi m : ℝ) + 1) :=
    mul_nonneg (mul_nonneg hc hα) hlog
  have hbare : (0 : ℝ) < oneOverAlphaBare := by unfold oneOverAlphaBare; norm_num
  exact mul_pos hbare (by linarith)

theorem alphaEffAtShell_pos (m : ℕ) (c : ℝ) (hc : 0 ≤ c) : 0 < alphaEffAtShell m c := by
  unfold alphaEffAtShell
  exact inv_pos.mpr (oneOverAlphaEffAtShell_pos m c hc)

/-- **The per-generator shell coupling is strictly positive** for a forward running. -/
theorem bindingCouplingAtShell_pos (m : ℕ) (k : So8Index) (c : ℝ) (hc : 0 ≤ c) :
    0 < bindingCouplingAtShell m k c := by
  unfold bindingCouplingAtShell
  have h1 : (0 : ℝ) < (latticeSimplexCount m : ℝ) := by exact_mod_cast latticeSimplexCount_pos m
  exact mul_pos h1 (alphaEffAtShell_pos m c hc)

/-! ## Sign of the network binding -/

/-- Nonnegative weights give nonnegative network binding. -/
theorem E_bind_from_network_nonneg (m : ℕ) (w : NetworkWeight) (c : ℝ)
    (hc : 0 ≤ c) (hw : ∀ k, 0 ≤ w k) : 0 ≤ E_bind_from_network m w c :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (bindingCouplingAtShell_pos m k c hc).le

/-- A single positive weight forces strictly positive network binding. -/
theorem E_bind_from_network_pos (m : ℕ) (w : NetworkWeight) (c : ℝ)
    (hc : 0 ≤ c) (hw : ∀ k, 0 ≤ w k) (hpos : ∃ k, 0 < w k) :
    0 < E_bind_from_network m w c := by
  obtain ⟨k₀, hk₀⟩ := hpos
  unfold E_bind_from_network
  exact Finset.sum_pos'
    (fun k _ => mul_nonneg (hw k) (bindingCouplingAtShell_pos m k c hc).le)
    ⟨k₀, Finset.mem_univ k₀, mul_pos hk₀ (bindingCouplingAtShell_pos m k₀ c hc)⟩

/-! ## Mass defect and the bound-state condition -/

/-- **Mass defect** of a nucleus: `A·M_nucleon − M_nucleus`. -/
noncomputable def networkMassDefect (m A : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight)
    (c : ℝ := 1) : ℝ :=
  (A : ℝ) * M_nucleon_avg - M_nucleus_from_network m A M_nucleon_avg w c

/-- **Mass defect equals the network binding.** -/
theorem networkMassDefect_eq (m A : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight) (c : ℝ) :
    networkMassDefect m A M_nucleon_avg w c = E_bind_from_network m w c := by
  unfold networkMassDefect M_nucleus_from_network; ring

/-- **Bound-state condition:** a nucleus lies below its constituents iff the binding is positive. -/
theorem nucleus_bound_iff_binding_pos (m A : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight) (c : ℝ) :
    M_nucleus_from_network m A M_nucleon_avg w c < (A : ℝ) * M_nucleon_avg
      ↔ 0 < E_bind_from_network m w c := by
  unfold M_nucleus_from_network; constructor <;> intro h <;> linarith

/-- A positive-weight network at a forward running gives a **bound** nucleus. -/
theorem nucleus_bound_of_positive_weight (m A : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight) (c : ℝ)
    (hc : 0 ≤ c) (hw : ∀ k, 0 ≤ w k) (hpos : ∃ k, 0 < w k) :
    M_nucleus_from_network m A M_nucleon_avg w c < (A : ℝ) * M_nucleon_avg :=
  (nucleus_bound_iff_binding_pos m A M_nucleon_avg w c).mpr
    (E_bind_from_network_pos m w c hc hw hpos)

/-! ## Curvature-driven binding: saturation and inward deepening -/

/-- **Curvature nuclear binding**: total binding `= A · δ_E(m)`, the curvature imprint per nucleon. -/
noncomputable def nuclearCurvatureBinding (m A : ℕ) : ℝ := (A : ℝ) * deltaE m

theorem nuclearCurvatureBinding_pos (m A : ℕ) (hA : 0 < A) : 0 < nuclearCurvatureBinding m A :=
  mul_pos (by exact_mod_cast hA) (deltaE_pos m)

/-- **Binding per nucleon is `δ_E(m)`** — independent of the mass number `A`. -/
theorem bindingPerNucleon_eq (m A : ℕ) (hA : 0 < A) :
    nuclearCurvatureBinding m A / (A : ℝ) = deltaE m := by
  have hA' : (A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  unfold nuclearCurvatureBinding
  field_simp

/-- **Saturation of the nuclear force:** binding per nucleon is the same for any two mass numbers at
a fixed shell. -/
theorem bindingPerNucleon_saturates (m A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    nuclearCurvatureBinding m A / (A : ℝ) = nuclearCurvatureBinding m B / (B : ℝ) := by
  rw [bindingPerNucleon_eq m A hA, bindingPerNucleon_eq m B hB]

/-- **Inner shells bind deeper:** the per-nucleon curvature binding strictly increases inward. -/
theorem bindingPerNucleon_deeper_inside {m m' : ℕ} (h : m < m') : deltaE m' < deltaE m :=
  deltaE_strictAnti h

/-- Curvature nuclear mass `A·M_nucleon − A·δ_E(m) = A·(M_nucleon − δ_E(m))`. -/
noncomputable def M_nucleus_curvature (m A : ℕ) (M_nucleon : ℝ) : ℝ :=
  (A : ℝ) * M_nucleon - nuclearCurvatureBinding m A

theorem M_nucleus_curvature_eq (m A : ℕ) (M_nucleon : ℝ) :
    M_nucleus_curvature m A M_nucleon = (A : ℝ) * (M_nucleon - deltaE m) := by
  unfold M_nucleus_curvature nuclearCurvatureBinding; ring

/-- The curvature-bound nucleus is **always bound** (`δ_E > 0` for every shell). -/
theorem nucleus_always_bound (m A : ℕ) (M_nucleon : ℝ) (hA : 0 < A) :
    M_nucleus_curvature m A M_nucleon < (A : ℝ) * M_nucleon := by
  unfold M_nucleus_curvature
  have := nuclearCurvatureBinding_pos m A hA
  linarith

end HqivSpine.Physics.NuclearBinding
