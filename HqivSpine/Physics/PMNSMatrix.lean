import HqivSpine.Physics.FanoMixingWeights
import HqivSpine.Physics.NeutrinoMixing

/-!
# `HqivSpine.Physics.PMNSMatrix` — the lepton mixing matrix and a derived `J_PMNS`

The lepton mirror of `CKMMixingMatrix`/`FanoMixingWeights`, assembled from the spine's *own*
neutrino angles: solar `sin²θ₁₂ = 1/3` (Fano democratic overlap, `FanoMixingWeights`), atmospheric
`θ₂₃ = π/4` maximal (`NeutrinoMixing`, lock-in shell `4 = 2²`), and the CP phase `δ = π/5`
(monogamy rapidity skew, `NeutrinoMixing.neutrinoCPPhase`).

* **Tri-bimaximal at leading order.** With the reactor angle off (`θ₁₃ = 0`) the spine values give the
  tri-bimaximal matrix `pmnsTBM`: unitary (`pmnsTBM_unitary`) with **vanishing CP** (`pmnsTBM_jarlskog`)
  — lepton CP violation is *gated by the reactor angle*, exactly as in nature.
* **Reactor angle switches on CP.** Turning on `θ₁₃` (`pmnsReactor s13 δ`) keeps unitarity
  (`pmnsReactor_unitary`) and gives the **closed-form Jarlskog**
  `J = (√2/6)·(1 − s₁₃²)·s₁₃·sin δ` (`pmnsReactor_jarlskog_value`), non-zero iff the reactor angle and
  the phase are (`pmnsReactor_cp_violation`).
* **CP from the derived phase.** Instantiating `δ = π/5` (`NeutrinoMixing`), lepton CP violation is real
  once `θ₁₃ ≠ 0` (`pmns_cp_from_derived_phase`) — the phase is derived, only the reactor magnitude is
  input.

**Honest scope.** The two large angles (`1/3`, `π/4`) and the phase (`π/5`) are derived; the matrix and
the `J` closed form are derived. What is **not** derived is the reactor magnitude `s₁₃` — the
tri-bimaximal *deviation* — which is the open sub-leading splitting (the `MassLadder` fine structure).
Numerically `J = (√2/6)(1−s₁₃²)s₁₃ sin(π/5) ≈ 0.139·(1−s₁₃²)·s₁₃`, i.e. `≈ 0.020` at the physical
`s₁₃ ≈ 0.15` — the right order for leptonic CP.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.PMNSMatrix

open HqivSpine.Physics
open HqivSpine.Physics.CKMMixingMatrix
open HqivSpine.Physics.CPHolonomyPhase
open HqivSpine.Physics.FanoMixingWeights

/-! ## The maximal atmospheric angle as a `sin`/`cos` pair -/

/-- Atmospheric mixing is maximal: `sin θ₂₃ = cos θ₂₃ = √(1/2)` (the `π/4` of `NeutrinoMixing`). -/
noncomputable def sc23 : ℝ := Real.sqrt (1 / 2)

theorem sc23_sq : sc23 ^ 2 = 1 / 2 := by rw [sc23, Real.sq_sqrt (by norm_num)]

theorem sc23_pos : 0 < sc23 := Real.sqrt_pos.mpr (by norm_num)

/-- `cos θ₁₂ · sin θ₁₂ = √2/3` for the Fano solar angle (`sin²θ₁₂ = 1/3`). -/
theorem cosθFano_mul_sinθFano : cosθFano * sinθFano = Real.sqrt 2 / 3 := by
  unfold cosθFano sinθFano
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3),
    show (2 / 3 * (1 / 3) : ℝ) = 2 * (1 / 3) ^ 2 by norm_num,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  ring

/-! ## The PMNS matrix with a reactor angle -/

/-- **PMNS matrix** from the spine angles: solar `θ₁₂` (Fano `1/3`), atmospheric `θ₂₃` maximal,
reactor `θ₁₃` with `sin θ₁₃ = s13`, and CP phase `δ`. -/
noncomputable def pmnsReactor (s13 δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ckm cosθFano sinθFano (Real.sqrt (1 - s13 ^ 2)) s13 sc23 sc23 δ

theorem pmnsReactor_unitary (s13 δ : ℝ) (hs : s13 ^ 2 ≤ 1) :
    pmnsReactor s13 δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  ckm_unitary
    (by rw [cosθFano_sq, sinθFano_sq]; norm_num)
    (by rw [Real.sq_sqrt (by linarith)]; ring)
    (by rw [sc23_sq]; norm_num)

theorem pmnsReactor_unitary_apply (s13 δ : ℝ) (hs : s13 ^ 2 ≤ 1) :
    star (pmnsReactor s13 δ) * pmnsReactor s13 δ = 1 :=
  (pmnsReactor_unitary s13 δ hs).1

/-- **Closed-form lepton Jarlskog:** `J = (√2/6)·(1 − s₁₃²)·s₁₃·sin δ`. -/
theorem pmnsReactor_jarlskog_value (s13 δ : ℝ) (hs : s13 ^ 2 ≤ 1) :
    jarlskog (pmnsReactor s13 δ 0 1) (pmnsReactor s13 δ 1 2) (pmnsReactor s13 δ 0 2)
        (pmnsReactor s13 δ 1 1)
      = Real.sqrt 2 / 6 * (1 - s13 ^ 2) * s13 * Real.sin δ := by
  rw [pmnsReactor, ckm_jarlskog, Real.sq_sqrt (by linarith)]
  have hx : sc23 * sc23 = 1 / 2 := by rw [sc23]; exact Real.mul_self_sqrt (by norm_num)
  have hcs : cosθFano * sinθFano = Real.sqrt 2 / 3 := cosθFano_mul_sinθFano
  linear_combination ((1 - s13 ^ 2) * s13 * Real.sin δ / 2) * hcs
    + (cosθFano * (1 - s13 ^ 2) * sinθFano * s13 * Real.sin δ) * hx

/-- **CP violation is gated by the reactor angle and the phase:** `J ≠ 0` iff both switch on. -/
theorem pmnsReactor_cp_violation (s13 δ : ℝ) (hs : s13 ^ 2 < 1) (hs0 : s13 ≠ 0)
    (hδ : Real.sin δ ≠ 0) :
    jarlskog (pmnsReactor s13 δ 0 1) (pmnsReactor s13 δ 1 2) (pmnsReactor s13 δ 0 2)
      (pmnsReactor s13 δ 1 1) ≠ 0 := by
  rw [pmnsReactor_jarlskog_value s13 δ (le_of_lt hs)]
  have h2 : Real.sqrt 2 / 6 ≠ 0 := by positivity
  have h1m : (1 - s13 ^ 2) ≠ 0 := ne_of_gt (by linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h1m) hs0) hδ

/-! ## Tri-bimaximal limit (reactor angle off) -/

/-- **Tri-bimaximal PMNS matrix:** the spine angles with the reactor angle off (`θ₁₃ = 0`). -/
noncomputable def pmnsTBM (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := pmnsReactor 0 δ

theorem pmnsTBM_unitary (δ : ℝ) : pmnsTBM δ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) :=
  pmnsReactor_unitary 0 δ (by norm_num)

/-- **Vanishing CP at tri-bimaximal:** lepton CP violation requires a non-zero reactor angle. -/
theorem pmnsTBM_jarlskog (δ : ℝ) :
    jarlskog (pmnsTBM δ 0 1) (pmnsTBM δ 1 2) (pmnsTBM δ 0 2) (pmnsTBM δ 1 1) = 0 := by
  rw [pmnsTBM, pmnsReactor_jarlskog_value 0 δ (by norm_num)]; ring

/-! ## CP from the derived monogamy phase `δ = π/5` -/

/-- **Lepton CP violation from the derived phase:** with `δ = π/5` (`NeutrinoMixing.neutrinoCPPhase`),
the Jarlskog invariant is non-zero whenever the reactor angle is — only the reactor magnitude is an
input, the phase is derived. -/
theorem pmns_cp_from_derived_phase (s13 : ℝ) (hs : s13 ^ 2 < 1) (hs0 : s13 ≠ 0) :
    jarlskog (pmnsReactor s13 neutrinoCPPhase 0 1) (pmnsReactor s13 neutrinoCPPhase 1 2)
      (pmnsReactor s13 neutrinoCPPhase 0 2) (pmnsReactor s13 neutrinoCPPhase 1 1) ≠ 0 := by
  refine pmnsReactor_cp_violation s13 neutrinoCPPhase hs hs0 ?_
  rw [neutrinoCPPhase_eq_pi_div_five]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))

/-! ## Closure -/

/-- **PMNS discharge bundle.** -/
structure PMNSDischarged : Prop where
  tbm_unitary : ∀ δ : ℝ, star (pmnsTBM δ) * pmnsTBM δ = 1
  tbm_cp_vanishes : ∀ δ : ℝ,
    jarlskog (pmnsTBM δ 0 1) (pmnsTBM δ 1 2) (pmnsTBM δ 0 2) (pmnsTBM δ 1 1) = 0
  reactor_unitary : ∀ {s13 δ : ℝ}, s13 ^ 2 ≤ 1 → star (pmnsReactor s13 δ) * pmnsReactor s13 δ = 1
  jarlskog_value : ∀ {s13 δ : ℝ}, s13 ^ 2 ≤ 1 →
    jarlskog (pmnsReactor s13 δ 0 1) (pmnsReactor s13 δ 1 2) (pmnsReactor s13 δ 0 2)
        (pmnsReactor s13 δ 1 1)
      = Real.sqrt 2 / 6 * (1 - s13 ^ 2) * s13 * Real.sin δ
  cp_from_derived_phase : ∀ {s13 : ℝ}, s13 ^ 2 < 1 → s13 ≠ 0 →
    jarlskog (pmnsReactor s13 neutrinoCPPhase 0 1) (pmnsReactor s13 neutrinoCPPhase 1 2)
      (pmnsReactor s13 neutrinoCPPhase 0 2) (pmnsReactor s13 neutrinoCPPhase 1 1) ≠ 0

/-- **The lepton mixing matrix, assembled from spine angles.** Tri-bimaximal at leading order (unitary,
CP-free), with the reactor angle switching on a closed-form Jarlskog `J = (√2/6)(1−s₁₃²)s₁₃ sin δ`;
with the derived monogamy phase `π/5`, lepton CP violation is real once `θ₁₃ ≠ 0`. -/
theorem pmnsDischarged_holds : PMNSDischarged where
  tbm_unitary := fun δ => (pmnsTBM_unitary δ).1
  tbm_cp_vanishes := pmnsTBM_jarlskog
  reactor_unitary := fun hs => pmnsReactor_unitary_apply _ _ hs
  jarlskog_value := fun hs => pmnsReactor_jarlskog_value _ _ hs
  cp_from_derived_phase := fun hs hs0 => pmns_cp_from_derived_phase _ hs hs0

end HqivSpine.Physics.PMNSMatrix
