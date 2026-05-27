import Hqiv.Physics.ActionHolonomyGlue
import Hqiv.Physics.ContinuousXiPath

/-!
# Readout-to-gauge seed on the minimal `Fin 4` cycle

Paper `papers/hqiv_octonionic_action_and_uniqueness.tex`, Subsection ``Minimal seed map''.

This module **defines** the alternating `±ω` edge pattern on the cyclic spacetime indices
(`Fin 4`) in the `(e₁,e₇)` internal directions and proves compatibility with the existing
holonomy lemmas (`sum_F_cyclicIndex_eq_zero`, `discreteSquareHolonomy_F_cyclic_eq_one`).

The imprint-weighted increment `imprintWeightedReadoutPhase` packages `omega_k_partial`,
`phi_of_shell`, and `alpha` exactly as in the manuscript.  Its continuous-ξ sibling
is the `ContinuousXiPath.imprintWeightedReadoutPhase_xi` alias; integer-step equality
is proved once an explicit discrete-continuous `Ωₖ` bridge is supplied.
-/

namespace Hqiv

open Hqiv.Physics

/-- Vertex profile on the minimal cycle: `0 → ω·c → ω·c → 0` on `Fin 4`, so cyclic edge sums cancel. -/
noncomputable def seedAProfileAux (ω c : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => ω * c
  | ⟨2, _⟩ => ω * c
  | ⟨3, _⟩ => 0

/-- Gauge potential on `Fin 8 × Fin 4`: channels `1` and `7` carry the `(cos θ, sin θ)` phase-lift plane; others `0`. -/
noncomputable def seedPotentialMinimalCycle (ω θ : ℝ) : Fin 8 → Fin 4 → ℝ := fun a μ =>
  if _ : a.val = 1 then seedAProfileAux ω (Real.cos θ) μ
  else if _ : a.val = 7 then seedAProfileAux ω (Real.sin θ) μ
  else 0

/-- Per-shell imprint used in the paper: `α · log(φ+1) · (Ω_{n+1} − Ω_n)` with `Ω = omega_k_partial`. -/
noncomputable def imprintWeightedReadoutPhase (n : ℕ) : ℝ :=
  alpha * Real.log (phi_of_shell n + 1) * (omega_k_partial (n + 1) - omega_k_partial n)

/-- Readout-facing alias for the continuous-ξ imprint increment. -/
noncomputable abbrev imprintWeightedReadoutPhase_xi_alias :=
  Hqiv.Physics.ContinuousXiPath.imprintWeightedReadoutPhase_xi

/-- Readout-facing alias for the integer-sample `Ωₖ` bridge used by the ξ path. -/
abbrev readoutOmegaKIntegerBridge :=
  Hqiv.Physics.ContinuousXiPath.OmegaKIntegerBridge

/--
Continuous and discrete imprint phases agree on adjacent integer samples once the
continuous `Ωₖ` readout is bridged to the discrete curvature ladder at those samples.
-/
theorem imprintWeightedReadoutPhase_xi_matches_integer_step
    (hΩ : readoutOmegaKIntegerBridge) (n : ℕ) :
    imprintWeightedReadoutPhase_xi_alias
        (Hqiv.Physics.xiOfShell n) (Hqiv.Physics.xiOfShell (n + 1)) =
      imprintWeightedReadoutPhase n := by
  unfold imprintWeightedReadoutPhase_xi_alias
  unfold Hqiv.Physics.ContinuousXiPath.imprintWeightedReadoutPhase_xi
  unfold imprintWeightedReadoutPhase
  rw [Hqiv.Physics.ContinuousXiPath.phi_xi_chart]
  rw [Hqiv.Physics.ContinuousXiPath.omegaK_xi_integer_increment_bridge hΩ n]

theorem seedPotentialMinimalCycle_cyclic_sum_F (ω θ : ℝ) (a : Fin 8) :
    ∑ i : Fin 4, F_from_A (seedPotentialMinimalCycle ω θ) a i (i + 1) = 0 :=
  sum_F_cyclicIndex_eq_zero (seedPotentialMinimalCycle ω θ) a

theorem seedPotentialMinimalCycle_discrete_holonomy_one (ω θ : ℝ) (a : Fin 8) :
    discreteSquareHolonomy (fun i => linearEnd (F_from_A (seedPotentialMinimalCycle ω θ) a i (i + 1))) =
        1 :=
  discreteSquareHolonomy_F_cyclic_eq_one (seedPotentialMinimalCycle ω θ) a

theorem imprintWeightedReadoutPhase_of_increment_zero {n : ℕ}
    (h : omega_k_partial (n + 1) = omega_k_partial n) : imprintWeightedReadoutPhase n = 0 := by
  simp [imprintWeightedReadoutPhase, h, sub_self, mul_zero]

theorem seedPotentialMinimalCycle_omega_zero (θ : ℝ) (a : Fin 8) (μ : Fin 4) :
    seedPotentialMinimalCycle 0 θ a μ = 0 := by
  unfold seedPotentialMinimalCycle
  split_ifs <;> fin_cases μ <;> simp [seedAProfileAux]

theorem seedPotentialMinimalCycle_of_imprint_increment_zero (n : ℕ) (θ : ℝ)
    (h : omega_k_partial (n + 1) = omega_k_partial n) :
    seedPotentialMinimalCycle (imprintWeightedReadoutPhase n) θ =
      seedPotentialMinimalCycle 0 θ := by
  rw [imprintWeightedReadoutPhase_of_increment_zero h]

end Hqiv
