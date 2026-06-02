import Hqiv.Physics.FanoTrialityDetuningScaffold

namespace Hqiv.Physics

/-!
# Hypercharge-path barrier scaffold

This file packages the user-facing "one universal detuned well + three discrete hypercharge paths"
story as a Lean scaffold:

- base well shape is `detunedShellSurface m`,
- path classes are `{-1, 0, +1}` encoded as turn complexity `2, 0, 1`,
- effective barrier is base + (turn count) * (turn increment).

Current status is intentionally conservative:

- a dedicated `Δ`-facing interface (`DeltaTurnIncrementModel`) is introduced,
- the active instance is still set equal to the same projected detuned well on a line tag,
- this yields the expected ordering straight < plus-turn < two-turn,
- but does not yet derive the increment (or the constant `1`) from explicit `Triality` equivariance.
-/

/-- Three discrete hypercharge-path classes in the scaffold.
`straight` is the base climb (`Y = 0`), `plusTurn` is one extra turn (`Y = +1`),
`minusTwoTurn` is two extra turns (`Y = -1`). -/
inductive HyperchargePath
  | straight
  | plusTurn
  | minusTwoTurn
  deriving DecidableEq, Repr

/-- Integer hypercharge label attached to the path class. -/
def HyperchargePath.hyperchargeValue : HyperchargePath → Int
  | .straight => 0
  | .plusTurn => 1
  | .minusTwoTurn => -1

/-- Turn complexity used by the barrier scaffold. -/
def HyperchargePath.turnCount : HyperchargePath → ℕ
  | .straight => 0
  | .plusTurn => 1
  | .minusTwoTurn => 2

/-- Universal detuned well shape reused by all vertices and path classes. -/
noncomputable def universalDetunedWell (m : ℕ) : ℝ :=
  detunedShellSurface m

/--
Interface for the `Δ`-driven per-turn increment model.
This is where future phase-lift/Fano/triality derivations should plug in.
-/
structure DeltaTurnIncrementModel where
  increment : FanoLineTag → ℕ → ℝ

/--
Current scaffold instance for the `Δ` turn increment.
Today this is the same projected denominator quotient used by the detuned well scaffold.
-/
noncomputable def currentDeltaTurnIncrementModel : DeltaTurnIncrementModel where
  increment line m := shellSurface m / trialityProjectedDenominatorTag line m

/--
Named `Δ`-facing increment map used by the path barrier.
This indirection keeps theorem names stable while allowing future model replacement.
-/
noncomputable def deltaTurnIncrement (line : FanoLineTag) (m : ℕ) : ℝ :=
  currentDeltaTurnIncrementModel.increment line m

/-- Per-turn barrier increment on a chosen Fano line. -/
noncomputable def turnIncrementBarrier (line : FanoLineTag) (m : ℕ) : ℝ :=
  deltaTurnIncrement line m

/--
Compatibility with the current projected denominator scaffold.
When the `Δ` model is replaced, this is the theorem expected to change.
-/
theorem deltaTurnIncrement_eq_projectedDetuned
    (line : FanoLineTag) (m : ℕ) :
    deltaTurnIncrement line m =
  shellSurface m / trialityProjectedDenominatorTag line m
    := by
  unfold deltaTurnIncrement currentDeltaTurnIncrementModel
  rfl

/--
Effective barrier for a hypercharge path:
base well + turn-count times the per-turn increment.
-/
noncomputable def hyperchargePathBarrier
    (line : FanoLineTag) (m : ℕ) (path : HyperchargePath) : ℝ :=
  universalDetunedWell m + (path.turnCount : ℝ) * turnIncrementBarrier line m

theorem turnIncrementBarrier_eq_universalDetunedWell (line : FanoLineTag) (m : ℕ) :
    turnIncrementBarrier line m = universalDetunedWell m := by
  unfold turnIncrementBarrier universalDetunedWell
  rw [deltaTurnIncrement_eq_projectedDetuned]
  exact (detunedShellSurface_eq_shell_div_trialityProjectedDenominator line m).symm

theorem hyperchargePathBarrier_eq_base_plus_turns
    (line : FanoLineTag) (m : ℕ) (path : HyperchargePath) :
    hyperchargePathBarrier line m path =
      universalDetunedWell m + (path.turnCount : ℝ) * universalDetunedWell m := by
  unfold hyperchargePathBarrier
  rw [turnIncrementBarrier_eq_universalDetunedWell]

theorem hyperchargePathBarrier_straight
    (line : FanoLineTag) (m : ℕ) :
    hyperchargePathBarrier line m .straight = universalDetunedWell m := by
  rw [hyperchargePathBarrier_eq_base_plus_turns]
  norm_num

theorem hyperchargePathBarrier_plusTurn
    (line : FanoLineTag) (m : ℕ) :
    hyperchargePathBarrier line m .plusTurn =
      universalDetunedWell m + universalDetunedWell m := by
  rw [hyperchargePathBarrier_eq_base_plus_turns]
  simp [HyperchargePath.turnCount]

theorem hyperchargePathBarrier_minusTwoTurn
    (line : FanoLineTag) (m : ℕ) :
    hyperchargePathBarrier line m .minusTwoTurn =
      universalDetunedWell m + 2 * universalDetunedWell m := by
  rw [hyperchargePathBarrier_eq_base_plus_turns]
  simp [HyperchargePath.turnCount]

theorem hyperchargePathBarrier_strict_order
    (line : FanoLineTag) (m : ℕ) :
    hyperchargePathBarrier line m .straight <
      hyperchargePathBarrier line m .plusTurn ∧
    hyperchargePathBarrier line m .plusTurn <
      hyperchargePathBarrier line m .minusTwoTurn := by
  have hpos : 0 < universalDetunedWell m := by
    simpa [universalDetunedWell] using detunedShellSurface_pos m
  constructor
  · rw [hyperchargePathBarrier_straight, hyperchargePathBarrier_plusTurn]
    linarith
  · rw [hyperchargePathBarrier_plusTurn, hyperchargePathBarrier_minusTwoTurn]
    linarith

end Hqiv.Physics
