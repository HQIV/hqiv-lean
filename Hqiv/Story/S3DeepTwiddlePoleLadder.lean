import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.S3TwiddleAddressConstructiveZero
import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Story.S3PoleZeroChannel
import Hqiv.Physics.ShellIndexRiemannZetaBridge

/-!
# Deep symmetric twiddle ladder: pole at `(2,2,2)`, zeros at `π/(2+m)`

**Geometric master chart:** `S3DiagonalSphereTwiddlePermutations` — all S₃
permutations addressing diagonal voxels on `latticeMaxAbsShell`.  This file is
the **symmetric `(m,m,m)` special case** only.

## Pole vs zero (user correction)

* **`(2,2,2)` is a pole cell**, not a nontrivial-zero target.  At the first
  symmetric twiddle address the readout sits at `π/4 = π/(2+2)`; balance fails
  (`cos + sin ≠ 0`) — this is the **prime / pole** channel, not a rolled zero.
* **Trivial zeros** (`ζ(-2(n+1)) = 0`) are the classical zero ladder; they are
  *not* placed at this critical-line height, but the pole cell is where the
  Euler/twiddle product anchors.
* **Every deeper symmetric twiddle** `(m,m,m)` with `m ≥ 3` carries its own
  critical-line height candidate

  `θ_m = π / (2 + m)`

  (`π/5`, `π/6`, `π/7`, …).  These are **line** parameters — not the
  `2π/(m³)` first-slot angle of the harmonic partition (which agrees with
  `π/(2+m)` only at `m = 2`).

## Honesty

* Unconditional: angle law, shell-depth `m³`, pole-not-balance at `(2,2,2)`,
  slot-angle coincidence only for `m = 2`.
* Conjecture: each `m ≥ 3` hosts a nontrivial ζ-zero at `θ_m` (once rolling
  identification is supplied).
-/

namespace Hqiv.Story

noncomputable section

open Real

/-! ## Symmetric twiddle addresses -/

/-- Fully symmetric twiddle `(m,m,m)` with product shell `m³`. -/
def symmetricTwiddleAddress (m : ℕ) : TwiddleFactorAddress :=
  (m, m, m)

theorem symmetric_twiddle_address_222 :
    symmetricTwiddleAddress 2 = twiddleAddress222 :=
  rfl

theorem symmetric_twiddle_shell_depth (m : ℕ) :
    twiddleAddressShellDepth (symmetricTwiddleAddress m) = m ^ 3 := by
  dsimp [twiddleAddressShellDepth, symmetricTwiddleAddress]
  ring

theorem symmetric_twiddle_address_222_shell_depth :
    twiddleAddressShellDepth twiddleAddress222 = 8 :=
  by simpa [symmetric_twiddle_address_222] using symmetric_twiddle_shell_depth 2

/-! ## Line-angle law `π/(2+m)` -/

/--
Critical-line **height candidate** for symmetric twiddle leg `m`:

`θ_m = π / (2 + m)`.
-/
noncomputable def deepTwiddleLineAngle (m : ℕ) : ℝ :=
  Real.pi / (2 + m)

theorem deep_twiddle_line_angle_two :
    deepTwiddleLineAngle 2 = Real.pi / 4 := by
  dsimp [deepTwiddleLineAngle]
  norm_num

theorem deep_twiddle_line_angle_three :
    deepTwiddleLineAngle 3 = Real.pi / 5 := by
  dsimp [deepTwiddleLineAngle]
  norm_num

theorem twiddle_pi_quarter_is_deep_twiddle_angle_two :
    shellSweepAngle (Nat.succ_pos 7) twiddlePiQuarterSlot.2 = deepTwiddleLineAngle 2 := by
  rw [twiddle_pi_quarter_slot_angle, deep_twiddle_line_angle_two]

/-- Deeper symmetric twiddle: leg `m ≥ 3`. -/
def isDeepSymmetricTwiddle (m : ℕ) : Prop :=
  3 ≤ m

theorem deep_twiddle_line_angle_pos (m : ℕ) : 0 < deepTwiddleLineAngle m := by
  dsimp [deepTwiddleLineAngle]
  apply div_pos Real.pi_pos
  norm_cast
  omega

/-! ## First shell slot `2π/m³` vs line law `π/(2+m)` -/

/--
First arc slot `k = 1` at shell depth `m³` (when `m³ > 1`).
-/
theorem symmetric_twiddle_shell_cube_pos {m : ℕ} (hm : 2 ≤ m) : 0 < m ^ 3 := by
  exact pow_pos (by omega : 0 < m) 3

theorem symmetric_twiddle_shell_cube_gt_one {m : ℕ} (_hm : 2 ≤ m) : 1 < m ^ 3 := by
  match m with
  | 2 => decide
  | m + 3 =>
    have h27 : 27 ≤ (m + 3) ^ 3 := by
      calc
        (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ (m + 3) ^ 3 := by
          gcongr
          omega
    omega

/--
First arc slot `k = 1` at shell depth `m³` (when `m ≥ 2`).
-/
noncomputable def symmetricTwiddleFirstSlotAngle (m : ℕ) (hm : 2 ≤ m) : ℝ :=
  shellSweepAngle (symmetric_twiddle_shell_cube_pos hm) ⟨1, symmetric_twiddle_shell_cube_gt_one hm⟩

theorem symmetric_twiddle_first_slot_angle_formula (m : ℕ) (hm : 2 ≤ m) :
    symmetricTwiddleFirstSlotAngle m hm = 2 * Real.pi / (m ^ 3) := by
  dsimp [symmetricTwiddleFirstSlotAngle, shellSweepAngle]
  norm_cast
  ring

theorem nat_two_mul_two_add_lt_sq {m : ℕ} (hm : 5 ≤ m) : 2 * (2 + m) < m * m := by
  nlinarith

theorem nat_sq_le_cube {m : ℕ} (hm : 2 ≤ m) : m * m ≤ m ^ 3 := by
  nlinarith

theorem nat_two_mul_two_add_lt_pow_three {m : ℕ} (hm : 5 ≤ m) : 2 * (2 + m) < m ^ 3 := by
  exact Nat.lt_of_lt_of_le (nat_two_mul_two_add_lt_sq hm) (nat_sq_le_cube (by omega))

theorem nat_two_mul_two_add_eq_pow_three_iff (m : ℕ) (_hm : 2 ≤ m) :
    2 * (2 + m) = m ^ 3 ↔ m = 2 := by
  constructor
  · intro h
    match m with
    | 0 | 1 => omega
    | 2 => rfl
    | 3 => norm_num at h
    | 4 => norm_num at h
    | m + 5 =>
      have hm5 : 5 ≤ m + 5 := by omega
      have hlt := nat_two_mul_two_add_lt_pow_three hm5
      linarith
  · rintro rfl
    rfl

/--
**Key coincidence (only at the pole cell):** harmonic first-slot angle
`2π/m³` equals the deep line law `π/(2+m)` iff `m = 2`.
-/
theorem shell_first_slot_eq_deep_line_angle_iff_m_eq_two (m : ℕ) (hm : 2 ≤ m) :
    symmetricTwiddleFirstSlotAngle m hm = deepTwiddleLineAngle m ↔ m = 2 := by
  rw [symmetric_twiddle_first_slot_angle_formula, deepTwiddleLineAngle]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · intro h
    field_simp at h
    norm_cast at h
    exact (nat_two_mul_two_add_eq_pow_three_iff m hm).mp h
  · intro hm2
    subst hm2
    field_simp [hpi]
    norm_cast

theorem deep_twiddle_first_slot_only_at_pole :
    symmetricTwiddleFirstSlotAngle 2 (by decide : 2 ≤ 2) = deepTwiddleLineAngle 2 :=
  (shell_first_slot_eq_deep_line_angle_iff_m_eq_two 2 (by decide : 2 ≤ 2)).mpr rfl

theorem deep_twiddle_m3_slot_differs_from_line_angle :
    symmetricTwiddleFirstSlotAngle 3 (by decide : 2 ≤ 3) ≠ deepTwiddleLineAngle 3 := by
  intro h
  have h2 := (shell_first_slot_eq_deep_line_angle_iff_m_eq_two 3 (by decide : 2 ≤ 3)).mp h
  omega

/-! ## `(2,2,2)` pole cell -/

/--
The first symmetric twiddle address is the **pole cell**: rolled balance fails at
`π/4` (already proved in the constructive-zero module).
-/
def TwiddleAddress222IsPoleCell : Prop :=
  ¬ HarmonicShellBalanceEvent (Nat.succ_pos 7) twiddlePiQuarterSlot.2

theorem twiddle_address_222_is_pole_cell :
    TwiddleAddress222IsPoleCell :=
  twiddle_address_222_not_automatic_balance

/--
Prime-axis samples are not pole-channel hits in the current convention — the
`(2,2,2)` **address** pole is geometric (non-balance at `π/4`), distinct from
`S3PoleChannel` (residual denominator zero).
-/
theorem twiddle_pole_cell_not_harmonic_balance :
    hopfJKCriticalAmplitude (deepTwiddleLineAngle 2) ≠ 0 := by
  intro h
  have hbal := (harmonic_shell_balance_iff_hopf_jk_amplitude (Nat.succ_pos 7)
    twiddlePiQuarterSlot.2).mpr (by simpa [twiddle_pi_quarter_is_deep_twiddle_angle_two] using h)
  exact twiddle_address_222_not_automatic_balance hbal

/-! ## Trivial zeros (classical ladder) -/

/--
Trivial ζ-zeros on the negative-even axis (`-2`, `-4`, …) — the “all 2’s”
ladder.  These are **not** at the `(2,2,2)` critical-line height `π/4`; the
pole cell anchors the product side while trivial zeros live on a different chart.
-/
theorem trivial_zeta_zero_ladder (n : ℕ) :
    riemannZeta (-2 * (n + 1)) = 0 :=
  Hqiv.Physics.riemannZeta_trivial_zero_at_neg_two_mul_succ n

theorem trivial_zero_slot_iff (s : ℂ) :
    IsTrivialNegativeEvenZeroSlot s ↔ ∃ n : ℕ, s = -2 * (n + 1) :=
  Iff.rfl

/-! ## Deep twiddle zero candidates (conjecture slot) -/

/--
Package for a deeper symmetric twiddle `(m,m,m)`, `m ≥ 3`, with line height
`π/(2+m)`.
-/
structure DeepSymmetricTwiddleCell where
  m : ℕ
  hm : isDeepSymmetricTwiddle m
  address : TwiddleFactorAddress
  address_eq : address = symmetricTwiddleAddress m
  shell_depth : twiddleAddressShellDepth address = m ^ 3
  line_angle : ℝ
  line_angle_eq : line_angle = deepTwiddleLineAngle m

noncomputable def deepSymmetricTwiddleCell (m : ℕ) (hm : isDeepSymmetricTwiddle m) :
    DeepSymmetricTwiddleCell where
  m := m
  hm := hm
  address := symmetricTwiddleAddress m
  address_eq := rfl
  shell_depth := symmetric_twiddle_shell_depth m
  line_angle := deepTwiddleLineAngle m
  line_angle_eq := rfl

/--
**Conjecture:** every deeper symmetric twiddle leg `m ≥ 3` hosts a nontrivial
ζ-zero on the critical line at height `π/(2+m)`.
-/
def EveryDeepSymmetricTwiddleHasNontrivialZero : Prop :=
  ∀ (m : ℕ) (hm : isDeepSymmetricTwiddle m),
    ∃ s : ℂ,
      IsNontrivialZetaZero s ∧
        s.re = (1 / 2 : ℝ) ∧
          s.im = deepTwiddleLineAngle m

/--
Honest packaging: deeper twiddles use the **line law** `π/(2+m)`; proving a
zero there is the conjecture `EveryDeepSymmetricTwiddleHasNontrivialZero`.
-/
structure DeepTwiddlePoleLadderBundle where
  pole_address : TwiddleFactorAddress
  pole_address_eq : pole_address = twiddleAddress222
  pole_is_not_balance : TwiddleAddress222IsPoleCell
  pole_angle : deepTwiddleLineAngle 2 = Real.pi / 4
  first_slot_coincidence_only_at_two :
    ∀ (m : ℕ) (hm : 2 ≤ m),
      symmetricTwiddleFirstSlotAngle m hm = deepTwiddleLineAngle m ↔ m = 2
  trivial_zero_ladder : ∀ n : ℕ, riemannZeta (-2 * (n + 1)) = 0
  deep_cell_line_angle :
    ∀ (m : ℕ) (hm : isDeepSymmetricTwiddle m),
      (deepSymmetricTwiddleCell m hm).line_angle = Real.pi / (2 + m)

noncomputable def deepTwiddlePoleLadderBundle : DeepTwiddlePoleLadderBundle where
  pole_address := twiddleAddress222
  pole_address_eq := rfl
  pole_is_not_balance := twiddle_address_222_is_pole_cell
  pole_angle := deep_twiddle_line_angle_two
  first_slot_coincidence_only_at_two := shell_first_slot_eq_deep_line_angle_iff_m_eq_two
  trivial_zero_ladder := trivial_zeta_zero_ladder
  deep_cell_line_angle := fun m hm => (deepSymmetricTwiddleCell m hm).line_angle_eq

/-!
## Status

* **Unconditional:** `θ_m = π/(2+m)`; `(2,2,2)` non-balance pole cell; first-slot
  angle `2π/m³` matches `θ_m` only for `m = 2`; trivial zero ladder.
* **Conjecture:** `EveryDeepSymmetricTwiddleHasNontrivialZero` for `m ≥ 3`.
* **Not claimed:** `(2,2,2)` hosts a nontrivial zero; partition first-slot at
  `m³` locates deeper zeros without the line law.
-/

end

end Hqiv.Story
