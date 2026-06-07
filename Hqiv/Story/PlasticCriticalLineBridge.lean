import Hqiv.Story.ArityFTADecomposition
import Hqiv.Story.ArityMirrorCancellationBridge
import Hqiv.Story.PlasticTwistedEulerCharacter
import Hqiv.Story.PlasticSpiralInterceptCoverage
import Hqiv.Story.S3EulerSO4PrimeAxisBridge
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Plastic critical-line bridge (Story)

Formal packaging of the statement:

If a point satisfies
1) FTA decomposition,
2) arity-mirror cancellation,
3) `k = 3` residue concentration,
4) 45° phase balance (`|X| = |R|`),

then its plastic phase corresponds to a zero on `Re(s) = 1/2`.

This file keeps the statement explicit and theorem-ready while deferring analytic
details to downstream modules.
-/

namespace Hqiv.Story

noncomputable section

/-- Phase balance on the analytic slice: 45° condition `|X| = |R|`. -/
def FortyFivePhaseBalance (R X : ℝ) : Prop :=
  |X| = |R|

/-- Minimal point data for the bridge statement. -/
structure PlasticLatticePoint where
  n : ℕ
  R : ℝ
  X : ℝ

/-- Compatibility alias for RH-balance phrasing used in notes. -/
abbrev PlasticRHBalancePoint := PlasticLatticePoint

/-- FTA decomposition condition at the point shell. -/
def HasFTADecomposition (P : PlasticLatticePoint) : Prop :=
  2 ≤ P.n

/-- Arity-mirror cancellation condition (packaged at shell index). -/
def HasArityMirrorCancellation (P : PlasticLatticePoint) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = P.n

/-- A nontrivial mirror factor pair forces the shell index to be **non-prime** (it is composite). -/
theorem not_prime_of_hasArityMirrorCancellation
    (P : PlasticLatticePoint) (h : HasArityMirrorCancellation P) :
    ¬ Nat.Prime P.n := by
  rcases h with ⟨a, b, ha, hb, hab⟩
  have a1 : a ≠ 1 := by rintro rfl; simp at ha
  have b1 : b ≠ 1 := by rintro rfl; simp at hb
  rw [← hab]
  simpa using Nat.not_prime_mul a1 b1

/--
Arithmetic core (no spiral dependence):
nontrivial factor vectors exist exactly on composite shells.
-/
theorem hasArityMirrorCancellation_iff_composite
    (P : PlasticLatticePoint) :
    HasArityMirrorCancellation P ↔ CompositeChannel P.n := by
  constructor
  · intro hVec
    rcases hVec with ⟨a, b, ha_gt1, hb_gt1, hab⟩
    have ha_pos : 0 < a := lt_trans (by decide : 0 < 1) ha_gt1
    have hb_pos : 0 < b := lt_trans (by decide : 0 < 1) hb_gt1
    have h2a : 2 ≤ a := Nat.succ_le_of_lt ha_gt1
    have h2n : 2 ≤ P.n := by
      calc
        2 ≤ a := h2a
        _ ≤ a * b := Nat.le_mul_of_pos_right a hb_pos
        _ = P.n := hab
    have ha_lt_n : a < P.n := by
      have hmul : a * 1 < a * b := Nat.mul_lt_mul_of_pos_left hb_gt1 ha_pos
      simpa [one_mul, hab] using hmul
    have hb_lt_n : b < P.n := by
      have hmul : 1 * b < a * b := Nat.mul_lt_mul_of_pos_right ha_gt1 hb_pos
      simpa [one_mul, hab] using hmul
    have hnotPrime : ¬ Nat.Prime P.n := by
      exact (Nat.not_prime_iff_exists_mul_eq h2n).2 ⟨a, b, ha_lt_n, hb_lt_n, hab⟩
    exact ⟨h2n, hnotPrime⟩
  · intro hComp
    exact compositeChannel_has_nontrivial_factor_pair hComp

/--
FTA shell depth (`2 ≤ P.n`) together with **no** arity-mirror factor pair forces **`P.n` prime**:
`HasArityMirrorCancellation` is equivalent to `CompositeChannel P.n`, so ruling out mirror
rules out composite shells at this scale.
-/
theorem Nat.Prime.of_hasFTADecomposition_of_not_hasArityMirrorCancellation
    (P : PlasticLatticePoint)
    (hFTA : HasFTADecomposition P)
    (hMirrorOff : ¬ HasArityMirrorCancellation P) :
    Nat.Prime P.n := by
  by_contra hnp
  exact hMirrorOff ((hasArityMirrorCancellation_iff_composite P).2 ⟨hFTA, hnp⟩)

/--
Refined nonzero channel: mirror-factor vectors are considered nonzero only on odd shells.
This captures the empirical rule that any shell with a factor of `2` lands in the zero channel.
-/
def HasNonzeroArityMirrorCancellation (P : PlasticLatticePoint) : Prop :=
  HasArityMirrorCancellation P ∧ P.n % 2 = 1

/--
Nonzero mirror vectors occur exactly on odd composite shells.
-/
theorem hasNonzeroArityMirrorCancellation_iff_oddComposite
    (P : PlasticLatticePoint) :
    HasNonzeroArityMirrorCancellation P ↔ CompositeChannel P.n ∧ P.n % 2 = 1 := by
  constructor
  · intro h
    refine ⟨(hasArityMirrorCancellation_iff_composite P).1 h.1, h.2⟩
  · intro h
    refine ⟨(hasArityMirrorCancellation_iff_composite P).2 h.1, h.2⟩

/--
Explicit zero-channel corollary: if `2 ∣ n`, the nonzero mirror-vector channel is impossible.
-/
theorem even_shell_forces_zero_nonzero_channel
    (P : PlasticLatticePoint)
    (hEven : P.n % 2 = 0) :
    ¬ HasNonzeroArityMirrorCancellation P := by
  intro hNZ
  have : (1 : ℕ) = 0 := by simpa [hEven] using hNZ.2
  exact Nat.one_ne_zero this

/--
`k = 2` arity marker (complex-plane layer in the story packaging).
-/
def IsK2Arity (k : ℕ) : Prop := k = 2

/--
On the `k = 2` arity (complex-plane layer), even shells are forced into the zero channel.
-/
theorem k2_even_shell_forces_zero_nonzero_channel
    (P : PlasticLatticePoint)
    (k : ℕ)
    (hk2 : IsK2Arity k)
    (hEven : P.n % 2 = 0) :
    ¬ HasNonzeroArityMirrorCancellation P := by
  have _ : k = 2 := hk2
  exact even_shell_forces_zero_nonzero_channel P hEven

/-- Residue concentrated on the `k = 3` channel. -/
def HasK3Residue (_P : PlasticLatticePoint) : Prop :=
  ∃ m : ℕ, m ≠ 0 ∧ annulusCubicCoeff m = k3OctantDiagCoeff m

/-- 45° phase-balance condition at the point. -/
def HasPhaseBalance45 (P : PlasticLatticePoint) : Prop :=
  FortyFivePhaseBalance P.R P.X

/--
A 3D lattice point "diagonalizes to 45°" if at least two coordinates are equal
or differ by at most one.
-/
def DiagonalizesTo45 (point : Fin 3 → ℤ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ Int.natAbs (point i - point j) ≤ 1

/--
The phase factor sits exactly on the 45° line (up to octant-sign symmetry):
`|Re z| = |Im z|`.
-/
def PhaseIsExactlyOn45Line (m : ℕ) : Prop :=
  let z := plasticPhaseFactor m
  |z.re| = |z.im|

/--
Strengthened 45° balance package: geometric diagonal preference together with
exact 45°-line phase symmetry.
-/
def HasPhaseBalance45Diag (P : PlasticRHBalancePoint) : Prop :=
  (∃ point : Fin 3 → ℤ, DiagonalizesTo45 point) ∧
    PhaseIsExactlyOn45Line P.n

/-- Canonical shell step readout for a lattice point. -/
def criticalLineStep (P : PlasticLatticePoint) : ℕ := P.n

/-- Critical-line zero predicate at imaginary height `t`. -/
def OnCriticalLine (t : ℝ) : Prop :=
  ∃ s : ℂ,
    s.re = (1 / 2 : ℝ) ∧
    s.im = t ∧
    riemannZeta s = 0

/--
Legacy over-strong bridge shape: every real height is a critical-line zeta zero.

This is kept only as an explicit guardrail for older notes.  The live bridge is
`PhaseForcesCriticalLine χ`, which realizes specific Euler/SO(4) cancellation
slots rather than arbitrary heights.
-/
abbrev PhaseForcesCriticalLine_Legacy : Prop :=
  ∀ t : ℝ, OnCriticalLine t

/--
Corrected phase bridge: surviving Euler-prime/SO(4) cancellation slots are
realized pointwise.  It does not assert zero existence at every height.
-/
def PhaseForcesCriticalLine (χ : PlasticTwiddleCharacter) : Prop :=
  EulerPrimeSO4FirstCancellationRealizesStrip χ

/--
Bridge theorem form:
FTA + mirror cancellation + `k=3` residue + 45° phase balance imply the
critical-line correspondence conclusion for the specific shell point.
-/
theorem plastic_phase_corresponds_to_critical_line_zero
    (P : PlasticLatticePoint)
    (hFTA : HasFTADecomposition P)
    (hMirror : HasArityMirrorCancellation P)
    (hK3 : HasK3Residue P)
    (h45 : HasPhaseBalance45 P)
    (hAnalytic :
      ∀ (P : PlasticRHBalancePoint),
        HasFTADecomposition P →
        HasArityMirrorCancellation P →
        HasK3Residue P →
          riemannZeta (⟨(1 / 2 : ℝ), plasticSpiralPhaseAtStep (criticalLineStep P)⟩ : ℂ) = 0) :
    OnCriticalLine (plasticSpiralPhaseAtStep (criticalLineStep P)) := by
  have _ := h45
  refine ⟨⟨(1 / 2 : ℝ), plasticSpiralPhaseAtStep (criticalLineStep P)⟩, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact hAnalytic P hFTA hMirror hK3

/--
Composite-shell instantiation helper:
for composite channels (`2 ≤ n`, not prime), the FTA and mirror conditions are
immediate from `ArityFTADecomposition`.
-/
theorem composite_point_has_fta_and_mirror
    (P : PlasticLatticePoint)
    (hComp : CompositeChannel P.n) :
    HasFTADecomposition P ∧ HasArityMirrorCancellation P := by
  refine ⟨hComp.1, ?_⟩
  exact (hasArityMirrorCancellation_iff_composite P).2 hComp

/-!
## Corrected phase bridge decomposition (analytic sub-goals)
-/

/-- Sub-goal 1: 45° phase balance forces `Re = Im` at the phase factor. -/
def PhaseBalanceImpliesReHalf : Prop :=
  ∀ (P : PlasticRHBalancePoint),
    HasPhaseBalance45Diag P →
      (plasticPhaseFactor (criticalLineStep P)).re = (plasticPhaseFactor (criticalLineStep P)).im

/-- Sub-goal 2: FTA + mirror + `k=3` residue force zeta vanishing at the critical-line candidate. -/
def LatticePhaseImpliesZetaZero : Prop :=
  ∀ (P : PlasticRHBalancePoint),
    HasFTADecomposition P →
    HasArityMirrorCancellation P →
    HasK3Residue P →
      riemannZeta (⟨(1 / 2 : ℝ), plasticSpiralPhaseAtStep (criticalLineStep P)⟩ : ℂ) = 0

/--
Decomposition wrapper: the remaining analytic work is represented as the conjunction
of the two natural sub-goals.
-/
theorem PhaseForcesCriticalLine_iff_two_subgoals :
    (χ : PlasticTwiddleCharacter) →
    (PhaseForcesCriticalLine χ → (PhaseBalanceImpliesReHalf ∧ LatticePhaseImpliesZetaZero)) →
    ((PhaseBalanceImpliesReHalf ∧ LatticePhaseImpliesZetaZero) → PhaseForcesCriticalLine χ) →
    (PhaseForcesCriticalLine χ ↔
      PhaseBalanceImpliesReHalf ∧ LatticePhaseImpliesZetaZero) := by
  intro χ hLeft hRight
  constructor
  · intro h
    exact hLeft h
  · intro h
    exact hRight h

end
end Hqiv.Story

