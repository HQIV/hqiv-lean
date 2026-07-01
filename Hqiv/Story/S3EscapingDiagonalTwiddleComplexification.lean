import Hqiv.Story.S3TwiddleAddressConstructiveZero

/-!
# Escaping diagonalization → complex twiddle readout

The diagonal-survivor reduction leaves a scalar lattice amplitude after
off-diagonal permutation pairs cancel.  This module complexifies that survivor
amplitude by the nonzero Hopf `j`–`k` twiddle phase.  The payoff is deliberately
local and honest:

* multiplying the escaped diagonal amplitude by `exp(π·j·k·i)` does not change
  its zero locus;
* when the `(m,m,1)` survivor-shell amplitude is identified with the rolled
  Hopf amplitude, the complexified shell is exactly `hopfJKTwiddleReadout`;
* balance at the linked slot therefore gives a complex twiddle-zero certificate.

This is a bridge from real diagonal cancellation to complex twiddle transport,
not a global prime-selection or Goldbach discharge.
-/

namespace Hqiv.Story

open Complex
open scoped BigOperators

noncomputable section

/-! ## Complexifying the escaped diagonal amplitude -/

/--
Complexified diagonal-shell readout: the escaped diagonal survivor amplitude
with the Hopf `j`–`k` unit-circle phase attached.
-/
noncomputable def complexifiedDiagonalTwiddleShellPartial
    (t : ℝ) (shell : Finset (Fin 3 → ℤ)) : ℂ :=
  hopfJKUnitCirclePhase t * twistedLatticeShellPartial t shell

theorem complexified_diagonal_twiddle_shell_partial_eq
    (t : ℝ) (shell : Finset (Fin 3 → ℤ)) :
    complexifiedDiagonalTwiddleShellPartial t shell =
      hopfJKUnitCirclePhase t * twistedLatticeShellPartial t shell :=
  rfl

/--
The complex twiddle phase is never the source of vanishing.  After escaping to
the diagonal survivor shell, complexification preserves exactly the same zero
locus as the real/diagonal amplitude.
-/
theorem complexified_diagonal_twiddle_vanishes_iff_base
    (t : ℝ) (shell : Finset (Fin 3 → ℤ)) :
    complexifiedDiagonalTwiddleShellPartial t shell = 0 ↔
      twistedLatticeShellPartial t shell = 0 := by
  constructor
  · intro h
    rw [complexifiedDiagonalTwiddleShellPartial, mul_eq_zero] at h
    rcases h with hPhase | hBase
    · unfold hopfJKUnitCirclePhase at hPhase
      exact False.elim (Complex.exp_ne_zero _ hPhase)
    · exact hBase
  · intro h
    simp [complexifiedDiagonalTwiddleShellPartial, h]

/--
Named bridge: any diagonal survivor shell may be complexified by the Hopf
twiddle without changing whether the escaped amplitude vanishes.
-/
def EscapingDiagonalizationComplexifiesTwiddle : Prop :=
  ∀ (t : ℝ) (shell : Finset (Fin 3 → ℤ)),
    (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) →
      (complexifiedDiagonalTwiddleShellPartial t shell = 0 ↔
        twistedLatticeShellPartial t shell = 0)

theorem escaping_diagonalization_complexifies_twiddle :
    EscapingDiagonalizationComplexifiesTwiddle :=
  fun t shell _hSurvivor => complexified_diagonal_twiddle_vanishes_iff_base t shell

/-! ## Agreement with the Hopf `j`–`k` twiddle -/

theorem complexified_diagonal_shell_eq_hopf_twiddle_of_amplitude
    {t : ℝ} {shell : Finset (Fin 3 → ℤ)}
    (hAmp : twistedLatticeShellPartial t shell = (hopfJKCriticalAmplitude t : ℂ)) :
    complexifiedDiagonalTwiddleShellPartial t shell = hopfJKTwiddleReadout t := by
  simp [complexifiedDiagonalTwiddleShellPartial, hopfJKTwiddleReadout, hAmp]

theorem complexified_diagonal_shell_vanishes_iff_hopf_twiddle
    {t : ℝ} {shell : Finset (Fin 3 → ℤ)}
    (hAmp : twistedLatticeShellPartial t shell = (hopfJKCriticalAmplitude t : ℂ)) :
    complexifiedDiagonalTwiddleShellPartial t shell = 0 ↔
      hopfJKTwiddleReadout t = 0 := by
  rw [complexified_diagonal_shell_eq_hopf_twiddle_of_amplitude hAmp]

/-! ## `(m,m,1)` specialization -/

/-- Complexified survivor-shell readout for the canonical `(m,m,1)` twiddle cell. -/
noncomputable def complexifiedTwiddleMMM1ShellPartial (m : ℕ) (hm : 2 ≤ m) : ℂ :=
  let addr := partitionAddressOfTwiddleMMM1 m hm
  let hn := twiddle_mmm1_slot_pos hm
  complexifiedDiagonalTwiddleShellPartial
    (criticalLineHeightOfPartition addr hn)
    (twiddleMMM1SurvivorShell m)

theorem complexified_twiddle_mmm1_eq_hopf_twiddle
    (m : ℕ) (hm : 2 ≤ m)
    (hIdent : TwiddleMMM1LatticeSumEqRollingAmplitude m hm) :
    complexifiedTwiddleMMM1ShellPartial m hm =
      hopfJKTwiddleReadout
        (criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
          (twiddle_mmm1_slot_pos hm)) := by
  dsimp [complexifiedTwiddleMMM1ShellPartial]
  exact complexified_diagonal_shell_eq_hopf_twiddle_of_amplitude hIdent

theorem complexified_twiddle_mmm1_zero_of_balance_and_rolling
    (m : ℕ) (hm : 2 ≤ m)
    (hbal : HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
      (partitionAddressOfTwiddleMMM1 m hm).slot.2)
    (hIdent : TwiddleMMM1LatticeSumEqRollingAmplitude m hm) :
    complexifiedTwiddleMMM1ShellPartial m hm = 0 := by
  rw [complexified_twiddle_mmm1_eq_hopf_twiddle m hm hIdent]
  simpa [criticalLineHeightOfPartition] using
    partition_balance_constructive_hopf_twiddle_vanishes
      (twiddle_mmm1_slot_pos hm) (partitionAddressOfTwiddleMMM1 m hm).slot.2 hbal

/--
Complexified reduced-survivor certificate for `(m,m,1)`: the escaped diagonal
shell survives permutation cancellation and its complex twiddle readout vanishes
at a balanced linked slot.
-/
theorem complexified_reduced_diagonal_survivor_shell_at_twiddle_mmm1
    (m : ℕ) (hm : 2 ≤ m)
    (hbal : HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
      (partitionAddressOfTwiddleMMM1 m hm).slot.2)
    (hIdent : TwiddleMMM1LatticeSumEqRollingAmplitude m hm) :
    ∃ shell : Finset (Fin 3 → ℤ),
      (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) ∧
        complexifiedDiagonalTwiddleShellPartial
          (criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
            (twiddle_mmm1_slot_pos hm))
          shell = 0 := by
  refine ⟨twiddleMMM1SurvivorShell m, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact twiddle_voxel_lattice_point_survives (twiddleAddressMMM1 m)
  · exact complexified_twiddle_mmm1_zero_of_balance_and_rolling m hm hbal hIdent

end

end Hqiv.Story
