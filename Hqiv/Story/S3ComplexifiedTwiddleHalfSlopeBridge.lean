import Hqiv.Story.S3EscapingDiagonalTwiddleComplexification
import Hqiv.Story.S3ExplicitFormulaDualitySlot

/-!
# Complexified twiddle coverage → half-slope bridge

`S3EscapingDiagonalTwiddleComplexification` proves the local mechanism:
after off-diagonal cancellation leaves a diagonal survivor shell, multiplying by
the Hopf `j`–`k` complex phase preserves the zero locus and matches
`hopfJKTwiddleReadout` when the lattice amplitude is identified with the rolled
amplitude.

This module records the exact global use of that mechanism.  A **coverage**
hypothesis saying that every nontrivial zero is localized by such a complexified
diagonal twiddle certificate supplies the `critical_line` field of
`SO8ProjectedHalfSlopeBridge`.  The midpoint field remains the existing
Goldbach-side payload; it is not inferred from twiddle complexification alone.
-/

namespace Hqiv.Story

noncomputable section

/-! ## Complexified twiddle localization of zeta zeros -/

/--
A nontrivial zero is localized by a complexified diagonal twiddle shell when it
is the critical-line point at some height `t`, and the escaped diagonal shell at
that height has vanishing complexified twiddle readout.
-/
def ComplexifiedDiagonalTwiddleLocalizesZero (s : ℂ) : Prop :=
  ∃ t : ℝ, ∃ shell : Finset (Fin 3 → ℤ),
    s = criticalLinePointAtHeight t ∧
      (∀ p, p ∈ shell → DiagonalPermutationSurvivor p) ∧
        complexifiedDiagonalTwiddleShellPartial t shell = 0

/--
Global complexified-twiddle coverage: every nontrivial zero admits one of the
complexified diagonal survivor certificates above.
-/
def ComplexifiedTwiddleZeroCoverage : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → ComplexifiedDiagonalTwiddleLocalizesZero s

theorem complexified_twiddle_localization_re_half
    {s : ℂ} (h : ComplexifiedDiagonalTwiddleLocalizesZero s) :
    s.re = (1 / 2 : ℝ) := by
  rcases h with ⟨t, _shell, hs, _hSurv, _hZero⟩
  rw [hs]
  simp [criticalLinePointAtHeight]

/--
The complexified twiddle coverage hypothesis is exactly the RH-side field of the
half-slope bridge: every nontrivial zero is forced onto `Re = 1/2`.
-/
theorem complexified_twiddle_coverage_forces_critical_line
    (hCover : ComplexifiedTwiddleZeroCoverage) :
    WeilPositivityForcesCriticalLine := by
  dsimp [WeilPositivityForcesCriticalLine, AllNontrivialZerosOnLine]
  intro s hzz
  exact complexified_twiddle_localization_re_half (hCover s hzz)

/--
Half-slope bridge from complexified twiddle coverage plus the already-named
midpoint-pair field.  This is the honest global theorem enabled by the new
complexified twiddle mechanism.
-/
theorem so8_half_slope_bridge_of_complexified_twiddle_coverage
    (hCover : ComplexifiedTwiddleZeroCoverage)
    (hMid : Hqiv.Geometry.SO4ZetaHolonomyForcesMidpointPairs 2) :
    SO8ProjectedHalfSlopeBridge 2 where
  critical_line := complexified_twiddle_coverage_forces_critical_line hCover
  midpoint_pairs := hMid

/-! ## `(m,m,1)` coverage specialization -/

/--
The `(m,m,1)` complexified-twiddle localizer for a zero: the zero is the
critical-line point at the linked partition height, the linked shell balances,
and the lattice/rolling identification equates the survivor-shell amplitude with
the Hopf amplitude.
-/
def ComplexifiedTwiddleMMM1LocalizesZero (s : ℂ) : Prop :=
  ∃ m : ℕ, ∃ hm : 2 ≤ m,
    s =
      criticalLinePointAtHeight
        (criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
          (twiddle_mmm1_slot_pos hm)) ∧
      HarmonicShellBalanceEvent (twiddle_mmm1_slot_pos hm)
        (partitionAddressOfTwiddleMMM1 m hm).slot.2 ∧
        TwiddleMMM1LatticeSumEqRollingAmplitude m hm

def ComplexifiedTwiddleMMM1ZeroCoverage : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → ComplexifiedTwiddleMMM1LocalizesZero s

theorem complexified_twiddle_mmm1_localization_to_diagonal
    {s : ℂ} (h : ComplexifiedTwiddleMMM1LocalizesZero s) :
    ComplexifiedDiagonalTwiddleLocalizesZero s := by
  rcases h with ⟨m, hm, hs, hbal, hIdent⟩
  refine ⟨
    criticalLineHeightOfPartition (partitionAddressOfTwiddleMMM1 m hm)
      (twiddle_mmm1_slot_pos hm),
    twiddleMMM1SurvivorShell m,
    hs,
    ?_,
    ?_⟩
  · intro p hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact twiddle_voxel_lattice_point_survives (twiddleAddressMMM1 m)
  · exact complexified_twiddle_mmm1_zero_of_balance_and_rolling m hm hbal hIdent

theorem complexified_twiddle_mmm1_coverage_forces_critical_line
    (hCover : ComplexifiedTwiddleMMM1ZeroCoverage) :
    WeilPositivityForcesCriticalLine :=
  complexified_twiddle_coverage_forces_critical_line
    (fun s hzz => complexified_twiddle_mmm1_localization_to_diagonal (hCover s hzz))

/--
The `(m,m,1)` specialization of the bridge theorem: if every nontrivial zero is
covered by the complexified `(m,m,1)` twiddle localizer, then the RH-side field
of the bridge is supplied.  Adding the midpoint-pair field gives
`SO8ProjectedHalfSlopeBridge 2`.
-/
theorem so8_half_slope_bridge_of_complexified_twiddle_mmm1_coverage
    (hCover : ComplexifiedTwiddleMMM1ZeroCoverage)
    (hMid : Hqiv.Geometry.SO4ZetaHolonomyForcesMidpointPairs 2) :
    SO8ProjectedHalfSlopeBridge 2 where
  critical_line := complexified_twiddle_mmm1_coverage_forces_critical_line hCover
  midpoint_pairs := hMid

end

end Hqiv.Story
