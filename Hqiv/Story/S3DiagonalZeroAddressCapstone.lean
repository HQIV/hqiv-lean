import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3ExplicitFormulaPrimePhaseCoincidence
import Hqiv.Story.HigherOrderArityDiagonalSymmetry
import Hqiv.Story.S3ConstructionsEquivalent

/-!
# Diagonal S³ zero address — master capstone

This module unifies the three charts of a nontrivial ζ-zero:

1. **Partition / circle chart** — twiddle-factor address `(a,b,c)` with a diagonal
   tuple (`isTwiddleTuple`) and harmonic-shell slot `(n,k)` with `n = a·b·c`;
2. **Rolling / S³ sample chart** — `ScaledS3Sample` with `RollingMatchesCriticalHeight`;
3. **Lattice diagonal chart** — `ZetaZeroArityDiagonalPoint` on a face 45° diagonal
   (`LiesOn45Diagonal`), packaged alongside the partition cell.

**Master target.**

`EveryNontrivialZeroHasDiagonalS3Address` — every nontrivial zero carries a witness
with all three charts aligned and `MatchedRollingZeroAt` (ζ identified with the
rolled residual on the zero channel).

**Capstone (proved here, no `sorry`).**

`EveryNontrivialZeroHasDiagonalS3Address → RiemannHypothesis`

via `MatchedRollingZeroAt → s.re = 1/2`.  The analytic inputs for *existence* of
witnesses remain `ExplicitFormulaLocalization`, `RollingZetaIdentificationAtCriticalLine`,
and a partition assignment at each height — not disguised as unconditional geometry.

## Honesty

* Proving **every** zero has a diagonal partition cell is the localization conjecture.
* Proving **RH** from a supplied witness is pure implication logic.
* `AllZetaZerosSatisfyArityDiagonalPreference` feeds the lattice leg; rolling
  identification feeds the ζ = residual leg; an explicit assignment bridges
  height → partition cell.
-/

namespace Hqiv.Story

noncomputable section

/-! ## Partition-chart diagonal address -/

/--
A **diagonal partition address**: twiddle tuple with at least two equal legs and a
harmonic-shell slot whose depth is the product shell `a·b·c`.
-/
structure DiagonalS3PartitionAddress where
  twiddle : TwiddleFactorAddress
  diagonal : isTwiddleTuple twiddle
  slot : HarmonicShellSlot
  shell_product :
    twiddleAddressShellDepth twiddle = slot.1

/-- Canonical first-cell partition address: `(2,2,2) ↦ shell 8, slot `k = 1`. -/
noncomputable def diagonalPartitionAddress222 : DiagonalS3PartitionAddress where
  twiddle := twiddleAddress222
  diagonal := by
    dsimp [isTwiddleTuple, twiddleAddress222]
    exact Or.inl rfl
  slot := twiddlePiQuarterSlot
  shell_product := twiddle_address_222_shell_depth

theorem diagonal_partition_address_222_twiddle :
    diagonalPartitionAddress222.twiddle = twiddleAddress222 :=
  rfl

theorem diagonal_partition_address_222_slot :
    diagonalPartitionAddress222.slot = twiddlePiQuarterSlot :=
  rfl

/-! ## Full diagonal S³ zero witness -/

/--
A **diagonal S³ zero witness** at `s`: partition cell + rolling sample with
`MatchedRollingZeroAt` (height match and ζ = S³ residual).
-/
structure DiagonalS3ZeroWitness (s : ℂ) where
  partition : DiagonalS3PartitionAddress
  sample : ScaledS3Sample
  matched : MatchedRollingZeroAt s sample

/--
**Master localization target:** every nontrivial ζ-zero admits a diagonal S³ witness.
-/
def EveryNontrivialZeroHasDiagonalS3Address : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → ∃ W : DiagonalS3ZeroWitness s, True

/--
**Lattice-chart specialization:** arity-diagonal witness at height `t = Im s` bundled
with a partition cell and rolling match.
-/
structure DiagonalS3ZeroWitnessWithArity (s : ℂ) extends DiagonalS3ZeroWitness s where
  arity : ZetaZeroArityDiagonalPoint
  arity_height : arity.t = s.im

/-! ## Master target aliases (equivalent charts) -/

/-- Same target as `EveryNontrivialZeroHasDiagonalS3Address` (named for paper index). -/
abbrev EveryZetaZeroIsDiagonalS3Address : Prop :=
  EveryNontrivialZeroHasDiagonalS3Address

theorem everyZetaZeroIsDiagonalS3Address_iff :
    EveryZetaZeroIsDiagonalS3Address ↔ EveryNontrivialZeroHasDiagonalS3Address :=
  Iff.rfl

/-! ## Implications to matched rolling and RH -/

theorem diagonal_witness_re_half {s : ℂ} (W : DiagonalS3ZeroWitness s) :
    s.re = (1 / 2 : ℝ) :=
  W.matched.1.1

theorem diagonal_witness_matched_rolling {s : ℂ} (W : DiagonalS3ZeroWitness s) :
    MatchedRollingZeroAt s W.sample :=
  W.matched

theorem diagonal_address_implies_matched_rolling_candidate
    (h : EveryNontrivialZeroHasDiagonalS3Address) :
    EveryNontrivialZeroHasMatchedRollingCandidate := by
  intro s hzz
  rcases h s hzz with ⟨W, _⟩
  exact ⟨W.sample, W.matched⟩

theorem RiemannHypothesis_of_everyDiagonalS3Address
    (h : EveryNontrivialZeroHasDiagonalS3Address) :
    RiemannHypothesis :=
  RiemannHypothesis_of_matchedRollingCandidates
    (diagonal_address_implies_matched_rolling_candidate h)

theorem RiemannHypothesis_of_everyZetaZeroIsDiagonalS3Address
    (h : EveryZetaZeroIsDiagonalS3Address) :
    RiemannHypothesis :=
  RiemannHypothesis_of_everyDiagonalS3Address h

/-! ## Balance on the partition slot (conditional identification) -/

theorem diagonal_witness_slot_balance_iff_zeta_zero_at_slot_angle
    (hId : RollingZetaIdentificationAtCriticalLine) {s : ℂ}
    (W : DiagonalS3ZeroWitness s) (hn : 0 < W.partition.slot.1)
    (hIm : s.im = shellSweepAngle hn W.partition.slot.2) :
    riemannZeta s = 0 ↔
      HarmonicShellBalanceEvent hn W.partition.slot.2 := by
  have hLine : s.re = (1 / 2 : ℝ) := diagonal_witness_re_half W
  have hEq : s = criticalLinePointAtHeight (shellSweepAngle hn W.partition.slot.2) := by
    apply Complex.ext
    · simpa [criticalLinePointAtHeight] using hLine
    · simpa [criticalLinePointAtHeight, hIm]
  simpa [hEq] using zeta_zero_iff_slot_coincidence_balance hId hn W.partition.slot.2

/-! ## Lattice diagonal → partition cell -/

/--
Partition twiddle tuple from a face-diagonal arity witness: use the equal
coordinate magnitude `(m,m,1)` so the product shell is `m²`.
-/
noncomputable def arityCoordinateMagnitude (P : ZetaZeroArityDiagonalPoint) : ℕ :=
  max 1 (Int.natAbs (P.point 0))

noncomputable def twiddleOfArityPoint (P : ZetaZeroArityDiagonalPoint) : TwiddleFactorAddress :=
  let m := arityCoordinateMagnitude P
  (m, m, 1)

theorem twiddle_of_arity_point_diagonal (P : ZetaZeroArityDiagonalPoint) :
    isTwiddleTuple (twiddleOfArityPoint P) := by
  dsimp [twiddleOfArityPoint, isTwiddleTuple]
  exact Or.inl rfl

theorem nat_lt_min_one_pred {n : ℕ} (hn : 0 < n) : min 1 (n - 1) < n := by
  rcases n with (_ | _ | n)
  · cases hn
  · decide
  · dsimp [min]
    omega

/--
Harmonic slot at depth `m²`: index `k = 1` when `m > 1`, else `k = 0` at shell `1`.
-/
noncomputable def slotOfArityPoint (P : ZetaZeroArityDiagonalPoint) : HarmonicShellSlot :=
  let m := arityCoordinateMagnitude P
  let n := m * m
  ⟨n, ⟨min 1 (n - 1), by
    have hm : 1 ≤ m := Nat.le_max_left 1 (Int.natAbs (P.point 0))
    exact nat_lt_min_one_pred (by dsimp [n]; nlinarith)⟩⟩

theorem slot_of_arity_point_depth (P : ZetaZeroArityDiagonalPoint) :
    twiddleAddressShellDepth (twiddleOfArityPoint P) = (slotOfArityPoint P).1 := by
  simp [twiddleOfArityPoint, twiddleAddressShellDepth, slotOfArityPoint,
    arityCoordinateMagnitude]

noncomputable def partitionAddressOfArityPoint (P : ZetaZeroArityDiagonalPoint) :
    DiagonalS3PartitionAddress where
  twiddle := twiddleOfArityPoint P
  diagonal := twiddle_of_arity_point_diagonal P
  slot := slotOfArityPoint P
  shell_product := slot_of_arity_point_depth P

theorem arity_diagonal_preference_implies_partition_cell
    (h : AllZetaZerosSatisfyArityDiagonalPreference) (t : ℝ)
    (hN : IsNontrivialZero t) :
    ∃ addr : DiagonalS3PartitionAddress, True := by
  rcases h t hN with ⟨P, _⟩
  exact ⟨partitionAddressOfArityPoint P, trivial⟩

/-! ## Height → partition assignment (existence conjecture slot) -/

/--
**Assignment conjecture slot (weaker than constructive zeros):** every real height
carries a diagonal partition cell label.  This is *not* the constructive program:
see `S3TwiddleAddressConstructiveZero` — balance at a twiddle slot forces a line
zero; full-line coverage / theta doubling is intentionally not claimed.
-/
def DiagonalPartitionAssignment : Prop :=
  ∀ t : ℝ, ∃ addr : DiagonalS3PartitionAddress, True

theorem diagonal_partition_assignment_at_222 :
    ∃ addr : DiagonalS3PartitionAddress, addr = diagonalPartitionAddress222 :=
  ⟨diagonalPartitionAddress222, rfl⟩

/-! ## Building witnesses from explicit-formula inputs -/

/--
From discrete Weil positivity + localization + rolling identification, every
nontrivial zero has a **rolling** diagonal witness (partition cell supplied
separately by `hAssign`).
-/
theorem diagonal_witness_of_explicit_identification_and_assignment
    (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine)
    (hAssign : DiagonalPartitionAssignment) (s : ℂ) (hzz : IsNontrivialZetaZero s) :
    ∃ W : DiagonalS3ZeroWitness s, True := by
  rcases hAssign s.im with ⟨addr, _⟩
  refine ⟨⟨addr, rolledSampleAtHeight s.im,
    matched_rolling_of_explicit_localization hWeil hLoc hId hzz⟩, trivial⟩

theorem everyNontrivialZeroHasDiagonalS3Address_of_explicit_identification_and_assignment
    (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine)
    (hAssign : DiagonalPartitionAssignment) :
    EveryNontrivialZeroHasDiagonalS3Address := by
  intro s hzz
  rcases diagonal_witness_of_explicit_identification_and_assignment
    hWeil hLoc hId hAssign s hzz with ⟨W, h⟩
  exact ⟨W, h⟩

theorem RiemannHypothesis_of_explicit_identification_and_assignment
    (hWeil : DiscreteWeilFormPositive) (hLoc : ExplicitFormulaLocalization)
    (hId : RollingZetaIdentificationAtCriticalLine)
    (hAssign : DiagonalPartitionAssignment) :
    RiemannHypothesis :=
  RiemannHypothesis_of_everyDiagonalS3Address
    (everyNontrivialZeroHasDiagonalS3Address_of_explicit_identification_and_assignment
      hWeil hLoc hId hAssign)

/-! ## Master capstone bundle -/

/--
Bundle packaging: diagonal partition cells, arity-diagonal lattice witnesses,
rolling identification, and the master RH capstone.
-/
structure DiagonalS3ZeroAddressCapstone where
  /-- Canonical first partition cell `(2,2,2) ↦ shell 8`. -/
  first_cell : DiagonalS3PartitionAddress
  first_cell_eq : first_cell = diagonalPartitionAddress222
  /-- Arity-diagonal preference yields partition cells at each height. -/
  arity_to_partition_of_preference :
    AllZetaZerosSatisfyArityDiagonalPreference →
      ∀ t, IsNontrivialZero t → ∃ addr : DiagonalS3PartitionAddress, True
  /-- Implication: master target ⇒ Mathlib RH. -/
  diagonal_implies_RH :
    EveryNontrivialZeroHasDiagonalS3Address → RiemannHypothesis
  /-- Implication: master target ⇒ matched rolling candidates. -/
  diagonal_implies_matched :
    EveryNontrivialZeroHasDiagonalS3Address →
      EveryNontrivialZeroHasMatchedRollingCandidate
  /-- Constructions equivalent: RH is the same target in every packaging. -/
  RH_packaging_equiv : Nonempty S3ComplexResidualModel ↔ RiemannHypothesis

noncomputable def diagonalS3ZeroAddressCapstone : DiagonalS3ZeroAddressCapstone where
  first_cell := diagonalPartitionAddress222
  first_cell_eq := rfl
  arity_to_partition_of_preference := arity_diagonal_preference_implies_partition_cell
  diagonal_implies_RH := RiemannHypothesis_of_everyDiagonalS3Address
  diagonal_implies_matched := diagonal_address_implies_matched_rolling_candidate
  RH_packaging_equiv := complexResidualModel_iff_RH

/-!
## Status

* **Unconditional:** definitions; `diagonalPartitionAddress222`; arity → partition
  map; `diagonal_address_implies_matched_rolling_candidate`;
  `RiemannHypothesis_of_everyDiagonalS3Address`; explicit+assignment constructor.
* **Master target (conjecture):** `EveryNontrivialZeroHasDiagonalS3Address`.
* **Analytic inputs for existence:** `ExplicitFormulaLocalization`,
  `RollingZetaIdentificationAtCriticalLine`, `DiagonalPartitionAssignment`
  (or full master target directly).
* **Not claimed:** arity preference alone implies RH without rolling identification;
  partition cell alone locates zeros without ζ = residual.
-/

end

end Hqiv.Story
