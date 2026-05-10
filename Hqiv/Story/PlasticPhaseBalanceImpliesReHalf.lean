import Hqiv.Story.PlasticCriticalLineBridge
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

/-!
# Phase-balance bridge (Story)

This module isolates the easier analytic sub-goal around exact 45-degree
phase symmetry (`|Re| = |Im|`) from geometric diagonalization.
-/

namespace Hqiv.Story

noncomputable section

/--
A point lies exactly on a 45-degree diagonal plane in `ℤ^3` when at least two
coordinates coincide.
-/
def LiesOn45Diagonal (point : Fin 3 → ℤ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ point i = point j

/-- On `Fin 3 → ℤ`, “two coordinates agree” is equivalent to one of the three axis pairs. -/
theorem liesOn45Diagonal_iff {p : Fin 3 → ℤ} :
    LiesOn45Diagonal p ↔ p 0 = p 1 ∨ p 0 = p 2 ∨ p 1 = p 2 := by
  constructor
  · rintro ⟨i, j, hij, he⟩
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inl he.symm
    · exact False.elim (hij rfl)
    · exact Or.inr (Or.inr he)
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr he.symm)
    · exact False.elim (hij rfl)
  · rintro (h01 | h02 | h12)
    · exact ⟨(0 : Fin 3), (1 : Fin 3), by decide, h01⟩
    · exact ⟨(0 : Fin 3), (2 : Fin 3), by decide, h02⟩
    · exact ⟨(1 : Fin 3), (2 : Fin 3), by decide, h12⟩

/--
Single unifying arithmetic fact (Sub-goal 1 backbone):
for all sufficiently large integers, there is a signed three-cubes
representation with at least one near-diagonal pair.
-/
def EverySufficientlyLargeIntegerIsNearDiagonalSumOfThreeSignedCubes : Prop :=
  ∃ someLargeBound : ℕ,
    ∀ m : ℕ, m > someLargeBound →
      ∃ j k l : ℤ,
        j ^ 3 + k ^ 3 + l ^ 3 = (m : ℤ) ∧
        (Int.natAbs (j - k) ≤ 1 ∨
         Int.natAbs (k - l) ≤ 1 ∨
         Int.natAbs (l - j) ≤ 1)

/--
Near-diagonal variant used throughout the root-scale shell story:
two coordinates are equal or differ by at most one.
-/
def LiesNear45Diagonal (point : Fin 3 → ℤ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ Int.natAbs (point i - point j) ≤ 1

/--
Strict **body diagonal** of the integer cube: all three coordinates coincide (`j = k = l`).

This is **stronger** than the Story survivor class `LiesOn45Diagonal` / `DiagonalPointHasPermutationSymmetry`
(two coordinates equal). It is kept for the bookkeeping lemma
`Hqiv.Story.latticePointStep_of_liesOnBodyDiagonal` (`m = 3j` when all three match).
-/
def LiesOnBodyDiagonal (point : Fin 3 → ℤ) : Prop :=
  point 0 = point 1 ∧ point 1 = point 2

theorem liesOnBodyDiagonal_implies_liesOn45Diagonal (point : Fin 3 → ℤ)
    (h : LiesOnBodyDiagonal point) : LiesOn45Diagonal point :=
  ⟨(0 : Fin 3), (1 : Fin 3), by decide, h.1⟩

theorem liesOnBodyDiagonal_implies_liesNear45Diagonal (point : Fin 3 → ℤ)
    (h : LiesOnBodyDiagonal point) : LiesNear45Diagonal point :=
  ⟨(0 : Fin 3), (1 : Fin 3), by decide, by
    rcases h with ⟨h01, _⟩
    simp [h01]⟩

/--
Geometric condition (coordinate-space, not complex-phase): a **face 45° diagonal**
point in `ℤ^3` — at least two coordinates coincide (`LiesOn45Diagonal`).

This is the survivor class used with the `0 ↔ 1` mirror (`fixedByMirrorSwap01` /
`LiesOn45Diagonal01` track in this file).

**Prime / cancellation arithmetic** (e.g. paired shell rays such as `5` and `5²`,
and the “two primes” bookkeeping) is **not** encoded here: it lives in the arity /
twisted-Euler mirror pipeline (`ArityMirrorCancellationBridge`, `PlasticTwistedEulerCharacter`,
`RapidityPolarFactorOracle`, …), not in the three-coordinate equality predicate.
-/
def DiagonalPointHasPermutationSymmetry (point : Fin 3 → ℤ) : Prop :=
  LiesOn45Diagonal point

/-- Coordinate reflection swapping axes `0` and `1` (and fixing `2`). -/
def mirrorSwap01 (point : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => point (if i = 0 then 1 else if i = 1 then 0 else 2)

/--
Arithmetic class for shell indices: prime powers `p^k` with `k ≥ 1`.
-/
def IsPrimePowerIndex (n : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧ n = p ^ k

/-- `15` is not a prime power (`3 * 5` with distinct primes). -/
theorem not_isPrimePowerIndex_fifteen : ¬ IsPrimePowerIndex 15 := by
  rintro ⟨p, k, hp, hk1, h15⟩
  have hpk : p ^ k = 15 := h15.symm
  have hp2 : 2 ≤ p := hp.two_le
  have h2k : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
  rw [hpk] at h2k
  have hk3 : k ≤ 3 := by
    by_contra h
    push_neg at h
    have hk4 : 4 ≤ k := by omega
    have h16 : 16 ≤ 2 ^ k := by
      calc
        (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mpr hk4
    linarith
  have hk3' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3' with rfl | rfl | rfl
  · simp only [pow_one] at hpk
    subst hpk
    norm_num at hp
  · have hpk2 : p * p = 15 := by simpa [pow_two, mul_assoc] using hpk
    have hp15 : p ≤ 15 := by nlinarith
    interval_cases p <;> omega
  · have hpk3 : p * p * p = 15 := by
      simpa [pow_succ, mul_assoc, pow_two] using hpk
    have hp15 : p ≤ 15 := by nlinarith
    interval_cases p <;> omega

/-- `10` is not a prime power (`2 * 5`). -/
theorem not_isPrimePowerIndex_ten : ¬ IsPrimePowerIndex 10 := by
  rintro ⟨p, k, hp, hk1, h10⟩
  have hpk : p ^ k = 10 := h10.symm
  have hp2 : 2 ≤ p := hp.two_le
  have h2k : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
  rw [hpk] at h2k
  have hk3 : k ≤ 3 := by
    by_contra h
    push_neg at h
    have hk4 : 4 ≤ k := by omega
    have h16 : 16 ≤ 2 ^ k := by
      calc
        (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mpr hk4
    linarith
  have hk3' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3' with rfl | rfl | rfl
  · simp only [pow_one] at hpk
    subst hpk
    norm_num at hp
  · have hpk2 : p * p = 10 := by simpa [pow_two, mul_assoc] using hpk
    have hp10 : p ≤ 10 := by nlinarith
    interval_cases p <;> omega
  · have hpk3 : p * p * p = 10 := by simpa [pow_succ, mul_assoc, pow_two] using hpk
    have hp10 : p ≤ 10 := by nlinarith
    interval_cases p <;> omega

/-- Prime-power shell index with an even exponent. -/
def IsEvenPrimePowerIndex (n : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧ k % 2 = 0 ∧ n = p ^ k

/-- Prime-power shell index with an odd exponent. -/
def IsOddPrimePowerIndex (n : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧ k % 2 = 1 ∧ n = p ^ k

/--
Any prime-power shell index splits into even-exponent or odd-exponent class.
-/
theorem primePower_even_or_odd_exponent
    {n : ℕ} (hPP : IsPrimePowerIndex n) :
    IsEvenPrimePowerIndex n ∨ IsOddPrimePowerIndex n := by
  rcases hPP with ⟨p, k, hp, hk1, hkPow⟩
  rcases Nat.even_or_odd k with hEven | hOdd
  · exact Or.inl ⟨p, k, hp, hk1, (Nat.even_iff.mp hEven), hkPow⟩
  · exact Or.inr ⟨p, k, hp, hk1, (Nat.odd_iff.mp hOdd), hkPow⟩

/-- A point is fixed by the `0 ↔ 1` mirror (self-paired under that reflection). -/
def FixedByMirrorSwap01 (point : Fin 3 → ℤ) : Prop :=
  mirrorSwap01 point = point

/--
Axis-01 diagonal condition (the explicit 45° diagonal plane for the `0 ↔ 1`
mirror).
-/
def LiesOn45Diagonal01 (point : Fin 3 → ℤ) : Prop :=
  point (0 : Fin 3) = point (1 : Fin 3)

/--
For the chosen mirror map, "fixed by mirror" is exactly "lies on the 01-diagonal
plane".
-/
theorem fixedByMirrorSwap01_iff_diagonal01
    (point : Fin 3 → ℤ) :
    FixedByMirrorSwap01 point ↔ LiesOn45Diagonal01 point := by
  constructor
  · intro hFix
    have hAt0 := congrArg (fun f => f (0 : Fin 3)) hFix
    simpa [FixedByMirrorSwap01, mirrorSwap01, LiesOn45Diagonal01] using hAt0.symm
  · intro hDiag01
    funext i
    fin_cases i
    · simpa [FixedByMirrorSwap01, mirrorSwap01, LiesOn45Diagonal01] using hDiag01.symm
    · simpa [FixedByMirrorSwap01, mirrorSwap01, LiesOn45Diagonal01] using hDiag01
    · simp [mirrorSwap01]

/--
On `ℤ^3`, if a point is not on a 45-degree diagonal plane then swapping the
first two coordinates yields a distinct mirror point.
-/
theorem non_diagonal_point_has_distinct_mirror
    (point : Fin 3 → ℤ)
    (hNotOnDiagonal : ¬ LiesOn45Diagonal point) :
    ∃ mirror : Fin 3 → ℤ,
      mirror ≠ point ∧
      (∀ i, mirror i = point (if i = 0 then 1 else if i = 1 then 0 else 2)) := by
  refine ⟨mirrorSwap01 point, ?_, ?_⟩
  · intro hEq
    have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
    have hDiag01 : point (0 : Fin 3) = point (1 : Fin 3) := by
      have hAt0 := congrArg (fun f => f (0 : Fin 3)) hEq
      simpa [mirrorSwap01] using hAt0.symm
    exact hNotOnDiagonal ⟨0, 1, h01, hDiag01⟩
  · intro i
    rfl

/--
Permutation-orbit cancellation predicate (placeholder): off the **face 45° diagonal**
(`LiesOn45Diagonal`), the orbit is treated as cancelling.

Then `¬ PermutationOrbitCancels point` is `¬¬ LiesOn45Diagonal point`, i.e. classical
double-negation packaging around the same face-diagonal class.
-/
def PermutationOrbitCancels (point : Fin 3 → ℤ) : Prop :=
  ¬ LiesOn45Diagonal point

/--
Diagonal survivor class under the permutation/octal symmetry picture.
-/
def DiagonalPermutationSurvivor (point : Fin 3 → ℤ) : Prop :=
  DiagonalPointHasPermutationSymmetry point ∧ ¬ PermutationOrbitCancels point

/--
Geometric-cancellation principle:
every point *not* on a face 45° diagonal is in the cancelling orbit class.
-/
def NonDiagonalPointsCancelByPermutation : Prop :=
  ∀ point : Fin 3 → ℤ,
    ¬ LiesOn45Diagonal point →
      PermutationOrbitCancels point

/-- Off–face-diagonal points lie in the cancelling class (`PermutationOrbitCancels`). -/
theorem nonDiagonalPointsCancelByPermutation_trivial :
    NonDiagonalPointsCancelByPermutation := by
  intro point hNotDiag
  simpa [PermutationOrbitCancels] using hNotDiag

/--
Face-diagonal points are the only survivors once the off-diagonal cancellation law
is assumed.
-/
theorem survivor_must_be_on_45_diagonal
    (hCancel : NonDiagonalPointsCancelByPermutation)
    (point : Fin 3 → ℤ)
    (hSurvive : ¬ PermutationOrbitCancels point) :
    LiesOn45Diagonal point := by
  by_contra hNotDiag
  exact hSurvive (hCancel point hNotDiag)

/--
If a point is fixed by the mirror, it cannot have a distinct mirror partner
under that same map.
-/
theorem fixed_point_has_no_distinct_swap01_mirror
    (point : Fin 3 → ℤ)
    (hFix : FixedByMirrorSwap01 point) :
    ¬ (∃ mirror : Fin 3 → ℤ,
        mirror ≠ point ∧
        (∀ i, mirror i = point (if i = 0 then 1 else if i = 1 then 0 else 2))) := by
  intro h
  rcases h with ⟨mirror, hNe, hMirror⟩
  have hMirrorEq : mirror = mirrorSwap01 point := by
    funext i
    simpa [mirrorSwap01] using hMirror i
  have hPointEqMirror : point = mirrorSwap01 point := hFix.symm
  have : mirror = point := by
    calc
      mirror = mirrorSwap01 point := hMirrorEq
      _ = point := by simpa using hPointEqMirror.symm
  exact hNe this

/--
Point model that carries both shell data and an explicit 3D lattice point.
This mirrors the sketch form where hypotheses mention `P.point`.
-/
structure PlasticRHBalancePointGeom extends PlasticLatticePoint where
  point : Fin 3 → ℤ

/--
Sketch lemma (assumption form, no `sorry`):
if a geometric point diagonalizes to 45°, then its shell step phase factor lies
exactly on the 45° line (`|Re| = |Im|`).
-/
def DiagonalImpliesPhaseExactlyOn45Line : Prop :=
  ∀ (P : PlasticRHBalancePointGeom),
    DiagonalizesTo45 P.point →
      PhaseIsExactlyOn45Line (criticalLineStep P.toPlasticLatticePoint)

/--
Core analytic content for Sub-goal 1 in "exact symmetry" form:
nontrivial geometric diagonalization forces exact 45-degree phase-line placement.
-/
def Subgoal1CoreAnalyticContent : Prop :=
  DiagonalImpliesPhaseExactlyOn45Line

/--
Geometric classification slot from the refined picture:
diagonal points belong to the prime-power survivor class.
-/
def DiagonalPointsArePrimePowerClass : Prop :=
  ∀ (P : PlasticRHBalancePointGeom),
    DiagonalizesTo45 P.point →
      IsPrimePowerIndex P.n

/--
Cubic/octal analytic lock slot:
prime-power shell indices land exactly on the 45° phase line.

This is the Diophantine `ℤ[ρ]` / 8-fold symmetry step isolated as a single
assumption.
-/
def CubicOctantPrimePowerPhaseLock : Prop :=
  ∀ n : ℕ, IsPrimePowerIndex n → PhaseIsExactlyOn45Line n

/--
Focused Diophantine core:
prime squares land exactly on the 45° phase line by the cubic/octal lock.
-/
def PrimeSquareCubicOctantPhaseLock : Prop :=
  ∀ (p : ℕ), Nat.Prime p → PhaseIsExactlyOn45Line (p ^ 2)

/--
Generic odd-exponent channel (user's "line law"): odd prime-power indices land
on the 45° line.
-/
def OddPrimePowerGenericPhaseLock : Prop :=
  ∀ n : ℕ, IsOddPrimePowerIndex n → PhaseIsExactlyOn45Line n

/--
Even exponent reduction channel:
an even prime-power index either is the square case itself or reduces to a
generic line-law representative.

This keeps the remaining arithmetic proof obligation explicit.
-/
def EvenPrimePowerReducesToSquareOrGeneric : Prop :=
  ∀ n : ℕ, IsEvenPrimePowerIndex n →
    (∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2) ∨ IsOddPrimePowerIndex n

/--
If even exponents reduce to (prime-square) or generic odd channel, then the
focused square lock plus odd generic lock produce the full even channel lock.
-/
theorem evenPrimePower_phaseLock_of_square_or_generic
    (hSquare : PrimeSquareCubicOctantPhaseLock)
    (hOddGeneric : OddPrimePowerGenericPhaseLock)
    (hReduce : EvenPrimePowerReducesToSquareOrGeneric) :
    ∀ n : ℕ, IsEvenPrimePowerIndex n → PhaseIsExactlyOn45Line n := by
  intro n hEvenPP
  rcases hReduce n hEvenPP with hSquareCase | hOddCase
  · rcases hSquareCase with ⟨p, hp, hnp⟩
    simpa [hnp] using hSquare p hp
  · exact hOddGeneric n hOddCase

/--
Refined split form of the remaining Diophantine lock:
`CubicOctantPrimePowerPhaseLock` follows once both exponent-parity channels
are controlled.

This encodes the user-guided next target:
- even prime-power exponents carry the dedicated cubic/octal shell lock,
- odd prime-power exponents lie on the 45° line by the generic line law.
-/
theorem cubicOctantPrimePowerPhaseLock_of_even_odd_split
    (hEven : ∀ n : ℕ, IsEvenPrimePowerIndex n → PhaseIsExactlyOn45Line n)
    (hOdd  : ∀ n : ℕ, IsOddPrimePowerIndex n → PhaseIsExactlyOn45Line n) :
    CubicOctantPrimePowerPhaseLock := by
  intro n hPP
  rcases primePower_even_or_odd_exponent hPP with hPPeven | hPPodd
  · exact hEven n hPPeven
  · exact hOdd n hPPodd

/--
Unifying-hinge reduction statement:
once the near-diagonal signed three-cubes fact is available, together with the
cubic/octal transfer law from near-diagonal cube data to phase-line placement,
the split prime-power channels follow.

This keeps the project honest about the one central arithmetic input while
deferring the transfer mechanics to a single explicit bridge.
-/
def NearDiagonalThreeCubesToPrimePowerPhaseChannels : Prop :=
  EverySufficientlyLargeIntegerIsNearDiagonalSumOfThreeSignedCubes →
    PrimeSquareCubicOctantPhaseLock ∧ OddPrimePowerGenericPhaseLock ∧
      EvenPrimePowerReducesToSquareOrGeneric

/--
Diagonal-to-45° phase lock derived from the two refined assumptions:
1) diagonal points are in the prime-power class,
2) cubic/octal phase lock for prime powers.
-/
theorem diagonalizes_to_45_implies_phase_exactly_on_45_line_of_cubic_octant
    (hClass : DiagonalPointsArePrimePowerClass)
    (hLock : CubicOctantPrimePowerPhaseLock) :
    DiagonalImpliesPhaseExactlyOn45Line := by
  intro P hDiag
  exact hLock P.n (hClass P hDiag)

/--
Geometric-arithmetic picture (refined): prime-power shells land on the diagonal
fixed class for the mirror map.
-/
def PrimePowerLandsOnDiagonalFixedClass : Prop :=
  ∀ (P : PlasticRHBalancePointGeom),
    IsPrimePowerIndex P.n →
      FixedByMirrorSwap01 P.point

/--
Prime-square geometric specialization:
prime-square shell indices admit a face-diagonal symmetric representative.
-/
def PrimeSquareHasDiagonalPermutationRepresentative : Prop :=
  ∀ (P : PlasticRHBalancePointGeom),
    (∃ p : ℕ, Nat.Prime p ∧ P.n = p ^ 2) →
      DiagonalPointHasPermutationSymmetry P.point

/--
Under the refined picture, prime-power points have no distinct mirror partner
for the `0 ↔ 1` reflection.
-/
theorem primePower_has_no_distinct_swap01_mirror
    (hPrimePowerDiag : PrimePowerLandsOnDiagonalFixedClass)
    (P : PlasticRHBalancePointGeom)
    (hPP : IsPrimePowerIndex P.n) :
    ¬ (∃ mirror : Fin 3 → ℤ,
        mirror ≠ P.point ∧
        (∀ i, mirror i = P.point (if i = 0 then 1 else if i = 1 then 0 else 2))) := by
  exact fixed_point_has_no_distinct_swap01_mirror P.point (hPrimePowerDiag P hPP)

/--
Named theorem form of the sketch, parameterized by the single remaining analytic
assumption.
-/
theorem diagonalizes_to_45_implies_phase_exactly_on_45_line
    (hExact : DiagonalImpliesPhaseExactlyOn45Line)
    (P : PlasticRHBalancePointGeom)
    (h : DiagonalizesTo45 P.point) :
    PhaseIsExactlyOn45Line (criticalLineStep P.toPlasticLatticePoint) :=
  hExact P h

/--
Sub-goal 1 extraction from the diagonal lemma, in the point-free bridge form.
-/
theorem phaseBalanceImpliesReHalf_of_diagonalLemma
    (hDiag : DiagonalImpliesPhaseExactlyOn45Line)
    (hLift :
      ∀ (P : PlasticRHBalancePoint),
        HasPhaseBalance45Diag P →
          ∃ Q : PlasticRHBalancePointGeom,
            Q.toPlasticLatticePoint = P ∧
            DiagonalizesTo45 Q.point)
    (hSign :
      ∀ n : ℕ, PhaseIsExactlyOn45Line n →
        (plasticPhaseFactor n).re = (plasticPhaseFactor n).im) :
    PhaseBalanceImpliesReHalf := by
  intro P hP
  rcases hLift P hP with ⟨Q, hQeq, hQdiag⟩
  have h45 : PhaseIsExactlyOn45Line (criticalLineStep Q.toPlasticLatticePoint) :=
    hDiag Q hQdiag
  have hReEqImQ :
      (plasticPhaseFactor (criticalLineStep Q.toPlasticLatticePoint)).re =
      (plasticPhaseFactor (criticalLineStep Q.toPlasticLatticePoint)).im :=
    hSign (criticalLineStep Q.toPlasticLatticePoint) h45
  simpa [hQeq] using hReEqImQ

/--
Exact-symmetry packaged version of Sub-goal 1.

Note: the symbol `PhaseBalanceImpliesReHalf` is already a `Prop` in
`PlasticCriticalLineBridge`; this theorem provides the derivation under the
three explicit bridge assumptions.
-/
theorem PhaseBalanceImpliesReHalf_from_exact_symmetry
    (hDiag : Subgoal1CoreAnalyticContent)
    (hLift :
      ∀ (P : PlasticRHBalancePoint),
        HasPhaseBalance45Diag P →
          ∃ Q : PlasticRHBalancePointGeom,
            Q.toPlasticLatticePoint = P ∧
            DiagonalizesTo45 Q.point)
    (hSign :
      ∀ n : ℕ, PhaseIsExactlyOn45Line n →
        (plasticPhaseFactor n).re = (plasticPhaseFactor n).im) :
    PhaseBalanceImpliesReHalf :=
  phaseBalanceImpliesReHalf_of_diagonalLemma hDiag hLift hSign

/--
Single-chain Sub-goal 1 bridge from the refined cubic/octal assumptions.
-/
theorem PhaseBalanceImpliesReHalf_from_cubic_octant_prime_power
    (hClass : DiagonalPointsArePrimePowerClass)
    (hLock : CubicOctantPrimePowerPhaseLock)
    (hLift :
      ∀ (P : PlasticRHBalancePoint),
        HasPhaseBalance45Diag P →
          ∃ Q : PlasticRHBalancePointGeom,
            Q.toPlasticLatticePoint = P ∧
            DiagonalizesTo45 Q.point)
    (hSign :
      ∀ n : ℕ, PhaseIsExactlyOn45Line n →
        (plasticPhaseFactor n).re = (plasticPhaseFactor n).im) :
    PhaseBalanceImpliesReHalf := by
  apply PhaseBalanceImpliesReHalf_from_exact_symmetry
  · exact diagonalizes_to_45_implies_phase_exactly_on_45_line_of_cubic_octant hClass hLock
  · exact hLift
  · exact hSign

end
end Hqiv.Story
