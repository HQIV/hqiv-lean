import Hqiv.Story.S3MidpointEckmannHiltonSoe
import Hqiv.Story.S3LogPhaseEdge

/-!
# Pythagorean inradius fibers as a Goldbach phase-cover test

This file is deliberately exploratory.  It checks whether the "circle randomness"
idea gives a non-restatement route into the Goldbach midpoint bridge.

The useful arithmetic carrier is the Euclid inradius

`r = (A + B - C) / 2 = n * (m - n)`.

The test matters because the integer-inradius fact alone has a small boundary
ambiguity: if `r` is prime, the divisor fiber has two branches (`n = 1` or
`m - n = 1`).  In the Goldbach-relevant non-axis range (`1 < n`), the ambiguity
disappears and prime inradius forces the gap-one branch.  Thus the missing
content is not the integer-radius identity; it is the phase-cover argument that
keeps the bridge on the non-axis/inverse-triple branch without assuming a
midpoint survivor.
-/

namespace Hqiv.Story

open Hqiv.Geometry

/-! ## Euclid inradius fiber -/

/-- First Euclid leg `A = m² - n²`. -/
def euclidLegA (m n : ℕ) : ℕ :=
  m ^ 2 - n ^ 2

/-- Second Euclid leg `B = 2mn`. -/
def euclidLegB (m n : ℕ) : ℕ :=
  2 * m * n

/-- Euclid hypotenuse `C = m² + n²`. -/
def euclidHypotenuse (m n : ℕ) : ℕ :=
  m ^ 2 + n ^ 2

/-- The integral Euclid inradius coordinate `r = n(m-n)`. -/
def euclidInradius (m n : ℕ) : ℕ :=
  n * (m - n)

/-- Integer first Euclid leg `A = m² - n²`. -/
def euclidLegZ_A (m n : ℤ) : ℤ :=
  m ^ 2 - n ^ 2

/-- Integer second Euclid leg `B = 2mn`. -/
def euclidLegZ_B (m n : ℤ) : ℤ :=
  2 * m * n

/-- Integer Euclid hypotenuse `C = m² + n²`. -/
def euclidHypotenuseZ (m n : ℤ) : ℤ :=
  m ^ 2 + n ^ 2

/-- Integer Euclid inradius coordinate `r = n(m-n)`. -/
def euclidInradiusZ (m n : ℤ) : ℤ :=
  n * (m - n)

/--
The Euclid excess `A+B-C` is twice the inradius.  This is the clean algebraic
form of the integer-incircle fact; positivity/primitivity are separate filters.
-/
theorem euclid_excessZ_eq_two_inradiusZ (m n : ℤ) :
    euclidLegZ_A m n + euclidLegZ_B m n - euclidHypotenuseZ m n =
      2 * euclidInradiusZ m n := by
  unfold euclidLegZ_A euclidLegZ_B euclidHypotenuseZ euclidInradiusZ
  ring

/-- Divisor-fiber form of the Euclid inradius. -/
def EuclidInradiusFiber (r n g : ℕ) : Prop :=
  0 < n ∧ 0 < g ∧ r = n * g

theorem euclid_inradius_fiber_of_gap {m n : ℕ} (_hnm : n ≤ m) (hn : 0 < n)
    (hg : 0 < m - n) :
    EuclidInradiusFiber (euclidInradius m n) n (m - n) := by
  exact ⟨hn, hg, rfl⟩

/--
Prime inradius fibers hit a boundary, but not a unique one: either `n = 1` or
the Euclid gap `g = m-n` is `1`.
-/
theorem prime_inradius_fiber_boundary {r n g : ℕ} (hr : Nat.Prime r)
    (h : EuclidInradiusFiber r n g) :
    n = 1 ∨ g = 1 := by
  rcases h with ⟨hn, _hg, hmul⟩
  have hndvd : n ∣ r := ⟨g, hmul⟩
  rcases (Nat.dvd_prime hr).mp hndvd with hn1 | hnr
  · exact Or.inl hn1
  · right
    apply Nat.mul_left_cancel hn
    calc
      n * g = r := hmul.symm
      _ = n := hnr.symm
      _ = n * 1 := by rw [Nat.mul_one]

/-- Once the axis branch `n = 1` is excluded, a prime inradius forces gap one. -/
theorem prime_inradius_non_axis_fiber_forces_gap_one {r n g : ℕ} (hr : Nat.Prime r)
    (h : EuclidInradiusFiber r n g) (hn : n ≠ 1) :
    g = 1 := by
  rcases prime_inradius_fiber_boundary hr h with hn1 | hg1
  · exact False.elim (hn hn1)
  · exact hg1

/-- In the Goldbach-relevant non-axis range `1 < n`, prime inradius forces gap one. -/
theorem prime_inradius_goldbach_range_forces_gap_one {r n g : ℕ} (hr : Nat.Prime r)
    (h : EuclidInradiusFiber r n g) (hn : 1 < n) :
    g = 1 :=
  prime_inradius_non_axis_fiber_forces_gap_one hr h (by omega)

/-- Prime inradius `3` has the gap-one branch. -/
theorem prime_three_inradius_gap_one_branch :
    EuclidInradiusFiber 3 3 1 := by
  norm_num [EuclidInradiusFiber]

/-- Prime inradius `3` also has the axis branch, so integrality alone does not select gap-one. -/
theorem prime_three_inradius_axis_branch :
    EuclidInradiusFiber 3 1 3 := by
  norm_num [EuclidInradiusFiber]

/-! ## Non-restatement hook into the existing EH obstruction -/

/--
The branch-selection content needed from circle/phase randomness.

This is intentionally phrased as the already-existing inverse-triple target rather than
as `CompositeMidpointHasSurvivor`: a proof here must turn duplicate reflected residue
crossings into a symmetric prime gap on the `N*g = square` locus.
-/
def PythagoreanPhaseCoverBranchSelection (N : ℕ) : Prop :=
  EckmannHiltonInverseTripleObstruction N

/--
If the phase-cover branch selection is proved, the existing EH chain discharges the
Goldbach midpoint at `N`.
-/
theorem pythagorean_phase_cover_branch_selection_implies_eh_discharge {N : ℕ}
    (hN : 4 ≤ N) (h : PythagoreanPhaseCoverBranchSelection N) :
    EckmannHiltonSoeDischarge N :=
  eckmann_hilton_forward_of_inverse_triple_obstruction hN h

/--
What extinction supplies unconditionally today: a duplicate reflected crossing.
The missing proof step is precisely to convert such a duplicate into the branch
selection above.
-/
theorem composite_extinction_supplies_duplicate_for_phase_cover {N : ℕ}
    (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ _c : ReflectDuplicateCrossing N, True :=
  eh_composite_extinction_reflect_duplicate hN hc hall

/-! ## Irrational prime-paired phase survivors -/

/--
Prime-paired irrational phase signature: the two prime log speeds have no
nontrivial integer relation.  This is the formal version of "the survivor is
irrational in phase"; it avoids choosing a particular quotient representation.
-/
def PrimePairedIrrationalPhase (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
    ∀ {k m : ℤ}, (k : ℝ) * Real.log p = (m : ℝ) * Real.log q → k = 0 ∧ m = 0

/-- Distinct primes carry an irrational/incommensurable phase pair. -/
theorem prime_paired_irrational_phase_of_distinct_primes {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    PrimePairedIrrationalPhase p q :=
  ⟨hp, hq, hne, fun h => prime_log_int_rel hp hq hne h⟩

/-- A strict midpoint survivor has a prime-paired irrational phase signature. -/
theorem strict_dual_survivor_has_irrational_phase {N p : ℕ}
    (hSurv : dualMidpointSurvivor N p) (hpLt : p < N) :
    PrimePairedIrrationalPhase p (2 * N - p) := by
  have hne : p ≠ 2 * N - p := by omega
  exact prime_paired_irrational_phase_of_distinct_primes hSurv.1 hSurv.2.1 hne

/--
A midpoint has an irrational phase survivor if some strict left slot survives and
its reflected prime partner supplies an incommensurable log phase.
-/
def IrrationalPhaseMidpointSurvivor (N : ℕ) : Prop :=
  ∃ p, dualMidpointSurvivor N p ∧ p < N ∧
    PrimePairedIrrationalPhase p (2 * N - p)

/-- Any composite midpoint survivor is automatically an irrational phase survivor. -/
theorem irrational_phase_survivor_of_composite_survivor {N : ℕ}
    (hc : ¬ Nat.Prime N) (hHas : CompositeMidpointHasSurvivor N) :
    IrrationalPhaseMidpointSurvivor N := by
  rcases hHas hc with ⟨p, hSurv⟩
  have hpLt : p < N := dual_composite_survivor_off_diagonal hc hSurv
  exact ⟨p, hSurv, hpLt, strict_dual_survivor_has_irrational_phase hSurv hpLt⟩

/--
EH discharge does not merely give a survivor at a composite midpoint; it gives a
survivor with an irrational prime-paired phase signature.
-/
theorem eckmann_hilton_discharge_gives_irrational_phase_survivor {N : ℕ}
    (hc : ¬ Nat.Prime N) (hDis : EckmannHiltonSoeDischarge N) :
    IrrationalPhaseMidpointSurvivor N :=
  irrational_phase_survivor_of_composite_survivor hc
    ((eckmann_hilton_discharge_iff_composite_survivor N).mp hDis)

/--
Honesty check: for a composite midpoint, "there is an irrational phase survivor"
is equivalent to the ordinary midpoint survivor statement.  The irrationality is
real, but by itself it is not a new existence proof.
-/
theorem irrational_phase_survivor_iff_composite_survivor {N : ℕ}
    (hc : ¬ Nat.Prime N) :
    IrrationalPhaseMidpointSurvivor N ↔ CompositeMidpointHasSurvivor N := by
  constructor
  · intro hIrr _hc'
    rcases hIrr with ⟨p, hSurv, _, _⟩
    exact ⟨p, hSurv⟩
  · exact irrational_phase_survivor_of_composite_survivor hc

/-! ## Finite stack escape form -/

/-- A left-prime slot is covered if some finite reflected stack modulus hits its partner. -/
def ReflectStackCovered (N p : ℕ) : Prop :=
  ∃ r, r ∈ finiteSoeAngleStack N ∧ reflectResidueCrossed N r p

/--
Finite-stack irrational escape: some off-diagonal prime slot is not covered by any
reflected rational/residue stack line.  This is the concrete "one survivor escapes
the rational circle cover" target.
-/
def FiniteStackIrrationalEscape (N : ℕ) : Prop :=
  ∃ p, p ∈ offDiagonalPrimeScanSlots N ∧ ¬ ReflectStackCovered N p

/-- An uncovered off-diagonal prime slot has a prime reflected partner, hence survives. -/
theorem escape_slot_gives_dual_survivor {N p : ℕ} (hN : 4 ≤ N)
    (hp : p ∈ offDiagonalPrimeScanSlots N) (hEsc : ¬ ReflectStackCovered N p) :
    dualMidpointSurvivor N p := by
  have hpData := (mem_offDiagonalPrimeScanSlots_iff (N := N) (by omega : 2 ≤ N)).mp hp
  rcases hpData with ⟨hpPrime, hp2, hpLt⟩
  have hq2 : 2 ≤ 2 * N - p := by omega
  have hqM : 2 * N - p ≤ 2 * N := by omega
  have hclear : ∀ r ∈ finiteSoeAngleStack N, ¬ reflectResidueCrossed N r p := by
    intro r hr hcross
    exact hEsc ⟨r, hr, hcross⟩
  have hqPrime : Nat.Prime (2 * N - p) :=
    (nat_prime_iff_reflect_stack_clear (N := N) (p := p) hq2 hqM).mpr hclear
  exact ⟨hpPrime, hqPrime, Nat.le_of_lt hpLt, by omega⟩

/-- A finite-stack escape gives an irrational phase survivor. -/
theorem finite_stack_escape_gives_irrational_phase_survivor {N : ℕ}
    (hN : 4 ≤ N) (hEsc : FiniteStackIrrationalEscape N) :
    IrrationalPhaseMidpointSurvivor N := by
  rcases hEsc with ⟨p, hp, hpEsc⟩
  have hSurv := escape_slot_gives_dual_survivor hN hp hpEsc
  have hpLt := (mem_offDiagonalPrimeScanSlots_iff (N := N) (by omega : 2 ≤ N)).mp hp |>.2.2
  exact ⟨p, hSurv, hpLt, strict_dual_survivor_has_irrational_phase hSurv hpLt⟩

/-- A finite-stack escape gives the usual composite midpoint survivor. -/
theorem finite_stack_escape_gives_composite_survivor {N : ℕ}
    (hN : 4 ≤ N) (hEsc : FiniteStackIrrationalEscape N) :
    CompositeMidpointHasSurvivor N := by
  intro _hc
  rcases hEsc with ⟨p, hp, hpEsc⟩
  exact ⟨p, escape_slot_gives_dual_survivor hN hp hpEsc⟩

/--
Conversely, a strict composite survivor is not covered by the reflected stack.  Thus
finite-stack escape is another exact form of the composite midpoint target.
-/
theorem finite_stack_escape_of_composite_survivor {N : ℕ}
    (hc : ¬ Nat.Prime N) (hHas : CompositeMidpointHasSurvivor N) :
    FiniteStackIrrationalEscape N := by
  rcases hHas hc with ⟨p, hSurv⟩
  have hpLt : p < N := dual_composite_survivor_off_diagonal hc hSurv
  have hN2 : 2 ≤ N := by
    have hp2 : 2 ≤ p := Nat.Prime.two_le hSurv.1
    omega
  have hpOff : p ∈ offDiagonalPrimeScanSlots N :=
    (mem_offDiagonalPrimeScanSlots_iff (N := N) hN2).mpr
      ⟨hSurv.1, Nat.Prime.two_le hSurv.1, hpLt⟩
  refine ⟨p, hpOff, ?_⟩
  intro hCover
  rcases hCover with ⟨r, hr, hcross⟩
  have hclear :=
    (nat_prime_iff_reflect_stack_clear (N := N) (p := p)
      (by omega : 2 ≤ 2 * N - p) (by omega : 2 * N - p ≤ 2 * N)).mp hSurv.2.1
  exact hclear r hr hcross

/-- For composite `N ≥ 4`, finite-stack irrational escape is equivalent to Goldbach midpoint survival. -/
theorem finite_stack_escape_iff_composite_survivor {N : ℕ}
    (hN : 4 ≤ N) (hc : ¬ Nat.Prime N) :
    FiniteStackIrrationalEscape N ↔ CompositeMidpointHasSurvivor N :=
  ⟨finite_stack_escape_gives_composite_survivor hN,
    finite_stack_escape_of_composite_survivor hc⟩

/-- Global finite-stack escape would prove Goldbach parity. -/
def FiniteStackIrrationalEscapeDischarge : Prop :=
  ∀ N : ℕ, 4 ≤ N → FiniteStackIrrationalEscape N

theorem finite_stack_escape_discharge_implies_goldbach_parity
    (hEsc : FiniteStackIrrationalEscapeDischarge) :
    GoldbachParity := by
  apply midpoint_goldbach_two_iff_goldbach_parity.mp
  refine midpoint_goldbach_of_composite_survivor (N₀ := 2) ?hPrime ?hComp
  · intro N _hN hPrime
    exact midpoint_sieve_survivor_of_prime hPrime
  · intro N _hN
    by_cases hN4 : 4 ≤ N
    · exact finite_stack_escape_gives_composite_survivor hN4 (hEsc N hN4)
    · intro hc
      have hsmall : N = 2 ∨ N = 3 := by omega
      rcases hsmall with rfl | rfl
      · exact False.elim (hc Nat.prime_two)
      · exact False.elim (hc Nat.prime_three)

/--
Finite-stack irrational escape fills the Goldbach half of the SO(8) bridge; an
independent RH proof supplies the zeta half.
-/
theorem finite_stack_escape_and_rh_implies_so8_bridge
    (hEsc : FiniteStackIrrationalEscapeDischarge) (hRH : RiemannHypothesis) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_two_iff_rh_and_goldbach_parity.mpr
    ⟨hRH, finite_stack_escape_discharge_implies_goldbach_parity hEsc⟩

/--
Same joint capstone using the bridge's native RH-side field.  This proves the
formal RH ∧ Goldbach package, but the RH content is exactly `hWeil`.
-/
theorem finite_stack_escape_and_weil_implies_rh_and_goldbach
    (hEsc : FiniteStackIrrationalEscapeDischarge)
    (hWeil : WeilPositivityForcesCriticalLine) :
    RiemannHypothesis ∧ GoldbachParity :=
  ⟨weilPositivity_iff_RiemannHypothesis.mp hWeil,
    finite_stack_escape_discharge_implies_goldbach_parity hEsc⟩

/-- Finite-stack escape plus Weil positivity constructs the full half-slope bridge. -/
theorem finite_stack_escape_and_weil_implies_so8_bridge
    (hEsc : FiniteStackIrrationalEscapeDischarge)
    (hWeil : WeilPositivityForcesCriticalLine) :
    SO8ProjectedHalfSlopeBridge 2 :=
  so8_projected_half_slope_two_iff_rh_and_goldbach_parity.mpr
    (finite_stack_escape_and_weil_implies_rh_and_goldbach hEsc hWeil)

/-! ## Global holonomy-to-Goldbach discharge -/

/--
Global phase-cover/holonomy discharge: every nontrivial composite midpoint in the
Goldbach range has the Pythagorean branch-selection obstruction.
-/
def PythagoreanHolonomyDischarge : Prop :=
  ∀ N : ℕ, 4 ≤ N → PythagoreanPhaseCoverBranchSelection N

/--
Global branch selection gives midpoint Goldbach from `N₀ = 2`.  Prime midpoints use
the diagonal survivor; composite midpoints `N ≥ 4` use the EH inverse-triple chain.
-/
theorem pythagorean_holonomy_discharge_implies_midpoint_goldbach
    (hHol : PythagoreanHolonomyDischarge) :
    MidpointGoldbachEventually 2 := by
  refine midpoint_goldbach_of_composite_survivor (N₀ := 2) ?hPrime ?hComp
  · intro N _hN hPrime
    exact midpoint_sieve_survivor_of_prime hPrime
  · intro N hN
    by_cases hN4 : 4 ≤ N
    · exact (eckmann_hilton_discharge_iff_composite_survivor N).mp
        (pythagorean_phase_cover_branch_selection_implies_eh_discharge hN4 (hHol N hN4))
    · intro hc
      have hsmall : N = 2 ∨ N = 3 := by omega
      rcases hsmall with rfl | rfl
      · exact False.elim (hc Nat.prime_two)
      · exact False.elim (hc Nat.prime_three)

/-- The global Pythagorean holonomy/phase-cover discharge implies Goldbach parity. -/
theorem pythagorean_holonomy_discharge_implies_goldbach_parity
    (hHol : PythagoreanHolonomyDischarge) :
    GoldbachParity :=
  midpoint_goldbach_two_iff_goldbach_parity.mp
    (pythagorean_holonomy_discharge_implies_midpoint_goldbach hHol)

end Hqiv.Story
