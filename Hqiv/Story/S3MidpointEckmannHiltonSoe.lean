import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Story.S3SoeSpectralBuild
import Hqiv.Story.S3MidpointConstructiveSpectralSlope
import Hqiv.Story.S3MidpointEulerSoeBridge
import Hqiv.Story.S3MidpointSO4DeltaOrbit

/-!
# Eckmann–Hilton collapse for the forward SoE at the Goldbach midpoint

## EH shape

Two unital operations on the **same** scan orbit share the involution `p ↦ 2N - p`:

1. **Forward SoE** (anchor `2`): `forwardResidueCrossed r p`
2. **Reflected SoE** (anchor `2N`): `reflectResidueCrossed N r p`

Survival at modulus `r` is the **meet** `dualModLineClear N r p`.  Meets commute, so the
finite stack is an **abelian** obstruction monoid — the Prop-level Eckmann–Hilton collapse.

The **unit** is the mirror slot `p = N`; it exists iff `N` is prime
(`mirror_slot_reflection_iff_prime`).  Composites miss the unit
(`composite_mirror_slot_fails`).

## Proved today (EH spine)

* forward / reflect legs **interchange** at each modulus (`eh_forward_reflect_interchange`);
* stack certificates **commute** across moduli (`eh_stack_certificate_commute`);
* positive-gap stack extinction ⇒ **no off-diagonal dual survivor**
  (`eh_extinction_forbids_off_diagonal_survivor`);
* composite + extinction ⇒ **no survivor at all** (`eh_extinction_and_composite_no_survivor`);
* spectral slot factors **commute** (`eh_spectral_slot_mul`, from `so4SpectralLine_mul`).

## Discharge ( = Goldbach midpoint for composites)

`EckmannHiltonSoeDischarge N` ≡ `ConstructiveSpectralForcesSlopeHit N` ≡
`EckmannHiltonForwardCollapse N` ≡ `CompositeMidpointHasSurvivor N`.  The EH argument
proves the **contrapositive skeleton** and the **extinction ⇒ crossing** pipeline; the
final implication `composite → ∃ survivor` is exactly `EckmannHiltonForwardCollapse N`.
-/

namespace Hqiv.Story

open Complex Hqiv.Geometry

noncomputable section

/-! ## 1. EH interchange on dual legs -/

theorem eh_forward_reflect_interchange (N r p : ℕ) :
    dualModLineClear N r p ↔
      (¬ reflectResidueCrossed N r p ∧ ¬ forwardResidueCrossed r p) := by
  unfold dualModLineClear
  exact and_comm

theorem eh_dualModLine_and_commute (N r s p : ℕ) :
    (dualModLineClear N r p ∧ dualModLineClear N s p) ↔
      (dualModLineClear N s p ∧ dualModLineClear N r p) :=
  and_comm

theorem eh_stack_slot_iff (N p : ℕ) (hpLe : p ≤ N) :
    (∀ r ∈ finiteSoeAngleStack N, dualModLineClear N r p) ↔
      gapSurvivesFiniteAngleStack N (midpointLeftGap N p) := by
  rw [gapSurvivesFiniteAngleStack_slot]
  rw [show N - midpointLeftGap N p = p from by rw [midpointLeftGap_le]; exact Nat.sub_sub_self hpLe]

theorem eh_stack_certificate_commute (N _g : ℕ) (r s : ℕ)
    (_hr : r ∈ finiteSoeAngleStack N) (_hs : s ∈ finiteSoeAngleStack N) :
    (dualModLineClear N r (N - _g) ∧ dualModLineClear N s (N - _g)) ↔
      (dualModLineClear N s (N - _g) ∧ dualModLineClear N r (N - _g)) :=
  and_comm

/-! ## 2. EH unit at the mirror -/

theorem eh_mirror_unit_iff_prime (N : ℕ) :
    symmetricPrimeReflectionAt N N ↔ Nat.Prime N :=
  mirror_slot_reflection_iff_prime N

theorem eh_composite_misses_unit (N : ℕ) (hc : ¬ Nat.Prime N) :
    ¬ symmetricPrimeReflectionAt N N :=
  composite_mirror_slot_fails N hc

/-! ## 3. Spectral EH: multiplicative slot factors commute -/

theorem eh_spectral_slot_mul (N p : ℕ) (s : ℂ) (hp : p ≤ N) :
    soeSlotSpectralChannel N p s =
      so4SpectralLine p s * so4SpectralLine (2 * N - p) s :=
  soeSlotSpectralChannel_eq_arms (N := N) (p := p) s hp

theorem eh_spectral_joint_mul (p q : ℕ) (s : ℂ) :
    so4SpectralLine (p * q) s = so4SpectralLine p s * so4SpectralLine q s :=
  so4SpectralLine_mul p q s

/-! ## 4. Extinction ⇒ no survivor (proved EH contrapositive) -/

/--
**EH contrapositive (proved).**  If every **positive** gap fails the abelian stack
certificate, no off-diagonal dual survivor exists.
-/
theorem eh_extinction_forbids_off_diagonal_survivor {N : ℕ}
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    {p : ℕ} (hSurv : dualMidpointSurvivor N p) (hc : ¬ Nat.Prime N) :
    False := by
  have hpLt : p < N := dual_composite_survivor_off_diagonal hc hSurv
  have hpLe : p ≤ N := hSurv.2.2.1
  have hpSlot : p ∈ midpointScanSlots N :=
    (mem_midpointScanSlots_iff (N := N) (p := p)).mpr
      ⟨Nat.Prime.two_le hSurv.1, hpLe⟩
  set g := midpointLeftGap N p
  have hg : g ∈ midpointGapOrbit N := gap_eq_leftGap_of_scan (N := N) hpSlot
  have hgap : N - p = g := (midpointLeftGap_le (N := N) (p := p)).symm
  have hgpos : 0 < g := by rw [← hgap]; omega
  have hp2 : 2 ≤ N - g := by rw [show N - g = p from by omega]; exact Nat.Prime.two_le hSurv.1
  have hle : N - g ≤ N := Nat.sub_le N g
  have hStack : gapSurvivesFiniteAngleStack N g :=
    (gap_survives_stack_iff_symmetric_prime (N := N) (g := g) hp2 hle).mpr
      ((symmetricPrimeReflectionAt_iff_gap (N := N) (p := p) hpLe).mp
        ((scan_slot_reflection_iff_survivor (N := N) (p := p) hpSlot).mpr hSurv))
  exact absurd hStack (hall g hg hgpos)

/--
**EH + composite (proved).**  Positive-gap stack extinction leaves no dual survivor.
-/
theorem eh_extinction_and_composite_no_survivor {N : ℕ} (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ¬ MidpointSieveSurvivorExists N := by
  intro ⟨p, hSurv⟩
  by_cases hpEq : p = N
  · have hdiag : dualMidpointSurvivor N N := hpEq ▸ hSurv
    exact hc ((dualMidpointSurvivor_diagonal_iff_prime N).mp hdiag)
  · exact eh_extinction_forbids_off_diagonal_survivor hall hSurv hc

theorem eh_extinction_contradicts_composite {N : ℕ} (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    (hGoldbach : CompositeMidpointHasSurvivor N) : False :=
  (eh_extinction_and_composite_no_survivor hc hall) (hGoldbach hc)

/-! ## 5. EH collapse target and equivalence -/

/--
**Eckmann–Hilton SoE discharge.**  The abelian stack cannot extinguish every positive
gap at a composite midpoint — equivalently some stack certificate survives.
-/
def EckmannHiltonSoeDischarge (N : ℕ) : Prop :=
  ConstructiveSpectralForcesSlopeHit N

theorem eckmann_hilton_discharge_iff_constructive (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ ConstructiveSpectralForcesSlopeHit N := Iff.rfl

theorem eckmann_hilton_discharge_iff_finite_extinction (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ FiniteStackCannotExtinctAllGaps N := by
  rw [eckmann_hilton_discharge_iff_constructive, finite_stack_extinction_iff_constructive]

theorem eckmann_hilton_discharge_iff_composite_survivor (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ CompositeMidpointHasSurvivor N := by
  rw [eckmann_hilton_discharge_iff_constructive, constructive_spectral_forces_iff_slope_hit,
      composite_slope_orbit_forces_iff_has_survivor]

theorem eckmann_hilton_discharge_iff_eh_forward (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ EckmannHiltonForwardCollapse N := by
  rw [eckmann_hilton_discharge_iff_finite_extinction]
  unfold EckmannHiltonForwardCollapse
  rfl

theorem eckmann_hilton_discharge_iff_midpoint_euler (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ MidpointEulerSoeDischarge N := by
  rw [eckmann_hilton_discharge_iff_composite_survivor, midpoint_euler_soe_discharge_iff_composite]

theorem eckmann_hilton_discharge_iff_soe_forward (N : ℕ) :
    EckmannHiltonSoeDischarge N ↔ SOEForwardForcesOffDiagonalReflection N := by
  rw [eckmann_hilton_discharge_iff_composite_survivor, soe_forward_forces_off_diagonal_iff_composite]

/--
**EH collapse (proved direction).**  If Goldbach holds at midpoint `N`, the abelian
stack cannot kill every positive gap when `N` is composite.
-/
theorem eckmann_hilton_collapse_of_composite_survivor {N : ℕ}
    (h : CompositeMidpointHasSurvivor N) : EckmannHiltonSoeDischarge N :=
  (eckmann_hilton_discharge_iff_composite_survivor N).mpr h

/--
**EH contrapositive (proved).**  Extinction of all positive stack certificates and
compositivity contradict `CompositeMidpointHasSurvivor`.
-/
theorem eckmann_hilton_extinction_contradicts_goldbach {N : ℕ} (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    (h : CompositeMidpointHasSurvivor N) : False :=
  eh_extinction_contradicts_composite hc hall h

/-! ## 6. EH assembly (proved pipeline) -/

/--
**EH assembly (proved).**  Stack extinction at a composite midpoint leaves no dual survivor.
-/
theorem eckmann_hilton_assembly_no_survivor {N : ℕ} (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ¬ MidpointSieveSurvivorExists N :=
  eh_extinction_and_composite_no_survivor hc hall

/--
**EH assembly (proved).**  Under extinction, every off-diagonal prime slot carries an explicit
reflect crossing from the finite abelian stack.
-/
theorem eckmann_hilton_extinction_forces_reflect_crossings {N : ℕ} (hN : 2 ≤ N) (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g)
    {p : ℕ} (hp : p ∈ offDiagonalPrimeScanSlots N) :
    ∃ r ∈ finiteSoeAngleStack N, reflectResidueCrossed N r p :=
  eh_extinction_no_survivor_forces_reflect_cross hN hc
    (eckmann_hilton_assembly_no_survivor hc hall) hall hp

/--
**EH contrapositive packaged.**  Forward collapse contradicts extinction.
-/
theorem eckmann_hilton_forward_contradicts_extinction {N : ℕ} (hc : ¬ Nat.Prime N)
    (hFwd : EckmannHiltonForwardCollapse N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) : False :=
  hFwd hc hall

/-! ## 6bis. EH cardinality + pigeonhole (proved) -/

theorem eh_stack_card_lt_off_diagonal_primes {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N) :
    Finset.card (finiteSoeAngleStack N) < Finset.card (offDiagonalPrimeScanSlots N) :=
  composite_offDiagonal_primes_gt_stack_card hN hc

theorem eckmann_hilton_extinction_reflect_cross_pigeonhole {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ p q, p ∈ offDiagonalPrimeScanSlots N ∧ q ∈ offDiagonalPrimeScanSlots N ∧ p ≠ q ∧
      ∃ r ∈ finiteSoeAngleStack N,
        reflectResidueCrossed N r p ∧ reflectResidueCrossed N r q :=
  composite_eh_extinction_reflect_cross_pigeonhole hN hc
    (eckmann_hilton_assembly_no_survivor hc hall) hall

theorem eckmann_hilton_forward_of_cardinality_obstruction {N : ℕ} (hN : 4 ≤ N)
    (hOb : EckmannHiltonCardinalityObstruction N) : EckmannHiltonSoeDischarge N :=
  (eckmann_hilton_discharge_iff_eh_forward N).mpr
    (eckmann_hilton_forward_collapse_of_cardinality_obstruction hN hOb)

/-!
**EH cardinality profile (open).**  Once `EckmannHiltonCardinalityObstruction N` holds, forward
collapse / Goldbach decode follows from the proved pigeonhole pipeline.
-/
def EckmannHiltonCardinalityProfile (N : ℕ) : Prop :=
  EckmannHiltonCardinalityObstruction N

theorem eckmann_hilton_discharge_of_cardinality_profile {N : ℕ} (hN : 4 ≤ N)
    (hProf : EckmannHiltonCardinalityProfile N) : EckmannHiltonSoeDischarge N :=
  eckmann_hilton_forward_of_cardinality_obstruction hN hProf

/-! ## 6ter. Inverse-Pythagorean gap + duplicate reflect (Layer 1 proved) -/

theorem eh_midpoint_gap_ng_square_iff_inverse_pythagorean {N g : ℕ} (hg : g ≤ N) :
    MidpointGapNgSquare N g ↔ InversePythagoreanMidpointGap N g :=
  ng_square_iff_diff_square hg

theorem eh_inverse_pythagorean_param_forward {m n : ℕ} (hmn : n ≤ m) :
    InversePythagoreanMidpointGap (m * m) (n * n) :=
  inverse_pythagorean_param_forward hmn

theorem eh_composite_extinction_reflect_duplicate {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ _c : ReflectDuplicateCrossing N, True :=
  composite_extinction_reflect_duplicate hN hc
    (eckmann_hilton_assembly_no_survivor hc hall) hall

theorem eh_inverse_triple_obstruction_implies_cardinality {N : ℕ}
    (hOb : EckmannHiltonInverseTripleObstruction N) :
    EckmannHiltonCardinalityObstruction N :=
  inverse_triple_obstruction_implies_cardinality hOb

theorem eckmann_hilton_forward_of_inverse_triple_obstruction {N : ℕ} (hN : 4 ≤ N)
    (hOb : EckmannHiltonInverseTripleObstruction N) : EckmannHiltonSoeDischarge N :=
  eckmann_hilton_forward_of_cardinality_obstruction hN
    (inverse_triple_obstruction_implies_cardinality hOb)

def EckmannHiltonInverseTripleProfile (N : ℕ) : Prop :=
  EckmannHiltonInverseTripleObstruction N

theorem eckmann_hilton_discharge_of_inverse_triple_profile {N : ℕ} (hN : 4 ≤ N)
    (hProf : EckmannHiltonInverseTripleProfile N) : EckmannHiltonSoeDischarge N :=
  eckmann_hilton_forward_of_inverse_triple_obstruction hN hProf

/-!
**EH inverse-triple profile (open).**  Duplicate reflect ⇒ symmetric prime gap on the
`N · g = □` locus; this subsumes the cardinality obstruction and yields forward collapse.

**SO(4)/Δ orbit obstruction (open).**  Duplicate reflect is orbit collision; closing
`SO4DeltaOrbitObstruction` yields EH cardinality — see `S3MidpointSO4DeltaOrbit`.
-/

theorem eh_composite_extinction_so4_collision {N : ℕ} (hN : 4 ≤ N) (hc : ¬ Nat.Prime N)
    (hall : ∀ g ∈ midpointGapOrbit N, 0 < g → ¬ gapSurvivesFiniteAngleStack N g) :
    ∃ _c : SO4GapOrbitCollision N, True :=
  composite_extinction_so4_collision hN hc
    (eckmann_hilton_assembly_no_survivor hc hall) hall

theorem eh_so4_delta_orbit_implies_cardinality {N : ℕ}
    (hOb : SO4DeltaOrbitObstruction N) :
    EckmannHiltonCardinalityObstruction N :=
  so4_delta_orbit_obstruction_implies_cardinality hOb

theorem eh_eckmann_hilton_forward_of_so4_delta_orbit {N : ℕ} (hN : 4 ≤ N)
    (hOb : SO4DeltaOrbitObstruction N) : EckmannHiltonSoeDischarge N :=
  eckmann_hilton_forward_of_cardinality_obstruction hN
    (eh_so4_delta_orbit_implies_cardinality hOb)

def EckmannHiltonSO4DeltaProfile (N : ℕ) : Prop :=
  SO4DeltaOrbitObstruction N

/-! ## 7. EH profile (unconditional inputs) -/

structure EckmannHiltonSoeProfile (N : ℕ) (s : ℂ) (hs : 0 < s.re) where
  spectral_build : ConstructiveSpectralSoeBuild N s hs
  forward_reflect_interchange : ∀ r p, dualModLineClear N r p ↔
    (¬ reflectResidueCrossed N r p ∧ ¬ forwardResidueCrossed r p)
  stack_commute : ∀ g r s, r ∈ finiteSoeAngleStack N → s ∈ finiteSoeAngleStack N →
    ((dualModLineClear N r (N - g) ∧ dualModLineClear N s (N - g)) ↔
      (dualModLineClear N s (N - g) ∧ dualModLineClear N r (N - g)))
  mirror_unit : symmetricPrimeReflectionAt N N ↔ Nat.Prime N
  composite_no_unit : ¬ Nat.Prime N → ¬ symmetricPrimeReflectionAt N N
  spectral_mul : ∀ p q, so4SpectralLine (p * q) s = so4SpectralLine p s * so4SpectralLine q s

theorem eckmann_hilton_soe_profile (N : ℕ) (s : ℂ) (hN : 2 ≤ N) (hs : 0 < s.re)
    (hc : ¬ Nat.Prime N) : EckmannHiltonSoeProfile N s hs where
  spectral_build := constructive_spectral_soe_build N s hN hs hc
  forward_reflect_interchange := fun r p => eh_forward_reflect_interchange N r p
  stack_commute := fun g r s hr hs => eh_stack_certificate_commute N g r s hr hs
  mirror_unit := eh_mirror_unit_iff_prime N
  composite_no_unit := fun hc => eh_composite_misses_unit N hc
  spectral_mul := fun p q => eh_spectral_joint_mul p q s

/-! ## 8. Examples (EH discharge) -/

theorem eckmann_hilton_discharge_four : EckmannHiltonSoeDischarge 4 :=
  eckmann_hilton_collapse_of_composite_survivor composite_midpoint_has_survivor_four

theorem eckmann_hilton_discharge_eight : EckmannHiltonSoeDischarge 8 :=
  eckmann_hilton_collapse_of_composite_survivor composite_midpoint_has_survivor_eight

theorem eckmann_hilton_discharge_fifteen : EckmannHiltonSoeDischarge 15 :=
  eckmann_hilton_collapse_of_composite_survivor composite_midpoint_has_survivor_fifteen

theorem constructive_spectral_forces_four_eh :
    ConstructiveSpectralForcesSlopeHit 4 := eckmann_hilton_discharge_four

theorem constructive_spectral_forces_eight_eh :
    ConstructiveSpectralForcesSlopeHit 8 := eckmann_hilton_discharge_eight

theorem constructive_spectral_forces_fifteen_eh :
    ConstructiveSpectralForcesSlopeHit 15 := eckmann_hilton_discharge_fifteen

end

end Hqiv.Story
