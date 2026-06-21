import Hqiv.Geometry.GoldbachG2Parity
import Hqiv.Geometry.ScaleOrbitMulMod
import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3DeltaHarmonicDischargeBridge
import Hqiv.Story.S3DeltaHolonomyMulModAnchorBridge
import Hqiv.Story.S3HarmonicMulModHolonomy
import Hqiv.Story.S3HopfMulModTransport

/-!
# SO(4) Δ-plaquette Lie promotion → harmonic mul-mod transport

The **Lie side is unconditional** on every shell:

* seed plaquette commutator `[J₀₁, J₁₃] = Δ₄`;
* harmonic real multiplier `6/5` from the Δ carrier;
* phase-lift Δ ∈ `G₂ ∪ {Δ}`.

The **arithmetic promotion** (coprime mul-mod sweep) is available on shell `n`
**iff** the harmonic cascade is coprime:

`HarmonicMulModMultiplierCoprimeObstruction n`.

That is the exact gate — not membership in the six certified witness shells.
Those shells are corollaries only.  The cascade still fails at `n = 770`; a fully
universal `∀ n, promotion` statement is therefore false without extending the
cascade or proving a global coprimality lemma.

## Geometric hook

Given any `LockedG2TangentLanding n`, a promotion yields `LockedScaleOrbit`.
Every `MidpointHarmonicMulModBundle` already carries coprimality, hence Lie
promotion + Hopf transport with no certified-shell hypothesis.
-/

namespace Hqiv.Story

open Hqiv.Geometry Hqiv.Algebra

noncomputable section

/-! ## Availability gate -/

/-- Lie promotion on shell `n` ⇔ harmonic cascade coprimality. -/
def SO4LiePromotionAvailable (n : ℕ) : Prop :=
  HarmonicMulModMultiplierCoprimeObstruction n

@[simp] theorem so4_lie_promotion_available_iff (n : ℕ) :
    SO4LiePromotionAvailable n ↔
      Nat.Coprime (harmonicOrbitMulModMultiplier n) n := by
  rfl

def MidpointLiePromotionAvailable (N : ℕ) : Prop :=
  SO4LiePromotionAvailable (2 * N)

/--
**Global target (open).**  Coprimality for every positive shell; false for the
present `{6,5,11,7}` cascade at `n = 770`.
-/
def GlobalHarmonicLiePromotion : Prop :=
  ∀ n, 0 < n → HarmonicMulModMultiplierCoprimeObstruction n

/-! ## Discrete Lie transport index on the shell chart -/

/--
**SO(4) shell transport index.**  The finite readout of Δ-plaquette holonomy on
the `n`-slot circle; on the promotion route this equals coprime mul-mod.
-/
def so4LieTransportIndex (n m x : ℕ) : ℕ :=
  scaleOrbitMulMod n m x

@[simp] theorem so4_lie_transport_index_eq_mul_mod (n m x : ℕ) :
    so4LieTransportIndex n m x = scaleOrbitMulMod n m x :=
  rfl

theorem so4_lie_transport_index_zero (n m : ℕ) :
    so4LieTransportIndex n m 0 = 0 := by
  simp [so4LieTransportIndex, scaleOrbitMulMod_zero]

/-! ## SO(4) Δ-plaquette promotion certificate -/

/--
**Lie promotion.**  The SO(4) Δ holonomy pack, plaquette commutator, harmonic
multiplier lock, and coprime mul-mod sweep on shell `n`.
-/
structure SO4DeltaMulModLiePromotion (n m : ℕ) where
  holonomy : SO4PhaseDeltaHolonomyPack
  plaquette_commutator_eq_delta :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      so4DeltaGenerator
  multiplier_from_harmonic : m = harmonicOrbitMulModMultiplier n
  sweep : MulModScaleOrbitSweep n m
  hits :
    ∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ so4LieTransportIndex n m x = k

namespace SO4DeltaMulModLiePromotion

variable {n m : ℕ}

theorem multiplier_coprime (P : SO4DeltaMulModLiePromotion n m) :
    Nat.Coprime m n :=
  P.sweep.coprime

theorem multiplier_obstruction (P : SO4DeltaMulModLiePromotion n m) :
    HarmonicMulModMultiplierCoprimeObstruction n := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction]
  rw [← P.multiplier_from_harmonic]
  exact P.multiplier_coprime

theorem transport_eq_mul_mod (_P : SO4DeltaMulModLiePromotion n m) (x : ℕ) :
    so4LieTransportIndex n m x = scaleOrbitMulMod n m x :=
  so4_lie_transport_index_eq_mul_mod n m x

theorem hits_via_mul_mod (P : SO4DeltaMulModLiePromotion n m) {k : ℕ}
    (hk₀ : 0 < k) (hk : k < n) :
    ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k := by
  obtain ⟨x, hxlt, heq⟩ := P.hits k hk₀ hk
  exact ⟨x, hxlt, by simpa [so4_lie_transport_index_eq_mul_mod] using heq⟩

end SO4DeltaMulModLiePromotion

/-! ## G₂ / Δ citation layer -/

structure G2DeltaMulModLiePromotion (n m : ℕ) extends SO4DeltaMulModLiePromotion n m where
  phase_lift_in_g2 : Hqiv.phaseLiftDelta ∈ G2UnionDelta
  harmonic_real : harmonicEvenOrbitMultiplier = 6 / 5

/-! ## General constructors (no certified-shell hypothesis) -/

/--
**General Lie promotion.**  Coprimality is the only arithmetic input beyond
`0 < n`; the plaquette and harmonic data are shell-independent.
-/
noncomputable def so4LiePromotion_of_coprime (n : ℕ) (hn : 0 < n)
    (hcop : HarmonicMulModMultiplierCoprimeObstruction n) :
    SO4DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n) where
  holonomy := so4_phase_delta_holonomy_pack_default
  plaquette_commutator_eq_delta := so4_seed_commutator_eq_so4_delta_generator
  multiplier_from_harmonic := rfl
  sweep := harmonic_mul_mod_sweep_of_coprime n hn hcop
  hits := fun k hk₀ hk =>
    harmonic_mul_mod_sweep_of_coprime_hits n hn hcop hk₀ hk

noncomputable def g2LiePromotion_of_coprime (n : ℕ) (hn : 0 < n)
    (hcop : HarmonicMulModMultiplierCoprimeObstruction n) :
    G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n) where
  toSO4DeltaMulModLiePromotion := so4LiePromotion_of_coprime n hn hcop
  phase_lift_in_g2 := phase_lift_delta_mem_g2_union
  harmonic_real := harmonicEvenOrbitMultiplier_eq_six_fifths

theorem so4_lie_promotion_exists_iff_coprime (n : ℕ) (hn : 0 < n) :
    Nonempty (SO4DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n)) ↔
      HarmonicMulModMultiplierCoprimeObstruction n :=
  ⟨fun ⟨P⟩ => P.multiplier_obstruction, fun hcop => ⟨so4LiePromotion_of_coprime n hn hcop⟩⟩

theorem g2_lie_promotion_exists_iff_coprime (n : ℕ) (hn : 0 < n) :
    Nonempty (G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n)) ↔
      HarmonicMulModMultiplierCoprimeObstruction n :=
  ⟨fun ⟨P⟩ => P.toSO4DeltaMulModLiePromotion.multiplier_obstruction,
    fun hcop => ⟨g2LiePromotion_of_coprime n hn hcop⟩⟩

theorem midpoint_bundle_coprime_obstruction {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    HarmonicMulModMultiplierCoprimeObstruction B.shell := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction]
  rw [← B.multiplier_eq]
  exact B.coprime

noncomputable def harmonic_midpoint_bundle_gives_lie_promotion {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    SO4DeltaMulModLiePromotion B.shell B.multiplier :=
  { holonomy := so4_phase_delta_holonomy_pack_default
    plaquette_commutator_eq_delta := so4_seed_commutator_eq_so4_delta_generator
    multiplier_from_harmonic := by rw [B.multiplier_eq]
    sweep := B.sweep
    hits := fun k hk₀ hk => by
      obtain ⟨x, hxlt, heq⟩ := mulModScaleOrbitSweep_hits B.sweep hk₀ hk
      exact ⟨x, hxlt, by simpa [so4_lie_transport_index_eq_mul_mod] using heq⟩ }

noncomputable def g2LiePromotion_of_bundle {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    G2DeltaMulModLiePromotion B.shell B.multiplier where
  toSO4DeltaMulModLiePromotion := harmonic_midpoint_bundle_gives_lie_promotion B
  phase_lift_in_g2 := phase_lift_delta_mem_g2_union
  harmonic_real := harmonicEvenOrbitMultiplier_eq_six_fifths

theorem every_harmonic_midpoint_bundle_has_lie_promotion {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    HarmonicMulModMultiplierCoprimeObstruction B.shell ∧
      Nonempty (SO4DeltaMulModLiePromotion B.shell B.multiplier) ∧
      Nonempty (G2DeltaMulModLiePromotion B.shell B.multiplier) := by
  have hcop := midpoint_bundle_coprime_obstruction B
  refine ⟨hcop, ⟨harmonic_midpoint_bundle_gives_lie_promotion B⟩, ⟨g2LiePromotion_of_bundle B⟩⟩

/-! ## Midpoint + Hopf packaging (general) -/

/--
Midpoint-level promotion from any harmonic bundle — no certified-shell list.
-/
structure MidpointSO4LiePromotion (N p q : ℕ) where
  bundle : MidpointHarmonicMulModBundle N p q

namespace MidpointSO4LiePromotion

variable {N p q : ℕ}

noncomputable def ofBundle (B : MidpointHarmonicMulModBundle N p q) :
    MidpointSO4LiePromotion N p q :=
  ⟨B⟩

noncomputable def promotion (P : MidpointSO4LiePromotion N p q) :
    SO4DeltaMulModLiePromotion P.bundle.shell P.bundle.multiplier :=
  harmonic_midpoint_bundle_gives_lie_promotion P.bundle

noncomputable def g2Promotion (P : MidpointSO4LiePromotion N p q) :
    G2DeltaMulModLiePromotion P.bundle.shell P.bundle.multiplier :=
  g2LiePromotion_of_bundle P.bundle

noncomputable def hopf (P : MidpointSO4LiePromotion N p q) :
    HopfMulModTransport N P.bundle.multiplier :=
  harmonic_midpoint_bundle_gives_hopf_transport P.bundle

theorem shell_eq_midpoint (P : MidpointSO4LiePromotion N p q) :
    P.bundle.shell = midpointShell N :=
  P.bundle.shell_eq

theorem coprime_obstruction (P : MidpointSO4LiePromotion N p q) :
    HarmonicMulModMultiplierCoprimeObstruction P.bundle.shell :=
  midpoint_bundle_coprime_obstruction P.bundle

end MidpointSO4LiePromotion

/-! ## Certified shells (corollaries only) -/

noncomputable def so4LiePromotionCertified (n : ℕ) (h : n ∈ certifiedGoldbachShells) :
    SO4DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n) :=
  so4LiePromotion_of_coprime n
    (by
      rcases mem_certifiedGoldbachShells_iff n |>.mp h with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (harmonic_multiplier_coprime_certified n h)

noncomputable def g2LiePromotionCertified (n : ℕ) (h : n ∈ certifiedGoldbachShells) :
    G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n) :=
  g2LiePromotion_of_coprime n
    (by
      rcases mem_certifiedGoldbachShells_iff n |>.mp h with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (harmonic_multiplier_coprime_certified n h)

noncomputable def midpointLiePromotion_four :
    MidpointSO4LiePromotion 4 3 5 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_four

noncomputable def midpointLiePromotion_six :
    MidpointSO4LiePromotion 6 5 7 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_six

noncomputable def midpointLiePromotion_eight :
    MidpointSO4LiePromotion 8 5 11 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_eight

noncomputable def midpointLiePromotion_nine :
    MidpointSO4LiePromotion 9 7 11 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_nine

noncomputable def midpointLiePromotion_ten :
    MidpointSO4LiePromotion 10 3 17 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_ten

noncomputable def midpointLiePromotion_fifteen :
    MidpointSO4LiePromotion 15 7 23 :=
  MidpointSO4LiePromotion.ofBundle harmonicMulModBundle_fifteen

theorem midpoint_lie_promotion_certified_small_composites :
    Nonempty (MidpointSO4LiePromotion 4 3 5) ∧
      Nonempty (MidpointSO4LiePromotion 6 5 7) ∧
      Nonempty (MidpointSO4LiePromotion 8 5 11) ∧
      Nonempty (MidpointSO4LiePromotion 9 7 11) ∧
      Nonempty (MidpointSO4LiePromotion 10 3 17) ∧
      Nonempty (MidpointSO4LiePromotion 15 7 23) := by
  refine ⟨⟨midpointLiePromotion_four⟩, ⟨midpointLiePromotion_six⟩, ⟨midpointLiePromotion_eight⟩,
    ⟨midpointLiePromotion_nine⟩, ⟨midpointLiePromotion_ten⟩, ⟨midpointLiePromotion_fifteen⟩⟩

/-! ## Locked scale orbit from promotion -/

noncomputable def lockedScaleOrbit_of_mul_mod_promotion
    {n : ℕ} (L : LockedG2TangentLanding n) (hn : 0 < n)
    (_P : SO4DeltaMulModLiePromotion n m) :
    LockedScaleOrbit L where
  lock_axis := L.locked.qsharp_pole_lock.pole
  axis_is_pole := rfl
  holonomy_certificate := delta_g2_holonomy_pole_certificate_of_locked hn L.locked
  scale_parameter := fun k => (k : ℝ)
  integer_positions := fun k _hk₀ hk =>
    ⟨rfl, scaleOrbitMulMod_complementary_sum n k (Nat.le_of_lt hk)⟩
  symmetric_return := fun _k hk₀ hk =>
    (scaleOrbitMulMod_bilateral_complement hk₀ hk).2

theorem mul_mod_lie_promotion_gives_locked_scale_orbit
    {n : ℕ} (L : LockedG2TangentLanding n) (hn : 0 < n)
    (P : SO4DeltaMulModLiePromotion n m) :
    Nonempty (LockedScaleOrbit L) :=
  ⟨lockedScaleOrbit_of_mul_mod_promotion L hn P⟩

/-! ## Carrier master certificates (general) -/

theorem delta_carrier_lie_promotion_of_coprime
    (_C : DeltaHarmonicUnconditionalCarrier) {n : ℕ} (hn : 0 < n)
    (hcop : HarmonicMulModMultiplierCoprimeObstruction n) :
    Nonempty (G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n)) :=
  ⟨g2LiePromotion_of_coprime n hn hcop⟩

theorem delta_carrier_harmonic_multiplier (_C : DeltaHarmonicUnconditionalCarrier) :
    harmonicEvenOrbitMultiplier = 6 / 5 :=
  harmonicEvenOrbitMultiplier_eq_six_fifths

theorem delta_carrier_lie_promotion_on_midpoint_bundle
    (_C : DeltaHarmonicUnconditionalCarrier) {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    HarmonicMulModMultiplierCoprimeObstruction B.shell ∧
      Nonempty (MidpointSO4LiePromotion N p q) := by
  rcases every_harmonic_midpoint_bundle_has_lie_promotion B with ⟨hcop, _, _⟩
  exact ⟨hcop, ⟨MidpointSO4LiePromotion.ofBundle B⟩⟩

theorem delta_carrier_lie_promotion_iff_coprime
    (_C : DeltaHarmonicUnconditionalCarrier) {n : ℕ} (hn : 0 < n) :
    Nonempty (G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n)) ↔
      HarmonicMulModMultiplierCoprimeObstruction n :=
  g2_lie_promotion_exists_iff_coprime n hn

theorem delta_carrier_certified_shell_lie_promotions
    (_C : DeltaHarmonicUnconditionalCarrier) :
    ∀ n ∈ certifiedGoldbachShells,
      Nonempty (G2DeltaMulModLiePromotion n (harmonicOrbitMulModMultiplier n)) ∧
        HarmonicMulModMultiplierCoprimeObstruction n := by
  intro n h
  exact ⟨⟨g2LiePromotionCertified n h⟩, harmonic_multiplier_coprime_certified n h⟩

theorem so4_harmonic_multiplier_locked_at_anchor :
    harmonicEvenOrbitMultiplier = 6 / 5 ∧
      harmonicOrbitMulModMultiplier 8 = 5 ∧
      harmonicOrbitMulModMultiplier 12 = 5 :=
  ⟨harmonic_orbit_multiplier_is_six_fifths,
    harmonic_orbit_mul_mod_multiplier_eight_eq_five,
    harmonic_orbit_mul_mod_multiplier_twelve_eq_five⟩

theorem delta_anchor_lie_promotion_certificate :
    Nonempty DeltaHolonomyMulModAnchorPack ∧
      HarmonicMulModMultiplierCoprimeObstruction 8 ∧
      Nonempty (SO4DeltaMulModLiePromotion 8 5) ∧
      Nonempty (G2DeltaMulModLiePromotion 8 (harmonicOrbitMulModMultiplier 8)) ∧
      Nonempty (MidpointSO4LiePromotion 4 3 5) ∧
      (harmonicEvenOrbitMultiplier = 6 / 5) ∧
      harmonicOrbitMulModMultiplier 8 = 5 := by
  have hcop8 : HarmonicMulModMultiplierCoprimeObstruction 8 := by
    dsimp [HarmonicMulModMultiplierCoprimeObstruction]
    exact coprime_five_eight
  refine ⟨delta_holonomy_mul_mod_anchor_pack_exists, hcop8, ?_, ?_, ⟨midpointLiePromotion_four⟩, ?_, ?_⟩
  · exact ⟨so4LiePromotion_of_coprime 8 (by decide) hcop8⟩
  · exact ⟨g2LiePromotion_of_coprime 8 (by decide) hcop8⟩
  · exact harmonic_orbit_multiplier_is_six_fifths
  · exact harmonic_orbit_mul_mod_multiplier_eight_eq_five

/-!
## Status

| Statement | Scope |
|-----------|-------|
| `so4LiePromotion_of_coprime` | **General:** any `n` with `0 < n` and coprimality |
| `every_harmonic_midpoint_bundle_has_lie_promotion` | **General:** any harmonic bundle |
| `delta_carrier_lie_promotion_iff_coprime` | **General:** promotion ⇔ obstruction |
| `GlobalHarmonicLiePromotion` | **Open:** fails at `n = 770` for present cascade |
| Certified shell defs | Witness corollaries only |

Global `DeltaHolonomyScaleOrbitCapturesIntegers` still needs
`LockedG2TangentLanding` for each shell — promotion discharges the orbit once a
landing and coprimality are both in hand.
-/

end

end Hqiv.Story
