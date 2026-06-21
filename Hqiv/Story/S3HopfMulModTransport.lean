import Hqiv.Geometry.ScaleOrbitMulMod
import Hqiv.Geometry.SoeModStackCombinatorics
import Hqiv.Story.S3GoldbachAnnulusCircle
import Hqiv.Story.S3HarmonicMulModHolonomy
import Hqiv.Story.S3HarmonicShellZeroCounting
import Hqiv.Topology.HopfShellComplex

/-!
# Hopf annulus ↔ coprime mul-mod transport

Unifies the **Goldbach Hopf circle** (`2N` slots, twiddle axis `N`) with the
**arithmetic holonomy** layer (`scaleOrbitMulMod`, `MulModScaleOrbitSweep`).

## Shared structure (proved here)

| Hopf / annulus | Mul-mod |
|----------------|---------|
| Circumference `goldbachAnnulusCircumference N = 2N` | Shell `midpointShell N` |
| Slot `p` at angle `2πp/(2N)` | Index `p < 2N` |
| Twiddle axis `N` (angle `π`) | Half-turn slot |
| Partner complement `p + q = 2N` | `k + (2N − k) = 2N` |
| Mod-stack quotient `r ∈ finiteSoeAngleStack N` | `scaleOrbitMulMod` descends mod `r` |
| Nested `HopfShell` winding `1,2,3` | Finite chart layers before global sweep |

## Status

| Layer | Content |
|-------|---------|
| **Proved** | Shell identification, `HopfMulModTransport`, slot bijection, angle readout |
| **Proved** | Nested quotient descent, certified harmonic bundles |
| **Proved** | Lie promotion on certified shells (`S3MulModSO4LiePromotion`) |
| **Open** | Global `HarmonicMulModMultiplierCoprimeObstruction`, prime slot selection |
| **Open** | Global `LockedG2TangentLandingExists` for all even shells |
-/

namespace Hqiv.Story

open Hqiv.Geometry Hqiv.Topology Real

noncomputable section

/-! ## Shell identification -/

theorem hopf_annulus_eq_midpoint_shell (N : ℕ) :
    goldbachAnnulusCircumference N = midpointShell N := by
  dsimp [goldbachAnnulusCircumference, midpointShell]

theorem hopf_twiddle_axis_eq_half_circumference (N : ℕ) :
    goldbachTwiddleAxis N * 2 = goldbachAnnulusCircumference N := by
  dsimp [goldbachTwiddleAxis, goldbachAnnulusCircumference]
  omega

/-! ## Hopf mul-mod transport certificate -/

/--
**Unified transport.**  Coprime mul-mod on the `2N`-slot Hopf annulus: the
multiplier permutes slot indices and sweeps every position below the shell.
-/
structure HopfMulModTransport (N m : ℕ) where
  axis : ℕ
  axis_eq : axis = N
  circumference : ℕ
  circumference_eq : circumference = goldbachAnnulusCircumference N
  pos : 0 < circumference
  multiplier : ℕ
  multiplier_eq : multiplier = m
  coprime : Nat.Coprime multiplier circumference
  sweep : MulModScaleOrbitSweep circumference multiplier

namespace HopfMulModTransport

variable {N m : ℕ}

theorem circumference_eq_midpoint_shell (T : HopfMulModTransport N m) :
    T.circumference = midpointShell N := by
  rw [T.circumference_eq, hopf_annulus_eq_midpoint_shell]

theorem axis_lt_circumference (T : HopfMulModTransport N m) (hN : 0 < N) :
    T.axis < T.circumference := by
  rw [T.axis_eq, T.circumference_eq]
  exact goldbach_twiddle_axis_lt_circumference hN

noncomputable def ofMulModSweep (N : ℕ) (m : ℕ) (hn : 0 < N)
    (hcop : Nat.Coprime m (goldbachAnnulusCircumference N)) :
    HopfMulModTransport N m where
  axis := N
  axis_eq := rfl
  circumference := goldbachAnnulusCircumference N
  circumference_eq := rfl
  pos := goldbach_shell_depth_pos hn
  multiplier := m
  multiplier_eq := rfl
  coprime := hcop
  sweep := mulModScaleOrbitSweep (goldbachAnnulusCircumference N) m
    (goldbach_shell_depth_pos hn) hcop

end HopfMulModTransport

/-! ## Slot index ↔ Hopf angle ↔ mul-mod step -/

theorem hopf_slot_angle_eq (N p : ℕ) (hN : 0 < N) (hp : p < goldbachAnnulusCircumference N) :
    goldbachLeftArmAngle N p hN hp =
      shellSweepAngle (goldbach_shell_depth_pos hN) ⟨p, hp⟩ := by
  unfold goldbachLeftArmAngle goldbachAnnulusCircumference
  simp [shellSweepAngle]

theorem hopf_mul_mod_slot_angle (N m : ℕ) (hN : 0 < N) (hcop : Nat.Coprime m (2 * N))
    (k : Fin (2 * N)) :
    shellSweepAngle (goldbach_shell_depth_pos hN) (mulModSlot (2 * N) m (by omega) hcop k) =
      2 * Real.pi * (scaleOrbitMulMod (2 * N) m k.val : ℝ) / (2 * N) := by
  dsimp [shellSweepAngle, mulModSlot, scaleOrbitMulMod, goldbachAnnulusCircumference]
  push_cast
  ring

private theorem hopf_mul_mod_slot_injective (N m : ℕ) (hN : 0 < N)
    (hcop : Nat.Coprime m (2 * N)) :
    Function.Injective (mulModSlot (2 * N) m (by omega) hcop) := by
  intro a b hab
  apply Fin.ext
  have hval : scaleOrbitMulMod (2 * N) m a.val = scaleOrbitMulMod (2 * N) m b.val := by
    simpa [mulModSlot] using congrArg Fin.val hab
  have hn : 0 < 2 * N := by omega
  haveI : NeZero (2 * N) := ⟨by omega⟩
  have hb := scaleOrbitMulMod_bijective hn hcop
  have hz : (a.val : ZMod (2 * N)) = (b.val : ZMod (2 * N)) := by
    have hmul :
        (m : ZMod (2 * N)) * (a.val : ZMod (2 * N)) =
          (m : ZMod (2 * N)) * (b.val : ZMod (2 * N)) := by
      rw [← scaleOrbitMulMod_zmod (2 * N) m a.val hn,
        ← scaleOrbitMulMod_zmod (2 * N) m b.val hn, hval]
    exact hb.1 hmul
  have hnat : a.val = b.val := by
    have hmod : a.val % (2 * N) = b.val % (2 * N) :=
      (ZMod.natCast_eq_natCast_iff' a.val b.val (2 * N)).1 hz
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact hmod
  exact hnat

private theorem hopf_mul_mod_slot_surjective (N m : ℕ) (hN : 0 < N)
    (hcop : Nat.Coprime m (2 * N)) :
    Function.Surjective (mulModSlot (2 * N) m (by omega) hcop) := by
  intro k
  have hn : 0 < 2 * N := by omega
  by_cases hk0 : k.val = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    ext
    simp [mulModSlot, scaleOrbitMulMod_zero, hk0]
  · have hkpos : 0 < k.val := by omega
    obtain ⟨x, hxlt, heq⟩ :=
      scaleOrbitMulMod_hits_position (k := k.val) hn hcop hkpos k.isLt
    exact ⟨⟨x, hxlt⟩, Fin.ext heq⟩

theorem hopf_mul_mod_slot_bijective (N m : ℕ) (hN : 0 < N) (hcop : Nat.Coprime m (2 * N)) :
    Function.Bijective (mulModSlot (2 * N) m (by omega) hcop) :=
  ⟨hopf_mul_mod_slot_injective N m hN hcop, hopf_mul_mod_slot_surjective N m hN hcop⟩

theorem hopf_mul_mod_sweeps_all_slots (T : HopfMulModTransport N m) {k : ℕ}
    (hk₀ : 0 < k) (hk : k < T.circumference) :
    ∃ x : ℕ, x < T.circumference ∧ scaleOrbitMulMod T.circumference T.multiplier x = k :=
  T.sweep.hits k hk₀ hk

/-! ## Bilateral complement (static annulus geometry) -/

theorem hopf_transport_bilateral_complement (T : HopfMulModTransport N m) {k : ℕ}
    (hk₀ : 0 < k) (hk : k < T.circumference) :
    k + (T.circumference - k) = T.circumference :=
  mulModScaleOrbitSweep_bilateral T.sweep hk₀ hk

theorem hopf_partner_arms_sum_to_circumference {N p q : ℕ} (h : GoldbachMidpointPair N p q) :
    goldbachAnnulusCircumference N = p + q := by
  dsimp [goldbachAnnulusCircumference]
  exact (h.right.right.right.right).symm

/-! ## Nested mod-stack quotients (Hopf sub-charts) -/

/--
A **nested chart layer**: mul-mod on the full `2N` circle restricts to mul-mod on
a stack modulus `r` when `r` divides the shell (CRT chart factor).
-/
structure NestedHopfMulModLayer (N r : ℕ) where
  mem_stack : r ∈ finiteSoeAngleStack N
  divides_shell : r ∣ goldbachAnnulusCircumference N

theorem hopf_mul_mod_descends_to_stack (N m x : ℕ) (r : ℕ)
    (L : NestedHopfMulModLayer N r) :
    scaleOrbitMulMod (goldbachAnnulusCircumference N) m x % r =
      scaleOrbitMulMod r (m % r) (x % r) :=
  scaleOrbitMulMod_respects_quotient (hr := L.divides_shell)

theorem nested_hopf_mul_mod_layer_fifteen (r : ℕ)
    (hr : r ∈ ({2, 3, 5} : Finset ℕ)) (hdiv : r ∣ 30) :
    NestedHopfMulModLayer 15 r :=
  { mem_stack := by
      rw [finiteSoeAngleStack_fifteen]
      exact hr
    divides_shell := by simpa [goldbachAnnulusCircumference] using hdiv }

theorem hopf_mul_mod_nested_fifteen_two :
    scaleOrbitMulMod 30 m x % 2 = scaleOrbitMulMod 2 (m % 2) (x % 2) :=
  hopf_mul_mod_descends_to_stack 15 m x 2 (nested_hopf_mul_mod_layer_fifteen 2 (by decide) (by decide))

theorem hopf_mul_mod_nested_fifteen_three :
    scaleOrbitMulMod 30 m x % 3 = scaleOrbitMulMod 3 (m % 3) (x % 3) :=
  hopf_mul_mod_descends_to_stack 15 m x 3 (nested_hopf_mul_mod_layer_fifteen 3 (by decide) (by decide))

theorem hopf_mul_mod_nested_fifteen_five :
    scaleOrbitMulMod 30 m x % 5 = scaleOrbitMulMod 5 (m % 5) (x % 5) :=
  hopf_mul_mod_descends_to_stack 15 m x 5 (nested_hopf_mul_mod_layer_fifteen 5 (by decide) (by decide))

/-! ## Certified harmonic shells -/

noncomputable def hopfMulModTransport_four :
    HopfMulModTransport 4 (harmonicOrbitMulModMultiplier 8) :=
  HopfMulModTransport.ofMulModSweep 4 (harmonicOrbitMulModMultiplier 8)
    (by decide) (harmonic_multiplier_coprime_certified 8 (by decide))

noncomputable def hopfMulModTransport_six :
    HopfMulModTransport 6 (harmonicOrbitMulModMultiplier 12) :=
  HopfMulModTransport.ofMulModSweep 6 (harmonicOrbitMulModMultiplier 12)
    (by decide) (harmonic_multiplier_coprime_certified 12 (by decide))

noncomputable def hopfMulModTransport_eight :
    HopfMulModTransport 8 (harmonicOrbitMulModMultiplier 16) :=
  HopfMulModTransport.ofMulModSweep 8 (harmonicOrbitMulModMultiplier 16)
    (by decide) (harmonic_multiplier_coprime_certified 16 (by decide))

noncomputable def hopfMulModTransport_nine :
    HopfMulModTransport 9 (harmonicOrbitMulModMultiplier 18) :=
  HopfMulModTransport.ofMulModSweep 9 (harmonicOrbitMulModMultiplier 18)
    (by decide) (harmonic_multiplier_coprime_certified 18 (by decide))

noncomputable def hopfMulModTransport_ten :
    HopfMulModTransport 10 (harmonicOrbitMulModMultiplier 20) :=
  HopfMulModTransport.ofMulModSweep 10 (harmonicOrbitMulModMultiplier 20)
    (by decide) (harmonic_multiplier_coprime_certified 20 (by decide))

noncomputable def hopfMulModTransport_fifteen :
    HopfMulModTransport 15 (harmonicOrbitMulModMultiplier 30) :=
  HopfMulModTransport.ofMulModSweep 15 (harmonicOrbitMulModMultiplier 30)
    (by decide) (harmonic_multiplier_coprime_certified 30 (by decide))

theorem hopf_mul_mod_transport_certified_small_composites :
    Nonempty (HopfMulModTransport 4 (harmonicOrbitMulModMultiplier 8)) ∧
      Nonempty (HopfMulModTransport 6 (harmonicOrbitMulModMultiplier 12)) ∧
      Nonempty (HopfMulModTransport 8 (harmonicOrbitMulModMultiplier 16)) ∧
      Nonempty (HopfMulModTransport 9 (harmonicOrbitMulModMultiplier 18)) ∧
      Nonempty (HopfMulModTransport 10 (harmonicOrbitMulModMultiplier 20)) ∧
      Nonempty (HopfMulModTransport 15 (harmonicOrbitMulModMultiplier 30)) := by
  refine ⟨⟨hopfMulModTransport_four⟩, ⟨hopfMulModTransport_six⟩, ⟨hopfMulModTransport_eight⟩,
    ⟨hopfMulModTransport_nine⟩, ⟨hopfMulModTransport_ten⟩, ⟨hopfMulModTransport_fifteen⟩⟩

noncomputable def harmonic_midpoint_bundle_gives_hopf_transport {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    HopfMulModTransport N B.multiplier := by
  rcases B.pair with ⟨hp, _, hle, _, _⟩
  have hN : 0 < N := by
    have : 1 < p := Nat.Prime.one_lt hp
    omega
  have hcop : Nat.Coprime B.multiplier (goldbachAnnulusCircumference N) := by
    rw [goldbachAnnulusCircumference, ← B.shell_eq]
    exact B.coprime
  exact HopfMulModTransport.ofMulModSweep N B.multiplier hN hcop

/-! ## Nested Hopf-shell generation cap (TUFT integrable windings) -/

theorem hopf_shell_integrable_windings :
    ∀ s : HopfShell, s.integrableWinding ↔ s.winding = 1 ∨ s.winding = 2 ∨ s.winding = 3 :=
  HopfShell.integrable_iff_winding_1_2_3

theorem hopf_shell_multiplicity_ladder (s : HopfShell) (h : s.integrable) :
    (s.winding + 1) ^ 2 = sphericalHarmonicDimS3 s.winding :=
  integrable_shell_multiplicity_matches s h
    ((HopfShell.integrable_iff_winding_1_2_3 s).1 h)

/-!
## Status

| Object | Role |
|--------|------|
| `HopfMulModTransport` | Full `2N` annulus + coprime sweep |
| `NestedHopfMulModLayer` | Mod-stack quotient descent |
| `hopf_mul_mod_transport_certified_small_composites` | Six witness midpoints |
| `harmonic_midpoint_bundle_gives_hopf_transport` | Harmonic bundle ⇒ transport |

Global Goldbach discharge still requires prime slot selection on swept positions,
not merely bijective transport.
-/

end

end Hqiv.Story
