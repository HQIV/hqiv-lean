import Hqiv.Story.S3FareyRayInterpolation
import Hqiv.Story.S3ThetaPartitionTwiddleAddress
import Mathlib.Tactic

/-!
# Farey mediant rays land on twiddle partition slots

`S3FareyRayInterpolation` places the Farey mediant on an exact harmonic slot
at shell depth `n₁ + m` and index `k₁ + k₂`.  This module shows how that slot
**lands** on twiddle-factor addresses `(a,b,c)` with product shell `a·b·c`.

## Landing modes

1. **Polar twiddle** `(1,1,N)` — unconditional: every Farey mediant slot is
   exactly the harmonic slot of `(1,1,n₁+m)` at index `k₁+k₂`.
2. **Leg-sum twiddle** `(a,b,c₁+c₂)` when parents share the first two legs
   `(a,b,c₁)` and `(a,b,c₂)` — the mediant shell `a·b·c₁ + a·b·c₂` equals
   `a·b·(c₁+c₂)`, so the same slot index carries the same angle.
3. **Witness** `(2,2,2)` + `(2,2,1)` → `(2,2,3)` at slot `2` on shell `12`.

## Honesty

* Proved: harmonic-slot coincidence (polar and leg-sum); diagonal twiddle tuple
  on leg-sum cells when `a = b`; explicit `(2,2,2)/(2,2,1)` witness.
* Not claimed: every mediant carries a Pythagorean hypotenuse labeling; balance /
  ζ-zeros; leg-sum when parents do not share `(a,b)` legs.
-/

namespace Hqiv.Story

noncomputable section

open Real

/-! ## Harmonic slot from a twiddle address -/

/-- Polar / axis twiddle address with product shell `N`. -/
def polarTwiddleAddress (N : ℕ) : TwiddleFactorAddress :=
  (1, 1, N)

theorem polar_twiddle_shell_depth (N : ℕ) :
    twiddleAddressShellDepth (polarTwiddleAddress N) = N := by
  simp [polarTwiddleAddress, twiddleAddressShellDepth]

theorem polar_twiddle_is_twiddle_tuple (N : ℕ) :
    isTwiddleTuple (polarTwiddleAddress N) := by
  dsimp [polarTwiddleAddress, isTwiddleTuple]
  exact Or.inl rfl

theorem twiddle_address_shell_depth_pos {addr : TwiddleFactorAddress} {k : ℕ}
    (hk : k < twiddleAddressShellDepth addr) : 0 < twiddleAddressShellDepth addr := by
  rcases addr with ⟨a, b, c⟩
  dsimp [twiddleAddressShellDepth] at hk ⊢
  rcases Nat.eq_zero_or_pos (a * b * c) with hzero | hpos
  · simp [hzero] at hk
  · exact hpos

/-- Harmonic-shell slot at index `k` on the product shell of `addr`. -/
noncomputable def harmonicShellSlotOfTwiddle (addr : TwiddleFactorAddress) (k : ℕ)
    (hk : k < twiddleAddressShellDepth addr) : HarmonicShellSlot :=
  ⟨twiddleAddressShellDepth addr, ⟨k, hk⟩⟩

theorem harmonic_shell_slot_of_twiddle_angle (addr : TwiddleFactorAddress) (k : ℕ)
    (hk : k < twiddleAddressShellDepth addr) :
    shellSweepAngle (twiddle_address_shell_depth_pos hk)
      (harmonicShellSlotOfTwiddle addr k hk).2 =
      2 * Real.pi * (k : ℝ) / twiddleAddressShellDepth addr := by
  rfl

/-! ## Farey mediant as a harmonic slot -/

noncomputable def fareyMediantHarmonicSlot {n₁ m : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (k₁ k₂ : ℕ) (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) : HarmonicShellSlot :=
  ⟨fareySumShell n₁ m,
    fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂⟩

theorem harmonic_shell_slot_ext {s t : HarmonicShellSlot} (hdepth : s.1 = t.1)
    (hindex : s.2.val = t.2.val) : s = t := by
  rcases s with ⟨n, k⟩
  rcases t with ⟨m, j⟩
  subst hdepth
  have hfin : k = j := Fin.ext hindex
  subst hfin
  rfl

theorem farey_mediant_harmonic_slot_eq (hn₁ : 0 < n₁) (hm : 0 < m)
    (k₁ k₂ : ℕ) (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    fareyMediantHarmonicSlot hn₁ hm k₁ k₂ hk₁ hk₂ =
      ⟨fareySumShell n₁ m, fareyMediantShellSlot hn₁ hm k₁ k₂ hk₁ hk₂⟩ := by
  rfl

theorem mem_farey_mediant_polar_slot {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    fareyMediantSlotIndex n₁ m k₁ k₂ <
      twiddleAddressShellDepth (polarTwiddleAddress (fareySumShell n₁ m)) := by
  simpa [polarTwiddleAddress, twiddleAddressShellDepth, fareySumShell] using
    mem_farey_mediant_slot hn₁ hm hk₁ hk₂

/-! ## Polar twiddle landing (unconditional) -/

/--
Every Farey mediant ray is the harmonic slot of the polar twiddle address
`(1,1,n₁+m)` at index `k₁+k₂`.
-/
theorem farey_mediant_lands_polar_twiddle {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) :
    fareyMediantHarmonicSlot hn₁ hm k₁ k₂ hk₁ hk₂ =
      harmonicShellSlotOfTwiddle (polarTwiddleAddress (fareySumShell n₁ m))
        (fareyMediantSlotIndex n₁ m k₁ k₂)
        (mem_farey_mediant_polar_slot hn₁ hm hk₁ hk₂) := by
  refine harmonic_shell_slot_ext ?hdepth ?hindex
  · simp [fareyMediantHarmonicSlot, harmonicShellSlotOfTwiddle, polarTwiddleAddress,
      twiddleAddressShellDepth, fareySumShell]
  · simp [fareyMediantHarmonicSlot, harmonicShellSlotOfTwiddle, fareyMediantShellSlot,
      fareyMediantSlotIndex]

/-! ## Leg-sum twiddle landing -/

/-- Twiddle address from shared first two legs and summed third leg. -/
def twiddleLegSumAddress (a b c₁ c₂ : ℕ) : TwiddleFactorAddress :=
  (a, b, c₁ + c₂)

theorem twiddle_leg_sum_shell_depth (a b c₁ c₂ : ℕ) :
    twiddleAddressShellDepth (twiddleLegSumAddress a b c₁ c₂) =
      a * b * c₁ + a * b * c₂ := by
  dsimp [twiddleLegSumAddress, twiddleAddressShellDepth]
  ring

theorem twiddle_parent_shell (a b c : ℕ) :
    twiddleAddressShellDepth (a, b, c) = a * b * c := by
  dsimp [twiddleAddressShellDepth]

theorem twiddle_parent_shell_pos {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < twiddleAddressShellDepth (a, b, c) := by
  dsimp [twiddleAddressShellDepth]
  exact Nat.mul_pos (Nat.mul_pos ha hb) hc

theorem twiddle_leg_sum_shell_pos {a b c₁ c₂ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    0 < twiddleAddressShellDepth (twiddleLegSumAddress a b c₁ c₂) := by
  rw [twiddle_leg_sum_shell_depth]
  nlinarith [Nat.mul_pos ha hb, hc₁, hc₂]

theorem twiddle_leg_sum_is_twiddle_tuple {a b c₁ c₂ : ℕ}
    (hab : a = b) :
    isTwiddleTuple (twiddleLegSumAddress a b c₁ c₂) := by
  dsimp [twiddleLegSumAddress, isTwiddleTuple]
  exact Or.inl hab

/--
When parents share legs `(a,b)`, the Farey sum shell `a·b·c₁ + a·b·c₂` equals
the product shell `a·b·(c₁+c₂)` of the leg-sum twiddle address.
-/
theorem farey_sum_shell_eq_leg_sum_depth (a b c₁ c₂ : ℕ) :
    fareySumShell (a * b * c₁) (a * b * c₂) =
      twiddleAddressShellDepth (twiddleLegSumAddress a b c₁ c₂) := by
  dsimp [fareySumShell, twiddleLegSumAddress, twiddleAddressShellDepth]
  ring

theorem mem_farey_mediant_leg_sum_slot {a b c₁ c₂ k₁ k₂ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hk₁ : k₁ < a * b * c₁) (hk₂ : k₂ < a * b * c₂) :
    fareyMediantSlotIndex (a * b * c₁) (a * b * c₂) k₁ k₂ <
      twiddleAddressShellDepth (twiddleLegSumAddress a b c₁ c₂) := by
  rw [twiddle_leg_sum_shell_depth]
  exact mem_farey_mediant_slot (twiddle_parent_shell_pos ha hb hc₁)
    (twiddle_parent_shell_pos ha hb hc₂) hk₁ hk₂

/--
**Leg-sum landing:** Farey mediant between twiddle parent rays `(a,b,c₁)` and
`(a,b,c₂)` lands on harmonic slot `(a·b·(c₁+c₂), k₁+k₂)` — the same slot as
`twiddleLegSumAddress a b c₁ c₂`.
-/
theorem farey_mediant_lands_leg_sum_twiddle {a b c₁ c₂ k₁ k₂ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hk₁ : k₁ < a * b * c₁) (hk₂ : k₂ < a * b * c₂) :
    fareyMediantHarmonicSlot (twiddle_parent_shell_pos ha hb hc₁)
      (twiddle_parent_shell_pos ha hb hc₂) k₁ k₂ hk₁ hk₂ =
      harmonicShellSlotOfTwiddle (twiddleLegSumAddress a b c₁ c₂)
        (fareyMediantSlotIndex (a * b * c₁) (a * b * c₂) k₁ k₂)
        (mem_farey_mediant_leg_sum_slot ha hb hc₁ hc₂ hk₁ hk₂) := by
  refine harmonic_shell_slot_ext ?hdepth ?hindex
  · simp [fareyMediantHarmonicSlot, harmonicShellSlotOfTwiddle, twiddleLegSumAddress,
      twiddleAddressShellDepth, fareySumShell, twiddle_parent_shell]
    ring
  · simp [fareyMediantHarmonicSlot, harmonicShellSlotOfTwiddle, fareyMediantShellSlot,
      fareyMediantSlotIndex]

theorem farey_mediant_lands_leg_sum_twiddle_angle {a b c₁ c₂ k₁ k₂ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hk₁ : k₁ < a * b * c₁) (hk₂ : k₂ < a * b * c₂) :
    shellSweepAngle
        (farey_sum_shell_pos (twiddle_parent_shell_pos ha hb hc₁)
          (twiddle_parent_shell_pos ha hb hc₂))
        (fareyMediantShellSlot (twiddle_parent_shell_pos ha hb hc₁)
          (twiddle_parent_shell_pos ha hb hc₂) k₁ k₂ hk₁ hk₂) =
      shellSweepAngle (twiddle_leg_sum_shell_pos ha hb hc₁ hc₂)
        ⟨fareyMediantSlotIndex (a * b * c₁) (a * b * c₂) k₁ k₂,
          mem_farey_mediant_leg_sum_slot ha hb hc₁ hc₂ hk₁ hk₂⟩ := by
  rw [farey_mediant_shell_angle, twiddle_parent_shell, twiddle_parent_shell]
  dsimp [shellSweepAngle, fareyMediantSlotIndex]
  rw [farey_sum_shell_eq_leg_sum_depth]
  norm_cast

/-! ## Witness: `(2,2,2)` + `(2,2,1)` → `(2,2,3)` -/

theorem twiddle_leg_sum_222_221 :
    twiddleLegSumAddress 2 2 2 1 = (2, 2, 3) := by
  rfl

private theorem two_pos : 0 < 2 := Nat.succ_pos 1
private theorem one_pos : 0 < 1 := Nat.succ_pos 0

theorem farey_mediant_lands_222_221_slot :
    fareyMediantHarmonicSlot (Nat.succ_pos 7) (Nat.succ_pos 3) 1 1
        (by decide) (by decide) =
      harmonicShellSlotOfTwiddle (2, 2, 3) 2 (by decide) :=
  farey_mediant_lands_leg_sum_twiddle two_pos two_pos (Nat.succ_pos 1) one_pos
    (by decide) (by decide)

theorem farey_mediant_lands_222_221_angle :
    shellSweepAngle (farey_sum_shell_pos (Nat.succ_pos 7) (Nat.succ_pos 3))
      (fareyMediantShellSlot (Nat.succ_pos 7) (Nat.succ_pos 3) 1 1
        (by decide) (by decide)) =
      shellSweepAngle (twiddle_leg_sum_shell_pos two_pos two_pos (Nat.succ_pos 1) one_pos)
        ⟨2, by decide⟩ :=
  farey_mediant_lands_leg_sum_twiddle_angle two_pos two_pos (Nat.succ_pos 1) one_pos
    (by decide) (by decide)

theorem twiddle_leg_sum_222_221_is_diagonal :
    isTwiddleTuple (twiddleLegSumAddress 2 2 2 1) :=
  twiddle_leg_sum_is_twiddle_tuple (a := 2) (b := 2) rfl

/-! ## Landing bundle -/

/--
A Farey mediant harmonic slot **lands** on a twiddle address when the slot
depth and index agree with the twiddle product shell.
-/
structure FareyTwiddleLanding where
  addr : TwiddleFactorAddress
  slot : HarmonicShellSlot
  depth_eq : twiddleAddressShellDepth addr = slot.1

noncomputable def fareyTwiddleLandingPolar {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m)
    (hk₁ : k₁ < n₁) (hk₂ : k₂ < m) : FareyTwiddleLanding where
  addr := polarTwiddleAddress (fareySumShell n₁ m)
  slot := fareyMediantHarmonicSlot hn₁ hm k₁ k₂ hk₁ hk₂
  depth_eq := by
    show twiddleAddressShellDepth (polarTwiddleAddress (fareySumShell n₁ m)) =
      (fareyMediantHarmonicSlot hn₁ hm k₁ k₂ hk₁ hk₂).fst
    simp [polarTwiddleAddress, twiddleAddressShellDepth, fareySumShell,
      fareyMediantHarmonicSlot]

noncomputable def fareyTwiddleLandingLegSum {a b c₁ c₂ k₁ k₂ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hk₁ : k₁ < a * b * c₁) (hk₂ : k₂ < a * b * c₂) : FareyTwiddleLanding where
  addr := twiddleLegSumAddress a b c₁ c₂
  slot := fareyMediantHarmonicSlot (twiddle_parent_shell_pos ha hb hc₁)
    (twiddle_parent_shell_pos ha hb hc₂) k₁ k₂ hk₁ hk₂
  depth_eq := by
    show twiddleAddressShellDepth (twiddleLegSumAddress a b c₁ c₂) =
      (fareyMediantHarmonicSlot (twiddle_parent_shell_pos ha hb hc₁)
        (twiddle_parent_shell_pos ha hb hc₂) k₁ k₂ hk₁ hk₂).fst
    simp [twiddleLegSumAddress, twiddleAddressShellDepth, fareySumShell,
      fareyMediantHarmonicSlot]
    ring

structure FareyTwiddleLandingBundle where
  /-- Polar twiddle lands every Farey mediant slot. -/
  polar_lands :
    ∀ {n₁ m k₁ k₂ : ℕ} (hn₁ : 0 < n₁) (hm : 0 < m) (hk₁ : k₁ < n₁) (hk₂ : k₂ < m),
      (fareyTwiddleLandingPolar hn₁ hm hk₁ hk₂).slot =
        harmonicShellSlotOfTwiddle (polarTwiddleAddress (fareySumShell n₁ m))
          (fareyMediantSlotIndex n₁ m k₁ k₂)
          (mem_farey_mediant_polar_slot hn₁ hm hk₁ hk₂)
  /-- Leg-sum twiddle lands when parents share `(a,b)`. -/
  leg_sum_lands :
    ∀ {a b c₁ c₂ k₁ k₂ : ℕ} (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
      (hk₁ : k₁ < a * b * c₁) (hk₂ : k₂ < a * b * c₂),
      (fareyTwiddleLandingLegSum ha hb hc₁ hc₂ hk₁ hk₂).slot =
        harmonicShellSlotOfTwiddle (twiddleLegSumAddress a b c₁ c₂)
          (fareyMediantSlotIndex (a * b * c₁) (a * b * c₂) k₁ k₂)
          (mem_farey_mediant_leg_sum_slot ha hb hc₁ hc₂ hk₁ hk₂)
  /-- Witness `(2,2,2)` + `(2,2,1)` on shell `12`, slot `2`. -/
  witness_222_221 :
    fareyMediantHarmonicSlot (Nat.succ_pos 7) (Nat.succ_pos 3) 1 1
      (by decide) (by decide) =
      harmonicShellSlotOfTwiddle (2, 2, 3) 2 (by decide)

noncomputable def fareyTwiddleLandingBundle : FareyTwiddleLandingBundle where
  polar_lands := @fun n₁ m k₁ k₂ hn₁ hm hk₁ hk₂ =>
    farey_mediant_lands_polar_twiddle hn₁ hm hk₁ hk₂
  leg_sum_lands := @fun a b c₁ c₂ k₁ k₂ ha hb hc₁ hc₂ hk₁ hk₂ =>
    farey_mediant_lands_leg_sum_twiddle ha hb hc₁ hc₂ hk₁ hk₂
  witness_222_221 := farey_mediant_lands_222_221_slot

/-!
## Status

* **Unconditional:** Farey mediant slot = polar twiddle `(1,1,n₁+m)` at `k₁+k₂`.
* **Structured:** shared-leg parents `(a,b,c₁)`, `(a,b,c₂)` land on `(a,b,c₁+c₂)`.
* **Witness:** `(2,2,2)` / `(2,2,1)` mediant → `(2,2,3)` at `π/3`.
* **Not claimed:** Pythagorean hypotenuse labeling; balance / ζ-zeros on landed slots.
-/

end

end Hqiv.Story
