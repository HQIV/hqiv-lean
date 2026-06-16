import Hqiv.Story.S3ExplicitFormulaPrimeLatticeTruncation
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Mathlib.GroupTheory.Perm.Basic

/-!
# Theta partition twiddle address `(2,2,2)` → shell `8` → pole readout at `π/4`

See `S3DiagonalSphereTwiddlePermutations` for the master object (S₃ permutation
orbits on diagonal lattice-sphere voxels).  `S3DeepTwiddlePoleLadder` records the
symmetric `(m,m,m)` special case; `(2,2,2)` is the **pole cell** there.

The Hopf circle is **not** the doubled-height plane.  On the circle the natural
counter is a **partition** of arc slots; on the SO(4) readout the height is
**doubled** to `(1, 2t)`.  This module packages the unconditional address
geometry and names the conjecture bridge.

## Minecraft-sphere intuition (ℤ³ analogy)

On a discrete sphere the **polar** voxels have only one nonzero coordinate.
The first **twiddle** voxel off the poles in the **product-address** chart is
`(2,2,2)`:

* two coordinates equal encodes the **twiddle pair** on `S¹`;
* the third tracks the **next factor** in the Euler product;
* **S₃ reflections** of the triple are the same partition cell.

The HQIV lift is **not** the voxel `(2,2,2) ∈ ℤ³` (that lies on shell
`2²+2²+2² = 12`).  The live address is the **product shell**

`2 · 2 · 2 = 8`,

the first nontrivial fully symmetric twiddle-factor triple, giving:

* first exact **π/4** arc slot at harmonic shell `n = 8`, index `k = 1`;
* **28** cumulative arc slots strictly before shell `8`
  (`cumulativeArcSlotCount 8 = 28`);
* SO(4) doubled first-zero endpoint `(1, 2t₁)` numerically near `(1, 28)`.

## Partition function

The slot **theta partition** through depth `N` is the Gram energy
`zeroLatticeGramEnergy N = ∑ amplitude²` — a nonnegative partition sum over
arc slots.  Twiddle-factor triples label **cells**; reflections quotient the
cell weight.

## Honesty

Everything through shell `8`, π/4, and slot count `28` is **unconditional**.
Matching `2t₁` to `28`, placing the first ζ-zero at this address, and reading
the partition peak from `(2,2,2)` are **named conjecture targets**, not theorems.
-/

namespace Hqiv.Story

noncomputable section

open Finset Real
open scoped BigOperators

/-! ## Twiddle-factor addresses -/

/-- A twiddle-factor address `(a,b,c)` — Minecraft-sphere style factor tuple. -/
abbrev TwiddleFactorAddress := ℕ × ℕ × ℕ

/-- Canonical first symmetric twiddle-factor address. -/
def twiddleAddress222 : TwiddleFactorAddress :=
  (2, 2, 2)

/-- Product shell depth from a factor address. -/
def twiddleAddressShellDepth (addr : TwiddleFactorAddress) : ℕ :=
  addr.1 * addr.2.1 * addr.2.2

/-- Fully symmetric twiddle tuple: all three factors equal and positive. -/
def isSymmetricTwiddleAddress (addr : TwiddleFactorAddress) : Prop :=
  let (a, b, c) := addr
  0 < a ∧ a = b ∧ b = c

/-- Twiddle pattern: at least two coordinates agree (twiddle pair + factor leg). -/
def isTwiddleTuple (addr : TwiddleFactorAddress) : Prop :=
  let (a, b, c) := addr
  a = b ∨ a = c ∨ b = c

/-! ## ℤ³ voxel analogy (honest scope) -/

/-- Squared radius on the ℤ³ voxel chart. -/
def voxelSumSq (a b c : ℕ) : ℕ :=
  a ^ 2 + b ^ 2 + c ^ 2

/-- Axis / polar voxel in the first octant: exactly one positive coordinate. -/
def isPolarVoxelAddress (a b c : ℕ) : Prop :=
  (0 < a ∧ b = 0 ∧ c = 0) ∨
    (0 < b ∧ a = 0 ∧ c = 0) ∨
    (0 < c ∧ a = 0 ∧ b = 0)

theorem twiddle_address_222_symmetric :
    isSymmetricTwiddleAddress twiddleAddress222 := by
  dsimp [twiddleAddress222, isSymmetricTwiddleAddress]
  exact ⟨by decide, rfl, rfl⟩

theorem twiddle_address_222_not_polar :
    ¬ isPolarVoxelAddress 2 2 2 := by
  dsimp [isPolarVoxelAddress]
  simp

theorem voxel_222_on_shell_twelve :
    voxelSumSq 2 2 2 = 12 := by
  decide

/-! ## Product address → shell `8` → π/4 -/

theorem twiddle_address_222_shell_depth :
    twiddleAddressShellDepth twiddleAddress222 = 8 :=
  rfl

/--
First nontrivial symmetric twiddle address: factors `> 1` force shell depth
at least `8`, with equality at `(2,2,2)`.
-/
theorem twiddle_address_222_first_nontrivial_symmetric :
    isSymmetricTwiddleAddress twiddleAddress222 ∧
      ∀ addr, isSymmetricTwiddleAddress addr → 1 < addr.1 →
        8 ≤ twiddleAddressShellDepth addr := by
  constructor
  · exact twiddle_address_222_symmetric
  · intro addr h hgt
    rcases addr with ⟨a, b, c⟩
    dsimp [isSymmetricTwiddleAddress, twiddleAddressShellDepth] at h ⊢
    rcases h with ⟨_, hab, hbc⟩
    subst hab hbc
    have ha : 2 ≤ a := by omega
    nlinarith [show 8 ≤ a * a * a from by nlinarith [ha]]

/-- Canonical π/4 slot at shell depth `8`. -/
def twiddlePiQuarterSlot : HarmonicShellSlot :=
  ⟨8, ⟨1, by decide⟩⟩

theorem twiddle_pi_quarter_slot_angle :
    shellSweepAngle (Nat.succ_pos 7) twiddlePiQuarterSlot.2 = Real.pi / 4 := by
  dsimp [twiddlePiQuarterSlot, shellSweepAngle]
  field_simp
  ring

theorem twiddle_pi_quarter_slot_eq :
    twiddlePiQuarterSlot = ⟨8, ⟨1, by decide⟩⟩ :=
  rfl

theorem twiddle_address_222_slot_is_pi_quarter :
    shellSweepAngle (Nat.succ_pos (twiddleAddressShellDepth twiddleAddress222 - 1))
      twiddlePiQuarterSlot.2 = Real.pi / 4 := by
  have hdepth : twiddleAddressShellDepth twiddleAddress222 = 8 :=
    twiddle_address_222_shell_depth
  dsimp [twiddlePiQuarterSlot, shellSweepAngle]
  rw [hdepth]
  field_simp
  ring

/-! ## Cumulative slot count `28` before shell `8` -/

theorem cumulative_slots_before_shell_eight :
    cumulativeArcSlotCount 8 = 28 := by
  simp [cumulative_arc_slot_count_eq]

theorem cumulative_slots_before_twiddle_address :
    cumulativeArcSlotCount (twiddleAddressShellDepth twiddleAddress222) = 28 := by
  rw [twiddle_address_222_shell_depth]
  exact cumulative_slots_before_shell_eight

/-! ## S₃ reflections of a twiddle cell -/

/-- Leg `i` of a twiddle-factor address. -/
def twiddleLeg (addr : TwiddleFactorAddress) : Fin 3 → ℕ
  | 0 => addr.1
  | 1 => addr.2.1
  | 2 => addr.2.2

theorem twiddleLeg_222 (i : Fin 3) : twiddleLeg twiddleAddress222 i = 2 := by
  fin_cases i <;> rfl

/-- Permute the three legs of a twiddle-factor address. -/
def permuteTwiddleAddress (σ : Equiv.Perm (Fin 3)) (addr : TwiddleFactorAddress) :
    TwiddleFactorAddress :=
  (twiddleLeg addr (σ 0), twiddleLeg addr (σ 1), twiddleLeg addr (σ 2))

theorem permute_twiddle_address_222_invariant (σ : Equiv.Perm (Fin 3)) :
    permuteTwiddleAddress σ twiddleAddress222 = twiddleAddress222 := by
  dsimp [permuteTwiddleAddress, twiddleAddress222]
  congr <;> exact twiddleLeg_222 _

/-- Reflection orbit of a twiddle address under leg permutations. -/
noncomputable def twiddleAddressOrbit (addr : TwiddleFactorAddress) : Finset TwiddleFactorAddress :=
  Finset.image (fun σ => permuteTwiddleAddress σ addr) Finset.univ

theorem mem_twiddle_address_222_orbit :
    twiddleAddress222 ∈ twiddleAddressOrbit twiddleAddress222 := by
  apply Finset.mem_image.mpr
  refine ⟨Equiv.refl (Fin 3), Finset.mem_univ _, ?_⟩
  exact permute_twiddle_address_222_invariant (Equiv.refl (Fin 3))

theorem unique_twiddle_address_222_orbit {a : TwiddleFactorAddress}
    (ha : a ∈ twiddleAddressOrbit twiddleAddress222) : a = twiddleAddress222 := by
  rcases Finset.mem_image.mp ha with ⟨σ, _, h⟩
  simpa [h] using permute_twiddle_address_222_invariant σ

theorem twiddle_address_222_orbit_singleton :
    twiddleAddressOrbit twiddleAddress222 = {twiddleAddress222} := by
  ext a
  simp only [Finset.mem_singleton]
  constructor
  · exact unique_twiddle_address_222_orbit
  · intro ha
    rw [ha]
    exact mem_twiddle_address_222_orbit

def twiddleAddressOrbitSize (addr : TwiddleFactorAddress) : ℕ :=
  (twiddleAddressOrbit addr).card

theorem twiddle_address_222_orbit_size :
    twiddleAddressOrbitSize twiddleAddress222 = 1 := by
  dsimp [twiddleAddressOrbitSize]
  rw [twiddle_address_222_orbit_singleton]
  simp

/-! ## Theta partition over arc slots -/

/--
**Slot theta partition** through shell depth `N`: sum of squared survivor
amplitudes — the partition-function backbone on the circle chart.
-/
noncomputable def shellThetaPartition (N : ℕ) : ℝ :=
  zeroLatticeGramEnergy N

theorem shell_theta_partition_nonneg (N : ℕ) :
    0 ≤ shellThetaPartition N :=
  zero_lattice_gram_energy_nonneg N

theorem shell_theta_partition_eq_gram_energy (N : ℕ) :
    shellThetaPartition N = zeroLatticeGramEnergy N :=
  rfl

/--
Partition weight of a twiddle cell: inverse orbit size × amplitude² at the
canonical slot when the address shell matches.
-/
noncomputable def twiddleCellPartitionWeight (addr : TwiddleFactorAddress)
    {n : ℕ} (hn : 0 < n) (k : Fin n) : ℝ :=
  (twiddleAddressOrbitSize addr : ℝ)⁻¹ * (slotSurvivorAmplitude hn k) ^ 2

theorem twiddle_cell_partition_weight_222 :
    twiddleCellPartitionWeight twiddleAddress222 (Nat.succ_pos 7)
        twiddlePiQuarterSlot.2 =
      (slotSurvivorAmplitude (Nat.succ_pos 7) twiddlePiQuarterSlot.2) ^ 2 := by
  dsimp [twiddleCellPartitionWeight]
  simp [twiddle_address_222_orbit_size]

/-! ## Doubled-height bridge (SO(4) readout plane) -/

/--
**Doubling conjecture target:** critical-line height `t` matches cumulative slot
count before shell `8` after SO(4) doubling — `2t = 28`, not `t = π/4`.
-/
def TwiddleAddressDoublingTarget (t : ℝ) : Prop :=
  2 * t = (cumulativeArcSlotCount 8 : ℝ)

theorem twiddle_doubling_target_slot_count :
    TwiddleAddressDoublingTarget ((cumulativeArcSlotCount 8 : ℝ) / 2) := by
  dsimp [TwiddleAddressDoublingTarget, cumulative_slots_before_shell_eight]
  ring

/--
First-zero SO(4) readout matches the doubling target when `2 · height = 28`.
-/
theorem so4_doubled_endpoint_snd_matches_slot_count
    (R : SO4FirstZeroOriginLineReadout)
    (hdouble : 2 * R.height = (cumulativeArcSlotCount 8 : ℝ)) :
    (so4DoubledComplexReadout R.zero_point).2 = (cumulativeArcSlotCount 8 : ℝ) := by
  simpa [so4DoubledComplexReadout_snd, hdouble] using congr_arg Prod.snd R.doubled_endpoint

/-! ## Named conjecture targets (not discharged here) -/

/--
**Conjecture:** the first nontrivial ζ-zero height satisfies the doubling target
`2t₁ = cumulativeArcSlotCount 8 = 28`.
-/
def FirstZeroDoublingConjecture : Prop :=
  ∃ (R : SO4FirstZeroOriginLineReadout), TwiddleAddressDoublingTarget R.height

/--
Under rolling identification, ζ vanishing at the π/4 slot angle is equivalent
to harmonic-shell balance — already packaged in the coincidence layer.
-/
theorem twiddle_pi_quarter_balance_iff_id
    (hId : RollingZetaIdentificationAtCriticalLine) :
    riemannZeta (criticalLinePointAtHeight
        (shellSweepAngle (Nat.succ_pos 7) twiddlePiQuarterSlot.2)) = 0 ↔
      HarmonicShellBalanceEvent (Nat.succ_pos 7) twiddlePiQuarterSlot.2 :=
  zeta_zero_iff_slot_coincidence_balance hId (Nat.succ_pos 7) twiddlePiQuarterSlot.2

/--
**Conjecture:** the shell-theta partition at depth `8` peaks at the
`(2,2,2)` / π/4 cell among symmetric twiddle addresses.
-/
def ThetaPartitionPeakAt222Conjecture : Prop :=
  ∀ addr, isSymmetricTwiddleAddress addr →
    twiddleAddressShellDepth addr ≤ 8 →
      twiddleCellPartitionWeight addr (Nat.succ_pos 7) twiddlePiQuarterSlot.2 ≤
        twiddleCellPartitionWeight twiddleAddress222 (Nat.succ_pos 7)
          twiddlePiQuarterSlot.2

/-! ## Unconditional address bundle -/

/--
Unconditional geometry: `(2,2,2) ↦ 8 ↦ π/4`, `28` slots before shell `8`,
S₃ cell singleton, partition weight at π/4, theta partition = Gram energy.
-/
structure ThetaPartitionTwiddleAddressBundle where
  address : TwiddleFactorAddress
  address_eq : address = twiddleAddress222
  shell_depth : twiddleAddressShellDepth address = 8
  pi_quarter_slot : HarmonicShellSlot
  pi_quarter_slot_eq : pi_quarter_slot = twiddlePiQuarterSlot
  pi_quarter_angle :
    shellSweepAngle (Nat.succ_pos 7) twiddlePiQuarterSlot.2 = Real.pi / 4
  slots_before : cumulativeArcSlotCount 8 = 28
  orbit_singleton : twiddleAddressOrbit address = {address}
  partition_nonneg : ∀ N, 0 ≤ shellThetaPartition N
  partition_eq_gram : ∀ N, shellThetaPartition N = zeroLatticeGramEnergy N

noncomputable def thetaPartitionTwiddleAddressBundle : ThetaPartitionTwiddleAddressBundle where
  address := twiddleAddress222
  address_eq := rfl
  shell_depth := twiddle_address_222_shell_depth
  pi_quarter_slot := twiddlePiQuarterSlot
  pi_quarter_slot_eq := rfl
  pi_quarter_angle := twiddle_pi_quarter_slot_angle
  slots_before := cumulative_slots_before_shell_eight
  orbit_singleton := twiddle_address_222_orbit_singleton
  partition_nonneg := shell_theta_partition_nonneg
  partition_eq_gram := fun _ => rfl

/--
Conjecture package: doubling target, π/4 balance under identification, and
partition peak at `(2,2,2)`.
-/
structure ThetaPartitionFirstZeroAddressConjecture where
  doubling : FirstZeroDoublingConjecture
  partition_peak : ThetaPartitionPeakAt222Conjecture

/-!
## Status

* **Unconditional:** `(2,2,2)` symmetric twiddle address; product shell `8`;
  first π/4 slot `(8,1)`; `28` cumulative slots before shell `8`; S₃ orbit
  singleton; `shellThetaPartition = zeroLatticeGramEnergy`; cell weight at π/4.
* **Conditional (proved):** π/4 slot balance ↔ ζ zero under rolling identification.
* **Conjecture targets:** `2t₁ = 28`; partition peak at `(2,2,2)`.
* **Not claimed:** `t₁ = π/4`; voxel `(2,2,2) ∈ ℤ³` equals the product address;
  conjectures imply RH without `ExplicitFormulaLocalization`.
-/

end

end Hqiv.Story
