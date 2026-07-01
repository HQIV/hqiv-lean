import HqivSpine.Physics.Blackbody
import HqivSpine.Algebra.G2

/-!
# `HqivSpine.Physics.LockIn` — the lock-in shell as the horizon ⇄ Planck-pole balance

The lock-in shell `referenceM = 4` is, in the rest of the spine, *posited* (it is just
`def referenceM : ℕ := 4`). This module earns it as the **unique discrete equilibrium**
of the horizon/Planck-pole tug of war that `Physics.Gravity` carries in continuous
form (the varying-G map `φ ↦ φ^(3/5)` with its two fixed points `φ = 0` = horizon and
`φ = 1` = Planck pole, `gEff_fixed_iff_nonneg`).

The discrete realisation of that tug of war runs on the **mode budget**. At shell `m`
the newly-unlocked modes are `N(m) = 8(m+1) = carrierMultiplicity·(m+1)` — the
octonion carrier times the radial depth — strictly **increasing outward** (more room
the farther from the Planck pole). A closed sector (`G₂ ∪ {Δ} ⇒ 𝔰𝔬(8)` on the
eight-channel carrier) needs a fixed **closure capacity** `C = 40`. The two pulls:

* **below lock-in** (`m < 4`) the modes fall *short* of capacity — the sector cannot
  close, so the configuration is driven **outward** (toward the horizon) to unlock more;
* **above lock-in** (`m > 4`) the modes *exceed* capacity — the surplus is untrapped
  and leaks, so the configuration is driven **inward** (toward the Planck pole) to shed it;
* **at lock-in** (`m = 4`) `N(4) = 40` exactly: every unlocked mode is booked, none
  missing and none surplus. This is a **stable** fixed point (a restoring force on both
  sides), and it is the **unique** solution of `N(m) = C` (`referenceM_unique_balance`).

So `referenceM = 4` is not merely the *minimal* feasible shell (the legacy one-sided
`N(m) ≥ 40 ↔ m ≥ 4` plus Occam): it is the *balanced* shell where inward demand meets
outward supply.

**The capacity is derived, not posited.** `C = 40 = 28 + 8 + 4` is the dimension of the
full closed gauge-sector spine:

* `𝔰𝔬(8) = 28` — the carrier rotation algebra, the closure target of `G₂ ∪ {Δ}` (the
  *genuine* linear-algebra dimension `finrank (skewMatrices 8)`, not a formula);
* `carrierMultiplicity = 8` — the octonion carrier it rotates;
* `spacetimeDim = 4` — the `3+1` base it is fibered over.

`sectorClosureCapacity_eq_so8_carrier_base` proves `C = dim 𝔰𝔬(8) + carrier + base`, and
`sectorClosureCapacity_eq_foundation_atoms` reduces it to foundation atoms
`(g₂ ⊕ 7 ⊕ 7) + carrier + base = (14+7+7)+8+4`. With the capacity derived, the lock-in
closes with **no posited integer** (`lockin_fully_closed`).

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-! ## New modes unlocked per shell -/

/-- **New modes unlocked at shell `m`**: the octonion carrier times the radial depth,
`N(m) = carrierMultiplicity·(m+1) = 8(m+1)` (the `ℕ`-valued count whose `ℝ`-cast is the
blackbody `shellModeMultiplicity`). Strictly increasing outward. -/
def newModes (m : ℕ) : ℕ := carrierMultiplicity * (m + 1)

theorem newModes_eq (m : ℕ) : newModes m = 8 * (m + 1) := by
  unfold newModes; rw [carrierMultiplicity_eq_eight]

/-- The mode count is the blackbody per-shell multiplicity (the `ℝ`-cast agrees). -/
theorem newModes_cast_eq_shellModeMultiplicity (m : ℕ) :
    (newModes m : ℝ) = shellModeMultiplicity m := by
  unfold newModes shellModeMultiplicity; push_cast; ring

/-- New modes increase **strictly outward** — more room the farther from the Planck pole. -/
theorem newModes_strictMono : StrictMono newModes := by
  intro a b h; rw [newModes_eq, newModes_eq]; omega

/-! ## Sector-closure capacity and the two-sided balance -/

/-- **Sector-closure capacity** `C = 40`: the dimension of the full closed gauge-sector
spine — the carrier rotation algebra `𝔰𝔬(8)` (the `G₂ ∪ {Δ}` closure target), the
octonion carrier it rotates, and the `3+1` spacetime base. It is **defined as** that
dimension; the value `40` is the derived consequence (`sectorClosureCapacity_eq_forty`). -/
def sectorClosureCapacity : ℕ :=
  soDim carrierMultiplicity + carrierMultiplicity + spacetimeDim

/-! ### The capacity is the carrier-algebra closure dimension; `40` is derived -/

/-- **The capacity evaluates to `40`** — `28 + 8 + 4` from the carrier rotation algebra,
the carrier, and the base. The number is an *output*, not a pin. -/
theorem sectorClosureCapacity_eq_forty : sectorClosureCapacity = 40 := by
  unfold sectorClosureCapacity
  rw [soDim_carrier, carrierMultiplicity_eq_eight, spacetimeDim_eq_four]

/-- **The capacity uses the genuine `𝔰𝔬(8)`.** The `soDim` count `= 28` coincides with
the *honest* linear-algebra dimension `finrank (skewMatrices 8)` of the carrier rotation
algebra — no formula is taken on faith. -/
theorem sectorClosureCapacity_eq_so8_carrier_base :
    sectorClosureCapacity
      = Module.finrank ℝ (Algebra.skewMatrices 8) + carrierMultiplicity + spacetimeDim := by
  unfold sectorClosureCapacity
  rw [Algebra.finrank_so8, soDim_carrier]

/-- **Capacity reduced to foundation atoms.** `𝔰𝔬(8)` branches as `28 = 𝔤₂ ⊕ 7 ⊕ 7`, so
`C = (14 + 7 + 7) + 8 + 4` — entirely `g2Dim`, two imaginary `7`-cosets, the carrier,
and the base. No free integer remains. -/
theorem sectorClosureCapacity_eq_foundation_atoms :
    sectorClosureCapacity
      = (g2Dim + imaginaryDim + imaginaryDim) + carrierMultiplicity + spacetimeDim := by
  unfold sectorClosureCapacity
  rw [soDim_carrier, g2Dim_eq_fourteen, imaginaryDim_eq_seven]

/-- **At lock-in the unlocked modes exactly fill the capacity:** `N(4) = 40`. -/
theorem newModes_referenceM : newModes referenceM = sectorClosureCapacity := by
  rw [newModes_eq, sectorClosureCapacity_eq_forty, show referenceM = 4 from rfl]

/-- **Below lock-in: under-capacity** (drives outward toward the horizon). -/
theorem newModes_lt_capacity_iff (m : ℕ) :
    newModes m < sectorClosureCapacity ↔ m < referenceM := by
  rw [newModes_eq, sectorClosureCapacity_eq_forty, show referenceM = 4 from rfl]; omega

/-- **Above lock-in: over-capacity** (drives inward toward the Planck pole). -/
theorem capacity_lt_newModes_iff (m : ℕ) :
    sectorClosureCapacity < newModes m ↔ referenceM < m := by
  rw [newModes_eq, sectorClosureCapacity_eq_forty, show referenceM = 4 from rfl]; omega

/-- **The balance is met at a unique shell:** `N(m) = C ↔ m = referenceM`. -/
theorem newModes_eq_capacity_iff (m : ℕ) :
    newModes m = sectorClosureCapacity ↔ m = referenceM := by
  rw [newModes_eq, sectorClosureCapacity_eq_forty, show referenceM = 4 from rfl]; omega

/-- **Uniqueness of the lock-in shell.** Any shell whose unlocked modes exactly fill the
closure capacity *is* the lock-in shell. -/
theorem referenceM_unique_balance {m : ℕ}
    (h : newModes m = sectorClosureCapacity) : m = referenceM :=
  (newModes_eq_capacity_iff m).mp h

/-- **The horizon ⇄ Planck-pole tug of war pins `referenceM = 4`.** Strictly under
capacity below it (outward pull to unlock modes), exactly at capacity on it, strictly
over capacity above it (inward pull to shed surplus) — a stable two-sided equilibrium,
not merely the minimal feasible shell. -/
theorem referenceM_lockin_balance :
    (∀ m : ℕ, m < referenceM → newModes m < sectorClosureCapacity) ∧
    newModes referenceM = sectorClosureCapacity ∧
    (∀ m : ℕ, referenceM < m → sectorClosureCapacity < newModes m) :=
  ⟨fun m h => (newModes_lt_capacity_iff m).mpr h,
   newModes_referenceM,
   fun m h => (capacity_lt_newModes_iff m).mpr h⟩

/-! ## Signed mode deficit — the restoring force -/

/-- **Mode deficit** `C − N(m)` as an integer: the directional drive of the tug of war.
Positive below lock-in (a deficit → outward pull toward the horizon), negative above
(a surplus → inward pull toward the Planck pole), zero at lock-in. -/
def modeDeficit (m : ℕ) : ℤ := (sectorClosureCapacity : ℤ) - (newModes m : ℤ)

theorem modeDeficit_eq (m : ℕ) : modeDeficit m = 40 - 8 * ((m : ℤ) + 1) := by
  unfold modeDeficit; rw [sectorClosureCapacity_eq_forty, newModes_eq]; push_cast; ring

/-- Each outward shell step unlocks eight more modes, so the deficit drops by eight. -/
theorem modeDeficit_succ (m : ℕ) : modeDeficit (m + 1) = modeDeficit m - 8 := by
  rw [modeDeficit_eq, modeDeficit_eq]; push_cast; ring

/-- **Outward pull below lock-in:** the deficit is positive exactly for `m < referenceM`. -/
theorem modeDeficit_pos_iff (m : ℕ) : 0 < modeDeficit m ↔ m < referenceM := by
  rw [modeDeficit_eq, show referenceM = 4 from rfl]; omega

/-- **Inward pull above lock-in:** the deficit is negative exactly for `referenceM < m`. -/
theorem modeDeficit_neg_iff (m : ℕ) : modeDeficit m < 0 ↔ referenceM < m := by
  rw [modeDeficit_eq, show referenceM = 4 from rfl]; omega

/-- **No net pull at lock-in:** the deficit vanishes exactly at `referenceM`. -/
theorem modeDeficit_eq_zero_iff (m : ℕ) : modeDeficit m = 0 ↔ m = referenceM := by
  rw [modeDeficit_eq, show referenceM = 4 from rfl]; omega

/-- Each outward shell step drops the deficit by eight, hence strictly decreases it. -/
theorem modeDeficit_succ_lt (m : ℕ) : modeDeficit (m + 1) < modeDeficit m := by
  rw [modeDeficit_succ]; linarith

/-- Below lock-in, stepping outward strictly reduces the positive deficit. -/
theorem modeDeficit_succ_lt_of_below {m : ℕ} (h : m < referenceM) :
    modeDeficit (m + 1) < modeDeficit m :=
  modeDeficit_succ_lt m

/-- Above lock-in, stepping outward makes the surplus more negative. -/
theorem modeDeficit_succ_lt_of_above {m : ℕ} (h : referenceM < m) :
    modeDeficit (m + 1) < modeDeficit m :=
  modeDeficit_succ_lt m

theorem modeDeficit_referenceM : modeDeficit referenceM = 0 :=
  (modeDeficit_eq_zero_iff referenceM).mpr rfl

/-! ## Capstone: the lock-in shell is fully closed -/

/-- **`referenceM = 4` is fully closed — no posited integer.** The closure capacity is
the derived gauge-sector dimension `dim 𝔰𝔬(8) + carrier + base`; the lock-in shell's
unlocked modes meet it exactly; and it is the *unique* shell that does. The horizon ⇄
Planck-pole tug of war pins `4`, end to end. -/
theorem lockin_fully_closed :
    sectorClosureCapacity
        = Module.finrank ℝ (Algebra.skewMatrices 8) + carrierMultiplicity + spacetimeDim ∧
    newModes referenceM = sectorClosureCapacity ∧
    (∀ m : ℕ, newModes m = sectorClosureCapacity → m = referenceM) :=
  ⟨sectorClosureCapacity_eq_so8_carrier_base, newModes_referenceM,
   fun _ h => referenceM_unique_balance h⟩

end HqivSpine.Physics
