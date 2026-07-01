import HqivSpine.Physics.Shell
import HqivSpine.Physics.Binding
import HqivSpine.Chemistry.Aufbau
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# `HqivSpine.Chemistry.Binding` — electronic binding energy, disentangled onto the spine

The legacy chemistry binding chain (`Hqiv.QuantumChemistry.AtomElectronicBinding`,
`CurvatureBondContact`) is pulled onto the spine and golfed. Three structurally significant pieces
survive, every constant derived from the spine's own `alphaEM = 3/5` and `referenceM = 4`:

* **Slater screening from first principles.** The increments `0.35 / 0.85 / 1.00` are not a fitted
  table. A deeper electron screens a whole unit by Gauss enclosure (`1`); a co-radial same-shell
  electron is only half enclosed (the monogamy half `1/2`); the valence carrier leaks across one
  shell by the lapse over the proton anchor, `leak = α / referenceM = (3/5)/4 = 0.15`. Hence
  same-shell `1/2 − leak = 0.35` and adjacent `1 − leak = 0.85` — exactly Slater.

* **Hydrogenic binding magnitude.** `|E| = μ Z_eff² / (2 n²)` (Hartree), with the textbook scaling
  laws (`∝ Z_eff²`, `∝ 1/n²`, linear in reduced mass `μ`) and the Slater effective charge over an
  occupancy, which never drops below `1` (a bound electron always sees at least unit charge).

* **Outside curvature contact.** Geometry-near bonding is the lattice power law `G_eff(η) = η^α`
  with the *same* `α = 3/5`: nonnegative, monotone in the contact participation, fixed point `1`.

Depends only on `HqivSpine.Physics` (`alphaEM`, `referenceM`, the so(8) network) and Mathlib.
No legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Binding

open HqivSpine.Physics
open scoped BigOperators

noncomputable section

/-! ## Slater screening from the lattice lapse -/

/-- Adjacent-shell penetration leak `α / referenceM = (3/5)/4`. -/
def screenPenetrationLeak : ℝ := alphaEM / (referenceM : ℝ)

/-- The leak is exactly `0.15`. -/
theorem screenPenetrationLeak_eq : screenPenetrationLeak = 0.15 := by
  unfold screenPenetrationLeak
  rw [alphaEM_eq, show ((referenceM : ℝ)) = 4 from by norm_num [referenceM]]
  norm_num

/-- Same-shell increment = monogamy half − leak. -/
def slaterSameShell : ℝ := 1 / 2 - screenPenetrationLeak

/-- Adjacent (n−1) increment = full Gauss enclosure − leak. -/
def slaterAdjacentShell : ℝ := 1 - screenPenetrationLeak

/-- Deep-shell increment = full Gauss enclosure. -/
def slaterDeepShell : ℝ := 1

/-- The deep-shell increment is exactly `1.00`. -/
theorem slaterDeepShell_eq : slaterDeepShell = 1 := rfl

/-- The derived same-shell increment is exactly Slater's `0.35`. -/
theorem slaterSameShell_eq : slaterSameShell = 0.35 := by
  unfold slaterSameShell; rw [screenPenetrationLeak_eq]; norm_num

/-- The derived adjacent increment is exactly Slater's `0.85`. -/
theorem slaterAdjacentShell_eq : slaterAdjacentShell = 0.85 := by
  unfold slaterAdjacentShell; rw [screenPenetrationLeak_eq]; norm_num

/-- Same-shell and adjacent increments differ by exactly the monogamy half `1/2`. -/
theorem slater_same_adjacent_gap : slaterAdjacentShell - slaterSameShell = 1 / 2 := by
  unfold slaterAdjacentShell slaterSameShell; ring

/-- Slater screening increment from one other electron at principal shell `nOther`, seen by a
target electron at shell `nTarget`. The three derived increments are placed by Gauss enclosure:
a **same-shell** co-radial electron is half-enclosed (`slaterSameShell = 0.35`), an **inner
adjacent** `n−1` electron is enclosed minus the one-shell leak (`slaterAdjacentShell = 0.85`),
a **deeper** `≤ n−2` electron is fully enclosed (`slaterDeepShell = 1`), and an **outer** electron
(`nOther > nTarget`) sits outside the Gauss surface and contributes **nothing**. This refines the
earlier two-level form so the derived `slaterDeepShell` is actually used and outer shells no longer
over-screen — exactly Slater's tabulated `0 / 0.35 / 0.85 / 1.00` placement. -/
def slaterShieldingIncrement (nTarget nOther : ℕ) : ℝ :=
  if nOther = nTarget then slaterSameShell
  else if nOther + 1 = nTarget then slaterAdjacentShell
  else if nOther < nTarget then slaterDeepShell
  else 0

/-- Same-shell electrons screen by `slaterSameShell` (`0.35`). -/
theorem slaterShieldingIncrement_same (n : ℕ) :
    slaterShieldingIncrement n n = slaterSameShell := by
  unfold slaterShieldingIncrement; simp

/-- An inner adjacent (`n−1`) electron screens by `slaterAdjacentShell` (`0.85`). -/
theorem slaterShieldingIncrement_adjacent (n : ℕ) :
    slaterShieldingIncrement (n + 1) n = slaterAdjacentShell := by
  unfold slaterShieldingIncrement
  rw [if_neg (by omega), if_pos rfl]

/-- A deeper (`≤ n−2`) electron is fully enclosed and screens by `slaterDeepShell` (`1.00`). -/
theorem slaterShieldingIncrement_deep (nTarget nOther : ℕ) (h : nOther + 1 < nTarget) :
    slaterShieldingIncrement nTarget nOther = slaterDeepShell := by
  unfold slaterShieldingIncrement
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

/-- An outer electron (`nOther > nTarget`) sits outside the Gauss surface and does not screen. -/
theorem slaterShieldingIncrement_outer (nTarget nOther : ℕ) (h : nTarget < nOther) :
    slaterShieldingIncrement nTarget nOther = 0 := by
  unfold slaterShieldingIncrement
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Slater coefficient on shell `s` as seen by a target at principal shell `nT`. -/
def slaterShieldCoeffAtShell (nT s : ℕ) : ℝ :=
  if s = nT then slaterSameShell
  else if s + 1 = nT then slaterAdjacentShell
  else if s < nT then slaterDeepShell
  else 0

theorem slaterShieldingIncrement_eq_coeff (nT s : ℕ) :
    slaterShieldingIncrement nT s = slaterShieldCoeffAtShell nT s := by
  unfold slaterShieldCoeffAtShell slaterShieldingIncrement
  split_ifs <;> try rfl <;> try simp [slaterSameShell, slaterAdjacentShell, slaterDeepShell]

private theorem shellElectronCount_eq_zero_of_gt (Z s nT : ℕ) (hZ : Z ≤ 118)
    (hle : ∀ j : Fin Z, Aufbau.principalBlock Z j ≤ nT) (hn : nT < s) :
    Aufbau.shellElectronCount Z s = 0 := by
  unfold Aufbau.shellElectronCount Aufbau.principalConfig
  by_contra hne
  have hpos : 0 < (Aufbau.principalList.take Z).count s := Nat.pos_iff_ne_zero.mpr hne
  have hmem : s ∈ (Aufbau.principalList.take Z) := List.count_pos_iff.mp hpos
  obtain ⟨i, hi, hs⟩ := List.mem_iff_getElem.mp hmem
  have hi' : i < Z := by
    rw [List.length_take] at hi
    exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hblock : Aufbau.principalBlock Z ⟨i, hi'⟩ = s := by
    unfold Aufbau.principalBlock
    grind [List.getElem_eq_getD, List.getElem_take]
  have := hle ⟨i, hi'⟩
  rw [hblock] at this
  omega

/-- Full indexed Aufbau shield sum equals the shell occupancy weighted coefficients. -/
theorem slaterShieldFinFull_eq_shellWeighted (Z nT : ℕ) (hZ : Z ≤ 118) :
    (∑ j : Fin Z, slaterShieldingIncrement nT (Aufbau.principalBlock Z j)) =
      ∑ s ∈ Finset.range 8, (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s := by
  calc
    ∑ j : Fin Z, slaterShieldingIncrement nT (Aufbau.principalBlock Z j) =
        ∑ s ∈ Finset.range 8, (Aufbau.shellElectronCount Z s : ℝ) *
          slaterShieldingIncrement nT s :=
      Aufbau.fin_sum_principalBlock Z hZ (fun s => slaterShieldingIncrement nT s)
    _ = ∑ s ∈ Finset.range 8, (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s :=
      Finset.sum_congr rfl fun s _ => by rw [slaterShieldingIncrement_eq_coeff]

private theorem fin_sum_sub_target (Z : ℕ) (target : Fin Z) (g : Fin Z → ℝ) :
    (∑ j : Fin Z, g j) - g target = ∑ j : Fin Z, if j = target then 0 else g j := by
  have htarget :
      (∑ j : Fin Z, if j = target then g j else 0) = g target := by
    rw [Fintype.sum_eq_single (f := fun j => if j = target then g j else 0) target]
    · simp
    · intro j hj; simp [hj]
  rw [sub_eq_iff_eq_add, ← htarget, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro j
  by_cases h : j = target <;> simp [h]
/-! ## Hydrogenic binding magnitude and Slater effective charge -/

/-- Hydrogenic binding magnitude in Hartree: `|E| = μ Z_eff² / (2 n²)`. -/
def hydrogenicBindingHartree (μ zEff n : ℝ) : ℝ := μ * zEff ^ 2 / (2 * n ^ 2)

/-- CODATA Hartree→eV unit bridge (a reporting unit label, not a fitted constant). -/
def hartreeToEv : ℝ := 27.211386245988

/-- Binding magnitude in eV. -/
def hydrogenicBindingEv (μ zEff n : ℝ) : ℝ := hydrogenicBindingHartree μ zEff n * hartreeToEv

/-- **Effective-charge scaling.** Binding scales as `Z_eff²` — doubling the seen charge quadruples
the binding. -/
theorem hydrogenicBinding_scales_zEff (μ zEff n : ℝ) :
    hydrogenicBindingHartree μ (2 * zEff) n = 4 * hydrogenicBindingHartree μ zEff n := by
  unfold hydrogenicBindingHartree; ring

/-- **Principal-number scaling.** Binding scales as `1/n²` — the `n → 2n` shell is four-fold
shallower. -/
theorem hydrogenicBinding_quarters_with_double_n (μ zEff n : ℝ) (hn : n ≠ 0) :
    hydrogenicBindingHartree μ zEff (2 * n) = hydrogenicBindingHartree μ zEff n / 4 := by
  unfold hydrogenicBindingHartree
  field_simp
  ring

/-- Binding is linear in the reduced mass `μ`. -/
theorem hydrogenicBinding_linear_in_mass (t μ zEff n : ℝ) :
    hydrogenicBindingHartree (t * μ) zEff n = t * hydrogenicBindingHartree μ zEff n := by
  unfold hydrogenicBindingHartree; ring

/-- **Slater effective charge** at site `target` of a `Z`-electron atom whose electrons sit in
principal blocks given by `block`. `Z_eff = max 1 (Z − ∑_{j≠target} shield)`. The occupancy `block`
is supplied abstractly, so this is independent of the (heavy) aufbau assignment. -/
def slaterEffectiveCharge (Z : ℕ) (block : Fin Z → ℕ) (target : Fin Z) : ℝ :=
  let shield :=
    ∑ j : Fin Z, if j = target then 0 else slaterShieldingIncrement (block target) (block j)
  max 1 ((Z : ℝ) - shield)

/-- **A bound electron always sees at least unit charge:** `Z_eff ≥ 1`. -/
theorem slaterEffectiveCharge_ge_one (Z : ℕ) (block : Fin Z → ℕ) (target : Fin Z) :
    1 ≤ slaterEffectiveCharge Z block target := le_max_left _ _

/-- Binding from a Slater-screened site is the hydrogenic magnitude at the derived effective
charge. -/
def atomicSiteBindingHartree (Z : ℕ) (block : Fin Z → ℕ) (target : Fin Z) (μ n : ℝ) : ℝ :=
  hydrogenicBindingHartree μ (slaterEffectiveCharge Z block target) n

/-- The screened-site binding is nonnegative for a physical reduced mass and shell. -/
theorem atomicSiteBindingHartree_nonneg
    (Z : ℕ) (block : Fin Z → ℕ) (target : Fin Z) (μ n : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ atomicSiteBindingHartree Z block target μ n := by
  unfold atomicSiteBindingHartree hydrogenicBindingHartree
  have hz : 0 ≤ slaterEffectiveCharge Z block target :=
    le_trans zero_le_one (slaterEffectiveCharge_ge_one Z block target)
  positivity

/-! ## Concrete Aufbau occupancy

`slaterEffectiveCharge` left the principal-block occupancy abstract. `Chemistry.Aufbau` derives it
from the Madelung `(n+ℓ)` rule, so we can now specialise to the *actual* electron configuration. -/

/-- Slater effective charge with the **derived** Madelung/Aufbau occupancy (`Aufbau.principalBlock`)
substituted for the abstract `block`. -/
def slaterEffectiveChargeAufbau (Z : ℕ) (target : Fin Z) : ℝ :=
  slaterEffectiveCharge Z (Aufbau.principalBlock Z) target

/-- The Aufbau-screened charge still never drops below unit charge. -/
theorem slaterEffectiveChargeAufbau_ge_one (Z : ℕ) (target : Fin Z) :
    1 ≤ slaterEffectiveChargeAufbau Z target :=
  slaterEffectiveCharge_ge_one _ _ _

/-- **Hydrogen sees the full nuclear charge:** `Z_eff = 1` (no other electrons to screen). -/
theorem slaterEffectiveChargeAufbau_hydrogen :
    slaterEffectiveChargeAufbau 1 ⟨0, by omega⟩ = 1 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  simp

/-- **Helium's derived effective charge is `1.65`.** Each `1s` electron screens the other by the
spine's same-shell increment `slaterSameShell = 0.35` (derived, not Slater's tabulated `0.30`), so
`Z_eff = 2 − 0.35 = 1.65`. -/
theorem slaterEffectiveChargeAufbau_helium :
    slaterEffectiveChargeAufbau 2 (0 : Fin 2) = 1.65 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  have h0 : Aufbau.principalBlock 2 (0 : Fin 2) = 1 := by decide
  have h1 : Aufbau.principalBlock 2 (1 : Fin 2) = 1 := by decide
  rw [Fin.sum_univ_two, h0, h1,
      show slaterShieldingIncrement 1 1 = slaterSameShell from slaterShieldingIncrement_same 1,
      slaterSameShell_eq]
  simp
  norm_num

/-- **Lithium's `2s` electron sees `Z_eff = 1.30`.** Two inner `1s` electrons each screen by the
adjacent increment `0.85`, so `Z_eff = 3 − 2·0.85 = 1.30` — exactly Slater's tabulated value. -/
theorem slaterEffectiveChargeAufbau_lithium :
    slaterEffectiveChargeAufbau 3 (2 : Fin 3) = 1.30 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  have h0 : Aufbau.principalBlock 3 (0 : Fin 3) = 1 := by decide
  have h1 : Aufbau.principalBlock 3 (1 : Fin 3) = 1 := by decide
  have h2 : Aufbau.principalBlock 3 (2 : Fin 3) = 2 := by decide
  rw [Fin.sum_univ_three, h0, h1, h2,
      show slaterShieldingIncrement 2 1 = slaterAdjacentShell from
        slaterShieldingIncrement_adjacent 1, slaterAdjacentShell_eq]
  simp
  norm_num

/-- **Beryllium's `2s` electron sees `Z_eff = 1.95`.** Two `1s` electrons screen by `0.85` and one
same-shell `2s` electron by `0.35`: `Z_eff = 4 − (2·0.85 + 0.35) = 1.95` — Slater's value. -/
theorem slaterEffectiveChargeAufbau_beryllium :
    slaterEffectiveChargeAufbau 4 (3 : Fin 4) = 1.95 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  have h0 : Aufbau.principalBlock 4 (0 : Fin 4) = 1 := by decide
  have h1 : Aufbau.principalBlock 4 (1 : Fin 4) = 1 := by decide
  have h2 : Aufbau.principalBlock 4 (2 : Fin 4) = 2 := by decide
  have h3 : Aufbau.principalBlock 4 (3 : Fin 4) = 2 := by decide
  rw [Fin.sum_univ_four, h0, h1, h2, h3,
      show slaterShieldingIncrement 2 1 = slaterAdjacentShell from
        slaterShieldingIncrement_adjacent 1, slaterAdjacentShell_eq,
      show slaterShieldingIncrement 2 2 = slaterSameShell from
        slaterShieldingIncrement_same 2, slaterSameShell_eq]
  simp
  norm_num

/-- **Carbon's `2p` electron sees `Z_eff = 3.25`.** Two `1s` electrons screen by `0.85` and three
co-radial `2s²2p¹` electrons by `0.35`: `Z_eff = 6 − (2·0.85 + 3·0.35) = 3.25` — Slater's value. -/
theorem slaterEffectiveChargeAufbau_carbon :
    slaterEffectiveChargeAufbau 6 (5 : Fin 6) = 3.25 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  have h0 : Aufbau.principalBlock 6 (0 : Fin 6) = 1 := by decide
  have h1 : Aufbau.principalBlock 6 (1 : Fin 6) = 1 := by decide
  have h2 : Aufbau.principalBlock 6 (2 : Fin 6) = 2 := by decide
  have h3 : Aufbau.principalBlock 6 (3 : Fin 6) = 2 := by decide
  have h4 : Aufbau.principalBlock 6 (4 : Fin 6) = 2 := by decide
  have h5 : Aufbau.principalBlock 6 (5 : Fin 6) = 2 := by decide
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5,
      show slaterShieldingIncrement 2 1 = slaterAdjacentShell from
        slaterShieldingIncrement_adjacent 1, slaterAdjacentShell_eq,
      show slaterShieldingIncrement 2 2 = slaterSameShell from
        slaterShieldingIncrement_same 2, slaterSameShell_eq]
  simp
  norm_num

/-! ## Shell-resolved Slater screening (mined from legacy `SlaterScaffold` bookkeeping)

Instead of expanding `Fin.sum_univ` past `8`, aggregate the derived `slaterShieldingIncrement` by
principal shell: inner `n ≤ nₜ−2` electrons are fully enclosed, `n = nₜ−1` is adjacent, co-radial
electrons at `n = nₜ` screen by the same-shell increment, and outer shells contribute nothing. -/

/-- Slater shielding on a valence electron at principal shell `nT`, from the derived shell
occupancy counts (excluding the target electron itself at `nT`). -/
def slaterShieldFromShellCounts (Z nT : ℕ) : ℝ :=
  (Finset.range nT).sum (fun n =>
    if n + 1 = nT then (Aufbau.shellElectronCount Z n : ℝ) * slaterAdjacentShell
    else if n + 1 < nT then (Aufbau.shellElectronCount Z n : ℝ) * slaterDeepShell
    else 0) +
    max 0 ((Aufbau.shellElectronCount Z nT : ℝ) - 1) * slaterSameShell

private theorem shellElectronCount_pos_of_block (Z nT : ℕ) (target : Fin Z)
    (hT : Aufbau.principalBlock Z target = nT) (hZ : Z ≤ 118) :
    0 < Aufbau.shellElectronCount Z nT := by
  unfold Aufbau.shellElectronCount Aufbau.principalConfig Aufbau.principalBlock at *
  rw [List.count_pos_iff, List.mem_iff_getElem]
  refine ⟨target.val, ?_, ?_⟩
  · rw [List.length_take, Nat.lt_min]
    exact ⟨target.isLt, by rw [Aufbau.principalList_length]; omega⟩
  · grind [List.getElem_eq_getD, List.getElem_take]

theorem slaterShieldFromShellCounts_eq_weighted (Z nT : ℕ) (hZ : Z ≤ 118)
    (hle : ∀ j : Fin Z, Aufbau.principalBlock Z j ≤ nT)
    (hpos : 0 < Aufbau.shellElectronCount Z nT) (hnT : nT ≤ 7) :
    slaterShieldFromShellCounts Z nT =
      (∑ s ∈ Finset.range 8, (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s) -
        slaterSameShell := by
  unfold slaterShieldFromShellCounts
  have houter (s : ℕ) (hs : nT < s) :
      (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s = 0 := by
    simp [shellElectronCount_eq_zero_of_gt Z s nT hZ hle hs]
  have hsplit :
      ∑ s ∈ Finset.range 8, (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s =
        ∑ s ∈ Finset.range (nT + 1), (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s := by
    have hico :
        ∑ s ∈ Finset.Ico (nT + 1) 8,
            (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      rcases Finset.mem_Ico.mp hs with ⟨hsle, _⟩
      exact houter s (Nat.lt_of_lt_of_le (Nat.lt_succ_self nT) hsle)
    have hle8 : nT + 1 ≤ 8 := Nat.succ_le_succ hnT
    rw [← Finset.sum_range_add_sum_Ico (f := fun s =>
      (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s) hle8, hico, add_zero]
  have hinner :
      (Finset.range nT).sum (fun n =>
          if n + 1 = nT then (Aufbau.shellElectronCount Z n : ℝ) * slaterAdjacentShell
          else if n + 1 < nT then (Aufbau.shellElectronCount Z n : ℝ) * slaterDeepShell
          else 0) =
        ∑ s ∈ Finset.range nT,
          (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hs' : s < nT := Finset.mem_range.mp hs
    have hterm :
        (if s + 1 = nT then (Aufbau.shellElectronCount Z s : ℝ) * slaterAdjacentShell
          else if s + 1 < nT then (Aufbau.shellElectronCount Z s : ℝ) * slaterDeepShell else 0) =
          (Aufbau.shellElectronCount Z s : ℝ) * slaterShieldCoeffAtShell nT s := by
      simp [slaterShieldCoeffAtShell, hs']
      split_ifs <;> simp [slaterShieldCoeffAtShell, hs'] <;> try omega
    simpa [hterm]
  have hge : 1 ≤ Aufbau.shellElectronCount Z nT := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  have hone : (1 : ℝ) ≤ (Aufbau.shellElectronCount Z nT : ℝ) := by exact_mod_cast hge
  have hsub : (0 : ℝ) ≤ (Aufbau.shellElectronCount Z nT : ℝ) - 1 := sub_nonneg.mpr hone
  rw [hinner]
  conv_rhs => rw [hsplit]
  rw [Finset.sum_range_succ]
  have hnt : slaterShieldCoeffAtShell nT nT = slaterSameShell := by
    dsimp [slaterShieldCoeffAtShell]
    simp [slaterSameShell_eq]
  have hmax : max 0 ((Aufbau.shellElectronCount Z nT : ℝ) - 1) =
      (Aufbau.shellElectronCount Z nT : ℝ) - 1 := by
    rw [max_comm]
    exact max_eq_left hsub
  rw [hnt, slaterSameShell_eq, hmax]
  ring

/-- **Shield-sum lemma:** excluded indexed Aufbau sum equals `slaterShieldFromShellCounts`. -/
theorem slaterShieldAufbauExcl_eq_shellCounts (Z nT : ℕ) (target : Fin Z)
    (hT : Aufbau.principalBlock Z target = nT)
    (hle : ∀ j : Fin Z, Aufbau.principalBlock Z j ≤ nT) (hZ : Z ≤ 118) (hnT : nT ≤ 7) :
    (∑ j : Fin Z, if j = target then 0 else
        slaterShieldingIncrement nT (Aufbau.principalBlock Z j)) =
      slaterShieldFromShellCounts Z nT := by
  have hfull := slaterShieldFinFull_eq_shellWeighted Z nT hZ
  have hpos := shellElectronCount_pos_of_block Z nT target hT hZ
  have hagg := slaterShieldFromShellCounts_eq_weighted Z nT hZ hle hpos hnT
  have hsub :=
      fin_sum_sub_target Z target (fun j => slaterShieldingIncrement nT (Aufbau.principalBlock Z j))
  rw [← hsub, hT, slaterShieldingIncrement_same, hfull, hagg]

/-- **Shell-resolved effective charge** at principal shell `nT` (valence electron convention). -/
def slaterEffectiveChargeAtShell (Z nT : ℕ) : ℝ :=
  max 1 ((Z : ℝ) - slaterShieldFromShellCounts Z nT)

/-- **First-principles valence `Z_eff`:** Slater charge at the highest occupied principal shell,
aggregated from derived shell occupancies — the primary route for `(Z) →` chemistry. -/
def valenceSlaterEffectiveCharge (Z : ℕ) : ℝ :=
  slaterEffectiveChargeAtShell Z (Aufbau.topPrincipal Z)

/-- Index of the last Madelung-filled electron (`Z` electrons ⇒ index `Z − 1`). -/
def valenceElectronIndex (Z : ℕ) (h : 0 < Z) : Fin Z := ⟨Z - 1, by omega⟩

theorem valenceSlaterEffectiveCharge_ge_one (Z : ℕ) :
    1 ≤ valenceSlaterEffectiveCharge Z := by
  unfold valenceSlaterEffectiveCharge slaterEffectiveChargeAtShell
  exact le_max_left _ _

/-- Valence hydrogenic binding magnitude (Hartree) from `Z` and reduced mass `μ` alone. -/
def valenceBindingHartree (Z : ℕ) (μ : ℝ) : ℝ :=
  hydrogenicBindingHartree μ (valenceSlaterEffectiveCharge Z) (Aufbau.topPrincipal Z : ℝ)

theorem valenceBindingHartree_nonneg (Z : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ valenceBindingHartree Z μ := by
  unfold valenceBindingHartree hydrogenicBindingHartree
  have hz : 0 ≤ valenceSlaterEffectiveCharge Z := le_trans zero_le_one (valenceSlaterEffectiveCharge_ge_one Z)
  positivity

theorem slaterShieldFromShellCounts_sodium :
    slaterShieldFromShellCounts 11 3 = 8.8 := by
  unfold slaterShieldFromShellCounts
  rw [slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  have h0 : (Aufbau.shellElectronCount 11 0 : ℝ) = 0 := by
    simp [Aufbau.shellElectronCount, Aufbau.principalConfig]
  have h1 : (Aufbau.shellElectronCount 11 1 : ℝ) = 2 := by exact_mod_cast Aufbau.sodium_shell_counts.1
  have h2 : (Aufbau.shellElectronCount 11 2 : ℝ) = 8 := by exact_mod_cast Aufbau.sodium_shell_counts.2.1
  have h3 : (Aufbau.shellElectronCount 11 3 : ℝ) = 1 := by exact_mod_cast Aufbau.sodium_shell_counts.2.2
  simp only [Finset.sum_range_succ, h0, h1, h2, h3]
  norm_num

theorem slaterEffectiveChargeAtShell_sodium :
    slaterEffectiveChargeAtShell 11 3 = 2.2 := by
  unfold slaterEffectiveChargeAtShell
  rw [slaterShieldFromShellCounts_sodium]
  norm_num

/-- **Sodium's `3s` electron sees `Z_eff = 2.20`.** Two `1s`, eight `n = 2`, and no co-radial
partner at `n = 3`: `Z_eff = 11 − (2·1 + 8·0.85) = 2.20`. -/
theorem slaterEffectiveChargeAufbau_sodium :
    slaterEffectiveChargeAufbau 11 (10 : Fin 11) = 2.2 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Aufbau.principalBlock_eleven, slaterShieldingIncrement,
    slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  norm_num

/-- **Witness: shell aggregate matches the indexed Aufbau sum** for sodium's `3s` electron. -/
theorem valenceSlaterEffectiveCharge_eq_aufbau_sodium :
    valenceSlaterEffectiveCharge 11 = slaterEffectiveChargeAufbau 11 (10 : Fin 11) := by
  unfold valenceSlaterEffectiveCharge
  rw [Aufbau.sodium_valence.1, slaterEffectiveChargeAtShell_sodium, slaterEffectiveChargeAufbau_sodium]

/-- **Chlorine's `3p` valence electron sees `Z_eff = 6.10`.** `Z_eff = 17 − (2·1 + 8·0.85 + 6·0.35)
= 6.10`. -/
theorem slaterEffectiveChargeAufbau_chlorine :
    slaterEffectiveChargeAufbau 17 (16 : Fin 17) = 6.1 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Aufbau.principalBlock_seventeen, slaterShieldingIncrement,
    slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  norm_num

/-- **Nitrogen's `2p` electron sees `Z_eff = 3.90`.** Matches the shell-resolved aggregate. -/
theorem slaterEffectiveChargeAufbau_nitrogen :
    slaterEffectiveChargeAufbau 7 (6 : Fin 7) = 3.9 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Aufbau.principalBlock_seven, slaterShieldingIncrement,
    slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  norm_num

/-- **Oxygen's `2p` electron sees `Z_eff = 4.55`.** Matches the shell-resolved aggregate. -/
theorem slaterEffectiveChargeAufbau_oxygen :
    slaterEffectiveChargeAufbau 8 (7 : Fin 8) = 4.55 := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Aufbau.principalBlock_eight, slaterShieldingIncrement,
    slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  norm_num

/-- **Generic bridge:** indexed Aufbau Slater charge equals the shell-resolved aggregate. -/
theorem slaterEffectiveChargeAtShell_eq_aufbau (Z nT : ℕ) (target : Fin Z)
    (hT : Aufbau.principalBlock Z target = nT)
    (hle : ∀ j : Fin Z, Aufbau.principalBlock Z j ≤ nT) (hZ : Z ≤ 118) (hnT : nT ≤ 7) :
    slaterEffectiveChargeAufbau Z target = slaterEffectiveChargeAtShell Z nT := by
  unfold slaterEffectiveChargeAufbau slaterEffectiveCharge slaterEffectiveChargeAtShell
  rw [hT, slaterShieldAufbauExcl_eq_shellCounts Z nT target hT hle hZ hnT]

private theorem principalBlock_le_topPrincipal (Z : ℕ) (hZ : Z ≤ 118) (j : Fin Z) :
    Aufbau.principalBlock Z j ≤ Aufbau.topPrincipal Z := by
  unfold Aufbau.topPrincipal Aufbau.principalConfig
  have hj : j.val < (Aufbau.principalList.take Z).length := by
    rw [List.length_take, Nat.lt_min]
    exact ⟨j.isLt, by rw [Aufbau.principalList_length]; omega⟩
  have hmem : Aufbau.principalBlock Z j ∈ Aufbau.principalList.take Z := by
    rw [List.mem_iff_getElem]
    refine ⟨j.val, hj, ?_⟩
    unfold Aufbau.principalBlock
    have hidx : j.val < Aufbau.principalList.length := by
      rw [Aufbau.principalList_length]; omega
    grind [List.getElem_eq_getD, List.getElem_take]
  exact Aufbau.le_foldr_max_of_mem hmem

/-- **Valence shell aggregate matches indexed Aufbau** when the last electron sits at the period. -/
theorem valenceSlaterEffectiveCharge_eq_aufbau {w : ℕ} (h : Aufbau.lastElectronInTopShell (w + 1))
    (hZ : w + 1 ≤ 118) :
    valenceSlaterEffectiveCharge (w + 1) =
      slaterEffectiveChargeAufbau (w + 1) ⟨w, by omega⟩ := by
  unfold valenceSlaterEffectiveCharge
  exact (slaterEffectiveChargeAtShell_eq_aufbau (w + 1) (Aufbau.topPrincipal (w + 1)) ⟨w, by omega⟩ h
    (fun j => principalBlock_le_topPrincipal (w + 1) hZ j) hZ (Aufbau.topPrincipal_le_seven (w + 1))).symm

theorem slaterEffectiveChargeAtShell_carbon :
    slaterEffectiveChargeAtShell 6 2 = 3.25 := by
  unfold slaterEffectiveChargeAtShell slaterShieldFromShellCounts
  rw [slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  obtain ⟨hc1, hc2⟩ := Aufbau.carbon_shell_counts
  simp only [Finset.sum_range_succ, hc1, hc2]
  norm_num

theorem slaterEffectiveChargeAtShell_nitrogen :
    slaterEffectiveChargeAtShell 7 2 = 3.9 := by
  unfold slaterEffectiveChargeAtShell slaterShieldFromShellCounts
  rw [slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  obtain ⟨hn1, hn2⟩ := Aufbau.nitrogen_shell_counts
  simp only [Finset.sum_range_succ, hn1, hn2]
  norm_num

theorem slaterEffectiveChargeAtShell_oxygen :
    slaterEffectiveChargeAtShell 8 2 = 4.55 := by
  unfold slaterEffectiveChargeAtShell slaterShieldFromShellCounts
  rw [slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  obtain ⟨ho1, ho2⟩ := Aufbau.oxygen_shell_counts
  simp only [Finset.sum_range_succ, ho1, ho2]
  norm_num

theorem valenceSlaterEffectiveCharge_eq_aufbau_carbon :
    valenceSlaterEffectiveCharge 6 = slaterEffectiveChargeAufbau 6 (5 : Fin 6) := by
  unfold valenceSlaterEffectiveCharge
  rw [Aufbau.carbon_valence.1, slaterEffectiveChargeAtShell_carbon, slaterEffectiveChargeAufbau_carbon]

theorem valenceSlaterEffectiveCharge_eq_aufbau_nitrogen :
    valenceSlaterEffectiveCharge 7 = slaterEffectiveChargeAufbau 7 (6 : Fin 7) := by
  unfold valenceSlaterEffectiveCharge
  rw [show Aufbau.topPrincipal 7 = 2 from by decide, slaterEffectiveChargeAtShell_nitrogen,
    slaterEffectiveChargeAufbau_nitrogen]

theorem valenceSlaterEffectiveCharge_eq_aufbau_oxygen :
    valenceSlaterEffectiveCharge 8 = slaterEffectiveChargeAufbau 8 (7 : Fin 8) := by
  unfold valenceSlaterEffectiveCharge
  rw [Aufbau.oxygen_valence.1, slaterEffectiveChargeAtShell_oxygen, slaterEffectiveChargeAufbau_oxygen]

theorem valenceSlaterEffectiveCharge_eq_aufbau_chlorine :
    valenceSlaterEffectiveCharge 17 = slaterEffectiveChargeAufbau 17 (16 : Fin 17) := by
  unfold valenceSlaterEffectiveCharge slaterEffectiveChargeAtShell slaterShieldFromShellCounts
  rw [Aufbau.chlorine_valence.1, slaterEffectiveChargeAufbau_chlorine]
  rw [slaterAdjacentShell_eq, slaterDeepShell_eq, slaterSameShell_eq]
  obtain ⟨hc1, hc2, hc3⟩ := Aufbau.chlorine_shell_counts
  simp only [Finset.sum_range_succ, hc1, hc2, hc3]
  norm_num

/-! ## Outside curvature contact `G_eff(η) = η^α` -/

/-- Outside contact coupling: the lattice power law at lapse `α = 3/5`. -/
def G_eff (η : ℝ) : ℝ := η ^ alphaEM

/-- Contact coupling is nonnegative for nonnegative participation. -/
theorem G_eff_nonneg (η : ℝ) (hη : 0 ≤ η) : 0 ≤ G_eff η := Real.rpow_nonneg hη _

/-- Full participation is the fixed point: `G_eff 1 = 1`. -/
theorem G_eff_one : G_eff 1 = 1 := Real.one_rpow _

/-- More contact participation never weakens the bond: `G_eff` is monotone in `η ≥ 0`. -/
theorem G_eff_mono (η₁ η₂ : ℝ) (h₁ : 0 ≤ η₁) (hle : η₁ ≤ η₂) : G_eff η₁ ≤ G_eff η₂ := by
  have hα : 0 ≤ alphaEM := by rw [alphaEM_eq]; norm_num
  exact Real.rpow_le_rpow h₁ hle hα

/-- A sub-unit contact is genuinely softer than full closure: `G_eff η ≤ 1` for `0 ≤ η ≤ 1`. -/
theorem G_eff_le_one (η : ℝ) (h₀ : 0 ≤ η) (h₁ : η ≤ 1) : G_eff η ≤ 1 := by
  rw [← G_eff_one]; exact G_eff_mono η 1 h₀ h₁

/-! ## Tie-in to the so(8) binding network

The chemistry binding magnitude above is the electronic (outer-shell) projection; the spine's
`Physics.M_composite_from_network` carries the full so(8) network binding. When the network binding
vanishes the composite mass is exactly the constituent total — the no-binding baseline against which
the screened electronic binding is the first correction. -/

theorem composite_mass_no_binding (m : ℕ) (M : ℝ) (c : ℝ) :
    M_composite_from_network m M (fun _ => 0) c = M := by
  unfold M_composite_from_network E_bind_from_network
  simp

end

end HqivSpine.Chemistry.Binding
