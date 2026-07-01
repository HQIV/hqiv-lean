import HqivSpine.Physics.Shell
import HqivSpine.Physics.Binding
import HqivSpine.Chemistry.Aufbau
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

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
