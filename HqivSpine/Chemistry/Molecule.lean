import HqivSpine.Physics.Shell
import HqivSpine.Foundation.Carrier
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.Molecule` — worked molecules on the zero-point shell ladder

The legacy `Hqiv.QuantumChemistry.H2` (and its `FiniteSiteQuantumChemistry` /
`ProteinResearch.latticeFullModeEnergy` substrate) computes a molecular **zero-point mode-energy
budget** as a sum of per-site contributions on the HQIV shell ladder. That whole layer rides on two
facts and one octonion factor — all spine-native:

* the per-shell mode count `availableModes m = carrierMultiplicity · C(m+2,2) = 4(m+2)(m+1)`
  (the `8` carrier channels over the stars-and-bars simplex `latticeSimplexCount m / 2`);
* the per-mode zero-point energy `φ(m)/2 = (m+1)` (`ℏω/2`, with `φ(m) = 2(m+1)` the spine mode count);
* hence the **single-site budget** `siteModeEnergy m = availableModes m · (φ(m)/2) = 4(m+2)(m+1)²`,
  with no fitted coefficient — the legacy `latticeFullModeEnergy_closed_form`.

A molecule is a finite list of site shells; its energy is the additive trace
`siteEnergyTrace shell = ∑ᵢ siteModeEnergy (shellᵢ)`. The homonuclear `n`-site closed form is
`n · siteModeEnergy m`, and the **diatomic H₂** at equal shells is `8(m+2)(m+1)²`, evaluating at the
proton anchor `referenceM = 4` to the exact `1200` (`h2SiteEnergy_referenceM_numeric`).

**Generalised for broader use.** The equations are stated at full generality:
* `siteModeEnergyOfCarrier c m = (c/2)(m+2)(m+1)²` for an **arbitrary carrier dimension `c`**, so the
  same law covers the whole Hopf / Cayley–Dickson ladder `c ∈ {1,2,4,8}` (ℝ, ℂ, ℍ, 𝕆); the spine
  octonion budget is the `c = carrierMultiplicity` instance (`siteModeEnergy_eq_ofCarrier`), monotone
  in `c` (`siteModeEnergyOfCarrier_mono_in_carrier`).
* `siteEnergyTrace_closed_form` gives the **polyatomic** sum for any `n`-site molecule, and the budget
  is **extensive** — fragments compose additively over `Fin.append` (`siteEnergyTrace_append`) and over
  `List` concatenation (`listSiteEnergy_append`), the two views agreeing
  (`siteEnergyTrace_eq_listSiteEnergy`).
* the two-site scaffold is the **general (heteronuclear) diatomic** `A–B` (`h2SiteEnergy_closed_form`,
  shells need not be equal); H₂ is the homonuclear instance.

Every constant is read off the foundation: `8 = carrierMultiplicity` (`Foundation.Carrier`),
`φ(m) = 2(m+1)` and `latticeSimplexCount m = (m+2)(m+1)` (`Physics.Shell`), `referenceM = 4`.

**Honest scope.** This is the dimensionless zero-point *mode-energy budget* of the separated-atom
ladder — the additive site trace, not yet the bond well. The actual H₂/LiH/H₂O *binding* energy
(the depth of the molecular curvature well relative to this budget) needs the bond layer
(`Chemistry.BondEnergy` for the sign, the heavy bonded-horizon Casimir for the magnitude) and is not
claimed here. No legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.Molecule

open HqivSpine.Physics
open HqivSpine.Foundation
open scoped BigOperators

noncomputable section

/-! ## The single-site zero-point mode-energy budget -/

/-- **Available modes at shell `m`** — the `carrierMultiplicity = 8` octonion channels distributed
over the stars-and-bars simplex `C(m+2,2) = latticeSimplexCount m / 2`. Octonion-factor anchored:
no posited `4`. -/
def availableModes (m : ℕ) : ℝ :=
  (carrierMultiplicity : ℝ) * ((latticeSimplexCount m : ℝ) / 2)

/-- Closed form `availableModes m = 4(m+2)(m+1)` — the `4 = 8/2 = carrierMultiplicity/2`. -/
theorem availableModes_eq (m : ℕ) :
    availableModes m = 4 * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
  unfold availableModes
  have hc : (carrierMultiplicity : ℝ) = 8 := by
    rw [carrierMultiplicity_eq_eight]; norm_num
  have hl : (latticeSimplexCount m : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    rw [latticeSimplexCount_eq_shellNumer]
    simp only [shellNumer]; push_cast; ring
  rw [hc, hl]; ring

theorem availableModes_pos (m : ℕ) : 0 < availableModes m := by
  rw [availableModes_eq]; positivity

/-- **Per-mode zero-point energy** `φ(m)/2 = (m+1)` (the `ℏω/2` slice, with `φ(m) = 2(m+1)`). -/
theorem perModeZeroPoint (m : ℕ) : (phi m : ℝ) / 2 = (m : ℝ) + 1 := by
  unfold phi; push_cast; ring

/-- **Single-site mode-energy budget** = available modes × per-mode zero point. The legacy
`latticeFullModeEnergy`. -/
def siteModeEnergy (m : ℕ) : ℝ :=
  availableModes m * ((phi m : ℝ) / 2)

/-- **First-principles closed form** `siteModeEnergy m = 4(m+2)(m+1)²` — no fitted coefficient. -/
theorem siteModeEnergy_closed_form (m : ℕ) :
    siteModeEnergy m = 4 * ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2 := by
  unfold siteModeEnergy
  rw [availableModes_eq, perModeZeroPoint]; ring

theorem siteModeEnergy_nonneg (m : ℕ) : 0 ≤ siteModeEnergy m := by
  rw [siteModeEnergy_closed_form]; positivity

theorem siteModeEnergy_pos (m : ℕ) : 0 < siteModeEnergy m := by
  rw [siteModeEnergy_closed_form]; positivity

/-- The budget **strictly increases outward** (deeper shells carry more zero-point modes). -/
theorem siteModeEnergy_strictMono : StrictMono siteModeEnergy := by
  intro a b hab
  rw [siteModeEnergy_closed_form, siteModeEnergy_closed_form]
  have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  -- `f(x) = 4(x+2)(x+1)² = 4(x³+4x²+5x+2)`, so `f(b)−f(a) = 4(b−a)(b²+ab+a²+4b+4a+5)`.
  have hp : 0 < ((b : ℝ) - a) * ((b : ℝ) ^ 2 + a * b + a ^ 2 + 4 * b + 4 * a + 5) := by
    apply mul_pos (by linarith)
    positivity
  nlinarith [hp]

/-! ## Generalization 1 — arbitrary carrier dimension (the Hopf ladder)

The octonion factor `8` enters only as the channel count of the carrier. Parametrising it gives the
same site-energy law for *any* carrier dimension `c`, in particular the lower normed-division rungs
`c ∈ {1, 2, 4, 8}` (ℝ, ℂ, ℍ, 𝕆 — `Foundation.divisionAlgebraDim`). The spine's octonion case is the
instance `c = carrierMultiplicity`. -/

/-- Available modes for a **general carrier dimension `c`**: `c` channels over the stars-and-bars
simplex `latticeSimplexCount m / 2`. -/
def availableModesOfCarrier (c m : ℕ) : ℝ :=
  (c : ℝ) * ((latticeSimplexCount m : ℝ) / 2)

/-- **General single-site budget** for carrier dimension `c`. -/
def siteModeEnergyOfCarrier (c m : ℕ) : ℝ :=
  availableModesOfCarrier c m * ((phi m : ℝ) / 2)

/-- **General closed form** `siteModeEnergyOfCarrier c m = (c/2)(m+2)(m+1)²`. -/
theorem siteModeEnergyOfCarrier_closed_form (c m : ℕ) :
    siteModeEnergyOfCarrier c m = (c : ℝ) / 2 * ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2 := by
  unfold siteModeEnergyOfCarrier availableModesOfCarrier
  have hl : (latticeSimplexCount m : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    rw [latticeSimplexCount_eq_shellNumer]; simp only [shellNumer]; push_cast; ring
  rw [hl, perModeZeroPoint]; ring

/-- **The octonion budget is the `c = carrierMultiplicity` instance.** -/
theorem siteModeEnergy_eq_ofCarrier (m : ℕ) :
    siteModeEnergy m = siteModeEnergyOfCarrier carrierMultiplicity m := rfl

/-- Same statement spelled through the Cayley–Dickson ladder: the carrier is the `transverseDim`
rung, `divisionAlgebraDim 3 = 8`. -/
theorem siteModeEnergy_eq_octonion_rung (m : ℕ) :
    siteModeEnergy m = siteModeEnergyOfCarrier (divisionAlgebraDim transverseDim) m := rfl

theorem siteModeEnergyOfCarrier_nonneg (c m : ℕ) : 0 ≤ siteModeEnergyOfCarrier c m := by
  rw [siteModeEnergyOfCarrier_closed_form]; positivity

/-- **Monotone in the carrier dimension:** more channels ⇒ a deeper per-site budget (at fixed shell).
The ladder ℝ < ℂ < ℍ < 𝕆 raises the budget. -/
theorem siteModeEnergyOfCarrier_mono_in_carrier {c d : ℕ} (m : ℕ) (h : c ≤ d) :
    siteModeEnergyOfCarrier c m ≤ siteModeEnergyOfCarrier d m := by
  rw [siteModeEnergyOfCarrier_closed_form, siteModeEnergyOfCarrier_closed_form]
  have hcd : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
  have hm : (0 : ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2 := by positivity
  nlinarith [hcd, hm]

/-! ## Molecules as additive site traces -/

/-- The total molecular zero-point budget = additive sum over the site shells. -/
def siteEnergyTrace {n : ℕ} (shell : Fin n → ℕ) : ℝ :=
  ∑ i, siteModeEnergy (shell i)

theorem siteEnergyTrace_nonneg {n : ℕ} (shell : Fin n → ℕ) :
    0 ≤ siteEnergyTrace shell :=
  Finset.sum_nonneg fun _ _ => siteModeEnergy_nonneg _

/-- A homonuclear `n`-site molecule: every site at the same shell `m`. -/
def homonuclearSpec (n m : ℕ) : Fin n → ℕ := fun _ => m

/-- **Homonuclear closed form** `siteEnergyTrace = n · siteModeEnergy m`. -/
theorem siteEnergyTrace_homonuclear (n m : ℕ) :
    siteEnergyTrace (homonuclearSpec n m) = (n : ℝ) * siteModeEnergy m := by
  unfold siteEnergyTrace homonuclearSpec
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **General polyatomic closed form** — the molecular budget is the per-site cubic summed over the
shell list, valid for *any* `n`-site molecule. -/
theorem siteEnergyTrace_closed_form {n : ℕ} (shell : Fin n → ℕ) :
    siteEnergyTrace shell
      = ∑ i, 4 * ((shell i : ℝ) + 2) * ((shell i : ℝ) + 1) ^ 2 :=
  Finset.sum_congr rfl fun i _ => siteModeEnergy_closed_form (shell i)

/-- **Fragment additivity (extensivity).** Joining two molecular fragments adds their budgets — the
zero-point energy is extensive, so sub-molecules compose freely. -/
theorem siteEnergyTrace_append {a b : ℕ} (s : Fin a → ℕ) (t : Fin b → ℕ) :
    siteEnergyTrace (Fin.append s t) = siteEnergyTrace s + siteEnergyTrace t := by
  simp only [siteEnergyTrace, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-! ## Generalization 2 — list-based molecular composition

A molecule of arbitrary, unstructured composition is a `List` of site shells; its budget is the
mapped sum, and composing molecules (`++`) adds their budgets. This lifts the legacy
`listLatticeEnergySum`. -/

/-- Molecular budget over an arbitrary list of site shells. -/
def listSiteEnergy (shells : List ℕ) : ℝ := (shells.map siteModeEnergy).sum

@[simp] theorem listSiteEnergy_nil : listSiteEnergy [] = 0 := rfl

@[simp] theorem listSiteEnergy_cons (m : ℕ) (shells : List ℕ) :
    listSiteEnergy (m :: shells) = siteModeEnergy m + listSiteEnergy shells := by
  simp [listSiteEnergy]

/-- **Composition adds budgets** — the list face of `siteEnergyTrace_append`. -/
theorem listSiteEnergy_append (s t : List ℕ) :
    listSiteEnergy (s ++ t) = listSiteEnergy s + listSiteEnergy t := by
  simp [listSiteEnergy]

theorem listSiteEnergy_nonneg (shells : List ℕ) : 0 ≤ listSiteEnergy shells := by
  unfold listSiteEnergy
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨m, _, rfl⟩ := hx
  exact siteModeEnergy_nonneg m

/-- A `Fin n` molecular trace is the list budget of its shell list — the two views agree. -/
theorem siteEnergyTrace_eq_listSiteEnergy {n : ℕ} (shell : Fin n → ℕ) :
    siteEnergyTrace shell = listSiteEnergy (List.ofFn shell) := by
  unfold siteEnergyTrace listSiteEnergy
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## Worked diatomic: H₂ -/

/-- Two-site shell assignment for an H₂ scaffold. -/
def h2Spec (mLeft mRight : ℕ) : Fin 2 → ℕ := ![mLeft, mRight]

/-- H₂ molecular zero-point budget. -/
def h2SiteEnergy (mLeft mRight : ℕ) : ℝ := siteEnergyTrace (h2Spec mLeft mRight)

theorem h2SiteEnergy_eq (mLeft mRight : ℕ) :
    h2SiteEnergy mLeft mRight = siteModeEnergy mLeft + siteModeEnergy mRight := by
  simp [h2SiteEnergy, siteEnergyTrace, h2Spec, Fin.sum_univ_two]

theorem h2SiteEnergy_nonneg (mLeft mRight : ℕ) : 0 ≤ h2SiteEnergy mLeft mRight := by
  rw [h2SiteEnergy_eq]; exact add_nonneg (siteModeEnergy_nonneg _) (siteModeEnergy_nonneg _)

/-- **General (heteronuclear) diatomic closed form** — the two sites need not share a shell, so the
same two-site scaffold serves any diatomic `A–B`. -/
theorem h2SiteEnergy_closed_form (mLeft mRight : ℕ) :
    h2SiteEnergy mLeft mRight
      = 4 * ((mLeft : ℝ) + 2) * ((mLeft : ℝ) + 1) ^ 2
        + 4 * ((mRight : ℝ) + 2) * ((mRight : ℝ) + 1) ^ 2 := by
  rw [h2SiteEnergy_eq, siteModeEnergy_closed_form, siteModeEnergy_closed_form]

theorem h2SiteEnergy_same_shell (m : ℕ) :
    h2SiteEnergy m m = 2 * siteModeEnergy m := by
  rw [h2SiteEnergy_eq]; ring

/-- Equal-shell H₂ closed form `8(m+2)(m+1)²` — twice the single-site budget. -/
theorem h2SiteEnergy_same_shell_closed_form (m : ℕ) :
    h2SiteEnergy m m = 8 * ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2 := by
  rw [h2SiteEnergy_same_shell, siteModeEnergy_closed_form]; ring

/-- H₂ at the proton anchor shell `m = referenceM`, closed form. -/
theorem h2SiteEnergy_referenceM_eq :
    h2SiteEnergy referenceM referenceM
      = 8 * ((referenceM : ℝ) + 2) * ((referenceM : ℝ) + 1) ^ 2 :=
  h2SiteEnergy_same_shell_closed_form referenceM

/-- **Numeric readout** `h2SiteEnergy referenceM referenceM = 1200` (at `m = 4`,
`8 · 6 · 5² = 1200`). The legacy `h2SiteEnergyTrace_referenceM_numeric`, spine-native. -/
theorem h2SiteEnergy_referenceM_numeric :
    h2SiteEnergy referenceM referenceM = 1200 := by
  rw [h2SiteEnergy_same_shell_closed_form]; norm_num [referenceM]

/-- **Bundle.** The H₂ worked molecule: additive trace, equal-shell closed form, and the proton-anchor
numeric readout, all from the spine constants. -/
theorem moleculeH2Discharged_holds :
    (∀ mL mR : ℕ, h2SiteEnergy mL mR = siteModeEnergy mL + siteModeEnergy mR) ∧
    (∀ m : ℕ, h2SiteEnergy m m = 8 * ((m : ℝ) + 2) * ((m : ℝ) + 1) ^ 2) ∧
    h2SiteEnergy referenceM referenceM = 1200 :=
  ⟨h2SiteEnergy_eq, h2SiteEnergy_same_shell_closed_form, h2SiteEnergy_referenceM_numeric⟩

end

end HqivSpine.Chemistry.Molecule
