import HqivSpine.Chemistry.Aufbau
import HqivSpine.Chemistry.Binding
import HqivSpine.Chemistry.Electronegativity
import HqivSpine.Chemistry.DynamicBinding
import HqivSpine.Chemistry.AtomDischarge
import HqivSpine.Chemistry.Spectroscopy
import HqivSpine.Physics.Shell
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `HqivSpine.Chemistry.Atom` — first-principles neutral-atom chemistry from `Z` alone

Golfed from legacy `AtomElectronicDischarge`, `AtomFromCharge`, and `AtomElectronicBinding`:
**every neutral-atom observable is a pure function of nuclear charge `Z`**, routed through the
derived Madelung occupancy (`Aufbau`), shell-resolved Slater screening (`Binding`), Mulliken
electronegativity (`Electronegativity`), and dynamic-binding Compton triplets (`DynamicBinding`).

No PDG/NIST inputs. Comparison numbers stay in docstrings only.

## The `(Z) →` pipeline

1. `Aufbau.topPrincipal Z`, `Aufbau.valenceCount Z`, `Aufbau.iupacMainGroupNumber Z`
2. `Binding.valenceSlaterEffectiveCharge Z` — shell-aggregated Slater `Z_eff`
3. `Binding.valenceBindingHartree Z μ` — hydrogenic valence binding at derived `(Z_eff, n)`
4. `Electronegativity.electronegativityFromCharge Z μ` — Mulliken χ from the same `(Z_eff, n)`
5. `DynamicBinding.comptonTripletFromCharge Z` — TUFT Compton slots for finite-site binding
6. `bondIonicCharacterFromCharge Z Z' μ` — heteronuclear ionic character from derived χ

Honest scope: **s/p main-group first-principles readout** through `Z = 118`; d/f block IUPAC
grouping and crystal-field splitting are not claimed.
-/

namespace HqivSpine.Chemistry.Atom

open HqivSpine.Chemistry
open HqivSpine.Physics

noncomputable section

/-! ## Neutral atom from nuclear charge -/

/-- First-principles neutral-atom specification extracted from `Z` alone. -/
structure AtomSpec where
  nuclearCharge : ℕ
  period : ℕ
  valenceCount : ℕ
  iupacGroup : ℕ
  valenceShell : ℕ
  slaterZeff : ℝ

/-- The canonical `(Z) →` atom specification (nonzero `Z` only). -/
def atomSpec (Z : ℕ) (h : 0 < Z) : AtomSpec :=
  { nuclearCharge := Z
    period := Aufbau.topPrincipal Z
    valenceCount := Aufbau.valenceCount Z
    iupacGroup := Aufbau.iupacMainGroupNumber Z
    valenceShell := Aufbau.topPrincipal Z
    slaterZeff := Binding.valenceSlaterEffectiveCharge Z }

theorem atomSpec_charge (Z : ℕ) (h : 0 < Z) : (atomSpec Z h).nuclearCharge = Z := rfl

theorem atomSpec_sodium :
    (atomSpec 11 (by omega)).valenceCount = 1 ∧
      (atomSpec 11 (by omega)).period = 3 ∧
        (atomSpec 11 (by omega)).slaterZeff = 2.2 := by
  refine ⟨Aufbau.sodium_valence.2, Aufbau.sodium_valence.1, ?_⟩
  unfold atomSpec Binding.valenceSlaterEffectiveCharge
  rw [Aufbau.sodium_valence.1, Binding.slaterEffectiveChargeAtShell_sodium]

/-! ## Electronegativity and binding from `Z` -/

/-- Mulliken electronegativity of the valence electron from `Z` and reduced mass `μ`. -/
def electronegativityFromCharge (Z : ℕ) (μ : ℝ) : ℝ :=
  Electronegativity.atomElectronegativity μ (Binding.valenceSlaterEffectiveCharge Z)
    (Aufbau.topPrincipal Z : ℝ)

/-- Valence ionization-scale binding (Hartree) from `Z` and `μ`. -/
def bindingHartreeFromCharge (Z : ℕ) (μ : ℝ) : ℝ :=
  Binding.valenceBindingHartree Z μ

theorem bindingHartreeFromCharge_eq (Z : ℕ) (μ : ℝ) :
    bindingHartreeFromCharge Z μ = Binding.valenceBindingHartree Z μ := rfl

theorem electronegativityFromCharge_eq (Z : ℕ) (μ : ℝ) :
    electronegativityFromCharge Z μ =
      Electronegativity.atomElectronegativity μ (Binding.valenceSlaterEffectiveCharge Z)
        (Aufbau.topPrincipal Z : ℝ) := rfl

theorem electronegativityFromCharge_nonneg (Z : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    0 ≤ electronegativityFromCharge Z μ := by
  unfold electronegativityFromCharge
  exact Electronegativity.atomElectronegativity_nonneg μ _ _ hμ

theorem electronegativityFromCharge_ge_hydrogenFloor (Z : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (h : 0 < Z) :
    Electronegativity.atomElectronegativity μ 1 (Aufbau.topPrincipal Z : ℝ) ≤
      electronegativityFromCharge Z μ := by
  unfold electronegativityFromCharge
  have hz := Binding.valenceSlaterEffectiveCharge_ge_one Z
  rcases eq_or_lt_of_le hz with heq | hlt
  · rw [heq]
  · have hn : (Aufbau.topPrincipal Z : ℝ) ≠ 0 := by
      have hnat : 0 < Aufbau.topPrincipal Z := Nat.lt_of_lt_of_le (by decide : 0 < 1) (Aufbau.topPrincipal_ge_one Z h)
      exact_mod_cast ne_of_gt hnat
    exact (Electronegativity.electronegativity_strictMono_in_zEff μ (Aufbau.topPrincipal Z : ℝ) 1
      (Binding.valenceSlaterEffectiveCharge Z) hμ hn (by norm_num) hlt).le

/-! ## Heteronuclear bond readouts from two charges -/

/-- Ionic character of a bond `Z₁–Z₂` from derived Mulliken electronegativities. -/
def bondIonicCharacterFromCharge (Z₁ Z₂ : ℕ) (μ : ℝ) : ℝ :=
  Spectroscopy.bondIonicCharacter (electronegativityFromCharge Z₁ μ)
    (electronegativityFromCharge Z₂ μ)

/-- First-principles heteronuclear bond specification from two nuclear charges. -/
structure DiatomicBondSpec where
  zHeavy : ℕ
  zLight : ℕ
  periodHeavy : ℕ
  chiHeavy : ℝ
  chiLight : ℝ
  ionicCharacter : ℝ

/-- Canonical `(Z₁, Z₂) →` diatomic bond readout (heavy/light split by charge). -/
def diatomicBondSpec (Z₁ Z₂ : ℕ) (μ : ℝ) : DiatomicBondSpec :=
  let zHeavy := max Z₁ Z₂
  let zLight := min Z₁ Z₂
  { zHeavy := zHeavy
    zLight := zLight
    periodHeavy := Aufbau.topPrincipal zHeavy
    chiHeavy := electronegativityFromCharge zHeavy μ
    chiLight := electronegativityFromCharge zLight μ
    ionicCharacter := bondIonicCharacterFromCharge Z₁ Z₂ μ }

theorem diatomicBondSpec_ionicCharacter (Z₁ Z₂ : ℕ) (μ : ℝ) :
    (diatomicBondSpec Z₁ Z₂ μ).ionicCharacter = bondIonicCharacterFromCharge Z₁ Z₂ μ := rfl

theorem bondIonicCharacterFromCharge_nonneg (Z₁ Z₂ : ℕ) (μ : ℝ) :
    0 ≤ bondIonicCharacterFromCharge Z₁ Z₂ μ :=
  Spectroscopy.bondIonicCharacter_nonneg _ _

theorem bondIonicCharacterFromCharge_homonuclear (Z : ℕ) (μ : ℝ) :
    bondIonicCharacterFromCharge Z Z μ = 0 :=
  Spectroscopy.bondIonicCharacter_homonuclear _

/-- Distinct valence `Z_eff` at the same shell forces a polar bond (e.g. C–O at period 2). -/
theorem polar_bond_from_distinct_zeff (Z₁ Z₂ : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (hZ₁ : 0 < Z₁)
    (hzeff : Binding.valenceSlaterEffectiveCharge Z₁ < Binding.valenceSlaterEffectiveCharge Z₂)
    (hperiod : Aufbau.topPrincipal Z₁ = Aufbau.topPrincipal Z₂) :
    0 < bondIonicCharacterFromCharge Z₁ Z₂ μ := by
  unfold bondIonicCharacterFromCharge electronegativityFromCharge
  have hn : (Aufbau.topPrincipal Z₁ : ℝ) ≠ 0 := by
    have hnat : 0 < Aufbau.topPrincipal Z₁ :=
      Nat.lt_of_lt_of_le (by decide : 0 < 1) (Aufbau.topPrincipal_ge_one Z₁ hZ₁)
    exact_mod_cast ne_of_gt hnat
  have hz1 : 0 ≤ Binding.valenceSlaterEffectiveCharge Z₁ := le_trans zero_le_one
    (Binding.valenceSlaterEffectiveCharge_ge_one Z₁)
  have hpol := Electronegativity.polar_bond_of_distinct_zEff μ (Binding.valenceSlaterEffectiveCharge Z₁)
    (Binding.valenceSlaterEffectiveCharge Z₂) (Aufbau.topPrincipal Z₁ : ℝ) hμ hn hz1 hzeff
  simpa [electronegativityFromCharge, hperiod] using hpol

/-! ## Dynamic binding slots from `Z` -/

/-- Compton triplet for finite-site dynamic binding readout, from discharge period. -/
def comptonTripletFromCharge (Z : ℕ) : DynamicBinding.ComptonTriplet :=
  if Z ≤ 1 then DynamicBinding.comptonTripletH2
  else if Aufbau.topPrincipal Z ≤ 2 then DynamicBinding.comptonTripletHeavyHydride
  else
    { m0 := referenceM + (Aufbau.topPrincipal Z - 3)
      m1 := referenceM + 1 + (Aufbau.topPrincipal Z - 3)
      m2 := referenceM }

theorem comptonTripletFromCharge_hydrogen :
    comptonTripletFromCharge 1 = DynamicBinding.comptonTripletH2 := by
  unfold comptonTripletFromCharge
  simp

theorem comptonTripletFromCharge_lithium :
    comptonTripletFromCharge 3 = DynamicBinding.comptonTripletHeavyHydride := by
  unfold comptonTripletFromCharge DynamicBinding.comptonTripletHeavyHydride
  have h : Aufbau.topPrincipal 3 = 2 := by decide
  simp [h, referenceM]

open HqivSpine.Physics.ContinuousHorizon

/-- Dynamic binding readout scaffold for atom `Z` at a supplied bond surplus. -/
noncomputable def dynamicReadoutFromCharge (Z : ℕ) (surplus : ℝ) : DynamicBinding.DynamicBindingReadout :=
  { eta := 1
    surplus := surplus
    vevGeomean := DynamicBinding.tuftVevGeometricMean (comptonTripletFromCharge Z)
    kappa := DynamicBinding.dynamicBindingCurvatureAtXi xiLockin }

theorem dynamicReadoutFromCharge_factorization (Z : ℕ) (surplus : ℝ) :
    DynamicBinding.dynamicBindingCore (dynamicReadoutFromCharge Z surplus) =
      surplus * DynamicBinding.tuftVevGeometricMean (comptonTripletFromCharge Z) *
        DynamicBinding.dynamicBindingCurvatureAtXi xiLockin := by
  unfold dynamicReadoutFromCharge DynamicBinding.dynamicBindingCore
  ring

/-! ## Tie to discharge registry -/

/-- `AtomDischarge` observables coincide with the first-principles `atomSpec` projection. -/
theorem atomDischargeObs_eq_spec (Z : ℕ) (h : 0 < Z) :
    (AtomDischarge.atomDischargeObs Z).period = (atomSpec Z h).period ∧
      (AtomDischarge.atomDischargeObs Z).valenceCount = (atomSpec Z h).valenceCount := by
  constructor <;> rfl

/-- **C–O is polar** from derived valence `Z_eff` (`3.25 < 4.55`) at period `2`. -/
theorem carbon_oxygen_bond_polar (μ : ℝ) (hμ : 0 < μ) :
    0 < bondIonicCharacterFromCharge 6 8 μ := by
  have hzeff : Binding.valenceSlaterEffectiveCharge 6 < Binding.valenceSlaterEffectiveCharge 8 := by
    unfold Binding.valenceSlaterEffectiveCharge Binding.slaterEffectiveChargeAtShell
      Binding.slaterShieldFromShellCounts
    rw [Aufbau.carbon_valence.1, Aufbau.oxygen_valence.1,
      Binding.slaterAdjacentShell_eq, Binding.slaterDeepShell_eq, Binding.slaterSameShell_eq]
    obtain ⟨hc1, hc2⟩ := Aufbau.carbon_shell_counts
    obtain ⟨ho1, ho2⟩ := Aufbau.oxygen_shell_counts
    simp only [Finset.sum_range_succ, hc1, hc2, ho1, ho2]
    norm_num
  apply polar_bond_from_distinct_zeff 6 8 μ hμ (by decide) hzeff Aufbau.carbon_valence.1

/-! ## Diatomic dynamic binding from two charges -/

/-- Compton triplet for a heteronuclear diatomic: heavy partner on discharge period, light on lock-in. -/
def comptonTripletFromDiatomic (Z₁ Z₂ : ℕ) : DynamicBinding.ComptonTriplet :=
  if min Z₁ Z₂ ≤ 1 then
    if max Z₁ Z₂ ≤ 3 then DynamicBinding.comptonTripletHeavyHydride
    else DynamicBinding.comptonTripletH2O
  else comptonTripletFromCharge (max Z₁ Z₂)

theorem comptonTripletFromDiatomic_lih :
    comptonTripletFromDiatomic 3 1 = DynamicBinding.comptonTripletLiH := by
  unfold comptonTripletFromDiatomic DynamicBinding.comptonTripletLiH
  simp

theorem comptonTripletFromDiatomic_h2o :
    comptonTripletFromDiatomic 8 1 = DynamicBinding.comptonTripletH2O := by
  unfold comptonTripletFromDiatomic DynamicBinding.comptonTripletH2O
  simp

/-- Bond-mode surplus on shell indices derived from the heavier partner's period. -/
def diatomicShellIndices (Z₁ Z₂ : ℕ) : ℕ × ℕ × ℕ :=
  let p := Aufbau.topPrincipal (max Z₁ Z₂)
  (referenceM + p, referenceM + max 0 (p - 1), referenceM)

noncomputable def diatomicBondSurplusFromCharge (Z₁ Z₂ : ℕ) : ℝ :=
  let (mt, m1, m2) := diatomicShellIndices Z₁ Z₂
  DynamicBinding.diatomicBondSurplus mt m1 m2

theorem diatomicBondSurplusFromCharge_lih :
    diatomicBondSurplusFromCharge 3 1 = DynamicBinding.lihBondSurplus := by
  unfold diatomicBondSurplusFromCharge diatomicShellIndices DynamicBinding.lihBondSurplus
    DynamicBinding.diatomicBondSurplus
  have h : Aufbau.topPrincipal 3 = 2 := by decide
  simp [h, referenceM]

/-- Dynamic binding readout for a diatomic `(Z₁, Z₂)` at derived shell surplus. -/
noncomputable def dynamicReadoutFromDiatomic (Z₁ Z₂ : ℕ) : DynamicBinding.DynamicBindingReadout :=
  { eta := 1
    surplus := diatomicBondSurplusFromCharge Z₁ Z₂
    vevGeomean := DynamicBinding.tuftVevGeometricMean (comptonTripletFromDiatomic Z₁ Z₂)
    kappa := DynamicBinding.dynamicBindingCurvatureAtXi xiLockin }

theorem dynamicReadoutFromDiatomic_factorization (Z₁ Z₂ : ℕ) :
    DynamicBinding.dynamicBindingCore (dynamicReadoutFromDiatomic Z₁ Z₂) =
      diatomicBondSurplusFromCharge Z₁ Z₂ *
        DynamicBinding.tuftVevGeometricMean (comptonTripletFromDiatomic Z₁ Z₂) *
          DynamicBinding.dynamicBindingCurvatureAtXi xiLockin := by
  unfold dynamicReadoutFromDiatomic DynamicBinding.dynamicBindingCore
  ring

/-- **LiH readout** matches the legacy heavy-hydride scaffold. -/
theorem dynamicReadoutFromDiatomic_lih_eq :
    dynamicReadoutFromDiatomic 3 1 =
      DynamicBinding.lihDynamicReadout DynamicBinding.lihBondSurplus := by
  unfold dynamicReadoutFromDiatomic DynamicBinding.lihDynamicReadout
  rw [diatomicBondSurplusFromCharge_lih, comptonTripletFromDiatomic_lih]

/-- When shell-aggregate and indexed Slater routes agree, discharge binding matches `bindingHartreeFromCharge`. -/
theorem bindingHartreeFromCharge_eq_discharge (Z : ℕ) (μ : ℝ) (h : 0 < Z)
    (hzeff : Binding.valenceSlaterEffectiveCharge Z =
      Binding.slaterEffectiveChargeAufbau Z ⟨Z - 1, by omega⟩) :
    AtomDischarge.electronicBindingHartree Z μ = bindingHartreeFromCharge Z μ := by
  dsimp [AtomDischarge.electronicBindingHartree, bindingHartreeFromCharge, Binding.valenceBindingHartree,
    Binding.atomicSiteBindingHartree, AtomDischarge.atomDischargeObs, Binding.slaterEffectiveChargeAufbau]
  rw [dif_pos h, hzeff]
  rfl

theorem bindingHartreeFromCharge_eq_discharge_sodium (μ : ℝ) :
    AtomDischarge.electronicBindingHartree 11 μ = bindingHartreeFromCharge 11 μ :=
  bindingHartreeFromCharge_eq_discharge 11 μ (by decide)
    Binding.valenceSlaterEffectiveCharge_eq_aufbau_sodium

/-- Pauling ionic fraction from two nuclear charges and reduced mass `μ`. -/
def bondPaulingIonicFractionFromCharge (Z₁ Z₂ : ℕ) (μ : ℝ) : ℝ :=
  Electronegativity.bondPaulingIonicFraction (electronegativityFromCharge Z₁ μ)
    (electronegativityFromCharge Z₂ μ)

theorem bondPaulingIonicFractionFromCharge_homonuclear (Z : ℕ) (μ : ℝ) :
    bondPaulingIonicFractionFromCharge Z Z μ = 0 := by
  unfold bondPaulingIonicFractionFromCharge electronegativityFromCharge
  exact Electronegativity.bondPaulingIonicFraction_homonuclear _

/-! ## Polyatomic readout: water from `(Z_O, Z_H, Z_H)` -/

/-- Triatomic `(Z₁, Z₂, Z₃) →` bond specification (heavy centre + two light partners). -/
structure TriatomicBondSpec where
  zCentre : ℕ
  zLight : ℕ
  periodCentre : ℕ
  chiCentre : ℝ
  chiLight : ℝ
  ionicCharacter : ℝ

/-- Canonical water readout: oxygen `8` with two hydrogens `1`. -/
def waterBondSpec (μ : ℝ) : TriatomicBondSpec :=
  { zCentre := 8
    zLight := 1
    periodCentre := Aufbau.topPrincipal 8
    chiCentre := electronegativityFromCharge 8 μ
    chiLight := electronegativityFromCharge 1 μ
    ionicCharacter := bondIonicCharacterFromCharge 8 1 μ }

theorem waterBondSpec_period : (waterBondSpec μ).periodCentre = 2 := by
  unfold waterBondSpec
  exact Aufbau.oxygen_valence.1

/-- Compton triplet for a triatomic with one heavy centre and two hydrogens. -/
def comptonTripletFromTriatomic (Zc Zl : ℕ) : DynamicBinding.ComptonTriplet :=
  if Zl ≤ 1 then DynamicBinding.comptonTripletH2O
  else comptonTripletFromDiatomic Zc Zl

theorem comptonTripletFromTriatomic_water :
    comptonTripletFromTriatomic 8 1 = DynamicBinding.comptonTripletH2O := by
  unfold comptonTripletFromTriatomic
  simp

/-- Bond surplus for O–H–O from the heavy centre's period. -/
def triatomicShellIndices (Zc Zl : ℕ) : ℕ × ℕ × ℕ := diatomicShellIndices Zc Zl

noncomputable def triatomicBondSurplusFromCharge (Zc Zl : ℕ) : ℝ :=
  let (mt, m1, m2) := triatomicShellIndices Zc Zl
  DynamicBinding.diatomicBondSurplus mt m1 m2

theorem triatomicBondSurplusFromCharge_water :
    triatomicBondSurplusFromCharge 8 1 = DynamicBinding.h2oBondSurplus := by
  unfold triatomicBondSurplusFromCharge triatomicShellIndices diatomicShellIndices
    DynamicBinding.h2oBondSurplus DynamicBinding.diatomicBondSurplus
  have h : Aufbau.topPrincipal 8 = 2 := Aufbau.oxygen_valence.1
  simp [h, referenceM]

/-- Dynamic binding readout for water `(8, 1, 1)` from nuclear charges alone. -/
noncomputable def dynamicReadoutFromWater : DynamicBinding.DynamicBindingReadout :=
  { eta := 1
    surplus := triatomicBondSurplusFromCharge 8 1
    vevGeomean := DynamicBinding.tuftVevGeometricMean (comptonTripletFromTriatomic 8 1)
    kappa := DynamicBinding.dynamicBindingCurvatureAtXi xiLockin }

theorem dynamicReadoutFromWater_eq_scaffold :
    dynamicReadoutFromWater =
      DynamicBinding.h2oDynamicReadout DynamicBinding.h2oBondSurplus := by
  unfold dynamicReadoutFromWater DynamicBinding.h2oDynamicReadout
  rw [triatomicBondSurplusFromCharge_water, comptonTripletFromTriatomic_water]

theorem dynamicReadoutFromWater_factorization :
    DynamicBinding.dynamicBindingCore dynamicReadoutFromWater =
      triatomicBondSurplusFromCharge 8 1 *
        DynamicBinding.tuftVevGeometricMean (comptonTripletFromTriatomic 8 1) *
          DynamicBinding.dynamicBindingCurvatureAtXi xiLockin := by
  unfold dynamicReadoutFromWater DynamicBinding.dynamicBindingCore
  ring

end

end HqivSpine.Chemistry.Atom
