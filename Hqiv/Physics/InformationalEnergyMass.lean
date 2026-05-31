import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.ComptonHorizonPhase
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.LapseMassReadout

/-!
# Informational energy and mass readout gauges

## Units

* **Natural units** (default in this file): `c = ħ = T_Pl = 1`.  Energies and masses share
  one dimension; `E_tot = m + 1/Δx` is the paper relation in this gauge
  (`informationalEnergyTotal`, `informationalEnergyAtXi`).
* **SI** (`informationalEnergyTotal_si`): restore `m c²` and `ħ c / Δx` explicitly.
  Conversion lemmas do not identify SI masses with natural-unit readouts unless
  `c` and `ħ` are fixed externally.

## Informational energy

Paper / HQIV axiom (natural units):

`E_tot = m + 1 / Δx` with `Δx ≤ Θ_local`.

On the continuous horizon chart, `Θ_local(ξ) = T(ξ) = T_Pl / ξ`
(`thetaLocal_xi`, `AuxiliaryField`, `ContinuousXiPath.T_xi`).

## Readout gauges (sector convention)

* **Additive localization** (`additiveLocalization`) — **boson / EW closure**:
  observable mass equals the full informational energy `m_rest + 1/Θ_local(ξ)`.
  Matches `horizonLocalizedBosonMass` (localization in the energy budget, not in `N`).

* **Multiplicative lapse** (`multiplicativeLapse`) — **hadron / constituent**:
  observable mass is the **rest slot only**, divided by `HQVM_lapse Φ (φ(ξ)) t`.
  Localization is **not** added to `E_tot` here; it is assumed to sit in the lapse
  increment (`LapseMassReadout`).  Double-counting is avoided by using `hadronMassFromXi`
  instead of `massFromXi` for this sector.

* **Hybrid** (`hybrid`) — **order is fixed**: form the **full** `E_tot` (additive content),
  **then** divide by `N_lapse`.  Equivalently:
  `hybrid = additiveLocalization → multiplicativeLapse` on the same `E_tot`.
  We do **not** use “lapse first, then add `1/Θ`”; that alternate is recorded as
  `massReadoutLapseThenLocalization` for future study only.

## Gauge transformation

`GaugeEquivalenceWitness` and `gauge_transformation_localization_to_lapse` show when
the additive and multiplicative readouts agree after calibrating `m_rest` at fixed
`(ξ, Φ, t)`.
-/

namespace Hqiv.Physics

open Hqiv
open ContinuousXiPath

namespace InformationalEnergyMass

/-! ## Natural vs SI units -/

/-- Marker: definitions below use **natural units** (`c = ħ = T_Pl = 1`). -/
def usesNaturalUnits : Prop := True

theorem usesNaturalUnits_iff_true : usesNaturalUnits ↔ True :=
  Iff.intro (fun _ => trivial) (fun _ => trivial)

/-! ## Core informational energy -/

/-- Natural-units informational energy: rest slot plus localization `1/Δx`. -/
noncomputable def informationalEnergyTotal (m Δx : ℝ) : ℝ :=
  m + 1 / Δx

theorem informationalEnergy_natural_units (m Δx : ℝ) :
    informationalEnergyTotal m Δx = m + 1 / Δx := rfl

/-- SI informational energy `E = m c² + ħ c / Δx` (requires `Δx ≠ 0`). -/
noncomputable def informationalEnergyTotal_si (m c ħ Δx : ℝ) : ℝ :=
  m * c ^ 2 + ħ * c / Δx

theorem informationalEnergyTotal_si_eq (m c ħ Δx : ℝ) :
    informationalEnergyTotal_si m c ħ Δx = m * c ^ 2 + ħ * c / Δx := rfl

/-- Bridge: SI energy reduces to natural-units form when `c = ħ = 1` and `Δx` is the same. -/
theorem informationalEnergyTotal_si_to_natural
    (m Δx : ℝ) (hc : c = 1) (hh : ħ = 1) :
    informationalEnergyTotal_si m c ħ Δx = informationalEnergyTotal m Δx := by
  unfold informationalEnergyTotal_si informationalEnergyTotal
  simp [hc, hh]

/-- Local horizon length `Θ_local(ξ) = T(ξ)` on the continuous chart. -/
noncomputable def thetaLocal_xi (ξ : ℝ) : ℝ :=
  T_xi ξ

theorem thetaLocal_xi_eq_T_xi (ξ : ℝ) : thetaLocal_xi ξ = T_xi ξ := rfl

theorem thetaLocal_xi_chart (m : ℕ) :
    thetaLocal_xi (xiOfShell m) = T m := by
  rw [thetaLocal_xi_eq_T_xi, T_xi_chart]

/-- Minimal localization energy `1 / Θ_local(ξ)` (requires `ξ ≠ 0`). -/
noncomputable def localizationEnergy (ξ : ℝ) : ℝ :=
  1 / thetaLocal_xi ξ

theorem localizationEnergy_eq_inv_theta (ξ : ℝ) :
    localizationEnergy ξ = 1 / thetaLocal_xi ξ := rfl

theorem localizationEnergy_eq_xi_over_T_Pl (ξ : ℝ) (hξ : ξ ≠ 0) :
    localizationEnergy ξ = ξ / T_Pl := by
  unfold localizationEnergy thetaLocal_xi T_xi
  rw [T_Pl_eq]
  field_simp [hξ]

/-- Same localization slot as `ContinuousXiCoupling.localizationEnergyXi`. -/
theorem localizationEnergy_eq_localizationEnergyXi (ξ : ℝ) (hξ : ξ ≠ 0) :
    localizationEnergy ξ = localizationEnergyXi ξ := by
  rw [localizationEnergyXi_eq_xi_over_T_Pl ξ hξ, localizationEnergy_eq_xi_over_T_Pl ξ hξ]

/-- Total informational energy at horizon coordinate `ξ` with rest slot `m_rest`. -/
noncomputable def informationalEnergyAtXi (m_rest ξ : ℝ) : ℝ :=
  informationalEnergyTotal m_rest (thetaLocal_xi ξ)

theorem informationalEnergyAtXi_eq (m_rest ξ : ℝ) :
    informationalEnergyAtXi m_rest ξ = m_rest + localizationEnergy ξ := by
  unfold informationalEnergyAtXi informationalEnergyTotal localizationEnergy thetaLocal_xi
  rfl

/-! ## Readout gauges -/

/-- How observable mass is extracted from `E_tot`. -/
inductive MassReadoutGauge where
  | additiveLocalization
  | multiplicativeLapse
  /-- Full `E_tot` (rest + `1/Θ`), then divide by `N_lapse` (not lapse-then-localize). -/
  | hybrid

/--
**Implemented hybrid order:** `E_tot` with additive localization, then `÷ N_lapse`.
Not used: divide rest by lapse first, then add `1/Θ` (`massReadoutLapseThenLocalization`).
-/
noncomputable def massReadoutLapseThenLocalization (m_rest loc lapse : ℝ) : ℝ :=
  m_rest / lapse + loc

/-- Observable mass from total informational energy and readout gauge. -/
noncomputable def massFromInformationalEnergy
    (E_tot : ℝ) (gauge : MassReadoutGauge) (lapse : ℝ) : ℝ :=
  match gauge with
  | .additiveLocalization => E_tot
  | .multiplicativeLapse => E_tot / lapse
  | .hybrid => E_tot / lapse

theorem massFromInformationalEnergy_additive (E_tot lapse : ℝ) :
    massFromInformationalEnergy E_tot .additiveLocalization lapse = E_tot := rfl

theorem massFromInformationalEnergy_multiplicative (E_tot lapse : ℝ) :
    massFromInformationalEnergy E_tot .multiplicativeLapse lapse = E_tot / lapse := rfl

theorem massFromInformationalEnergy_hybrid_eq_additive_then_lapse (E_tot lapse : ℝ) :
    massFromInformationalEnergy E_tot .hybrid lapse =
      massFromInformationalEnergy
        (massFromInformationalEnergy E_tot .additiveLocalization 1) .multiplicativeLapse lapse := by
  simp [massFromInformationalEnergy]

theorem massFrom_multiplicative_unit_lapse (E : ℝ) :
    massFromInformationalEnergy E .multiplicativeLapse 1 = E := by
  simp [massFromInformationalEnergy, div_one]

/-- At unit lapse, additive and multiplicative gauges agree on the same `E_tot`. -/
theorem massReadout_additive_eq_multiplicative_when_lapse_one (E : ℝ) :
    massFromInformationalEnergy E .additiveLocalization 1 =
      massFromInformationalEnergy E .multiplicativeLapse 1 := by
  simp [massFromInformationalEnergy, div_one]

/-! ## Gauge transformation (localization ↔ lapse) -/

/--
Witness that additive localization and multiplicative lapse readouts coincide at the
same horizon slot once the rest mass is calibrated.

**Equality:** `m_rest + loc = m_rest / N_lapse` with `loc = 1/Θ_local(ξ)` in the
natural-units chart.
-/
structure GaugeEquivalenceWitness where
  m_rest : ℝ
  loc : ℝ
  lapse : ℝ
  h_lapse_ne_one : lapse ≠ 1
  h_mass_eq : m_rest + loc = m_rest / lapse

/--
Rest mass that equates additive (`m + loc`) and multiplicative (`m / N`) readouts
at fixed localization `loc` and lapse `N ≠ 1`:

`m_rest = loc · N / (1 - N)`  (requires `N ≠ 1`).
-/
noncomputable def m_rest_gauge_calibration (loc lapse : ℝ) (_hN : lapse ≠ 1) : ℝ :=
  loc * lapse / (1 - lapse)

theorem m_rest_gauge_calibration_add_loc
    (loc lapse : ℝ) (hN : lapse ≠ 1) (hl : lapse ≠ 0) :
    m_rest_gauge_calibration loc lapse hN + loc =
      m_rest_gauge_calibration loc lapse hN / lapse := by
  unfold m_rest_gauge_calibration
  have hone : (1 : ℝ) - lapse ≠ 0 := sub_ne_zero.mpr (Ne.symm hN)
  field_simp [hone, hl]
  ring

/-- Build a witness from `loc` and `N_lapse ≠ 1`. -/
noncomputable def gaugeEquivalenceWitness (loc lapse : ℝ) (hN : lapse ≠ 1) (hl : lapse ≠ 0) :
    GaugeEquivalenceWitness where
  m_rest := m_rest_gauge_calibration loc lapse hN
  loc := loc
  lapse := lapse
  h_lapse_ne_one := hN
  h_mass_eq := m_rest_gauge_calibration_add_loc loc lapse hN hl

/--
**Gauge transformation (core):** at calibrated `m_rest`, the additive readout on
`E_tot = m_rest + loc` equals the multiplicative readout on the rest slot only.
-/
theorem gauge_transformation_localization_to_lapse
    (loc lapse : ℝ) (hN : lapse ≠ 1) (hl : lapse ≠ 0) :
    massFromInformationalEnergy
        (m_rest_gauge_calibration loc lapse hN + loc) .additiveLocalization 1 =
      massFromInformationalEnergy
        (m_rest_gauge_calibration loc lapse hN) .multiplicativeLapse lapse := by
  have h := m_rest_gauge_calibration_add_loc loc lapse hN hl
  simp [massFromInformationalEnergy, h]

/-- At `N = 1`, gauges agree only if localization vanishes. -/
theorem gauge_equivalence_iff_loc_zero_at_unit_lapse
    (m_rest loc N : ℝ) (hN : N = 1) :
    (m_rest + loc = m_rest / N) ↔ loc = 0 := by
  subst hN
  constructor
  · intro h
    have : m_rest + loc = m_rest := by simpa [div_one] using h
    linarith
  · intro hloc
    simp [hloc, div_one]

/-! ## Continuous ξ particle readout -/

/-- Mass readout at continuous horizon coordinate `ξ_p` (coupling-solver output). -/
noncomputable def massFromXi
    (m_raw ξ_p Φ t : ℝ) (gauge : MassReadoutGauge) : ℝ :=
  massFromInformationalEnergy (informationalEnergyAtXi m_raw ξ_p) gauge (shellLapse_xi ξ_p Φ t)

theorem massFromXi_eq_massFromInformationalEnergy (m_raw ξ_p Φ t : ℝ) (gauge : MassReadoutGauge) :
    massFromXi m_raw ξ_p Φ t gauge =
      massFromInformationalEnergy (informationalEnergyAtXi m_raw ξ_p) gauge
        (shellLapse_xi ξ_p Φ t) := rfl

theorem massFromXi_chart (m_raw : ℝ) (m : ℕ) (Φ t : ℝ) (gauge : MassReadoutGauge) :
    massFromXi m_raw (xiOfShell m) Φ t gauge =
      massFromInformationalEnergy (informationalEnergyAtXi m_raw (xiOfShell m)) gauge
        (shellLapse m Φ t) := by
  unfold massFromXi
  rw [shellLapse_xi_chart]

/-! ## Bridges to existing mass modules -/

theorem xiOfShell_bosonClosure_eq_six :
    xiOfShell bosonClosureShell = 6 := by
  unfold xiOfShell
  rw [bosonClosureShell_eq_succ_reference, referenceM_eq_four]
  norm_num

theorem thetaLocal_xi_bosonClosure_eq_bosonClosureThetaLocal :
    thetaLocal_xi (xiOfShell bosonClosureShell) = bosonClosureThetaLocal := by
  rw [thetaLocal_xi_eq_T_xi, bosonClosureThetaLocal_value, xiOfShell_bosonClosure_eq_six]
  unfold T_xi T_Pl
  norm_num

theorem localizationEnergy_bosonClosure_eq_lowerBound :
    localizationEnergy (xiOfShell bosonClosureShell) = bosonLocalizationEnergyLowerBound := by
  unfold localizationEnergy bosonLocalizationEnergyLowerBound
  rw [thetaLocal_xi_bosonClosure_eq_bosonClosureThetaLocal]

theorem informationalEnergyAtXi_boson_eq_horizonLocalized (mass : ℝ) :
    informationalEnergyAtXi mass (xiOfShell bosonClosureShell) =
      horizonLocalizedBosonMass mass := by
  rw [informationalEnergyAtXi_eq, horizon_localization_layer_eq_add_raw,
    localizationEnergy_bosonClosure_eq_lowerBound]

theorem massFrom_additive_boson_eq_horizonLocalized (mass : ℝ) :
    massFromInformationalEnergy
      (informationalEnergyAtXi mass (xiOfShell bosonClosureShell))
      .additiveLocalization 1 =
      horizonLocalizedBosonMass mass := by
  rw [massFromInformationalEnergy_additive, informationalEnergyAtXi_boson_eq_horizonLocalized]

theorem lapseMassReadout_eq_multiplicative_gauge
    (raw : RawShellMass) (m : ℕ) (Φ t : ℝ) :
    lapseMassReadout raw m Φ t =
      massFromInformationalEnergy (raw m) .multiplicativeLapse (shellLapse m Φ t) := by
  unfold lapseMassReadout massFromInformationalEnergy shellLapse
  rfl

theorem lapseMassReadout_eq_additive_gauge_at_unit_lapse
    (raw : RawShellMass) (m : ℕ) (Φ t : ℝ) (hlapse : shellLapse m Φ t = 1) :
    lapseMassReadout raw m Φ t =
      massFromInformationalEnergy (raw m) .additiveLocalization 1 := by
  rw [lapseMassReadout_eq_multiplicative_gauge]
  simp [massFromInformationalEnergy, hlapse, div_one]

/-- When localization is folded into `E_tot`, additive gauge matches boson horizon layer. -/
theorem massFromXi_boson_additive_eq_horizonLocalized (m_raw : ℝ) (Φ t : ℝ) :
    massFromXi m_raw (xiOfShell bosonClosureShell) Φ t .additiveLocalization =
      horizonLocalizedBosonMass m_raw := by
  rw [massFromXi, massFromInformationalEnergy_additive, informationalEnergyAtXi_boson_eq_horizonLocalized]

/-- Hadron-style readout on the rest slot only (localization in lapse, not in `1/Θ`). -/
noncomputable def hadronMassFromXi (m_raw ξ_p Φ t : ℝ) : ℝ :=
  massFromInformationalEnergy m_raw .multiplicativeLapse (shellLapse_xi ξ_p Φ t)

theorem hadronMassFromXi_eq_lapseMassReadout
    (m_raw : ℝ) (m : ℕ) (Φ t : ℝ) :
    hadronMassFromXi m_raw (xiOfShell m) Φ t =
      lapseMassReadout (constantRawShellMass m_raw) m Φ t := by
  unfold hadronMassFromXi lapseMassReadout constantRawShellMass shellLapse_xi
    massFromInformationalEnergy shellLapse
  simp [phi_xi_chart]

/-- Hybrid at `ξ` applies boson-style `E_tot` then hadron-style lapse. -/
noncomputable def hybridMassFromXi (m_raw ξ_p Φ t : ℝ) : ℝ :=
  massFromInformationalEnergy (informationalEnergyAtXi m_raw ξ_p) .hybrid (shellLapse_xi ξ_p Φ t)

theorem hybridMassFromXi_eq_additive_then_lapse (m_raw ξ_p Φ t : ℝ) :
    hybridMassFromXi m_raw ξ_p Φ t =
      massFromInformationalEnergy (informationalEnergyAtXi m_raw ξ_p) .hybrid
        (shellLapse_xi ξ_p Φ t) := rfl

/--
Continuous-ξ gauge transformation: full `E_tot` readout (additive) equals rest-slot lapse
readout (multiplicative) at calibrated `m_rest`.
-/
theorem gauge_transformation_at_xi
    (ξ Φ t : ℝ) (hN : shellLapse_xi ξ Φ t ≠ 1) (hl : shellLapse_xi ξ Φ t ≠ 0) :
    massFromInformationalEnergy
        (informationalEnergyAtXi
          (m_rest_gauge_calibration (localizationEnergy ξ) (shellLapse_xi ξ Φ t) hN) ξ)
        .additiveLocalization 1 =
      massFromInformationalEnergy
        (m_rest_gauge_calibration (localizationEnergy ξ) (shellLapse_xi ξ Φ t) hN)
        .multiplicativeLapse (shellLapse_xi ξ Φ t) := by
  rw [informationalEnergyAtXi_eq]
  exact gauge_transformation_localization_to_lapse
    (localizationEnergy ξ) (shellLapse_xi ξ Φ t) hN hl

theorem gauge_transformation_at_xi_hadron_alias
    (ξ Φ t : ℝ) (hN : shellLapse_xi ξ Φ t ≠ 1) (hl : shellLapse_xi ξ Φ t ≠ 0) :
    massFromXi
      (m_rest_gauge_calibration (localizationEnergy ξ) (shellLapse_xi ξ Φ t) hN)
      ξ Φ t .additiveLocalization =
      hadronMassFromXi
        (m_rest_gauge_calibration (localizationEnergy ξ) (shellLapse_xi ξ Φ t) hN)
        ξ Φ t := by
  rw [massFromXi, hadronMassFromXi, massFromInformationalEnergy_additive]
  exact gauge_transformation_at_xi ξ Φ t hN hl

/-- At unit lapse, multiplicative readout returns the rest slot unchanged. -/
theorem multiplicative_rest_at_unit_lapse (m_rest ξ Φ t : ℝ)
    (hlapse : shellLapse_xi ξ Φ t = 1) :
    massFromInformationalEnergy m_rest .multiplicativeLapse (shellLapse_xi ξ Φ t) = m_rest := by
  rw [massFromInformationalEnergy_multiplicative, hlapse, div_one]

/-- When the solver row holds (`c₀ = target`), additive `E_tot` equals `2π · Ω_k(ξ_G)`. -/
theorem informationalEnergy_satisfied_when_row_holds (ξG c₀ : ℝ) (hξ : ξG ≠ 0) :
    c₀ = (informationalEnergyMassRow ξG).target →
      informationalEnergyAtXi c₀ ξG =
        twoPi * omegaKContinuous ξG xiLockin := by
  intro h
  rw [informationalEnergyAtXi_eq, h, informationalEnergyMassRow_target,
    localizationEnergy_eq_localizationEnergyXi ξG hξ]
  linarith

/-- Same row identity as a curvature-fraction readout: `E_tot / (2π) = Ω_k(ξ_G)`. -/
theorem informationalEnergy_over_twoPi_eq_omegaK_when_row_holds (ξG c₀ : ℝ) (hξ : ξG ≠ 0) :
    c₀ = (informationalEnergyMassRow ξG).target →
      informationalEnergyAtXi c₀ ξG / twoPi = omegaKContinuous ξG xiLockin := by
  intro h
  rw [informationalEnergy_satisfied_when_row_holds ξG c₀ hξ h]
  unfold twoPi
  field_simp [ne_of_gt Real.pi_pos]

end InformationalEnergyMass

end Hqiv.Physics
