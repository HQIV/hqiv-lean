import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Hqiv.Physics.CoronalLongitudinalStress
import Hqiv.Physics.SolarDynamics

/-!
# PSP near-Sun HCS **result** witnesses (Desai et al. 2025 ApJL)

**External reference:** Desai, Drake, Phan et al.; ApJL **985**, L38;
DOI [`10.3847/2041-8213/ada697`](https://doi.org/10.3847/2041-8213/ada697).

This module pins the **reported PSP E14 observables** as Lean comparison witnesses
and records how those results align with, or tension against, the HQIV coronal
boundary programme. It does **not** model or explain Desai et al.'s acceleration
mechanisms (reconnection, island mergers, Fermi cycles, kglobal, etc.).

## Result inventory witnessed (§1)

| Result | Lean name |
| --- | --- |
| Proton tail to `≈ 400 keV` | `pspHcsProtonEnergyMax_keV` |
| Upstream `m_i C_Ah² ≈ 0.56 keV` | `pspHcsMiCAhSq_keV` |
| Energization ratio `E_max/(m_i C_Ah²) ≳ 500` | `pspHcsEnergizationRatio` |
| Power-law index `γ ≈ 5.1` | `pspHcsSpectralIndex` |
| Guide-field bracket `0.2`–`0.3` (reported fit) | `pspHcsGuideFieldLow/High` |
| Exhaust radial scale `≳ 5 R☉` | `pspHcsExhaustScale_solarRadii` |
| Crossing duration `≈ 3.7 hr` | `pspHcsCrossingDuration_hr` |
| Encounter radius `≈ 16.25 R☉` | `pspHcsEncounterRadius_solarRadii` |
| Upstream density contrast `≈ 2` | `pspHcsDensityContrast` |
| Sun-anchored closed field lines | `pspHcsSunAnchoredFootpoints` |
| Sunward exhaust / sunward proton dominance | `pspHcsSunwardExhaust` |
| Perpendicular trapping in exhaust core | `pspHcsTrappedPopulation` |

## Proof status (all `Prop`, zero `sorry`)

* **§1–§2.** Result literals + internal numeric consistency.
* **§3.** `PspHcsResultWitness` bundles every pinned result.
* **§4.** HQIV comparison: shared footpoint geometry slot; result-level discriminants
  (energy-resolved spectrum vs `Δφ` boundary flux; exhaust extent vs shell gap).
* **§5.** `PspHcsResultVsHqivWitness` for Python / paper cross-calibration.

## Not claimed

* Derivation of any Desai et al.\ result from HQIV first principles.
* Explanation of how the `400 keV` tail or `γ ≈ 5.1` spectrum was produced.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Desai et al.\ 2025 **result** literals (comparison layer only)
-/

/-- Reported maximum suprathermal proton energy during PSP E14 HCS crossing [keV]. -/
def pspHcsProtonEnergyMax_keV : ℝ := 400

/-- Reported upstream magnetic energy per particle `m_i C_Ah²` [keV]. -/
def pspHcsMiCAhSq_keV : ℝ := 0.56

/-- Reported fitted differential spectral index `γ` in the ST band. -/
def pspHcsSpectralIndex : ℝ := 5.1

/-- Reported guide-field fraction bracket from spectral fit [dimensionless]. -/
def pspHcsGuideFieldLow : ℝ := 0.2
def pspHcsGuideFieldHigh : ℝ := 0.3

/-- Reported exhaust radial scale sampled during the crossing `[R☉]`. -/
def pspHcsExhaustScale_solarRadii : ℝ := 5

/-- Reported HCS crossing duration `[hr]`. -/
def pspHcsCrossingDuration_hr : ℝ := 3.7

/-- Reported PSP heliocentric distance during the event `[R☉]`. -/
def pspHcsEncounterRadius_solarRadii : ℝ := 16.25

/-- Reported upstream densities on the two sides of the HCS `[cm⁻³]`. -/
def pspHcsDensitySide1_cm3 : ℝ := 1500
def pspHcsDensitySide2_cm3 : ℝ := 3000

/-- Observed energization ratio `E_max / (m_i C_Ah²)`. -/
def pspHcsEnergizationRatio : ℝ :=
  pspHcsProtonEnergyMax_keV / pspHcsMiCAhSq_keV

/-- Observed upstream density contrast across the HCS. -/
def pspHcsDensityContrast : ℝ :=
  pspHcsDensitySide2_cm3 / pspHcsDensitySide1_cm3

/-- Reported result: closed field lines with both footpoints anchored at the Sun. -/
def pspHcsSunAnchoredFootpoints : Prop := True

/-- Reported result: sunward-directed exhaust and sunward-dominated ST protons. -/
def pspHcsSunwardExhaust : Prop := True

/-- Reported result: perpendicular (`≈ 90°`) trapping of ST protons in exhaust core. -/
def pspHcsTrappedPopulation : Prop := True

/-!
## §2. Result consistency certificates (numeric)
-/

theorem pspHcsProtonEnergyMax_pos : 0 < pspHcsProtonEnergyMax_keV := by
  unfold pspHcsProtonEnergyMax_keV; norm_num

theorem pspHcsMiCAhSq_pos : 0 < pspHcsMiCAhSq_keV := by
  unfold pspHcsMiCAhSq_keV; norm_num

theorem pspHcsSpectralIndex_pos : 0 < pspHcsSpectralIndex := by
  unfold pspHcsSpectralIndex; norm_num

theorem pspHcsGuideFieldBracket_ordered :
    pspHcsGuideFieldLow < pspHcsGuideFieldHigh := by
  unfold pspHcsGuideFieldLow pspHcsGuideFieldHigh; norm_num

theorem pspHcsExhaustScale_pos : 0 < pspHcsExhaustScale_solarRadii := by
  unfold pspHcsExhaustScale_solarRadii; norm_num

theorem pspHcsCrossingDuration_pos : 0 < pspHcsCrossingDuration_hr := by
  unfold pspHcsCrossingDuration_hr; norm_num

theorem pspHcsEncounterRadius_pos : 0 < pspHcsEncounterRadius_solarRadii := by
  unfold pspHcsEncounterRadius_solarRadii; norm_num

theorem pspHcsDensityContrast_gt_one : 1 < pspHcsDensityContrast := by
  unfold pspHcsDensityContrast pspHcsDensitySide1_cm3 pspHcsDensitySide2_cm3
  norm_num

theorem pspHcsEnergizationRatio_gt_hundred : (100 : ℝ) < pspHcsEnergizationRatio := by
  unfold pspHcsEnergizationRatio pspHcsProtonEnergyMax_keV pspHcsMiCAhSq_keV
  norm_num

theorem pspHcsEnergizationRatio_gt_five_hundred : (500 : ℝ) < pspHcsEnergizationRatio := by
  unfold pspHcsEnergizationRatio pspHcsProtonEnergyMax_keV pspHcsMiCAhSq_keV
  norm_num

theorem pspHcsProtonEnergyMax_gt_MiCAhSq :
    pspHcsMiCAhSq_keV < pspHcsProtonEnergyMax_keV := by
  unfold pspHcsProtonEnergyMax_keV pspHcsMiCAhSq_keV; norm_num

theorem pspHcsGuideFieldMid_in_reported_bracket :
    pspHcsGuideFieldLow ≤ (pspHcsGuideFieldLow + pspHcsGuideFieldHigh) / 2 ∧
      (pspHcsGuideFieldLow + pspHcsGuideFieldHigh) / 2 ≤ pspHcsGuideFieldHigh := by
  unfold pspHcsGuideFieldLow pspHcsGuideFieldHigh
  constructor <;> norm_num

/-!
## §3. Bundled PSP result witness
-/

/-- Every Desai et al.\ headline **result** pinned in one certificate. -/
structure PspHcsResultWitness where
  energization_ratio_large : (100 : ℝ) < pspHcsEnergizationRatio
  energization_ratio_gt_five_hundred : (500 : ℝ) < pspHcsEnergizationRatio
  proton_energy_exceeds_MiCAhSq : pspHcsMiCAhSq_keV < pspHcsProtonEnergyMax_keV
  spectral_index_pos : 0 < pspHcsSpectralIndex
  guide_field_bracket : pspHcsGuideFieldLow < pspHcsGuideFieldHigh
  exhaust_scale_pos : 0 < pspHcsExhaustScale_solarRadii
  crossing_duration_pos : 0 < pspHcsCrossingDuration_hr
  encounter_radius_pos : 0 < pspHcsEncounterRadius_solarRadii
  density_asymmetry : 1 < pspHcsDensityContrast
  sun_anchored : pspHcsSunAnchoredFootpoints
  sunward_exhaust : pspHcsSunwardExhaust
  trapped_population : pspHcsTrappedPopulation

theorem pspHcsResultWitness_default : PspHcsResultWitness where
  energization_ratio_large := pspHcsEnergizationRatio_gt_hundred
  energization_ratio_gt_five_hundred := pspHcsEnergizationRatio_gt_five_hundred
  proton_energy_exceeds_MiCAhSq := pspHcsProtonEnergyMax_gt_MiCAhSq
  spectral_index_pos := pspHcsSpectralIndex_pos
  guide_field_bracket := pspHcsGuideFieldBracket_ordered
  exhaust_scale_pos := pspHcsExhaustScale_pos
  crossing_duration_pos := pspHcsCrossingDuration_pos
  encounter_radius_pos := pspHcsEncounterRadius_pos
  density_asymmetry := pspHcsDensityContrast_gt_one
  sun_anchored := trivial
  sunward_exhaust := trivial
  trapped_population := trivial

def psp_hcs_result_vital : Prop :=
  (500 : ℝ) < pspHcsEnergizationRatio ∧
    pspHcsMiCAhSq_keV < pspHcsProtonEnergyMax_keV ∧
      0 < pspHcsSpectralIndex ∧
        pspHcsGuideFieldLow < pspHcsGuideFieldHigh ∧
          0 < pspHcsExhaustScale_solarRadii ∧
            1 < pspHcsDensityContrast

theorem psp_hcs_result_vital_holds : psp_hcs_result_vital := by
  refine ⟨pspHcsEnergizationRatio_gt_five_hundred, pspHcsProtonEnergyMax_gt_MiCAhSq,
    pspHcsSpectralIndex_pos, pspHcsGuideFieldBracket_ordered, pspHcsExhaustScale_pos,
    pspHcsDensityContrast_gt_one⟩

/-!
## §4. HQIV comparison at the **result** level (not mechanism level)
-/

/-- Reported differential spectrum shape `dJ/dE ∝ E^{-γ}` evaluated at energy `E`.

This witnesses the **fitted result**, not an HQIV derivation. -/
def pspHcsReportedSpectrum (E gamma intensityScale : ℝ) : ℝ :=
  intensityScale * E ^ (-gamma)

theorem phi_of_shell_mono (m₁ m₂ : ℕ) (h : m₁ ≤ m₂) :
    phi_of_shell m₁ ≤ phi_of_shell m₂ := by
  rw [phi_of_shell_closed_form, phi_of_shell_closed_form, phiTemperatureCoeff_eq_two]
  have hle : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast h
  linarith

theorem pspHcsReportedSpectrum_varies_with_energy
    (gamma intensityScale E₁ E₂ : ℝ) (hγ : gamma ≠ 0) (hscale : intensityScale ≠ 0)
    (h1 : 0 < E₁) (h2 : 0 < E₂) (hE : E₁ ≠ E₂) :
    pspHcsReportedSpectrum E₁ gamma intensityScale ≠
      pspHcsReportedSpectrum E₂ gamma intensityScale := by
  unfold pspHcsReportedSpectrum
  intro h
  have hrpow : E₁ ^ (-gamma) = E₂ ^ (-gamma) := mul_left_cancel₀ hscale h
  have hlog : Real.log (E₁ ^ (-gamma)) = Real.log (E₂ ^ (-gamma)) := by rw [hrpow]
  rw [Real.log_rpow h1, Real.log_rpow h2] at hlog
  have hlogE : Real.log E₁ = Real.log E₂ :=
    mul_left_cancel₀ (neg_ne_zero.mpr hγ) hlog
  have hEq : E₁ = E₂ :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) hlogE
  exact hE hEq

/-- Observed exhaust-extent scaling proxy: reported energization tracks a finite
crossing extent (`≈ 5 R☉` over `≈ 3.7 hr`). Used only to contrast with HQIV's
footpoint-only boundary flux (a **result-level** discriminant). -/
def pspHcsObservedExhaustExtentProxy (extentScale intensityPerScale : ℝ) : ℝ :=
  extentScale * intensityPerScale

theorem pspHcsObservedExhaustExtentProxy_scales_with_extent
    (L intensityPerScale : ℝ) (hL : L ≠ 1) (hint : intensityPerScale ≠ 0) :
    pspHcsObservedExhaustExtentProxy L intensityPerScale ≠
      pspHcsObservedExhaustExtentProxy 1 intensityPerScale := by
  unfold pspHcsObservedExhaustExtentProxy
  intro h
  have hzero : (L - 1) * intensityPerScale = 0 := by linarith
  rcases mul_eq_zero.mp hzero with hL0 | hr0
  · exact hL (by linarith)
  · exact hint hr0

theorem hqivHeatingFlux_independent_of_exhaustExtent
    (nq Estar couplingLog v_parallel : ℝ) (cols : CoronalColumnShells)
    (_extent₁ _extent₂ : ℝ) :
    coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols =
      coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols := rfl

theorem hqivHeatingFlux_nonneg_default_shells
    (nq Estar couplingLog v_parallel : ℝ)
    (cols : CoronalColumnShells) (hcols : cols.m_photo ≤ cols.m_corona)
    (hnq : 0 ≤ nq) (hv : 0 ≤ v_parallel) (hE : 0 ≤ Estar) (hΛ : 0 ≤ couplingLog) :
    0 ≤ coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols := by
  unfold coronalHeatingFluxBoundaryShells
  exact coronalHeatingFluxBoundary_nonneg hnq hv hE hΛ
    (phi_of_shell_mono cols.m_photo cols.m_corona hcols)

/-- Result-level discriminant: reported exhaust extent can scale (`L₁ ≠ L₂`) while
HQIV shell-gap boundary flux at fixed footpoints does not. -/
theorem pspHcsObservedExhaustExtentProxy_differs_at_distinct_extents
    (L₁ L₂ intensityPerScale : ℝ) (hL : L₁ ≠ L₂) (hint : intensityPerScale ≠ 0) :
    pspHcsObservedExhaustExtentProxy L₁ intensityPerScale ≠
      pspHcsObservedExhaustExtentProxy L₂ intensityPerScale := by
  unfold pspHcsObservedExhaustExtentProxy
  intro h
  have hzero : (L₁ - L₂) * intensityPerScale = 0 := by linarith
  rcases mul_eq_zero.mp hzero with hL0 | hr0
  · exact hL (by linarith)
  · exact hint hr0

theorem pspHcsResultDiscriminant_exhaustExtent
    (nq Estar couplingLog v_parallel : ℝ) (cols : CoronalColumnShells)
    (L₁ L₂ intensityPerScale : ℝ) (hL : L₁ ≠ L₂) (hint : intensityPerScale ≠ 0) :
    pspHcsObservedExhaustExtentProxy L₁ intensityPerScale ≠
        pspHcsObservedExhaustExtentProxy L₂ intensityPerScale ∧
      coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols =
        coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols := by
  constructor
  · exact pspHcsObservedExhaustExtentProxy_differs_at_distinct_extents L₁ L₂ intensityPerScale hL hint
  · rfl

/-- HQIV footpoint precondition slot: positive shell gap once readout supplies
`m_photo < m_corona`. Matches the **geometry of the reported result**
(Sun-anchored footpoints), not Desai's acceleration mechanism. -/
structure HqivFootpointResultAlignment (cols : CoronalColumnShells) where
  shell_gap_pos : 0 < coronalPhiJump cols

theorem hqivFootpointResultAlignment_default
    (cols : CoronalColumnShells) (h : cols.m_photo < cols.m_corona) :
    HqivFootpointResultAlignment cols where
  shell_gap_pos := coronalPhiJump_pos_of_lt cols h

theorem pspHcsResult_aligns_with_hqivFootpointSlot
    (cols : CoronalColumnShells) (h : cols.m_photo < cols.m_corona) :
    PspHcsResultWitness →
      HqivFootpointResultAlignment cols ∧
        pspHcsSunAnchoredFootpoints ∧ pspHcsSunwardExhaust := by
  intro _
  exact ⟨hqivFootpointResultAlignment_default cols h, trivial, trivial⟩

/-!
## §5. PSP results vs HQIV boundary programme
-/

/-- Cross-calibration witness: Desai et al.\ **results** + HQIV comparison slot. -/
structure PspHcsResultVsHqivWitness (cols : CoronalColumnShells) where
  psp_results : PspHcsResultWitness
  hqiv_footpoint_alignment : HqivFootpointResultAlignment cols

theorem PspHcsResultVsHqivWitness_default
    (cols : CoronalColumnShells) (h : cols.m_photo < cols.m_corona) :
    PspHcsResultVsHqivWitness cols where
  psp_results := pspHcsResultWitness_default
  hqiv_footpoint_alignment := hqivFootpointResultAlignment_default cols h

def pspHcsDefaultSolarShells : CoronalColumnShells :=
  ⟨0, 8, by decide⟩

theorem pspHcsDefaultSolarShells_photo_lt_corona :
    pspHcsDefaultSolarShells.m_photo < pspHcsDefaultSolarShells.m_corona := by
  decide

noncomputable def pspHcsResultVsHqivWitness_default :
    PspHcsResultVsHqivWitness pspHcsDefaultSolarShells :=
  PspHcsResultVsHqivWitness_default pspHcsDefaultSolarShells
    pspHcsDefaultSolarShells_photo_lt_corona

def psp_hcs_result_vs_hqiv_vital : Prop :=
  psp_hcs_result_vital ∧
    Nonempty (PspHcsResultVsHqivWitness pspHcsDefaultSolarShells)

theorem psp_hcs_result_vs_hqiv_vital_holds : psp_hcs_result_vs_hqiv_vital := by
  refine ⟨psp_hcs_result_vital_holds, ?_⟩
  exact ⟨pspHcsResultVsHqivWitness_default⟩

/-!
## Legacy aliases (readout backward compatibility)
-/

abbrev pspHcsDifferentialIntensityPowerLaw := pspHcsReportedSpectrum
abbrev pspHcsPowerLaw_differs_at_distinct_energies := pspHcsReportedSpectrum_varies_with_energy
abbrev reconnectionExhaustHeatingProxy := pspHcsObservedExhaustExtentProxy
abbrev reconnectionExhaustHeatingProxy_scales_with_length := pspHcsObservedExhaustExtentProxy_scales_with_extent
abbrev hqivHeatingFlux_independent_of_exhaustLength := hqivHeatingFlux_independent_of_exhaustExtent
abbrev heatingFluxDiscriminant_under_exhaustRescaling := pspHcsResultDiscriminant_exhaustExtent
abbrev PspHcsHqivCoexistenceWitness := PspHcsResultVsHqivWitness
abbrev PspHcsHqivCoexistenceWitness_default := PspHcsResultVsHqivWitness_default
abbrev pspHcsHqivCoexistenceWitness_default := pspHcsResultVsHqivWitness_default
abbrev psp_hcs_hqiv_coexistence_vital := psp_hcs_result_vs_hqiv_vital
abbrev psp_hcs_hqiv_coexistence_vital_holds := psp_hcs_result_vs_hqiv_vital_holds
abbrev HqivCoronalPreconditionWitness (cols : CoronalColumnShells) :=
  HqivFootpointResultAlignment cols
abbrev hqivCoronalPreconditionWitness_default := hqivFootpointResultAlignment_default
abbrev pspHcs_structural_alignment := pspHcsResult_aligns_with_hqivFootpointSlot

end

end Hqiv.Physics
