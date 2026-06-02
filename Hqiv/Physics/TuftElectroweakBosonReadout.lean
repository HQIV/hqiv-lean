import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ContinuousXiMixingGeometry
import Hqiv.Physics.DoublePreferredAxis
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.WeakDoubletCarrierGaugeQuadratic
import Hqiv.Physics.QuarkSectorFromEWGauge
import Mathlib.Data.Real.Sqrt

namespace Hqiv.Physics

/-!
# Electroweak boson readout on the dynamic TUFT chart

Primary masses at horizon coordinate `ξ`:

* **W** — primary readout `M_W^{\mathrm{closure}} · \sqrt{v_{\mathrm{lock}}/v_{\mathrm{gauge}}}` times
  the heavy-gap scale (`tuftElectroweakScaleAtXi`), i.e.
  `tuftMW_atXi_GeV = M_W_derived · scale · tuftVevSqrtBridgeLockin`.
  The equivalent geometric-mean form `tuftMW_geometricMean_atXi_GeV` matches for every
  `ξ` and lock-in vev `vevLockin_MeV > 0` (`tuftMW_geometricMean_atXi_GeV_eq`).
* **Z** — W mass divided by `cos θ_W` with **geometric** `sin²θ_W` from the weak vs EM
  Gauss-shell detuned imprint (`ContinuousXiMixingGeometry`), not the naive
  `(g_SU2 + g_U1)` line that overshoots PDG.
* **Higgs** — primary readout `√(2λ) v(ξ)` with derived quartic `λ` from the scalar
  closure witness and **pinned electroweak vev** `v(ξ)`, plus a monogamy-weighted
  horizon-localization term `γ · (1 / Θ_{\mathrm{local}})` on the scalar portal.
  Raw `2 v_scalar` on the outer shell remains diagnostic.

The legacy `M_Z_derived = (1 + γ) M_W_derived` row remains in `DerivedGaugeAndLeptonSector`
as a diagnostic only.
-/

open ContinuousXiMixingGeometry

/-- Geometric Weinberg angle at lock-in: weak shell `electroweakPhiShell`, EM Gauss shell `emGaussShell`. -/
noncomputable def sin2ThetaWGeometricLockin : ℝ :=
  sin2ThetaWGeometricShell electroweakPhiShell emGaussShell

/-- `cos θ_W` from geometric `sin²θ_W` (lock-in mixing row). -/
noncomputable def cosThetaWGeometricLockin : ℝ :=
  Real.sqrt (1 - sin2ThetaWGeometricLockin)

/-- Vev / heavy-gap scale factor relative to the lock-in slice `ξ = 5`. -/
noncomputable def tuftElectroweakScaleAtXi (ξ : ℝ) : ℝ :=
  heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi xiLockin

/-- Geometric gauge-sector vev at lock-in: `M_W / g_SU2` (outer-closure normalization). -/
noncomputable def tuftGaugeVevAtLockin_GeV : ℝ :=
  M_W_derived / su2CouplingDerived

theorem su2CouplingDerived_pos : 0 < su2CouplingDerived := by
  unfold su2CouplingDerived trialityOrder
  norm_num

theorem gammaDerived_pos : 0 < gammaDerived := by
  unfold gammaDerived
  rw [alpha_eq_3_5]
  norm_num

theorem tuftGaugeVevAtLockin_GeV_eq :
    tuftGaugeVevAtLockin_GeV = (1176 : ℝ) / 5 := by
  unfold tuftGaugeVevAtLockin_GeV
  rw [boson_witness_M_W]
  unfold su2CouplingDerived trialityOrder
  norm_num

theorem tuftGaugeVevAtLockin_GeV_pos : 0 < tuftGaugeVevAtLockin_GeV := by
  rw [tuftGaugeVevAtLockin_GeV_eq]
  norm_num

/-- Sqrt bridge between closure gauge vev and lock-in electroweak vev (constant ratio). -/
noncomputable def tuftVevSqrtBridgeLockin (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  Real.sqrt ((vevLockin_MeV / 1000) / tuftGaugeVevAtLockin_GeV)

/-- Squared vev bridge (`b * b` avoids Lean parsing `f x ^ 2` as `f (x ^ 2)`). -/
noncomputable def tuftVevSqrtBridgeSq (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  let b := tuftVevSqrtBridgeLockin vevLockin_MeV
  b * b

/-- Pinned SM W line `g_{\mathrm{SU2}} v(ξ)` (GeV). -/
noncomputable def tuftMW_pinnedAtXi_GeV
    (ξ : ℝ) (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  su2CouplingDerived * (tuftVevAtXi_MeV ξ vevLockin_MeV / 1000)

/-- Dynamic W mass (GeV): closure × vev bridge × heavy-gap scale. -/
noncomputable def tuftMW_atXi_GeV
    (ξ : ℝ) (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  M_W_derived * tuftElectroweakScaleAtXi ξ * tuftVevSqrtBridgeLockin vevLockin_MeV

/-- Equivalent geometric-mean form: `scale · √(M_W^{\mathrm{closure}} M_W^{\mathrm{pinned}})`. -/
noncomputable def tuftMW_geometricMean_atXi_GeV
    (ξ : ℝ) (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  tuftElectroweakScaleAtXi ξ *
    Real.sqrt (M_W_derived * tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV)

/-- Dynamic Z mass (GeV) with geometric Weinberg mixing (supersedes naive `M_Z_derived`). -/
noncomputable def tuftMZ_atXi_GeV (ξ : ℝ) (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  tuftMW_atXi_GeV ξ vevLockin_MeV / cosThetaWGeometricLockin

/-- Raw scalar-closure Higgs (GeV): `2 v_scalar` with heavy-gap scale only. -/
noncomputable def tuftMH_scalarClosure_atXi_GeV (ξ : ℝ) : ℝ :=
  m_H_derived * tuftElectroweakScaleAtXi ξ

/-- Monogamy fraction of the boson-shell horizon-localization energy (GeV). -/
noncomputable def tuftMH_scalarMonogamyLocalization_GeV : ℝ :=
  gammaDerived * bosonLocalizationEnergyLowerBound

/-- Primary Higgs mass (GeV): `√(2 λ v²)` + scalar-portal localization. -/
noncomputable def tuftMH_atXi_GeV
    (ξ : ℝ) (vevLockin_MeV : ℝ := electroweakVev_MeV) : ℝ :=
  Real.sqrt (2 * higgsQuarticLambdaGaugeWitness) * (tuftVevAtXi_MeV ξ vevLockin_MeV / 1000) +
    tuftMH_scalarMonogamyLocalization_GeV

theorem higgsQuarticLambdaGaugeWitness_pos : 0 < higgsQuarticLambdaGaugeWitness := by
  unfold higgsQuarticLambdaGaugeWitness
  apply div_pos
  · rw [boson_witness_m_H]
    norm_num
  · apply mul_pos (by norm_num : 0 < (2 : ℝ))
    exact pow_pos vacuumExpectationValueGauge_pos 2

theorem tuftElectroweakScaleAtXi_lockin :
    tuftElectroweakScaleAtXi xiLockin = 1 := by
  unfold tuftElectroweakScaleAtXi
  have hgap : heavy_lepton_gap_at_xi xiLockin ≠ 0 := ne_of_gt (heavy_lepton_gap_at_xi_pos xiLockin (by
    rw [xiLockin_eq_five]; norm_num))
  field_simp [hgap]

theorem tuftVevSqrtBridgeLockin_pos (vevLockin_MeV : ℝ := electroweakVev_MeV)
    (hvev : 0 < vevLockin_MeV) : 0 < tuftVevSqrtBridgeLockin vevLockin_MeV := by
  unfold tuftVevSqrtBridgeLockin
  apply Real.sqrt_pos.mpr
  exact div_pos (div_pos hvev (by norm_num : 0 < (1000 : ℝ))) tuftGaugeVevAtLockin_GeV_pos

theorem tuftVevSqrtBridgeSq_pos (vevLockin_MeV : ℝ := electroweakVev_MeV)
    (hvev : 0 < vevLockin_MeV) : 0 < tuftVevSqrtBridgeSq vevLockin_MeV := by
  dsimp [tuftVevSqrtBridgeSq]
  exact mul_pos (tuftVevSqrtBridgeLockin_pos vevLockin_MeV hvev)
    (tuftVevSqrtBridgeLockin_pos vevLockin_MeV hvev)

theorem tuftVevSqrtBridgeSq_eq_sq (vevLockin_MeV : ℝ := electroweakVev_MeV) :
    tuftVevSqrtBridgeSq vevLockin_MeV =
      tuftVevSqrtBridgeLockin vevLockin_MeV * tuftVevSqrtBridgeLockin vevLockin_MeV := by
  dsimp [tuftVevSqrtBridgeSq]

theorem tuftMW_pinned_over_gaugeVev_eq_bridge_sq (vevLockin_MeV : ℝ := electroweakVev_MeV)
    (hvev : 0 < vevLockin_MeV) :
    tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV / tuftGaugeVevAtLockin_GeV =
      su2CouplingDerived * tuftVevSqrtBridgeSq vevLockin_MeV := by
  unfold tuftMW_pinnedAtXi_GeV tuftGaugeVevAtLockin_GeV
  rw [tuftVevAtXi_MeV_lockin vevLockin_MeV]
  dsimp [tuftVevSqrtBridgeSq, tuftVevSqrtBridgeLockin]
  simp only [su2CouplingDerived, trialityOrder]
  rw [tuftGaugeVevAtLockin_GeV_eq, boson_witness_M_W]
  have hratio_nonneg : 0 ≤ vevLockin_MeV * 5 / (1000 * 1176) := by positivity
  field_simp [show (392 : ℝ) / 5 ≠ 0 by norm_num, show (1176 : ℝ) ≠ 0 by norm_num,
    show (1000 : ℝ) ≠ 0 by norm_num]
  rw [Real.sq_sqrt hratio_nonneg]
  ring

theorem tuftMW_sqrt_body_eq_closure_times_bridge (vevLockin_MeV : ℝ := electroweakVev_MeV)
    (hvev : 0 < vevLockin_MeV) :
    Real.sqrt (M_W_derived * tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV) =
      M_W_derived * tuftVevSqrtBridgeLockin vevLockin_MeV := by
  have hpin := tuftMW_pinned_over_gaugeVev_eq_bridge_sq vevLockin_MeV hvev
  have hMW : M_W_derived = su2CouplingDerived * tuftGaugeVevAtLockin_GeV := by
    unfold tuftGaugeVevAtLockin_GeV
    field_simp [su2CouplingDerived_pos.ne']
  have hpinned :
      tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV =
        su2CouplingDerived * tuftGaugeVevAtLockin_GeV * tuftVevSqrtBridgeSq vevLockin_MeV := by
    rw [(div_eq_iff tuftGaugeVevAtLockin_GeV_pos.ne').mp hpin]
    ring
  have hbridge_nonneg : 0 ≤ tuftVevSqrtBridgeLockin vevLockin_MeV :=
    le_of_lt (tuftVevSqrtBridgeLockin_pos vevLockin_MeV hvev)
  have hsq :
      M_W_derived * tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV =
        M_W_derived ^ 2 * tuftVevSqrtBridgeSq vevLockin_MeV := by
    rw [hMW, hpinned]
    ring
  calc Real.sqrt (M_W_derived * tuftMW_pinnedAtXi_GeV xiLockin vevLockin_MeV)
      = Real.sqrt (M_W_derived ^ 2 * tuftVevSqrtBridgeSq vevLockin_MeV) := by rw [hsq]
    _ = M_W_derived * tuftVevSqrtBridgeLockin vevLockin_MeV := by
      have hMW_nonneg : 0 ≤ M_W_derived := le_of_lt M_W_derived_pos
      have hprod_nonneg : 0 ≤ M_W_derived * tuftVevSqrtBridgeLockin vevLockin_MeV :=
        mul_nonneg hMW_nonneg hbridge_nonneg
      have hsq' :
          (M_W_derived * tuftVevSqrtBridgeLockin vevLockin_MeV) ^ 2 =
            M_W_derived ^ 2 * tuftVevSqrtBridgeSq vevLockin_MeV := by
        rw [tuftVevSqrtBridgeSq_eq_sq vevLockin_MeV]
        ring
      rw [← Real.sqrt_sq hprod_nonneg, hsq']

theorem tuftMW_geometricMean_atXi_GeV_eq (ξ : ℝ)
    (vevLockin_MeV : ℝ := electroweakVev_MeV) (hvev : 0 < vevLockin_MeV) :
    tuftMW_geometricMean_atXi_GeV ξ vevLockin_MeV = tuftMW_atXi_GeV ξ vevLockin_MeV := by
  unfold tuftMW_geometricMean_atXi_GeV tuftMW_atXi_GeV
  rw [tuftMW_sqrt_body_eq_closure_times_bridge vevLockin_MeV hvev]
  ring

theorem tuftMW_geometricMean_atXi_GeV_eq_lockin (hvev : 0 < electroweakVev_MeV := electroweakVev_MeV_pos) :
    tuftMW_geometricMean_atXi_GeV xiLockin = tuftMW_atXi_GeV xiLockin :=
  tuftMW_geometricMean_atXi_GeV_eq xiLockin electroweakVev_MeV hvev

theorem tuftMW_atXi_GeV_eq_closure_times_sqrt_bridge (ξ : ℝ)
    (vevLockin_MeV : ℝ := electroweakVev_MeV) :
    tuftMW_atXi_GeV ξ vevLockin_MeV =
      M_W_derived * tuftElectroweakScaleAtXi ξ * tuftVevSqrtBridgeLockin vevLockin_MeV := rfl

theorem tuftMW_atXi_GeV_lockin :
    tuftMW_atXi_GeV xiLockin = M_W_derived * tuftVevSqrtBridgeLockin := by
  simp [tuftMW_atXi_GeV, tuftElectroweakScaleAtXi_lockin]

theorem tuftMH_scalarClosure_atXi_GeV_lockin :
    tuftMH_scalarClosure_atXi_GeV xiLockin = m_H_derived := by
  simp [tuftMH_scalarClosure_atXi_GeV, tuftElectroweakScaleAtXi_lockin]

theorem sin2ThetaWGeometricLockin_eq_triality_times_imprint :
    sin2ThetaWGeometricLockin =
      sin2ThetaWTriality * geometricResonanceStep electroweakPhiShell emGaussShell := by
  rfl

theorem sin2ThetaWTriality_eq_four_twenty_ninths : sin2ThetaWTriality = (4 : ℝ) / 29 := by
  unfold sin2ThetaWTriality
  rw [alpha_eq_3_5]
  norm_num

theorem geometricResonanceStep_electroweak_emGauss_eq :
    geometricResonanceStep electroweakPhiShell emGaussShell = (42 : ℝ) / 25 := by
  rw [electroweakPhiShell_val, emGaussShell_val]
  unfold geometricResonanceStep detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
    gamma_HQIV
  rw [alpha_eq_3_5]
  norm_num

theorem sin2ThetaWGeometricLockin_eq :
    sin2ThetaWGeometricLockin = (168 : ℝ) / 725 := by
  rw [sin2ThetaWGeometricLockin_eq_triality_times_imprint, sin2ThetaWTriality_eq_four_twenty_ninths,
    geometricResonanceStep_electroweak_emGauss_eq]
  norm_num

theorem sin2ThetaWGeometricLockin_lt_one : sin2ThetaWGeometricLockin < 1 := by
  rw [sin2ThetaWGeometricLockin_eq]
  norm_num

theorem sin2ThetaWGeometricLockin_le_one : sin2ThetaWGeometricLockin ≤ 1 := by
  linarith [sin2ThetaWGeometricLockin_lt_one]

theorem cosThetaWGeometricLockin_sq :
    cosThetaWGeometricLockin ^ 2 = 1 - sin2ThetaWGeometricLockin := by
  unfold cosThetaWGeometricLockin
  rw [Real.sq_sqrt (sub_nonneg.mpr sin2ThetaWGeometricLockin_le_one)]

theorem tuftMZ_atXi_GeV_lockin :
    tuftMZ_atXi_GeV xiLockin =
      M_W_derived * tuftVevSqrtBridgeLockin / cosThetaWGeometricLockin := by
  simp [tuftMZ_atXi_GeV, tuftMW_atXi_GeV_lockin]

theorem tuftMW_atXi_GeV_pos (ξ : ℝ) (hξ : 1 < ξ)
    (vevLockin_MeV : ℝ := electroweakVev_MeV) (hvev : 0 < vevLockin_MeV) :
    0 < tuftMW_atXi_GeV ξ vevLockin_MeV := by
  unfold tuftMW_atXi_GeV
  have hscale : 0 < tuftElectroweakScaleAtXi ξ := by
    unfold tuftElectroweakScaleAtXi
    exact div_pos (heavy_lepton_gap_at_xi_pos ξ hξ) (heavy_lepton_gap_at_xi_pos xiLockin (by
      rw [xiLockin_eq_five]; norm_num))
  exact mul_pos (mul_pos M_W_derived_pos hscale)
    (tuftVevSqrtBridgeLockin_pos vevLockin_MeV hvev)

theorem cosThetaWGeometricLockin_pos : 0 < cosThetaWGeometricLockin := by
  unfold cosThetaWGeometricLockin
  exact Real.sqrt_pos.mpr (by linarith [sin2ThetaWGeometricLockin_lt_one])

theorem tuftMZ_atXi_GeV_pos (ξ : ℝ) (hξ : 1 < ξ)
    (vevLockin_MeV : ℝ := electroweakVev_MeV) (hvev : 0 < vevLockin_MeV) :
    0 < tuftMZ_atXi_GeV ξ vevLockin_MeV := by
  unfold tuftMZ_atXi_GeV
  exact div_pos (tuftMW_atXi_GeV_pos ξ hξ vevLockin_MeV hvev) cosThetaWGeometricLockin_pos

theorem tuftMH_scalarMonogamyLocalization_GeV_pos :
    0 < tuftMH_scalarMonogamyLocalization_GeV := by
  unfold tuftMH_scalarMonogamyLocalization_GeV
  exact mul_pos gammaDerived_pos bosonLocalizationEnergyLowerBound_pos

theorem tuftMH_atXi_GeV_pos (ξ : ℝ) (hξ : 1 < ξ)
    (vevLockin_MeV : ℝ := electroweakVev_MeV) (hvev : 0 < vevLockin_MeV) :
    0 < tuftMH_atXi_GeV ξ vevLockin_MeV := by
  unfold tuftMH_atXi_GeV
  have hlam : 0 < higgsQuarticLambdaGaugeWitness :=
    higgsQuarticLambdaGaugeWitness_pos
  have hbody : 0 < 2 * higgsQuarticLambdaGaugeWitness := by
    exact mul_pos (by norm_num : 0 < (2 : ℝ)) hlam
  have hsqrt : 0 < Real.sqrt (2 * higgsQuarticLambdaGaugeWitness) :=
    Real.sqrt_pos.mpr hbody
  exact add_pos (mul_pos hsqrt (div_pos (tuftVevAtXi_MeV_pos ξ vevLockin_MeV hξ hvev)
      (by norm_num))) tuftMH_scalarMonogamyLocalization_GeV_pos

end Hqiv.Physics
