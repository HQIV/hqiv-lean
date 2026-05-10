import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.LeptonGenerationLockin
import Hqiv.Physics.ModalFrequencyHorizon
import Hqiv.Physics.QuarterPeriodRelaxation
import Hqiv.Geometry.OctonionicLightCone

/-!
# Charged-lepton resonance ladder, global-detuning obstruction

Independent of Triality / SO(8) Lie closure. Shared Rindler scaffolding lives in `GlobalDetuning`
(`effCorrected`, `effUnified`, `GlobalDetuningHypothesis`, lapse bridge).

Shell anchors **`m_tau`**, **`m_mu`**, **`m_e`** match **`LeptonGenerationLockin`** — keep in sync
(τ at lock-in; μ and e on larger shells).

**HQVM packaging:** see `GlobalDetuningHypothesis.fromLapseScalars` and
`deltaGlobal_eq_lambda_mul_lapseIncrement` (proved).

**No PDG closure.**

This file is now the preferred lightweight modal/horizon readout layer for the charged-lepton ladder:
it stays independent of the thicker resonance-anchor phenomenology in `ChargedLeptonResonance.lean`
while still exposing the same detuned-surface ratios through `ModalFrequencyHorizonSpec`.

**Sphere-split relaxation:** `tauRelaxedQuarterSpec` / `muonRelaxedQuarterSpec` / `electronRelaxedQuarterSpec`
keep the legacy `S⁷` spectral weight; `tauRelaxedQuarterSpecS3` / `muonRelaxedQuarterSpecS3` /
`electronRelaxedQuarterSpecS3` and `kTauMuRelaxedQuarterS3` / `kMuERelaxedQuarterS3` use the quaternion
phase-sphere `S³` bridge from `QuarterPeriodRelaxation`. The outer-shell neutrino readout
`nuElectronRelaxedQuarterSpecS3` shares the same `S³` machinery on the outer readout `m_nu_e = referenceM + 2`.
-/

namespace Hqiv.Physics.LeptonResonanceGlobalDetuning

open scoped Real
open Hqiv

noncomputable section

/-!
### A. Local ladder
-/

/-- τ / μ / e shells — kept definitionally aligned with `LeptonGenerationLockin`. -/
def m_tau : ℕ := leptonHeavyVertexShell

noncomputable def m_mu : ℕ := leptonMuonShell

noncomputable def m_e : ℕ := leptonElectronShell

/-- Lightweight modal-frequency / horizon wrapper for the τ lock-in line. -/
noncomputable def tauModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_tau

/-- Lightweight modal-frequency / horizon wrapper for the μ readout shell. -/
noncomputable def muonModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_mu

/-- Lightweight modal-frequency / horizon wrapper for the e readout shell. -/
noncomputable def electronModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_e

theorem m_tau_gt_referenceM : referenceM < m_tau := by
  simpa [m_tau] using leptonHeavyVertexShell_gt_referenceM

noncomputable def eff (m : ℕ) : ℝ :=
  shellSurface m / rindlerDetuningShared (m : ℝ)

theorem eff_eq_detunedShellSurface (m : ℕ) : eff m = detunedShellSurface m := by
  unfold eff detunedShellSurface
  rfl

theorem eff_eq_modal_detunedSurfaceReadout_tau (m : ℕ) :
    tauModalFrequencySpec.detunedSurfaceReadout m = eff m := by
  rw [show tauModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_tau by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]
  rw [eff_eq_detunedShellSurface]

theorem eff_eq_modal_detunedSurfaceReadout_muon (m : ℕ) :
    muonModalFrequencySpec.detunedSurfaceReadout m = eff m := by
  rw [show muonModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_mu by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]
  rw [eff_eq_detunedShellSurface]

theorem eff_pos (m : ℕ) : 0 < eff m := by
  simpa [eff_eq_detunedShellSurface] using detunedShellSurface_pos m

theorem eff_eq_effCorrected_zero (m : ℕ) : eff m = effCorrected 0 m := by
  rw [eff_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

/-- μ–τ surface ratio (outer / inner); same direction as `ChargedLeptonResonance.resonance_k_tau_mu`. -/
noncomputable def kTauMu : ℝ :=
  eff m_mu / eff m_tau

/-- e–μ surface ratio (outer / inner); same direction as `ChargedLeptonResonance.resonance_k_mu_e`. -/
noncomputable def kMuE : ℝ :=
  eff m_e / eff m_mu

/--
Three-jet lepton effective surface readout candidate.
This preserves the lock-in shell value and probes curvature away from `referenceM`.
-/
noncomputable def effThreeJet (m : ℕ) : ℝ :=
  Hqiv.Physics.detunedShellSurfaceThreeJet m

/-- Three-jet μ–τ surface ratio candidate. -/
noncomputable def kTauMuThreeJet : ℝ :=
  effThreeJet m_mu / effThreeJet m_tau

/-- Three-jet e–μ surface ratio candidate. -/
noncomputable def kMuEThreeJet : ℝ :=
  effThreeJet m_e / effThreeJet m_mu

/-- Cubic-phase relaxed quarter-period spec centered on the τ lock-in shell (`S⁷` Laplace weight). -/
noncomputable def tauRelaxedQuarterSpec : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominal Hqiv.Algebra.rep8SMinus 1 m_tau

/-- Cubic-phase relaxed quarter-period spec centered on the μ shell (`S⁷` weight). -/
noncomputable def muonRelaxedQuarterSpec : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominal Hqiv.Algebra.rep8SPlus 1 m_mu

/-- Cubic-phase relaxed quarter-period spec centered on the e shell (`S⁷` weight). -/
noncomputable def electronRelaxedQuarterSpec : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominal Hqiv.Algebra.rep8V 1 m_e

/-- Same τ-centered packaging, but with **`S³`** (quaternion / spin–charge phase sphere) spectral weight. -/
noncomputable def tauRelaxedQuarterSpecS3 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS3 Hqiv.Algebra.rep8SMinus 1 m_tau

/-- μ shell readout with **`S³`** weight. -/
noncomputable def muonRelaxedQuarterSpecS3 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS3 Hqiv.Algebra.rep8SPlus 1 m_mu

/-- e shell readout with **`S³`** weight. -/
noncomputable def electronRelaxedQuarterSpecS3 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS3 Hqiv.Algebra.rep8V 1 m_e

/-- Electron-neutrino suppression shell index (same row as `DerivedGaugeAndLeptonSector.neutrinoSuppressionModalFrequencySpec`). -/
def m_nu_e : ℕ := referenceM + 2

/-- Outer electron-neutrino modal wrapper (shell-only; no mass anchor here). -/
noncomputable def nuElectronModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_nu_e

/-- Electron-neutrino channel with **`S³`** relaxation: triality axis `rep8SMinus` on the outer neutrino shell. -/
noncomputable def nuElectronRelaxedQuarterSpecS3 : RelaxedQuarterModalSpec :=
  relaxedQuarterModalFromShellNominalS3 Hqiv.Algebra.rep8SMinus 1 m_nu_e

/-- Relaxed quarter-period detuned surface readout candidate (τ-centered). -/
noncomputable def effRelaxedQuarter (m : ℕ) : ℝ :=
  tauRelaxedQuarterSpec.relaxedDetunedSurfaceReadout m

/-- `S³`-weighted relaxed detuned surface readout (τ-centered). -/
noncomputable def effRelaxedQuarterS3 (m : ℕ) : ℝ :=
  tauRelaxedQuarterSpecS3.relaxedDetunedSurfaceReadout m

/-- Relaxed-quarter μ–τ surface ratio candidate. -/
noncomputable def kTauMuRelaxedQuarter : ℝ :=
  tauRelaxedQuarterSpec.relaxedGeometricStepReadout m_mu m_tau

/-- Relaxed-quarter e–μ surface ratio candidate. -/
noncomputable def kMuERelaxedQuarter : ℝ :=
  muonRelaxedQuarterSpec.relaxedGeometricStepReadout m_e m_mu

/-- `S³`-weighted μ–τ ratio candidate (charged-lepton / spin–charge sector on `S³`). -/
noncomputable def kTauMuRelaxedQuarterS3 : ℝ :=
  tauRelaxedQuarterSpecS3.relaxedGeometricStepReadout m_mu m_tau

/-- `S³`-weighted e–μ ratio candidate. -/
noncomputable def kMuERelaxedQuarterS3 : ℝ :=
  muonRelaxedQuarterSpecS3.relaxedGeometricStepReadout m_e m_mu

lemma muonRelaxedQuarterSpec_base_detuning_ne_zero (m : ℕ) :
    muonRelaxedQuarterSpec.base.detuning1Jet m ≠ 0 := by
  unfold muonRelaxedQuarterSpec relaxedQuarterModalFromShellNominal
    RelaxedQuarterModalSpec.fromBaseTagged modalFrequencyHorizonFromShellNominal
  change rindlerDetuningShared (m : ℝ) ≠ 0
  have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hpos : 0 < rindlerDetuningShared (m : ℝ) := by
    unfold rindlerDetuningShared c_rindler_shared
    rw [gamma_eq_2_5]
    nlinarith
  exact ne_of_gt hpos

theorem kMuERelaxedQuarter_abs_le_kinetic_control
    (κ : ℝ) (hκ : 0 ≤ κ) (A : Fin 8 → Fin 4 → ℝ) (x : ℝ)
    (hctrl :
      muonRelaxedQuarterSpec.relaxationLoad m_mu ≤
        κ * (∑ a : Fin 8, ∑ i : Fin 4, ((Hqiv.Physics.linearEnd (F_from_A A a i (i + 1))) x - x) ^ 2)) :
    |kMuERelaxedQuarter| ≤ |kMuE| * (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
  have hbase :
      muonRelaxedQuarterSpec.base.geometricStepReadout m_e m_mu = kMuE := by
    unfold muonRelaxedQuarterSpec relaxedQuarterModalFromShellNominal
      RelaxedQuarterModalSpec.fromBaseTagged
    rw [geometricStepReadout_fromShellNominal]
    unfold kMuE geometricResonanceStep
    simp [eff_eq_detunedShellSurface]
  have hdet_e : muonRelaxedQuarterSpec.base.detuning1Jet m_e ≠ 0 :=
    muonRelaxedQuarterSpec_base_detuning_ne_zero m_e
  have hdet_mu : muonRelaxedQuarterSpec.base.detuning1Jet m_mu ≠ 0 :=
    muonRelaxedQuarterSpec_base_detuning_ne_zero m_mu
  have hmain := RelaxedQuarterModalSpec.abs_relaxedGeometricStepReadout_le_kinetic_control
      (spec := muonRelaxedQuarterSpec) m_e m_mu hdet_e hdet_mu κ hκ A x hctrl
  have hmain' :
      |kMuERelaxedQuarter| ≤
        |muonRelaxedQuarterSpec.base.geometricStepReadout m_e m_mu| *
          (1 + κ * ((-4 : ℝ) * L_O_kinetic A)) := by
    simpa [kMuERelaxedQuarter] using hmain
  simpa [hbase] using hmain'

theorem kTauMu_pos : 0 < kTauMu :=
  div_pos (eff_pos m_mu) (eff_pos m_tau)

theorem kMuE_pos : 0 < kMuE :=
  div_pos (eff_pos m_e) (eff_pos m_mu)

theorem kTauMu_eq_eff_ratio : kTauMu = eff m_mu / eff m_tau :=
  rfl

theorem kMuE_eq_eff_ratio : kMuE = eff m_e / eff m_mu :=
  rfl

theorem kTauMu_eq_geometricResonanceStep : kTauMu = geometricResonanceStep m_mu m_tau := by
  unfold kTauMu geometricResonanceStep
  simp [eff_eq_detunedShellSurface]

theorem kMuE_eq_geometricResonanceStep : kMuE = geometricResonanceStep m_e m_mu := by
  unfold kMuE geometricResonanceStep
  simp [eff_eq_detunedShellSurface]

theorem kTauMu_eq_modal_geometricStepReadout :
    kTauMu = tauModalFrequencySpec.geometricStepReadout m_mu m_tau := by
  rw [show tauModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_tau by rfl]
  rw [geometricStepReadout_fromShellNominal]
  simpa using kTauMu_eq_geometricResonanceStep

theorem kMuE_eq_modal_geometricStepReadout :
    kMuE = muonModalFrequencySpec.geometricStepReadout m_e m_mu := by
  rw [show muonModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_mu by rfl]
  rw [geometricStepReadout_fromShellNominal]
  simpa using kMuE_eq_geometricResonanceStep

noncomputable def kTauMuCorrected (δ : ℝ) : ℝ :=
  effCorrected δ m_mu / effCorrected δ m_tau

noncomputable def kMuECorrected (δ : ℝ) : ℝ :=
  effCorrected δ m_e / effCorrected δ m_mu

/-!
### Algebraic obstruction
-/

theorem tau_mu_ratio_iff_delta_linear (δ r₁ : ℝ) (Sτ Sμ : ℝ) (τ μ : ℝ)
    (hSμ : Sμ ≠ 0) (hDτ : 1 + c_rindler_shared * τ + δ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) :
    (Sτ / (1 + c_rindler_shared * τ + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) = r₁ ↔
      δ * (Sτ - r₁ * Sμ) = r₁ * Sμ * (1 + c_rindler_shared * τ) - Sτ * (1 + c_rindler_shared * μ) := by
  have hne : Sμ * (1 + c_rindler_shared * τ + δ) ≠ 0 := mul_ne_zero hSμ hDτ
  have hrewrite :
      (Sτ / (1 + c_rindler_shared * τ + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) =
        (Sτ * (1 + c_rindler_shared * μ + δ)) / (Sμ * (1 + c_rindler_shared * τ + δ)) := by
    field_simp [hSμ, hDτ, hDμ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sτ * (1 + c_rindler_shared * μ + δ) = r₁ * Sμ * (1 + c_rindler_shared * τ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sτ * (1 + c_rindler_shared * μ + δ) = r₁ * Sμ * (1 + c_rindler_shared * τ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem mu_tau_ratio_iff_delta_linear (δ r₁ : ℝ) (Sτ Sμ : ℝ) (τ μ : ℝ)
    (hSτ : Sτ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) (hDτ : 1 + c_rindler_shared * τ + δ ≠ 0) :
    (Sμ / (1 + c_rindler_shared * μ + δ)) / (Sτ / (1 + c_rindler_shared * τ + δ)) = r₁ ↔
      δ * (Sμ - r₁ * Sτ) = r₁ * Sτ * (1 + c_rindler_shared * μ) - Sμ * (1 + c_rindler_shared * τ) := by
  have hne : Sτ * (1 + c_rindler_shared * μ + δ) ≠ 0 := mul_ne_zero hSτ hDμ
  have hrewrite :
      (Sμ / (1 + c_rindler_shared * μ + δ)) / (Sτ / (1 + c_rindler_shared * τ + δ)) =
        (Sμ * (1 + c_rindler_shared * τ + δ)) / (Sτ * (1 + c_rindler_shared * μ + δ)) := by
    field_simp [hSτ, hDμ, hDτ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sμ * (1 + c_rindler_shared * τ + δ) = r₁ * Sτ * (1 + c_rindler_shared * μ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sμ * (1 + c_rindler_shared * τ + δ) = r₁ * Sτ * (1 + c_rindler_shared * μ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem mu_e_ratio_iff_delta_linear (δ r₂ : ℝ) (Sμ Se : ℝ) (μ e : ℝ)
    (hSe : Se ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) (hDe : 1 + c_rindler_shared * e + δ ≠ 0) :
    (Sμ / (1 + c_rindler_shared * μ + δ)) / (Se / (1 + c_rindler_shared * e + δ)) = r₂ ↔
      δ * (Sμ - r₂ * Se) = r₂ * Se * (1 + c_rindler_shared * μ) - Sμ * (1 + c_rindler_shared * e) := by
  have hne : Se * (1 + c_rindler_shared * μ + δ) ≠ 0 := mul_ne_zero hSe hDμ
  have hrewrite :
      (Sμ / (1 + c_rindler_shared * μ + δ)) / (Se / (1 + c_rindler_shared * e + δ)) =
        (Sμ * (1 + c_rindler_shared * e + δ)) / (Se * (1 + c_rindler_shared * μ + δ)) := by
    field_simp [hSe, hDμ, hDe]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sμ * (1 + c_rindler_shared * e + δ) = r₂ * Se * (1 + c_rindler_shared * μ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sμ * (1 + c_rindler_shared * e + δ) = r₂ * Se * (1 + c_rindler_shared * μ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem e_mu_ratio_iff_delta_linear (δ r₂ : ℝ) (Sμ Se : ℝ) (μ e : ℝ)
    (hSμ : Sμ ≠ 0) (hDe : 1 + c_rindler_shared * e + δ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) :
    (Se / (1 + c_rindler_shared * e + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) = r₂ ↔
      δ * (Se - r₂ * Sμ) = r₂ * Sμ * (1 + c_rindler_shared * e) - Se * (1 + c_rindler_shared * μ) := by
  have hne : Sμ * (1 + c_rindler_shared * e + δ) ≠ 0 := mul_ne_zero hSμ hDe
  have hrewrite :
      (Se / (1 + c_rindler_shared * e + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) =
        (Se * (1 + c_rindler_shared * μ + δ)) / (Sμ * (1 + c_rindler_shared * e + δ)) := by
    field_simp [hSμ, hDe, hDμ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Se * (1 + c_rindler_shared * μ + δ) = r₂ * Sμ * (1 + c_rindler_shared * e + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Se * (1 + c_rindler_shared * μ + δ) = r₂ * Sμ * (1 + c_rindler_shared * e + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

noncomputable def Sτ : ℝ := shellSurface m_tau
noncomputable def Sμ : ℝ := shellSurface m_mu
noncomputable def Se : ℝ := shellSurface m_e

noncomputable def τr : ℝ := (m_tau : ℝ)
noncomputable def μr : ℝ := (m_mu : ℝ)
noncomputable def er : ℝ := (m_e : ℝ)

theorem shellSurface_ne_zero (m : ℕ) : shellSurface m ≠ 0 := by
  unfold shellSurface
  have h1 : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
  have h2 : (0 : ℝ) < (m + 2 : ℝ) := by exact_mod_cast Nat.succ_pos _
  nlinarith

noncomputable def δNumTauMu (r₁ : ℝ) : ℝ :=
  r₁ * Sτ * (1 + c_rindler_shared * μr) - Sμ * (1 + c_rindler_shared * τr)

noncomputable def δDenTauMu (r₁ : ℝ) : ℝ :=
  Sμ - r₁ * Sτ

noncomputable def δNumMuE (r₂ : ℝ) : ℝ :=
  r₂ * Sμ * (1 + c_rindler_shared * er) - Se * (1 + c_rindler_shared * μr)

noncomputable def δDenMuE (r₂ : ℝ) : ℝ :=
  Se - r₂ * Sμ

noncomputable def singleDeltaCompatResidual (r₁ r₂ : ℝ) : ℝ :=
  δNumTauMu r₁ * δDenMuE r₂ - δNumMuE r₂ * δDenTauMu r₁

theorem kTauMuCorrected_eq_iff_delta_linear (δ r₁ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0) :
    kTauMuCorrected δ = r₁ ↔
      δ * (Sμ - r₁ * Sτ) = δNumTauMu r₁ := by
  simpa [kTauMuCorrected, effCorrected, rindlerDenWithDelta, Sτ, Sμ, τr, μr, δNumTauMu]
    using mu_tau_ratio_iff_delta_linear δ r₁ _ _ _ _ (shellSurface_ne_zero m_tau) hDμ hDτ

theorem kMuECorrected_eq_iff_delta_linear (δ r₂ : ℝ)
    (hDμ : rindlerDenWithDelta δ m_mu ≠ 0) (hDe : rindlerDenWithDelta δ m_e ≠ 0) :
    kMuECorrected δ = r₂ ↔
      δ * (Se - r₂ * Sμ) = δNumMuE r₂ := by
  simpa [kMuECorrected, effCorrected, rindlerDenWithDelta, Sμ, Se, μr, er, δNumMuE]
    using e_mu_ratio_iff_delta_linear δ r₂ _ _ _ _ (shellSurface_ne_zero m_mu) hDe hDμ

theorem single_delta_both_ratios_implies_compat_aux (δ r₁ r₂ : ℝ)
    (h₁ : δ * (Sμ - r₁ * Sτ) = δNumTauMu r₁) (h₂ : δ * (Se - r₂ * Sμ) = δNumMuE r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 := by
  unfold singleDeltaCompatResidual δDenTauMu δDenMuE
  have hτ : δNumTauMu r₁ = δ * (Sμ - r₁ * Sτ) := h₁.symm
  have hμ : δNumMuE r₂ = δ * (Se - r₂ * Sμ) := h₂.symm
  rw [hτ, hμ]
  ring

theorem both_ratios_implies_compat_residual_zero (δ r₁ r₂ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0)
    (hDe : rindlerDenWithDelta δ m_e ≠ 0)
    (hkm : kTauMuCorrected δ = r₁) (hke : kMuECorrected δ = r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 := by
  have h1' := (kTauMuCorrected_eq_iff_delta_linear δ r₁ hDτ hDμ).1 hkm
  have h2' := (kMuECorrected_eq_iff_delta_linear δ r₂ hDμ hDe).1 hke
  exact single_delta_both_ratios_implies_compat_aux δ r₁ r₂ h1' h2'

theorem necessary_compat_of_single_delta (δ r₁ r₂ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0)
    (hDe : rindlerDenWithDelta δ m_e ≠ 0)
    (hkm : kTauMuCorrected δ = r₁) (hke : kMuECorrected δ = r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 :=
  both_ratios_implies_compat_residual_zero δ r₁ r₂ hDτ hDμ hDe hkm hke

theorem compat_residual_eq_zero_iff_deltaEq (r₁ r₂ : ℝ)
    (hden1 : Sμ - r₁ * Sτ ≠ 0) (hden2 : Se - r₂ * Sμ ≠ 0) :
    singleDeltaCompatResidual r₁ r₂ = 0 ↔
      δNumTauMu r₁ / (Sμ - r₁ * Sτ) = δNumMuE r₂ / (Se - r₂ * Sμ) := by
  unfold singleDeltaCompatResidual δDenTauMu δDenMuE
  rw [sub_eq_zero, ← div_eq_div_iff hden1 hden2]

/-!
### Open problem (documentation)
-/

def OpenProblem : Prop :=
  True

end

end Hqiv.Physics.LeptonResonanceGlobalDetuning
