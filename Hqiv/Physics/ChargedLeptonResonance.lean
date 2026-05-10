import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Algebra.Triality
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.LeptonGenerationLockin
import Hqiv.Physics.ModalFrequencyHorizon

namespace Hqiv.Physics

open Hqiv.Algebra
open scoped Real

/-!
## Charged-lepton resonance factors (lock-in shells)

**Phenomenology:** depends on the current shell-selection witness exported by
`LeptonGenerationLockin` and a τ mass anchor — not a pure axiom derivation.
The interface for a future first-principles shell pick now lives in
`OuterHorizonLeptonShellSelection`; the present active μ/e shells are now
threshold-derived from the existing detuned-surface ladder, though the broader
support-band physics is still open.
See `archive/abandoned/MASS_LADDER_PHENOMENOLOGY.md`.

Shell indices follow **`LeptonGenerationLockin`**: τ at the first charge-decorated support shell
above `referenceM`, μ and e on **larger**
outer-horizon shells (lighter generations farther out). The resonance factors are ratios of
detuned surfaces `effectiveSurface m m = shellSurface m / rindlerDetuningShared (m : ℝ)` with
the **outer** shell in the numerator so `resonance_k_* > 1` along τ → μ → e.
The Rindler slack `δ_rindler_*` compares each step to standing-wave-lift thresholds exported by
`LeptonGenerationLockin`, rather than fixed shell numerals.

**Absolute τ scale:** dimensionful GeV masses still use `m_tau_from_resonance` (PDG central value)
as an explicit anchor. Ratios `m_mu_from_resonance`, `m_e_from_resonance` are **then** fixed by the
proved surface ratios `resonance_k_*` on the selected shells. The separate witness
`m_tau_from_lockin_surface_candidate` lives in the `E_Pl = 1` / lock-in normalization story (`= 16/9`);
`m_tau_from_lockin_surface_candidate_approx_resonance` is an **alignment check** between those two
languages, not a derivation of the PDG number from discrete lattice axioms.

The abandoned **τ = highest ℕ shell** (Planck-volume) model is preserved only as
`archive/abandoned/GenerationResonanceTauHighestShell.lean` (not part of the default build).

This module now exposes explicit modal readout wrappers for the τ/μ/e ladder, but that route should be
treated as a **provisional scratch path** rather than the preferred lightweight lepton interface.
The current μ/e phenomenology from the shell-threshold readout is not yet satisfactory; the cleaner
modal/horizon spines are `LeptonResonanceGlobalDetuning.lean` (lightweight ratios/obstruction) and
`DerivedGaugeAndLeptonSector.lean` (outer-horizon closure witnesses).
-/

noncomputable def relTol : ℝ := 1 / 500

def approxRel (a b : ℝ) : Prop :=
  (a - b) ^ 2 ≤ relTol ^ 2 * b ^ 2

notation:50 a " ≈ " b => approxRel a b

def surfaceArea (m : ℕ) : ℝ := shellSurface m

noncomputable def c_rindler : ℝ := c_rindler_shared

noncomputable def rindlerDetuning (mass : ℝ) : ℝ := rindlerDetuningShared mass

noncomputable def effectiveSurface (m : ℕ) (genMass : ℝ) : ℝ :=
  surfaceArea m / rindlerDetuning genMass

theorem effectiveSurface_eq_detunedShellSurface (m : ℕ) :
    effectiveSurface m (m : ℝ) = detunedShellSurface m := by
  unfold effectiveSurface surfaceArea rindlerDetuning detunedShellSurface
  rfl

theorem legacy_effectiveSurface_eq_effCorrected_zero (m : ℕ) :
    effectiveSurface m (m : ℝ) = effCorrected 0 m := by
  rw [effectiveSurface_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

/-- τ mass in **natural units with Planck energy set to unity** (`E_Pl = 1`).

There is no third “Planck witness” here: either the Planck unit is the reference
(`1`) and dimensionful masses are expressed as dimensionless ratios to it, or the
overall scale is `0` and the sector collapses. Any other positive overall factor is
just a change of units—equivalent to rescaling `1`. -/
def m_tau_Pl : ℝ := 1.45537e-19

/-- τ-generation shell (lock-in heavy vertex). -/
noncomputable def m_tau : ℕ := leptonHeavyVertexShell

/-- μ-generation shell. -/
noncomputable def m_mu : ℕ := leptonMuonShell

/-- e-generation shell (outermost among the three). -/
noncomputable def m_e : ℕ := leptonElectronShell

/-- Modal-frequency / horizon spec for the τ lock-in line. -/
noncomputable def tauModalFrequencySpec : ModalFrequencyHorizonSpec := leptonModalFrequencySpec

/-- Modal-frequency / horizon spec for the μ readout shell. -/
noncomputable def muonModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_mu

/-- Modal-frequency / horizon spec for the e readout shell. -/
noncomputable def electronModalFrequencySpec : ModalFrequencyHorizonSpec :=
  modalFrequencyHorizonFromShellNominal m_e

theorem tauModalFrequencySpec_detunedSurfaceReadout :
    tauModalFrequencySpec.detunedSurfaceReadout m_tau = effectiveSurface m_tau m_tau := by
  rw [show tauModalFrequencySpec = modalFrequencyHorizonFromShellNominal leptonHeavyVertexShell by
        rfl]
  rw [detunedSurfaceReadout_fromShellNominal]
  exact effectiveSurface_eq_detunedShellSurface m_tau

theorem muonModalFrequencySpec_detunedSurfaceReadout :
    muonModalFrequencySpec.detunedSurfaceReadout m_mu = effectiveSurface m_mu m_mu := by
  rw [show muonModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_mu by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]
  exact effectiveSurface_eq_detunedShellSurface m_mu

theorem electronModalFrequencySpec_detunedSurfaceReadout :
    electronModalFrequencySpec.detunedSurfaceReadout m_e = effectiveSurface m_e m_e := by
  rw [show electronModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_e by rfl]
  rw [detunedSurfaceReadout_fromShellNominal]
  exact effectiveSurface_eq_detunedShellSurface m_e

theorem charged_lepton_resonance_uses_current_shell_selection :
    m_tau = leptonHeavyVertexShell ∧
      m_mu = currentOuterHorizonLeptonShellSelection.muonShell ∧
      m_e = currentOuterHorizonLeptonShellSelection.electronShell := by
  exact ⟨rfl, rfl, rfl⟩

noncomputable def resonance_k_tau_mu : ℝ :=
  effectiveSurface m_mu m_mu / effectiveSurface m_tau m_tau

noncomputable def resonance_k_mu_e : ℝ :=
  effectiveSurface m_e m_e / effectiveSurface m_mu m_mu

noncomputable def leptonResonanceAxis : ResonanceAxis := leptonAxis m_tau

/-- Rindler slack vs. the τ → μ standing-wave lift threshold. -/
noncomputable def δ_rindler_tau_muon : ℝ :=
  resonance_k_tau_mu / chargedLeptonTauMuThreshold - 1

/-- Rindler slack vs. the μ → e standing-wave lift threshold. -/
noncomputable def δ_rindler_muon_e : ℝ :=
  resonance_k_mu_e / chargedLeptonMuEThreshold - 1

theorem effectiveSurface_shell_pos (m : ℕ) : 0 < effectiveSurface m (m : ℝ) := by
  rw [effectiveSurface_eq_detunedShellSurface]
  exact detunedShellSurface_pos m

theorem resonance_k_tau_mu_pos : 0 < resonance_k_tau_mu :=
  div_pos (effectiveSurface_shell_pos m_mu) (effectiveSurface_shell_pos m_tau)

theorem resonance_k_mu_e_pos : 0 < resonance_k_mu_e :=
  div_pos (effectiveSurface_shell_pos m_e) (effectiveSurface_shell_pos m_mu)

theorem resonance_k_tau_mu_eq_surface_ratio :
    resonance_k_tau_mu = effectiveSurface m_mu m_mu / effectiveSurface m_tau m_tau := rfl

theorem resonance_k_mu_e_eq_surface_ratio :
    resonance_k_mu_e = effectiveSurface m_e m_e / effectiveSurface m_mu m_mu := rfl

theorem resonance_k_tau_mu_eq_geometricResonanceStep :
    resonance_k_tau_mu = geometricResonanceStep leptonMuonShell leptonHeavyVertexShell := by
  unfold resonance_k_tau_mu geometricResonanceStep m_tau m_mu
  simp only [effectiveSurface_eq_detunedShellSurface]

theorem resonance_k_mu_e_eq_geometricResonanceStep :
    resonance_k_mu_e = geometricResonanceStep leptonElectronShell leptonMuonShell := by
  unfold resonance_k_mu_e geometricResonanceStep m_mu m_e
  simp only [effectiveSurface_eq_detunedShellSurface]

theorem resonance_k_tau_mu_eq_modal_readout :
    resonance_k_tau_mu = tauModalFrequencySpec.geometricStepReadout m_mu m_tau := by
  rw [show tauModalFrequencySpec = modalFrequencyHorizonFromShellNominal leptonHeavyVertexShell by
        rfl]
  rw [geometricStepReadout_fromShellNominal]
  simpa [m_tau, m_mu, tauModalFrequencySpec] using resonance_k_tau_mu_eq_geometricResonanceStep

theorem resonance_k_mu_e_eq_modal_readout :
    resonance_k_mu_e = muonModalFrequencySpec.geometricStepReadout m_e m_mu := by
  rw [show muonModalFrequencySpec = modalFrequencyHorizonFromShellNominal m_mu by rfl]
  rw [geometricStepReadout_fromShellNominal]
  simpa [m_mu, m_e, muonModalFrequencySpec] using resonance_k_mu_e_eq_geometricResonanceStep

/--
Charged-lepton content count: lepton number + electric charge.

This is a minimal local bookkeeping factor for the heavy lock-in τ candidate,
not a full shell-selection theorem for μ/e.
-/
def chargedLeptonContentCount : ℕ := 2

/--
Lock-in normalization for a τ candidate built from the heavy shell's own
detuned surface and the monogamy split.

The intent is to keep τ on the lock-in shell while leaving lighter generations
to descend by the existing resonance ratios on looser outer shells.
-/
noncomputable def tauLockinSurfaceNormalization : ℝ :=
  (2 * gamma_HQIV) / shellSurface m_tau

/--
Candidate τ mass from the heavy lock-in shell, charged-lepton content, and the
local detuned surface.

This is deliberately named a **candidate**: it is a “take a swing” outer/lock-in
closure witness, not yet a first-principles theorem replacing the resonance
anchor across the whole charged-lepton ladder.
-/
noncomputable def m_tau_from_lockin_surface_candidate : ℝ :=
  tauLockinSurfaceNormalization * (chargedLeptonContentCount : ℝ) ^ 2 * effectiveSurface m_tau m_tau

theorem m_tau_from_lockin_surface_candidate_closed_form :
    m_tau_from_lockin_surface_candidate = 16 / ((m_tau : ℝ) + 5) := by
  unfold m_tau_from_lockin_surface_candidate tauLockinSurfaceNormalization chargedLeptonContentCount
  unfold effectiveSurface rindlerDetuning rindlerDetuningShared c_rindler_shared surfaceArea shellSurface
  rw [gamma_eq_2_5]
  field_simp
  ring

theorem m_tau_from_lockin_surface_candidate_pos :
    0 < m_tau_from_lockin_surface_candidate := by
  rw [m_tau_from_lockin_surface_candidate_closed_form]
  positivity

theorem m_tau_from_lockin_surface_candidate_le_eight_fifths :
    m_tau_from_lockin_surface_candidate ≤ 8 / 5 := by
  rw [m_tau_from_lockin_surface_candidate_closed_form]
  have href : referenceM = 4 := by
    unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
    norm_num
  have hgt4 : (4 : ℕ) < m_tau := by
    simpa [m_tau, href] using leptonHeavyVertexShell_gt_referenceM
  have hm5 : 5 ≤ m_tau := Nat.succ_le_of_lt hgt4
  have hden_nat : 10 ≤ m_tau + 5 := Nat.add_le_add_right hm5 5
  have hden : (10 : ℝ) ≤ (m_tau : ℝ) + 5 := by
    exact_mod_cast hden_nat
  have hpos : 0 < (m_tau : ℝ) + 5 := by positivity
  refine (div_le_iff₀ hpos).2 ?_
  nlinarith

/--
**Phenomenological τ mass anchor (GeV).** Numeric literal `1776.86e-3` = `1776.86 MeV` expressed in GeV,
using a PDG-style central value for the τ pole mass (same convention as other SM scale witnesses in
this repo).

**Not Lean-derived:** this is **not** the same statement as `m_tau_from_lockin_surface_candidate`
(which stays a shell-readout candidate in the Planck-unit τ line). Treat it as the **dimensionful
calibration** that fixes the charged-lepton GeV ladder once the geometric factors `resonance_k_*` are
known.

**Downstream definitions (same file):**
`m_mu_from_resonance := m_tau_from_resonance / resonance_k_tau_mu`,
`m_e_from_resonance := m_mu_from_resonance / resonance_k_mu_e`.

**Removing handwaving:** any claim to “derive τ without external input” must replace this `def` with a
proved closure equality, or introduce a different absolute normalization theorem; until then the
machinery is **the same** as for quarks (detuned surfaces, geometric steps), but the **overall mass
unit** for this sector is explicitly anchored here.
-/
def m_tau_from_resonance : ℝ := 1776.86e-3
noncomputable def m_mu_from_resonance : ℝ := m_tau_from_resonance / resonance_k_tau_mu
noncomputable def m_e_from_resonance : ℝ := m_mu_from_resonance / resonance_k_mu_e

theorem m_tau_from_lockin_surface_candidate_lt_resonance :
    m_tau_from_lockin_surface_candidate < m_tau_from_resonance := by
  have hle : m_tau_from_lockin_surface_candidate ≤ 8 / 5 :=
    m_tau_from_lockin_surface_candidate_le_eight_fifths
  have hlt : (8 / 5 : ℝ) < m_tau_from_resonance := by
    unfold m_tau_from_resonance
    norm_num
  exact lt_of_le_of_lt hle hlt

theorem approxRel_div_right {a b r : ℝ} (hr : r ≠ 0) (h : a ≈ b) :
    a / r ≈ b / r := by
  unfold approxRel at h ⊢
  have hr2 : 0 < r ^ 2 := by
    exact sq_pos_of_ne_zero hr
  calc
    (a / r - b / r) ^ 2 = (a - b) ^ 2 / r ^ 2 := by
      field_simp [hr]
    _ ≤ (relTol ^ 2 * b ^ 2) / r ^ 2 := by
      exact div_le_div_of_nonneg_right h (by positivity)
    _ = relTol ^ 2 * (b / r) ^ 2 := by
      field_simp [hr]

noncomputable def resonanceK (fromGen toGen : So8RepIndex) : ℝ :=
  match fromGen, toGen with
  | ⟨2, _⟩, ⟨1, _⟩ => chargedLeptonTauMuThreshold * (1 + δ_rindler_tau_muon)
  | ⟨1, _⟩, ⟨0, _⟩ => chargedLeptonMuEThreshold * (1 + δ_rindler_muon_e)
  | _, _ => 1

theorem resonanceK_tau_mu_eq_resonance_k :
    resonanceK ⟨2, by decide⟩ ⟨1, by decide⟩ = resonance_k_tau_mu := by
  have hthr_pos : 0 < chargedLeptonTauMuThreshold :=
    lt_trans zero_lt_one chargedLeptonTauMuThreshold_gt_one
  have hthr_ne : chargedLeptonTauMuThreshold ≠ 0 := ne_of_gt hthr_pos
  have hmain :
      chargedLeptonTauMuThreshold * (resonance_k_tau_mu * chargedLeptonTauMuThreshold⁻¹) =
        resonance_k_tau_mu := by
    calc
      chargedLeptonTauMuThreshold * (resonance_k_tau_mu * chargedLeptonTauMuThreshold⁻¹) =
          resonance_k_tau_mu * (chargedLeptonTauMuThreshold * chargedLeptonTauMuThreshold⁻¹) := by
        ring
      _ = resonance_k_tau_mu := by
        simp [hthr_ne]
  simpa [resonanceK, δ_rindler_tau_muon, div_eq_mul_inv] using hmain

theorem resonanceK_mu_e_eq_resonance_k :
    resonanceK ⟨1, by decide⟩ ⟨0, by decide⟩ = resonance_k_mu_e := by
  have hthr_pos : 0 < chargedLeptonMuEThreshold :=
    lt_trans zero_lt_one chargedLeptonMuEThreshold_gt_one
  have hthr_ne : chargedLeptonMuEThreshold ≠ 0 := ne_of_gt hthr_pos
  have hmain :
      chargedLeptonMuEThreshold * (resonance_k_mu_e * chargedLeptonMuEThreshold⁻¹) =
        resonance_k_mu_e := by
    calc
      chargedLeptonMuEThreshold * (resonance_k_mu_e * chargedLeptonMuEThreshold⁻¹) =
          resonance_k_mu_e * (chargedLeptonMuEThreshold * chargedLeptonMuEThreshold⁻¹) := by
        ring
      _ = resonance_k_mu_e := by
        simp [hthr_ne]
  simpa [resonanceK, δ_rindler_muon_e, div_eq_mul_inv] using hmain

noncomputable def resonanceProduct (gen : So8RepIndex) : ℝ :=
  match gen with
  | ⟨2, _⟩ => 1
  | ⟨1, _⟩ => resonance_k_tau_mu
  | ⟨0, _⟩ => resonance_k_tau_mu * resonance_k_mu_e

/--
Detuned μ candidate obtained by relaxing the heavy τ lock-in candidate along the
τ → μ resonance step.
-/
noncomputable def m_mu_from_lockin_surface_candidate : ℝ :=
  m_tau_from_lockin_surface_candidate / resonance_k_tau_mu

/--
Detuned e candidate obtained by one further relaxation step on the outer shell.
-/
noncomputable def m_e_from_lockin_surface_candidate : ℝ :=
  m_mu_from_lockin_surface_candidate / resonance_k_mu_e

theorem m_mu_from_lockin_surface_candidate_eq_tau_over_resonance :
    m_mu_from_lockin_surface_candidate =
      m_tau_from_lockin_surface_candidate / resonance_k_tau_mu := rfl

theorem m_e_from_lockin_surface_candidate_eq_mu_over_resonance :
    m_e_from_lockin_surface_candidate =
      m_mu_from_lockin_surface_candidate / resonance_k_mu_e := rfl

theorem m_mu_from_lockin_surface_candidate_eq_tau_over_modal_readout :
    m_mu_from_lockin_surface_candidate =
      m_tau_from_lockin_surface_candidate / tauModalFrequencySpec.geometricStepReadout m_mu m_tau := by
  rw [m_mu_from_lockin_surface_candidate_eq_tau_over_resonance, resonance_k_tau_mu_eq_modal_readout]

theorem m_e_from_lockin_surface_candidate_eq_mu_over_modal_readout :
    m_e_from_lockin_surface_candidate =
      m_mu_from_lockin_surface_candidate / muonModalFrequencySpec.geometricStepReadout m_e m_mu := by
  rw [m_e_from_lockin_surface_candidate_eq_mu_over_resonance, resonance_k_mu_e_eq_modal_readout]

theorem m_e_from_lockin_surface_candidate_eq_tau_over_resonanceProduct :
    m_e_from_lockin_surface_candidate =
      m_tau_from_lockin_surface_candidate / (resonance_k_tau_mu * resonance_k_mu_e) := by
  unfold m_e_from_lockin_surface_candidate m_mu_from_lockin_surface_candidate
  have hτμ : resonance_k_tau_mu ≠ 0 := ne_of_gt resonance_k_tau_mu_pos
  have hμe : resonance_k_mu_e ≠ 0 := ne_of_gt resonance_k_mu_e_pos
  field_simp [hτμ, hμe]

theorem m_mu_from_lockin_surface_candidate_lt_resonance :
    m_mu_from_lockin_surface_candidate < m_mu_from_resonance := by
  unfold m_mu_from_lockin_surface_candidate m_mu_from_resonance
  exact (div_lt_div_iff_of_pos_right resonance_k_tau_mu_pos).2
    m_tau_from_lockin_surface_candidate_lt_resonance

theorem m_e_from_lockin_surface_candidate_lt_resonance :
    m_e_from_lockin_surface_candidate < m_e_from_resonance := by
  unfold m_e_from_lockin_surface_candidate m_e_from_resonance
  exact (div_lt_div_iff_of_pos_right resonance_k_mu_e_pos).2
    m_mu_from_lockin_surface_candidate_lt_resonance

theorem resonanceProduct_eq_fano_core (gen : So8RepIndex) :
    resonanceProduct gen =
      resonanceProductFromSteps resonance_k_tau_mu resonance_k_mu_e gen := by
  fin_cases gen <;> rfl

theorem planck_electron_mass_from_tau_resonance :
    m_tau_Pl * (1 / resonanceProduct ⟨0, by decide⟩) =
      m_tau_Pl / (resonance_k_tau_mu * resonance_k_mu_e) := by
  simp [resonanceProduct]
  field_simp

theorem tau_to_muon_resonance :
    effectiveSurface m_tau m_tau = effectiveSurface m_mu m_mu / resonance_k_tau_mu := by
  rw [resonance_k_tau_mu_eq_surface_ratio]
  have hτ := ne_of_gt (effectiveSurface_shell_pos m_tau)
  have hμ := ne_of_gt (effectiveSurface_shell_pos m_mu)
  field_simp [Ne.symm hτ, Ne.symm hμ]

theorem muon_to_electron_resonance :
    effectiveSurface m_mu m_mu = effectiveSurface m_e m_e / resonance_k_mu_e := by
  rw [resonance_k_mu_e_eq_surface_ratio]
  have hμ := ne_of_gt (effectiveSurface_shell_pos m_mu)
  have he := ne_of_gt (effectiveSurface_shell_pos m_e)
  field_simp [Ne.symm hμ, Ne.symm he]

noncomputable def leptonMonogamyThreshold : ℝ := effectiveSurface m_e m_tau_Pl + 1

theorem exactly_three_generations_and_no_more :
    ∃ k3 : ℕ,
      effectiveSurface (m_e + k3) m_tau_Pl < leptonMonogamyThreshold ∧
      ¬ ∃ fourthGen : So8RepIndex,
        fourthGen ≠ rep8V ∧ fourthGen ≠ rep8SPlus ∧ fourthGen ≠ rep8SMinus := by
  refine ⟨0, ?_, ?_⟩
  · simp [leptonMonogamyThreshold]
  · rintro ⟨g, h0, h1, h2⟩
    fin_cases g <;> simp_all [rep8V, rep8SPlus, rep8SMinus]

end Hqiv.Physics
