import Mathlib.Tactic
import Hqiv.Physics.ConservedContentMassBridge
import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.FanoSectorSpectralMassEmergence

/-!
## Mass spectrum witness (single export chain)

This file adds **no new anchors**. It concatenates existing strict inequalities so that an ordered
“spectrum” is visible in one place, and it uses the anchor-free lock-in τ candidate rather than the
phenomenological `m_tau_from_resonance` scale:

1. derived ν ladder (`neutrino_derived_mass_ladder_strict` in `DerivedGaugeAndLeptonSector`);
2. neutral weak-boson witness `M_Z_derived` and charged witness ordering `M_W < M_Z`;
3. τ lock-in candidate `m_tau_from_lockin_surface_candidate = 4/5`;
4. the heavy up-like color-composed witness (`m_top_GeV` normalization).

For the **content-class** shell ansatz at fixed `(k, δ, m)` with `0 < k` and `RindlerDenDeltaPos δ m`,
see `massScalingAnsatz_fermion_three_rungs_strict_order` in `ConservedContentMassBridge`.

### GeV normalization vs PDG (charged leptons)

Mapping lock-in candidates to GeV uses the **single** scale `tauLockinToResonanceScale` from
`ChargedLeptonResonance` (ratio of the PDG-style τ pole anchor `m_tau_from_resonance` to the
discharged `4/5` candidate). With the proved shells `μ = 33`, `e = 58`, the resonance factors become
the explicit rationals `resonance_k_tau_mu = 175/76` and `resonance_k_mu_e = 4484/2499`.

Under that τ anchor, the resulting `m_mu_from_resonance` / `m_e_from_resonance` are **much larger**
than the PDG μ/e centrals exported as `m_mu_PDG` / `m_e_PDG` in `DerivedGaugeAndLeptonSector` — this is
a quantitative mismatch lemma, not a fit claim.
-/

namespace Hqiv.Physics

/-- Explicit anchor-free charged-lepton candidate ladder in the current normalized lock-in units.

The absolute top rung is now discharged (`τ = 4/5`); the lighter rungs are the existing geometric
readout quotients. This is a mass ladder, not just an inequality chain. -/
theorem chargedLepton_lockin_candidate_mass_ladder :
    m_tau_from_lockin_surface_candidate = (4 : ℝ) / 5 ∧
      m_mu_from_lockin_surface_candidate = ((4 : ℝ) / 5) / resonance_k_tau_mu ∧
        m_e_from_lockin_surface_candidate =
          ((4 : ℝ) / 5) / (resonance_k_tau_mu * resonance_k_mu_e) := by
  refine ⟨m_tau_from_lockin_surface_candidate_eq_four_fifths, ?_, ?_⟩
  · rw [m_mu_from_lockin_surface_candidate_eq_tau_over_resonance,
      m_tau_from_lockin_surface_candidate_eq_four_fifths]
  · rw [m_e_from_lockin_surface_candidate_eq_tau_over_resonanceProduct,
      m_tau_from_lockin_surface_candidate_eq_four_fifths]

/-- Strict ordering of the anchor-free charged-lepton candidate ladder. -/
theorem chargedLepton_lockin_candidate_strict_ladder :
    m_e_from_lockin_surface_candidate < m_mu_from_lockin_surface_candidate ∧
      m_mu_from_lockin_surface_candidate < m_tau_from_lockin_surface_candidate :=
  ⟨m_e_from_lockin_surface_candidate_lt_m_mu_from_lockin_surface_candidate,
    m_mu_from_lockin_surface_candidate_lt_m_tau_from_lockin_surface_candidate⟩

/-- Anchor-free τ candidate sits above the derived electron-neutrino witness. -/
theorem m_nu_e_derived_lt_tau_lockin_candidate :
    m_nu_e_derived < m_tau_from_lockin_surface_candidate := by
  rw [m_nu_e_derived_eq_suppression_times_M_Z, outerHorizonNeutrinoSuppression_eq_inv_140,
    boson_witness_M_Z, m_tau_from_lockin_surface_candidate_eq_four_fifths]
  norm_num

/-- The τ lock-in candidate sits below the top-normalized heavy color witness without using
`m_tau_from_resonance`. -/
theorem tau_lockin_candidate_lt_top_colored_witness :
    m_tau_from_lockin_surface_candidate < allowedColorResonanceMass .upLike .heavy := by
  rw [m_tau_from_lockin_surface_candidate_eq_four_fifths,
    allowedColorResonanceMass_upLike_heavy_eq_top_GeV]
  norm_num [m_top_GeV]

/-- Longest unconditional strict chain currently exported without extra hypotheses:
ν ladder → `M_Z` → `M_W` sits below `M_Z` → derived τ lock-in candidate → top-colored witness. -/
theorem mass_scale_spectrum_neutrinos_weak_boson_tauCandidate_to_top :
    m_nu_tau_derived < m_nu_mu_derived ∧
      m_nu_mu_derived < m_nu_e_derived ∧
        m_nu_e_derived < M_Z_derived ∧
          M_W_derived < M_Z_derived ∧
            m_nu_e_derived < m_tau_from_lockin_surface_candidate ∧
              m_tau_from_lockin_surface_candidate < allowedColorResonanceMass .upLike .heavy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact neutrino_derived_mass_ladder_strict.1
  · exact neutrino_derived_mass_ladder_strict.2
  · exact m_nu_e_derived_lt_M_Z_derived
  · exact M_W_derived_lt_M_Z_derived
  · exact m_nu_e_derived_lt_tau_lockin_candidate
  · exact tau_lockin_candidate_lt_top_colored_witness

/-- PDG-style τ pole anchor used for GeV calibration (same literal as `m_tau_from_resonance`). -/
theorem m_tau_anchor_eq_pdg_lit : m_tau_from_resonance = (177686 : ℝ) / 100000 := by
  unfold m_tau_from_resonance
  norm_num

/-- GeV readout of a lock-in candidate via the τ pole anchor (same factor on all three rungs). -/
noncomputable def chargedLeptonLockinCandidateGeV (x : ℝ) : ℝ :=
  tauLockinToResonanceScale * x

theorem chargedLepton_lockin_candidate_GeV_eq_resonance_masses :
    chargedLeptonLockinCandidateGeV m_tau_from_lockin_surface_candidate = m_tau_from_resonance ∧
      chargedLeptonLockinCandidateGeV m_mu_from_lockin_surface_candidate = m_mu_from_resonance ∧
        chargedLeptonLockinCandidateGeV m_e_from_lockin_surface_candidate = m_e_from_resonance := by
  unfold chargedLeptonLockinCandidateGeV
  exact chargedLepton_resonance_ladder_eq_scaled_lockin_candidate_ladder

/-- With the τ anchor, HQIV μ/e resonance masses overshoot PDG μ/e centrals (numeric fact). -/
theorem m_mu_PDG_lt_m_mu_from_resonance : m_mu_PDG < m_mu_from_resonance := by
  simp only [m_mu_PDG, m_tau_from_resonance, m_mu_from_resonance, resonance_k_tau_mu_eq_rat]
  norm_num

/-- With the τ anchor, HQIV e resonance mass overshoots the PDG e central (numeric fact). -/
theorem m_e_PDG_lt_m_e_from_resonance : m_e_PDG < m_e_from_resonance := by
  simp only [m_e_PDG, m_tau_from_resonance, m_e_from_resonance, m_mu_from_resonance,
    resonance_k_mu_e_eq_rat, resonance_k_tau_mu_eq_rat]
  norm_num

/-!
## Alternative mechanism: neutral-closure normalization (no τ-PDG anchor)

This route sets the charged-lepton scale from the derived neutral witness `m_nu_e_derived`
plus charge-decoration lift, then reuses the same geometric resonance steps for μ/e.
-/

/-- Alternative τ-scale from neutral-closure witness and charge-decoration lift. -/
noncomputable def m_tau_from_neutralLift : ℝ :=
  chargeDecoratedStandingWaveLift * m_nu_e_derived

/-- Alternative μ/e scales by the same geometric relaxation steps as the lock-in candidate ladder. -/
noncomputable def m_mu_from_neutralLift : ℝ := m_tau_from_neutralLift / resonance_k_tau_mu
noncomputable def m_e_from_neutralLift : ℝ := m_mu_from_neutralLift / resonance_k_mu_e

theorem m_tau_from_neutralLift_eq : m_tau_from_neutralLift = (2744 : ℝ) / 875 := by
  unfold m_tau_from_neutralLift
  rw [chargeDecoratedStandingWaveLift_eq_four, m_nu_e_derived_eq_suppression_times_M_Z,
    outerHorizonNeutrinoSuppression_eq_inv_140, boson_witness_M_Z]
  norm_num

theorem m_mu_from_neutralLift_eq :
    m_mu_from_neutralLift = (4256 : ℝ) / 3125 := by
  unfold m_mu_from_neutralLift
  rw [m_tau_from_neutralLift_eq, resonance_k_tau_mu_eq_rat]
  norm_num

theorem m_e_from_neutralLift_eq :
    m_e_from_neutralLift = (139944 : ℝ) / 184375 := by
  unfold m_e_from_neutralLift
  rw [m_mu_from_neutralLift_eq, resonance_k_mu_e_eq_rat]
  norm_num

theorem neutralLift_strict_ladder :
    m_e_from_neutralLift < m_mu_from_neutralLift ∧
      m_mu_from_neutralLift < m_tau_from_neutralLift := by
  constructor
  · unfold m_e_from_neutralLift
    have hμ : 0 < m_mu_from_neutralLift := by
      rw [m_mu_from_neutralLift_eq]
      norm_num
    have hk : 1 < resonance_k_mu_e := by
      rw [resonance_k_mu_e_eq_rat]
      norm_num
    have hkpos : 0 < resonance_k_mu_e := lt_trans zero_lt_one hk
    exact (div_lt_iff₀ hkpos).2 (by nlinarith)
  · unfold m_mu_from_neutralLift
    have hτ : 0 < m_tau_from_neutralLift := by
      rw [m_tau_from_neutralLift_eq]
      norm_num
    have hk : 1 < resonance_k_tau_mu := by
      rw [resonance_k_tau_mu_eq_rat]
      norm_num
    have hkpos : 0 < resonance_k_tau_mu := lt_trans zero_lt_one hk
    exact (div_lt_iff₀ hkpos).2 (by nlinarith)

theorem m_tau_from_resonance_lt_m_tau_from_neutralLift :
    m_tau_from_resonance < m_tau_from_neutralLift := by
  rw [m_tau_from_neutralLift_eq]
  norm_num [m_tau_from_resonance]

theorem m_mu_PDG_lt_m_mu_from_neutralLift : m_mu_PDG < m_mu_from_neutralLift := by
  rw [m_mu_from_neutralLift_eq]
  norm_num [m_mu_PDG]

theorem m_e_PDG_lt_m_e_from_neutralLift : m_e_PDG < m_e_from_neutralLift := by
  rw [m_e_from_neutralLift_eq]
  norm_num [m_e_PDG]

/-!
## TUFT / Beltrami spectral ladder (external mining)

See `HopfShellBeltramiMassBridge` and `AGENTS/TUFT_HOPF_SPECTRAL_MINING.md`.
The Beltrami generation ordering is independent of the τ-PDG anchor mismatch lemmas above.
-/

/-- Beltrami minimal eigenvalues for the three integrable Hopf-fiber sectors are strictly ordered. -/
theorem mass_spectrum_beltrami_generation_order :
    tuftMinimalBeltramiEigenvalue 1 < tuftMinimalBeltramiEigenvalue 2 ∧
      tuftMinimalBeltramiEigenvalue 2 < tuftMinimalBeltramiEigenvalue 3 :=
  tuftMinimalBeltrami_strict_on_generations

/-- Same spectral ladder sits below the top-colored witness (numeric). -/
theorem mass_spectrum_beltrami_to_top :
    tuftMinimalBeltramiEigenvalue 1 < allowedColorResonanceMass .upLike .heavy := by
  rw [allowedColorResonanceMass_upLike_heavy_eq_top_GeV, tuftMinimalBeltrami_one]
  norm_num [m_top_GeV]

/-- Emergent detuning: τ→μ resonance is a ratio of sector Gaussian leading weights. -/
theorem mass_spectrum_tau_mu_emergent :
    resonance_k_tau_mu =
      sectorGaussianLeadingWeight leptonMuonShell / sectorGaussianLeadingWeight leptonHeavyVertexShell :=
  resonance_k_tau_mu_eq_sectorGaussian_ratio

/-- Three Fano generations ↔ three Hopf fiber windings. -/
theorem mass_spectrum_three_generations_hopf_fano :
    Fintype.card ResonanceGeneration = 3 ∧
      (∀ g : ResonanceGeneration, HopfFiberWinding (g.val + 1)) :=
  ⟨resonanceGeneration_card_eq_three, hopfFiberWinding_of_resonanceGeneration⟩

end Hqiv.Physics
