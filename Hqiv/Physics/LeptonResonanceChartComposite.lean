import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.FanoSectorSpectralMassEmergence
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.HalfStepBeltramiShellBridge
import Hqiv.Physics.HopfShellBeltramiMassBridge

namespace Hqiv.Physics

/-!
# Charged-lepton resonance as composite shell / jet readouts

Shows that PDG-free lepton mass ratios come from **distant** detuned-shell ladders
(`m = 15, 33, 58`), factorized into bare shell area and O-Maxwell 1-jet quotients,
and **distinct** from the lock-in / holonomy charts where `4/3` and `3/2` appear.
-/

/-! ## Factorization (emergent sector-Gaussian quotients) -/

theorem resonance_k_tau_mu_eq_shell_over_jet_factorization :
    resonance_k_tau_mu =
      (shellSurface leptonMuonShell / shellSurface leptonHeavyVertexShell) /
        (omaxwellFanoDetuning1Jet leptonMuonShell / omaxwellFanoDetuning1Jet leptonHeavyVertexShell) := by
  rw [resonance_k_tau_mu_eq_geometricResonanceStep]
  exact geometricResonanceStep_eq_shell_and_jet_quotient leptonMuonShell leptonHeavyVertexShell

theorem resonance_k_mu_e_eq_shell_over_jet_factorization :
    resonance_k_mu_e =
      (shellSurface leptonElectronShell / shellSurface leptonMuonShell) /
        (omaxwellFanoDetuning1Jet leptonElectronShell / omaxwellFanoDetuning1Jet leptonMuonShell) := by
  rw [resonance_k_mu_e_eq_geometricResonanceStep]
  exact geometricResonanceStep_eq_shell_and_jet_quotient leptonElectronShell leptonMuonShell

theorem resonance_k_tau_mu_eq_sectorGaussian_ratio_emergent :
    resonance_k_tau_mu =
      sectorGaussianLeadingWeight leptonMuonShell / sectorGaussianLeadingWeight leptonHeavyVertexShell :=
  resonance_k_tau_mu_eq_sectorGaussian_ratio

theorem resonance_k_mu_e_eq_sectorGaussian_ratio_emergent :
    resonance_k_mu_e =
      sectorGaussianLeadingWeight leptonElectronShell / sectorGaussianLeadingWeight leptonMuonShell :=
  resonance_k_mu_e_eq_sectorGaussian_ratio

/-! ## Chart separation: lepton ladder ≠ Beltrami / lock-in neighbors -/

theorem resonance_k_tau_mu_ne_beltrami_four_thirds :
    resonance_k_tau_mu ≠ tuftBeltramiResonanceRatio 3 2 := by
  rw [resonance_k_tau_mu_eq_rat, tuftBeltramiResonanceRatio_tau_mu]
  norm_num

theorem resonance_k_tau_mu_ne_geometric_lockin_neighbor :
    resonance_k_tau_mu ≠ geometricResonanceStep 4 3 := by
  rw [resonance_k_tau_mu_eq_rat, geometricResonanceStep_four_three_eq_four_thirds]
  norm_num

theorem resonance_k_mu_e_ne_beltrami_three_halves :
    resonance_k_mu_e ≠ tuftBeltramiResonanceRatio 2 1 := by
  rw [resonance_k_mu_e_eq_rat, tuftBeltramiResonanceRatio_mu_e]
  norm_num

theorem resonance_k_mu_e_ne_holonomy_vertex_ratio :
    resonance_k_mu_e ≠
      holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle := by
  rw [resonance_k_mu_e_eq_rat, holonomyRowRhs_middle_heavy_ratio]
  norm_num

/-! ## Bundled witness -/

/-- Lepton resonance factors are emergent composites, not the local Beltrami/holonomy ratios. -/
structure LeptonResonanceChartCompositeWitness where
  tau_mu_factorized : resonance_k_tau_mu =
    sectorGaussianLeadingWeight leptonMuonShell / sectorGaussianLeadingWeight leptonHeavyVertexShell
  mu_e_factorized : resonance_k_mu_e =
    sectorGaussianLeadingWeight leptonElectronShell / sectorGaussianLeadingWeight leptonMuonShell
  tau_mu_ne_beltrami : resonance_k_tau_mu ≠ tuftBeltramiResonanceRatio 3 2
  mu_e_ne_beltrami : resonance_k_mu_e ≠ tuftBeltramiResonanceRatio 2 1
  mu_e_ne_holonomy_vertices :
    resonance_k_mu_e ≠ holonomyRowRhs fanoVertexHeavyGen / holonomyRowRhs fanoVertexMiddle

theorem leptonResonanceChartCompositeWitness_default : LeptonResonanceChartCompositeWitness where
  tau_mu_factorized := resonance_k_tau_mu_eq_sectorGaussian_ratio_emergent
  mu_e_factorized := resonance_k_mu_e_eq_sectorGaussian_ratio_emergent
  tau_mu_ne_beltrami := resonance_k_tau_mu_ne_beltrami_four_thirds
  mu_e_ne_beltrami := resonance_k_mu_e_ne_beltrami_three_halves
  mu_e_ne_holonomy_vertices := resonance_k_mu_e_ne_holonomy_vertex_ratio

end Hqiv.Physics
