import HqivSpine.Physics.GenerationDetunedLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.HeavyQuarkAbsoluteScale
import HqivSpine.Physics.NeutrinoAbsoluteScale
import HqivSpine.Physics.CarrierMonogamySuppression
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.SpineMassDischarge` — capstone for spine-native fermion mass factors

Generation masses combine **Hopf-chart detuning** (`GenerationDetunedLadder`) with **extended
detuned-shell resonance** on outer ladder shells `15 → 33 → 58` (`GenerationResonanceLadder`).
Neutrino absolute scale uses **carrier monogamy suppression** `γ/(7·8)`.

**Structural ratios closed:** `μ/e = 4484/2499`, `τ/μ = 175/76` (legacy resonance targets mined
spine-native). PDG-scale discharge still requires the TUFT sector-spectral programme — not vev injection
into the spine modules.
-/

namespace HqivSpine.Physics.SpineMassDischarge

open HqivSpine.Physics
open HqivSpine.Physics.GenerationDetunedLadder
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.LeptonAbsoluteScale
open HqivSpine.Physics.HeavyQuarkAbsoluteScale
open HqivSpine.Physics.NeutrinoAbsoluteScale
open HqivSpine.Physics.CarrierMonogamySuppression

/-! ## Resonance-refined generation ladder -/

theorem spine_lepton_mu_over_e :
    leptonGroundFactor 2 / leptonGroundFactor 1 = 4484 / 2499 :=
  generationResonanceMassFactor_mu_over_electron

theorem spine_lepton_tau_over_mu :
    leptonGroundFactor 3 / leptonGroundFactor 2 = 175 / 76 :=
  generationResonanceMassFactor_tau_over_muon

theorem spine_resonance_shells :
    leptonHeavyResonanceShell = 15 ∧
      leptonMuonResonanceShell = 33 ∧ leptonElectronResonanceShell = 58 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Neutrino carrier closure -/

theorem spine_neutrino_suppression :
    neutrinoCarrierSuppression = carrierMonogamySuppression := rfl

theorem spine_neutrino_suppression_eq_inv_140 :
    neutrinoCarrierSuppression = 1 / 140 :=
  carrierMonogamySuppression_eq_inv_140

/-! ## Structural closure (PDG MeV discharge quarantined) -/

theorem spine_structural_generation_ratios_closed :
    leptonGroundFactor 2 / leptonGroundFactor 1 = 4484 / 2499 ∧
      leptonGroundFactor 3 / leptonGroundFactor 2 = 175 / 76 :=
  ⟨spine_lepton_mu_over_e, spine_lepton_tau_over_mu⟩

/-! ## Capstone -/

structure SpineMassDischargeClosure where
  hopf_ladder : GenerationDetunedLadder.GenerationDetunedLadderClosure
  resonance_ladder : GenerationResonanceLadder.GenerationResonanceLadderClosure
  lepton_mu_over_e : leptonGroundFactor 2 / leptonGroundFactor 1 = 4484 / 2499
  lepton_tau_over_mu : leptonGroundFactor 3 / leptonGroundFactor 2 = 175 / 76
  carrier_suppression : neutrinoCarrierSuppression = 1 / 140
  structural_ratios : leptonGroundFactor 2 / leptonGroundFactor 1 = 4484 / 2499 ∧
    leptonGroundFactor 3 / leptonGroundFactor 2 = 175 / 76

noncomputable def spineMassDischargeClosure : SpineMassDischargeClosure where
  hopf_ladder := generationDetunedLadderClosure
  resonance_ladder := generationResonanceLadderClosure
  lepton_mu_over_e := spine_lepton_mu_over_e
  lepton_tau_over_mu := spine_lepton_tau_over_mu
  carrier_suppression := spine_neutrino_suppression_eq_inv_140
  structural_ratios := spine_structural_generation_ratios_closed

theorem referenceM_spine_mass_discharge_closed : Nonempty SpineMassDischargeClosure :=
  ⟨spineMassDischargeClosure⟩

end HqivSpine.Physics.SpineMassDischarge
