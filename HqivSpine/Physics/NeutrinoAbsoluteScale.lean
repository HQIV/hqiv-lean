import HqivSpine.Physics.MassLadder
import HqivSpine.Physics.GenerationResonanceLadder
import HqivSpine.Physics.LeptonAbsoluteScale
import HqivSpine.Physics.SectorNestedHopfBinding
import HqivSpine.Physics.CarrierMonogamySuppression
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.NowSliceCausalDiamond
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NeutrinoAbsoluteScale` — neutrinos on the one-slot nested Hopf trace

The one-slot content-class trace (`l = 1`) is **derived** in `ContentClassCompositeTrace` and wired
on nested Hopf chart rows in `SectorNestedHopfBinding` with the same proton-style inversion
`M = constituent − E_bind` as charged leptons and quarks.

**Nested Hopf readout.** `m_ν,readout(s, n) = massUnit(s) · generationResonanceMassFactor(n) / 4`.

**Absolute mass.** The chargeless mode has no inner well; the physical mass is the matched
charged-lepton anchor damped by **carrier monogamy suppression** `γ/(7·8) = 1/140`
(`CarrierMonogamySuppression`) — not an outer-horizon shell narrative.

  `m_ν,abs(s, g) = m_ℓ(s, g) · carrierMonogamySuppression = m_ℓ(s, g) / 140`.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.NeutrinoAbsoluteScale

open HqivSpine.Physics
open HqivSpine.Physics.GenerationResonanceLadder
open HqivSpine.Physics.NestedHopfBinding
open HqivSpine.Physics.SectorNestedHopfBinding
open HqivSpine.Physics.ContentClassCompositeTrace
open HqivSpine.Physics.CarrierMonogamySuppression
open HqivSpine.Physics.LeptonAbsoluteScale
open HqivSpine.Physics.CausalDiamond
open HqivSpine.Physics.NowSliceFromLattice

/-! ## Generation windings (parallel to charged leptons) -/

inductive NeutrinoGeneration
  | electron
  | muon
  | tau
  deriving DecidableEq, Repr

def NeutrinoGeneration.winding : NeutrinoGeneration → ℕ
  | .electron => 1
  | .muon => 2
  | .tau => 3

def NeutrinoGeneration.toLeptonGeneration : NeutrinoGeneration → LeptonGeneration
  | .electron => .electron
  | .muon => .muon
  | .tau => .tau

theorem NeutrinoGeneration.winding_eq_lepton (g : NeutrinoGeneration) :
    g.winding = g.toLeptonGeneration.winding := by
  rcases g with _ | _ | _ <;> rfl

def neutrinoHopfShell (g : NeutrinoGeneration) : IntegrableHopfShell :=
  leptonHopfShell g.toLeptonGeneration

theorem neutrinoHopfShell_winding (g : NeutrinoGeneration) :
    (neutrinoHopfShell g).winding = g.winding := by
  rw [neutrinoHopfShell, leptonHopfShell_winding, NeutrinoGeneration.winding_eq_lepton]

/-! ## One-slot nested Hopf readout -/

/-- **Dimensionless neutrino factor** at winding `n`: detuned generation factor / 4. -/
noncomputable def neutrinoGroundFactor (n : ℕ) : ℝ := generationResonanceMassFactor n / 4

theorem neutrinoGroundFactor_eq (n : ℕ) :
    neutrinoGroundFactor n = generationResonanceMassFactor n / 4 := rfl

theorem neutrinoGroundFactor_eq_lepton_scaled (n : ℕ) :
    neutrinoGroundFactor n =
      intrinsicWaveComplexity .neutrino / intrinsicWaveComplexity .chargedLepton *
        leptonGroundFactor n := by
  unfold neutrinoGroundFactor leptonGroundFactor intrinsicWaveComplexity conservedTripleCount
  ring

noncomputable def neutrinoMassReadout (s : NowSlice) (g : NeutrinoGeneration) : ℝ :=
  s.readout (neutrinoGroundFactor g.winding)

theorem neutrinoMassReadout_eq (s : NowSlice) (g : NeutrinoGeneration) :
    neutrinoMassReadout s g = s.massUnit * neutrinoGroundFactor g.winding := by
  unfold neutrinoMassReadout neutrinoGroundFactor
  rfl

theorem neutrinoMassReadout_over_lepton (s : NowSlice) (g : NeutrinoGeneration)
    (hN : s.massUnit ≠ 0) :
    neutrinoMassReadout s g / leptonMassReadout s g.toLeptonGeneration = (1 : ℝ) / 4 := by
  rw [neutrinoMassReadout_eq, leptonMassReadout_eq, neutrinoGroundFactor_eq,
    show g.toLeptonGeneration.winding = g.winding from
      (NeutrinoGeneration.winding_eq_lepton g).symm]
  have hgen : 0 < generationResonanceMassFactor g.winding :=
    generationResonanceMassFactor_pos (by rcases g with _ | _ | _ <;> decide)
  field_simp [hN, ne_of_gt hgen]

theorem neutrinoMassReadout_electron (s : NowSlice) :
    neutrinoMassReadout s .electron = s.massUnit * (759696 / 3138800) := by
  rw [neutrinoMassReadout_eq, NeutrinoGeneration.winding, neutrinoGroundFactor_eq,
    generationResonanceMassFactor_electron]
  ring

theorem neutrinoMassReadout_muon (s : NowSlice) :
    neutrinoMassReadout s .muon = s.massUnit * (76 / 175) := by
  rw [neutrinoMassReadout_eq, NeutrinoGeneration.winding, neutrinoGroundFactor_eq,
    generationResonanceMassFactor_muon]
  ring

theorem neutrinoMassReadout_tau (s : NowSlice) :
    neutrinoMassReadout s .tau = s.massUnit := by
  rw [neutrinoMassReadout_eq, NeutrinoGeneration.winding, neutrinoGroundFactor_eq,
    generationResonanceMassFactor_heavy]
  ring

/-! ## Carrier monogamy suppression -/

/-- **Carrier monogamy suppression** for absolute neutrino mass (not shell-indexed). -/
noncomputable def neutrinoCarrierSuppression : ℝ := carrierMonogamySuppression

theorem neutrinoCarrierSuppression_eq_inv_140 :
    neutrinoCarrierSuppression = 1 / 140 :=
  carrierMonogamySuppression_eq_inv_140

noncomputable def neutrinoChargedAnchor (s : NowSlice) (g : NeutrinoGeneration) : ℝ :=
  leptonMassReadout s g.toLeptonGeneration

theorem neutrinoChargedAnchor_eq (s : NowSlice) (g : NeutrinoGeneration) :
    neutrinoChargedAnchor s g = leptonMassReadout s g.toLeptonGeneration := rfl

/-! ## Absolute mass = anchor × carrier suppression -/

noncomputable def neutrinoAbsoluteMass (s : NowSlice) (g : NeutrinoGeneration) : ℝ :=
  neutrinoAbsoluteMassFromAnchor (neutrinoChargedAnchor s g)

theorem neutrinoAbsoluteMass_eq (s : NowSlice) (g : NeutrinoGeneration) :
    neutrinoAbsoluteMass s g =
      neutrinoChargedAnchor s g * neutrinoCarrierSuppression := by
  unfold neutrinoAbsoluteMass neutrinoAbsoluteMassFromAnchor
  rfl

theorem neutrinoAbsoluteMass_eq_lepton_over_140 (s : NowSlice) (g : NeutrinoGeneration) :
    neutrinoAbsoluteMass s g = leptonMassReadout s g.toLeptonGeneration / 140 := by
  rw [neutrinoAbsoluteMass_eq, neutrinoChargedAnchor_eq, neutrinoCarrierSuppression_eq_inv_140]
  field_simp

theorem neutrinoAbsoluteMass_lt_charged (s : NowSlice) (g : NeutrinoGeneration)
    (hPhi : 0 < 1 + s.bigPhi) (hphi : 0 ≤ s.phi) (ht : 0 ≤ s.apparentAge) :
    0 < neutrinoAbsoluteMass s g ∧
      neutrinoAbsoluteMass s g < leptonMassReadout s g.toLeptonGeneration := by
  have hχ := leptonMassReadout_pos s g.toLeptonGeneration hPhi hphi ht
  exact neutrinoAbsoluteMassFromAnchor_lt_anchor hχ

/-! ## Lock-in diamond -/

theorem lockin_neutrinoMassReadout_electron :
    neutrinoMassReadout lockinNowSlice .electron = 3798480 / 3138800 := by
  rw [neutrinoMassReadout_electron, lockinNowSlice_massUnit]
  norm_num

theorem lockin_neutrinoMassReadout_muon :
    neutrinoMassReadout lockinNowSlice .muon = 76 / 35 := by
  rw [neutrinoMassReadout_muon, lockinNowSlice_massUnit]
  norm_num

theorem lockin_neutrinoMassReadout_tau :
    neutrinoMassReadout lockinNowSlice .tau = 5 := by
  rw [neutrinoMassReadout_tau, lockinNowSlice_massUnit]

theorem lockin_neutrinoAbsoluteMass_electron :
    neutrinoAbsoluteMass lockinNowSlice .electron = 3798480 / 109858000 := by
  rw [neutrinoAbsoluteMass_eq_lepton_over_140]
  simp only [NeutrinoGeneration.toLeptonGeneration]
  rw [lockin_leptonMassReadout_electron]
  norm_num

theorem lockin_neutrinoAbsoluteMass_muon :
    neutrinoAbsoluteMass lockinNowSlice .muon = 304 / 4900 := by
  rw [neutrinoAbsoluteMass_eq_lepton_over_140]
  simp only [NeutrinoGeneration.toLeptonGeneration]
  rw [lockin_leptonMassReadout_muon]
  norm_num

theorem lockin_neutrinoAbsoluteMass_tau :
    neutrinoAbsoluteMass lockinNowSlice .tau = 1 / 7 := by
  rw [neutrinoAbsoluteMass_eq_lepton_over_140]
  simp only [NeutrinoGeneration.toLeptonGeneration]
  rw [lockin_leptonMassReadout_tau]
  norm_num

/-! ## Capstone -/

structure NeutrinoAbsoluteScaleClosure where
  ground_factor : ∀ n, neutrinoGroundFactor n = generationResonanceMassFactor n / 4
  readout_quarter_lepton :
    ∀ (s : NowSlice) (g : NeutrinoGeneration), s.massUnit ≠ 0 →
      neutrinoMassReadout s g / leptonMassReadout s g.toLeptonGeneration = 1 / 4
  absolute_from_anchor :
    ∀ (s : NowSlice) (g : NeutrinoGeneration),
      neutrinoAbsoluteMass s g = leptonMassReadout s g.toLeptonGeneration / 140
  carrier_suppression : neutrinoCarrierSuppression = 1 / 140
  lockin_readouts :
    neutrinoMassReadout lockinNowSlice .electron = 3798480 / 3138800 ∧
    neutrinoMassReadout lockinNowSlice .muon = 76 / 35 ∧
    neutrinoMassReadout lockinNowSlice .tau = 5
  lockin_absolute :
    neutrinoAbsoluteMass lockinNowSlice .electron = 3798480 / 109858000 ∧
    neutrinoAbsoluteMass lockinNowSlice .muon = 304 / 4900 ∧
    neutrinoAbsoluteMass lockinNowSlice .tau = 1 / 7

noncomputable def neutrinoAbsoluteScaleClosure : NeutrinoAbsoluteScaleClosure where
  ground_factor := fun n => neutrinoGroundFactor_eq n
  readout_quarter_lepton := fun s g hN => neutrinoMassReadout_over_lepton s g hN
  absolute_from_anchor := fun s g => neutrinoAbsoluteMass_eq_lepton_over_140 s g
  carrier_suppression := neutrinoCarrierSuppression_eq_inv_140
  lockin_readouts :=
    ⟨lockin_neutrinoMassReadout_electron, lockin_neutrinoMassReadout_muon,
      lockin_neutrinoMassReadout_tau⟩
  lockin_absolute :=
    ⟨lockin_neutrinoAbsoluteMass_electron, lockin_neutrinoAbsoluteMass_muon,
      lockin_neutrinoAbsoluteMass_tau⟩

end HqivSpine.Physics.NeutrinoAbsoluteScale
