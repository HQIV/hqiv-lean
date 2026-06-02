import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Geometry.Now
import Hqiv.Geometry.UniverseAge

/-!
# BBN as an epoch on the temperature ladder (universe age)

Light-element synthesis is **not** evaluated at the lock-in shell `referenceM ≈ 4` (QCD/baryogenesis).
It occurs when the cosmological temperature is in the BBN window (≈ 0.01–1 MeV), i.e. on shells
`m + 1 = T_Pl_MeV / T_MeV` (order `10²²` on the discrete ladder).

**Today** (`T ≈ T_CMB`) sits on a vastly larger shell (`nowShellPaper` in `Now.lean`); the observed
D/H and Y_p are **relics** frozen at the BBN epoch, not outputs of present-day network weights.

This module packages:
* shell ↔ temperature ↔ MeV maps (`bbnShellIndexFromMeV`, `shellIndexForTemperature`);
* lock-in–anchored binding Q's with **epoch temperature** in Boltzmann/Hubble factors;
* contrast readouts: BBN mid-epoch vs CMB today.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Mid-epoch BBN temperature (MeV) for default integration / readout. -/
def bbnMidEpochTemperatureMeV : ℝ := 1 / 10

/-- Lock-in temperature on the MeV map: `T_Pl_MeV / (referenceM + 1)`. -/
noncomputable def lockinTemperatureMeV : ℝ :=
  T_Pl_MeV / (referenceM + 1 : ℝ)

/-- CMB temperature today on the MeV map (order-of-magnitude `T_CMB / T_Pl`). -/
noncomputable def cmbTemperatureMeV : ℝ := T_CMB_natural * T_Pl_MeV

/-- Shell index at BBN mid-epoch (real-valued). -/
noncomputable def bbnMidEpochShell : ℝ :=
  bbnShellIndexFromMeV bbnMidEpochTemperatureMeV

/-- Shell index at lock-in on the MeV map. -/
noncomputable def lockinShellFromMeV : ℝ :=
  bbnShellIndexFromMeV lockinTemperatureMeV

/-- Cluster binding Q at lock-in shell (nuclear-scale network witness). -/
noncomputable def bbnDeuteronQAtLockin : ℝ :=
  bbnDeuteronBindingQ derivedProtonMass

noncomputable def bbnHelium4QAtLockin : ℝ :=
  bbnHelium4BindingQ derivedProtonMass

/-- Weak freeze-out temperature from η and the HQIV mass gap: `T_f = Q_np / log(η₁₀)`. -/
noncomputable def bbnFreezeoutTemperatureMeV (η : ℝ) : ℝ :=
  bbnNeutronProtonGap / Real.log (eta10 η)

/-- Y_p uses the **single** freeze-out temperature (not the instantaneous epoch T). -/
noncomputable def bbnYpAtFreezeout (η : ℝ) : ℝ :=
  bbnYpFromNeutronFraction (bbnNeutronProtonRatio (bbnFreezeoutTemperatureMeV η) bbnNeutronProtonGap)

/-- Light-element ratios at epoch `T_MeV` with lock-in Q's and η. -/
noncomputable def bbnDHAtEpoch (η T_MeV : ℝ) : ℝ :=
  (eta10 η) ^ bbnDH_etaExponent derivedProtonMass *
    bbnThermalSinkFactor bbnDeuteronQAtLockin bbnHelium4QAtLockin T_MeV

noncomputable def bbnHe3HAtEpoch (η T_MeV : ℝ) : ℝ :=
  (eta10 η) ^ bbnHe3_etaExponent derivedProtonMass *
    bbnThermalSinkFactor (bbnClusterBinding bbnBindingShell 3) bbnHelium4QAtLockin T_MeV

noncomputable def bbnLi7HAtEpoch (η T_MeV : ℝ) : ℝ :=
  (eta10 η) ^ bbnLi7_etaExponent derivedProtonMass *
    bbnThermalSinkFactor (bbnHelium4QAtLockin * (7 / 4 : ℝ)) bbnHelium4QAtLockin T_MeV

structure BBNEpochReadout where
  T_MeV : ℝ
  shellIndex : ℝ
  Yp : ℝ
  DH : ℝ
  He3H : ℝ
  Li7H : ℝ

/-- Readout at an arbitrary BBN-era temperature. -/
noncomputable def bbnEpochReadout (η T_MeV : ℝ) : BBNEpochReadout where
  T_MeV := T_MeV
  shellIndex := bbnShellIndexFromMeV T_MeV
  Yp := bbnYpAtFreezeout η
  DH := bbnDHAtEpoch η T_MeV
  He3H := bbnHe3HAtEpoch η T_MeV
  Li7H := bbnLi7HAtEpoch η T_MeV

/-- Mid-epoch BBN (T = 0.1 MeV) at lock-in η. -/
noncomputable def bbnEpochReadoutMid : BBNEpochReadout :=
  bbnEpochReadout eta_paper bbnMidEpochTemperatureMeV

/-- Today (CMB temperature): same formulas — abundances are **not** being synthesized now. -/
noncomputable def bbnEpochReadoutToday : BBNEpochReadout :=
  bbnEpochReadout eta_paper cmbTemperatureMeV

/-- Lock-in shell temperature readout (QCD scale on the MeV map — **not** the BBN epoch). -/
noncomputable def bbnEpochReadoutLockinShell : BBNEpochReadout :=
  bbnEpochReadout eta_paper lockinTemperatureMeV

/-- BBN mid-epoch shell is vastly larger than lock-in on the ladder (numeric certificate). -/
theorem bbnMidEpochShell_gt_lockinShell : lockinShellFromMeV < bbnMidEpochShell := by
  unfold bbnMidEpochShell lockinShellFromMeV bbnShellIndexFromMeV lockinTemperatureMeV
      bbnMidEpochTemperatureMeV T_Pl_MeV referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

/-- CMB shell index exceeds BBN mid-epoch (today is colder). -/
theorem bbnMidEpochShell_lt_nowShell : bbnMidEpochShell < nowShellPaper := by
  unfold bbnMidEpochShell nowShellPaper bbnShellIndexFromMeV bbnMidEpochTemperatureMeV
      shellIndexForTemperature T_CMB_natural T_Pl_MeV
  norm_num

theorem eta_bbn_epoch_eq_eta_paper :
    eta_at_horizon m_lockin m_lockin = eta_paper :=
  eta_bbn_eq_eta_paper

theorem bbnInternalTemperatureMeV_eq_freezeout (η : ℝ) :
    bbnInternalTemperatureMeV η bbnNeutronProtonGap = bbnFreezeoutTemperatureMeV η := by
  unfold bbnInternalTemperatureMeV bbnFreezeoutTemperatureMeV bbnNeutronProtonGap
  rfl

theorem bbnPartitionTemperatureMeV_eq_midEpoch :
    bbnPartitionTemperatureMeV = bbnMidEpochTemperatureMeV := rfl

theorem bbnYpAtFreezeout_pos : 0 < bbnYpAtFreezeout eta_paper := by
  unfold bbnYpAtFreezeout bbnYpFromNeutronFraction bbnNeutronProtonRatio bbnNeutronProtonGap
  positivity

theorem bbnEpochReadoutMid_freezeout_Yp :
    bbnEpochReadoutMid.Yp = bbnYpAtFreezeout eta_paper := rfl

theorem bbnDHAtEpoch_pos (η : ℝ) (T_MeV : ℝ) (hη10 : 1 < eta10 η) (hT : 0 < T_MeV) :
    0 < bbnDHAtEpoch η T_MeV := by
  unfold bbnDHAtEpoch bbnDH_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight eta10
  have hηpos : 0 < eta10 η := lt_trans (by norm_num : (0 : ℝ) < 1) hη10
  exact mul_pos (Real.rpow_pos_of_pos hηpos _) (bbnBoltzmannWeight_pos _ _)

def bbn_epoch_vital_readout : Prop :=
  lockinShellFromMeV < bbnMidEpochShell ∧
    bbnMidEpochShell < nowShellPaper ∧
      eta_at_horizon m_lockin m_lockin = eta_paper ∧
        0 < bbnEpochReadoutMid.Yp ∧
          0 < bbnEpochReadoutMid.DH ∧
            0 < bbnEpochReadoutMid.He3H ∧
              0 < bbnEpochReadoutMid.Li7H

theorem bbn_epoch_vital_readout_holds : bbn_epoch_vital_readout := by
  refine ⟨bbnMidEpochShell_gt_lockinShell, bbnMidEpochShell_lt_nowShell, eta_bbn_epoch_eq_eta_paper, ?_⟩
  dsimp [bbnEpochReadoutMid, bbnEpochReadout]
  have hT : 0 < bbnMidEpochTemperatureMeV := by norm_num [bbnMidEpochTemperatureMeV]
  have hη10 : 1 < eta10 eta_paper := eta10_eta_paper_gt_one
  have hηpos : 0 < eta10 eta_paper := lt_trans (by norm_num : (0 : ℝ) < 1) hη10
  refine ⟨bbnYpAtFreezeout_pos, ?_, ?_, ?_⟩
  · exact bbnDHAtEpoch_pos eta_paper bbnMidEpochTemperatureMeV hη10 hT
  · unfold bbnHe3HAtEpoch bbnHe3_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight eta10
    exact mul_pos (Real.rpow_pos_of_pos hηpos _) (bbnBoltzmannWeight_pos _ _)
  · unfold bbnLi7HAtEpoch bbnLi7_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight eta10
    exact mul_pos (Real.rpow_pos_of_pos hηpos _) (bbnBoltzmannWeight_pos _ _)

end

end Hqiv.Physics
