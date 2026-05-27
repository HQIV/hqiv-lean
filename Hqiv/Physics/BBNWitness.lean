import Hqiv.Physics.BBNEpochNetwork

/-!
# BBN integrated witness certificates (Python → Lean)

Values are exported by `scripts/hqiv_bbn_epoch_network.py` into `data/bbn_witnesses.json`.
They certify the **epoch cooling network** readout against the weak freeze-out partition witness,
without importing Coc semi-analytic fits as HQIV inputs.

Structural proofs (η, ladder, weak freeze-out Y_p positivity) live in `BBNNetworkFromWeights`
and `BBNEpochEvolution`; this file pins the **numeric** integrated network output.
-/

namespace Hqiv.Physics

noncomputable section

/-- Lock-in n–p gap (MeV), aligned with `data/hqiv_witnesses.json`. -/
def bbnNeutronProtonGap_MeV_witness : ℝ := 1.293

/-- Weak freeze-out Y_p from the weight partition (`bbn_window_integrated.Yp`). -/
def bbnYpFreezeoutWitness : ℝ := 0.2469135802469136

/-- Observed comparison band (Cooke et al. style; comparison layer only). -/
def bbnObservedYpCenter : ℝ := 0.244
def bbnObservedYpTolerance : ℝ := 0.004
def bbnObservedYpLow : ℝ := bbnObservedYpCenter - bbnObservedYpTolerance
def bbnObservedYpHigh : ℝ := bbnObservedYpCenter + bbnObservedYpTolerance

theorem bbnNeutronProtonGap_MeV_witness_pos : 0 < bbnNeutronProtonGap_MeV_witness := by
  unfold bbnNeutronProtonGap_MeV_witness
  norm_num

theorem bbnYpFreezeoutWitness_in_observed_band :
    bbnObservedYpLow ≤ bbnYpFreezeoutWitness ∧ bbnYpFreezeoutWitness ≤ bbnObservedYpHigh := by
  unfold bbnYpFreezeoutWitness bbnObservedYpLow bbnObservedYpHigh bbnObservedYpCenter
      bbnObservedYpTolerance
  constructor <;> norm_num

theorem bbnYpAtFreezeout_eta_paper_pos : 0 < bbnYpAtFreezeout eta_paper :=
  bbnYpAtFreezeout_pos

/-- Epoch-network ⁴He mass fraction (`epoch_network_integration.Yp`). -/
def bbnIntegratedYpWitness : ℝ := 0.2490520165152789

def bbnIntegratedFreezeWitness_MeV : ℝ := 0.7150406619827524

theorem bbnIntegratedYpWitness_pos : 0 < bbnIntegratedYpWitness := by
  unfold bbnIntegratedYpWitness
  norm_num

theorem bbnIntegratedFreezeWitness_pos : 0 < bbnIntegratedFreezeWitness_MeV := by
  unfold bbnIntegratedFreezeWitness_MeV
  norm_num

noncomputable def bbnIntegratedReadoutWitness : BBNIntegratedReadout where
  Yp := bbnIntegratedYpWitness
  DH := 0
  He3H := 0
  Li7H := 0
  T_freeze_MeV := bbnIntegratedFreezeWitness_MeV
  n_steps := 400

theorem bbnIntegratedReadoutWitness_Yp :
    bbnIntegratedReadoutWitness.Yp = bbnIntegratedYpWitness := rfl

theorem bbnIntegratedReadoutWitness_freeze :
    bbnIntegratedReadoutWitness.T_freeze_MeV = bbnIntegratedFreezeWitness_MeV := rfl

/-- Integrated epoch network stays within 1% of the weak freeze-out partition Y_p. -/
theorem bbnIntegratedYp_near_freezeout_witness :
    |bbnIntegratedYpWitness - bbnYpFreezeoutWitness| < (0.01 : ℝ) := by
  unfold bbnIntegratedYpWitness bbnYpFreezeoutWitness
  norm_num [abs_lt]

def bbn_integrated_witness_vital : Prop :=
  bbnObservedYpLow ≤ bbnYpFreezeoutWitness ∧
    bbnYpFreezeoutWitness ≤ bbnObservedYpHigh ∧
      |bbnIntegratedYpWitness - bbnYpFreezeoutWitness| < (0.01 : ℝ) ∧
        0 < bbnIntegratedFreezeWitness_MeV ∧
          0 < bbnIntegratedYpWitness

theorem bbn_integrated_witness_vital_holds : bbn_integrated_witness_vital :=
  ⟨bbnYpFreezeoutWitness_in_observed_band.1, bbnYpFreezeoutWitness_in_observed_band.2,
    bbnIntegratedYp_near_freezeout_witness, bbnIntegratedFreezeWitness_pos,
    bbnIntegratedYpWitness_pos⟩

end

end Hqiv.Physics
