import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.BBNEpochEvolution
import Hqiv.Physics.BBNEpochNetwork
import Hqiv.Physics.BBNWitness

/-!
# Big-bang nucleosynthesis (umbrella)

**Primary:** `BBNNetworkFromWeights` — light-element abundances from composite-trace binding,
isotope-ladder valley weights, `derivedDeltaM`, and lock-in η.

**Comparison layer (SM reference only):** Coc et al. (2015) semi-analytic fits below; not HQIV inputs.

Python: `scripts/hqiv_bbn_abundances.py` → `data/bbn_witnesses.json`.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

def eta10_anchor : ℝ := 6.10

/-- Coc et al. 2015 Eq. 13 — **comparison only**, not derived from HQIV weights. -/
noncomputable def bbnYpMassFraction_coc2015 (η N_ν τ_n : ℝ) : ℝ :=
  0.24703 * (eta10 η / eta10_anchor) ^ (-(39 / 1000 : ℝ)) * (N_ν / 3) ^ (163 / 1000 : ℝ) *
    (τ_n / 880.3) ^ (73 / 100 : ℝ)

noncomputable def bbnDHNumberRatio_coc2015 (η : ℝ) : ℝ :=
  2.579e-5 * (eta10_anchor / eta10 η) ^ (161 / 100 : ℝ)

/-- Re-export primary network readout. -/
abbrev bbnReadoutAtLockin := bbnNetworkReadoutAtLockin

theorem bbn_vital_readout_holds : bbn_network_vital_readout :=
  bbn_network_vital_readout_holds

theorem bbn_epoch_vital_holds : bbn_epoch_vital_readout :=
  bbn_epoch_vital_readout_holds

theorem bbn_integrated_witness_holds : bbn_integrated_witness_vital :=
  bbn_integrated_witness_vital_holds

/-- Combined BBN certificate: network weights + epoch ladder + integrated Python witness. -/
def bbn_full_vital_readout : Prop :=
  bbn_network_vital_readout ∧ bbn_epoch_vital_readout ∧ bbn_integrated_witness_vital

theorem bbn_full_vital_readout_holds : bbn_full_vital_readout :=
  ⟨bbn_network_vital_readout_holds, bbn_epoch_vital_readout_holds, bbn_integrated_witness_vital_holds⟩

end

end Hqiv.Physics
