import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Physics.BaryogenesisDynamicBulk

/-!
# Baryogenesis (umbrella)

Ratio-level baryon-asymmetry bookkeeping on the shared HQIV spine. **Baryogenesis is an
application** of the null-lattice / curvature-ratio / $G_2\cup\{\Delta\}$ sector package
(nucleon binding, SM synthesis, chemistry, BBN, outside-closure witnesses use the same spine);
it is not the programme objective.

Lock-in is at `m_lockin = referenceM = 4` — the first shell row with enough octonion-mode
budget for the full sector readout (`new_modes_referenceM_numeric`, `G2_plus_Delta_closes_to_so8`).

- **`BaryogenesisCore`:** shells, `T_QCD` / `T_lockin`, δE at QCD, Ω_k lock-in — **no** `eta_paper`.
- **`BaryogenesisEtaPaper`:** quarantined paper value (imported only through the witness module).
- **`BaryogenesisWitness`:** `eta_at_horizon` and calibration theorems.
- **`BaryogenesisDynamicBulk`:** colour-singlet projector, `Ω_b` readout, comparison-layer η bridge.

For proofs that must not depend on the PDG-style η anchor, import `BaryogenesisCore` alone.
 -/

-- (Re-export: all symbols live in `Hqiv` from the two modules above.)
