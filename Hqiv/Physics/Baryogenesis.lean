import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.BaryogenesisWitness

/-!
# Baryogenesis (umbrella)

- **`BaryogenesisCore`:** shells, `T_QCD` / `T_lockin`, δE at QCD, Ω_k lock-in — **no** `eta_paper`.
- **`BaryogenesisEtaPaper`:** quarantined paper value (imported only through the witness module).
- **`BaryogenesisWitness`:** `eta_at_horizon` and calibration theorems.

For proofs that must not depend on the PDG-style η anchor, import `BaryogenesisCore` alone.
-/

-- (Re-export: all symbols live in `Hqiv` from the two modules above.)
