/-
Machine-checked scope for `papers/hqiv_rapidity_manifold_so8_closure` (Appendix A,
“Formal Verification Map”): discrete growth / curvature, SAT shared-manifold
rapidity transport, packaged causal forcing theorems, and a symbolic
\(G_2+\Delta\to\mathfrak{so}(8)\) closure interface.

**Build:** `lake build HQIVPaperClaims`

This root is intentionally narrower than `HQIVLEAN` (no SM/GR/lepton stack, quantum
mechanics layers, etc.): it is the **recommended library target** when auditing only
Appendix~A. Elaboration time can still be substantial because the transitive cone includes
`OctonionicLightCone`, but it intentionally avoids the heavy Lie-closure matrix certificate cone.
-/

import Hqiv.Story.CausalRapidityForcing
import Hqiv.SO8ClosureSymbolic
