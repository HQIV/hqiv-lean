/-
Machine-checked scope for HQIV paper appendices: discrete null-lattice / curvature
layer, packaged causal forcing (`CausalRapidityForcing`), and the symbolic
\(\mathfrak{so}(8)\) closure interface (axioms packaging the generator matrices).

Covers `papers/closure.tex` (Zenodo companion) and
`papers/hqiv_rapidity_manifold_so8_closure` (Appendix A, “Formal Verification Map”).

**Build:** `lake build HQIVPaperClaims`

This root is intentionally narrower than `HQIVLEAN` (no SM/GR/lepton stack, quantum
mechanics layers, etc.): it is the **recommended library target** when auditing only
Appendix~A / closure claims. Elaboration time can still be substantial because the
transitive cone includes `OctonionicLightCone`, but it intentionally avoids the heavy
Lie-closure matrix certificate cone (`Hqiv.GeneratorsLieClosure` / `Hqiv.LieBracketCell.*`).
-/

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Story.CausalRapidityForcing
import Hqiv.SO8ClosureSymbolic
