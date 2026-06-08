/-
Machine-checked scope for `papers/closure.tex` (Zenodo companion): discrete
null-lattice / curvature layer and the symbolic \(\mathfrak{so}(8)\) closure
interface (axioms packaging the generator matrices).

**Build:** `lake build HQIVPaperClaims`

This root is intentionally narrow: no SM stack, no SAT / satisfiability formalism,
and no heavy matrix Lie-closure certificate (`Hqiv.GeneratorsLieClosure` /
`Hqiv.LieBracketCell.*`). For the optional packaged causal-forcing cone used by
other HQIV manuscripts, import `Hqiv.Story.CausalRapidityForcing` from the full
library (`HQIVLEAN`) instead.
-/

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.SO8ClosureSymbolic
