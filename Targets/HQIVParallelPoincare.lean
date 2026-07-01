/-
Discrete parallel Poincaré programme (HQIV-native topology as **output**).

**Build:** `lake build HQIVParallelPoincare`

* `Hqiv.Topology.ParallelPoincareScaffold` — roadmap + proved template track.
* `Hqiv.Topology.ParallelPoincareReferenceModel` — template-pinned reference witness.
* `Hqiv.Topology.SignedShellBudget` — signed `shellBudgetMismatch` ledger + `xiHalfStep` regime.
* `Hqiv.Topology.ShellOpeningEvolution` — `shellOpeningStep`, lex `RealLyapunovDescent`, `S3NullReference` convergence.
* `Hqiv.Physics.ThermodynamicArrowFromShellOpening` — ladder laws + opening arrow bridge.
-/

import Hqiv.Topology.ParallelPoincareScaffold
import Hqiv.Topology.ParallelPoincareReferenceModel
import Hqiv.Topology.SignedShellBudget
import Hqiv.Topology.ShellOpeningEvolution
import Hqiv.Physics.ThermodynamicArrowFromShellOpening
