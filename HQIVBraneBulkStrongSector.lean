-- Brane–bulk / strong-sector integration roots: Fano-truss readout, phase-lift cost slot,
-- discrete holonomy/kinetic readout, packaged Yang-Mills-facing carrier (`G₂`/`Δ` in
-- `HQIVYangMillsPackage`), and O–Maxwell holonomy glue.
-- Build: `lake build HQIVBraneBulkStrongSector` (run **one** at a time; do not stack with `HQIVSO8Closure`).
-- Heavy generated Lie: `lake build Hqiv.Algebra.G2DeltaGeneratedLie` or `lake build HQIVSO8Closure`.
import Hqiv.Physics.BraneBulkFanoTruss
import Hqiv.Physics.G2AutomorphismEnergyCost
import Hqiv.Physics.DiscreteYMConfinement
import Hqiv.Physics.HQIVYangMillsPackage
import Hqiv.Physics.ActionHolonomyGlue
