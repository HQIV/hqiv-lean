import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.OMaxwellRationalMassLadder
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.QuarkOMaxwellBridge

/-!
Light-weight witness-only build entrypoint.

This exists so `lake build` can compile only the derived witness modules
used by `scripts/export_witnesses.lean`, without pulling in the heavy
`So8CoordMatrix` dependency chain.
-/

