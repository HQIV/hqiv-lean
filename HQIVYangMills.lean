-- Stable import surface for the packaged lightcone/manifold/algebra object.
-- This target is intended to sit between the default lightweight CI roots and the
-- full experimental repo root. It re-exports the discrete light-cone core, the
-- manifold bridge layers, the stable algebra package surface, and the canonical
-- Yang-Mills-facing package object.
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Geometry.SpatialSliceManifold
import Hqiv.Geometry.SpatialSliceContinuumBridge
import Hqiv.Geometry.ManifoldLagrangianScaffold
import Hqiv.Algebra.G2Embedding
import Hqiv.Algebra.PhaseLiftDelta
import Hqiv.Algebra.Triality
import Hqiv.Algebra.SMEmbedding
import Hqiv.Algebra.AnomalyCancellation
import HQIVSO8Closure
import Hqiv.Physics.HQIVYangMillsPackage
