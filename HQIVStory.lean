--| End-to-end narrative spine: light cone → … → Dojo YM/NS problem wiring.
--| Build: `lake build HQIVStory` — see `AGENTS/REFACTOR_END_TO_END_PLAN.md`
--| Octonion Lie DOF (28 = dim so(8), backbone `sorry` in Story; proof: `HQIVSO8Closure` / `Hqiv.SO8Closure`)
--| Gap inventory: `MassGapWiring`; completion `MassGapCompletionBundle`; partial QFT builder `MassGapCompletionScaffold`
--| O-Maxwell + patch QM ↔ Dojo slot hub: `Hqiv.Story.OMaxwellQMToDojoSlot` (`OMaxwellQMToDojo` names); continuum hub `Hqiv.Physics.LightConeMaxwellQFTBridge`
--| Millennium bridge patch slot: `MillenniumBridgePatchVacuum` (`MillenniumG`, `PatchHilbert`, `patchVacuum`, `patchHilbertPatchBridge`); patch↔toy Hilbert bridge `PatchToWightmanToyHilbertBridge`; patch Wightman+ladder Hamiltonian scaffold `MillenniumBridgePatchPoincareWightman`
--| `FiniteMassSpectrum` vs zero Hamiltonian: `MillenniumFiniteMassObstruction`, `MillenniumBridgeToyWitness.not_FiniteMassSpectrum_of_wightman_hamiltonian_eq_zero`
--| Dojo YM interface witness: `QuantumYangMillsHQIVInterface` / `QuantumYangMillsFromPatchHQIV` (patch jet `hqivPatchJetOperatorValuedDistribution`); obligations `hqiv_promotion_obligations_hqivInterfaceQFT` in `YMRemainingObligations`; ladder scale decoupled via `LadderGapCandidateWell` so `Chapter08` can import PatchHQIV (`MassGap.nonempty_hqivInterface_quantumYangMills`)
--| Dynamic-well theorem shell: `WellShapeFromDynamics`
import Hqiv.Story.MassGapWiring
import Hqiv.Story.MassGapCompletionBundle
import Hqiv.Story.MassGapCompletionScaffold
import Hqiv.Story.WellShapeFromDynamics
import Hqiv.Story.YMInputsFromWellDynamics
import Hqiv.Story.DiscreteOMaxwellToYMInputs
import Hqiv.Story.DiscreteOMaxwellHQIVInstance
import Hqiv.Story.OMaxwellQMToDojoSlot
import Hqiv.Story.SketchesConsumedLadderWell
import Hqiv.Story.YMBridgeProvedHelpers
import Hqiv.Story.MillenniumBridgePatchVacuum
import Hqiv.Story.PatchToWightmanToyHilbertBridge
import Hqiv.Story.MillenniumBridgePatchPoincareWightman
import Hqiv.Story.NonabelianSO8SmearedPatchField
--| HQIV-facing Dojo `QuantumYangMillsTheory` interface witness (not mass gap)
import Hqiv.Story.QuantumYangMillsHQIVInterface
import Hqiv.Story.MillenniumBridgeToyWitness
import Hqiv.Story.MillenniumFiniteMassObstruction
import Hqiv.Story.GaugeGroupFromHQIVSketch
import Hqiv.Story.HQIVGaugeConstructionBlueprint
import Hqiv.Story.YMRemainingObligations
import Hqiv.Story.NSRemainingObligations
import Hqiv.Story.HQIVDissipativeBridge
import Hqiv.Story.PlasticSpiralInterceptCoverage
import Hqiv.Story.HigherOrderArityDiagonalSymmetry
import Hqiv.Story.ArityMirrorCancellationBridge
import Hqiv.Story.ArityFTADecomposition
import Hqiv.Story.PlasticTwistedEulerCharacter
import Hqiv.Story.S3PrimeAxisCancellation
import Hqiv.Story.S3DiscretePrimeAxisSampling
import Hqiv.Story.S3EulerSO4PrimeAxisBridge
import Hqiv.Story.PlasticCriticalLineBridge
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Story.NearDiagonalThreeCubes
import Hqiv.Story.PlasticLatticePhaseImpliesZetaZero
import Hqiv.Story.PlasticRHBridgeFinal
import Hqiv.Story.S3ToZetaBridge
import Hqiv.Story.S3RHZeroSetBridge
import Hqiv.Story.S3SurvivorsForcePhase
import Hqiv.Story.S3RHObligationEquivalence
import Hqiv.Story.S3QuaternionOrientation
import Hqiv.Story.S3ZeroEquationEquivalence
import Hqiv.Story.S3ZetaAlgebraicLock
import Hqiv.Story.S3ZetaResidualModel
import Hqiv.Story.S3CenteredResidualModel
import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3PoleZeroChannel
import Hqiv.Story.S3ComplexResidualModel
import Hqiv.Story.S3RotationRigidity
import Hqiv.Story.S3TwiddleRigidityForcesLine
import Hqiv.Story.S3DeltaOrbitOffStrip
import Hqiv.Story.S3ZetaClosedForm
import Hqiv.Story.S3RHDischarge
import Hqiv.Story.S3SO4InteriorWitness
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Story.S3HarmonicDeltaEvenOrbit
import Hqiv.Story.S3ZetaAxisRotationProjection
import Hqiv.Story.S3InteriorStripHClosedForm
import Hqiv.Story.S3InteriorPathA
import Hqiv.Story.S3ZeroProducingOrbits
import Hqiv.Story.S3InteriorPathE
import Hqiv.Story.S3ZeroOrbitPathE
import Hqiv.Story.S3PathCHolonomy
import Hqiv.Story.S3StripRollingProjection
import Hqiv.Story.S3HopfShellHolonomy
import Hqiv.Story.S3OrbitVsPointwiseGap
import Hqiv.Story.S3PrimalitySlotDecoupling
import Hqiv.Story.S3DivisorPairingSelectsSquares
import Hqiv.Story.S3TwiddleResidualMoebius
import Hqiv.Story.S3FiniteSymmetryCannotIsolatePrimes
import Hqiv.Story.S3SixPolesResidual
import Hqiv.Story.S3EulerCircleLatticePoints
import Hqiv.Story.S3ExplicitFormulaDualitySlot
import Hqiv.Story.S3WeilPositivityCriterion
import Hqiv.Story.S3ExplicitFormulaIdentity
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3HarmonicPrimeZetaPath
import Hqiv.Story.S3EulerExplicitFormulaLocalization
import Hqiv.Story.S3ConstructionsEquivalent
