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
import Hqiv.Story.PlasticCriticalLineBridge
import Hqiv.Story.PlasticPhaseBalanceImpliesReHalf
import Hqiv.Story.NearDiagonalThreeCubes
import Hqiv.Story.PlasticLatticePhaseImpliesZetaZero
import Hqiv.Story.PlasticRHBridgeFinal
