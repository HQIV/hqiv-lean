import Hqiv.Physics.FanoHolonomyOverlap
import Hqiv.Physics.FanoMixingMatrix
import Hqiv.Physics.CkmHolonomyReadout
import Hqiv.Physics.PMNSHolonomyReadout
import Hqiv.Physics.RareDecayReadout
import Hqiv.Physics.FlavorCPObservable
import Hqiv.Physics.FlavorDifferentialReadout
import Hqiv.Physics.FlavorLongitudinalAmplitudeBridge
import Hqiv.Physics.GluonSieversHopfBridge
import Hqiv.Physics.HiggsSelfCouplingReadout
import Hqiv.Physics.SMEFTDiscreteExporter
import Hqiv.Physics.PartonCarrierEvolution
import Hqiv.Physics.PatchScatteringUnitarity
import Hqiv.Physics.CosmologicalPerturbationReadout

/-!
# Proof spine inventory

Central import hub for the self-reinforcing proof ladder. Each certificate
aggregates the theorem spine for one phase; see `docs/PROOF_SPINE_MAP.md`.
-/

namespace Hqiv.Physics

/-- Phase 1: Fano holonomy overlap infrastructure. -/
abbrev ProofPhase1 := FanoHolonomyOverlapCertificate

/-- Phase 2: CKM holonomy readout. -/
abbrev ProofPhase2 := CkmHolonomyReadout

/-- Phase 3: PMNS holonomy readout. -/
abbrev ProofPhase3 := PMNSHolonomyReadout

/-- Phase 4: Rare decay + CP observables + differential/angular distributions. -/
structure ProofPhase4 where
  rare : RareDecayReadoutCertificate
  cp : FlavorCPObservableCertificate
  differential : FlavorDifferentialReadoutCertificate
  longitudinal : FlavorLongitudinalAmplitudeCertificate

/-- Strong-sector bridge to Sievers glueball narrative (convergent octonionic Hopf picture). -/
abbrev ProofPhaseStrongBridge := GluonSieversHopfBridgeCertificate

/-- Phase 5: EW precision + SMEFT. -/
structure ProofPhase5 where
  higgs : HiggsCouplingCertificate
  smeft : SMEFTDiscreteExportCertificate

/-- Phase 6: Strong sector / collider. -/
structure ProofPhase6 where
  pdf : PartonCarrierEvolutionCertificate
  unitarity : PatchScatteringUnitarityCertificate

/-- Phase 7: Cosmology capstone. -/
abbrev ProofPhase7 := CosmologicalPerturbationCertificate

structure ProofSpineInventory where
  phase1 : ProofPhase1
  phase2 : ProofPhase2
  phase3 : ProofPhase3
  phase4 : ProofPhase4
  phase5 : ProofPhase5
  phase6 : ProofPhase6
  phase7 : ProofPhase7
  strong_bridge : ProofPhaseStrongBridge

noncomputable def proofSpineInventory_holds : ProofSpineInventory where
  phase1 := fanoHolonomyOverlapCertificate_holds
  phase2 := assembleCkmHolonomyReadout
  phase3 := assemblePMNSHolonomyReadout
  phase4 := {
    rare := rareDecayReadoutCertificate_holds
    cp := flavorCPObservableCertificate_holds
    differential := flavorDifferentialReadoutCertificate_holds
    longitudinal := flavorLongitudinalAmplitudeCertificate_holds
  }
  phase5 := { higgs := higgsCouplingCertificate_holds, smeft := smeftDiscreteExportCertificate_holds }
  phase6 := { pdf := partonCarrierEvolutionCertificate_holds, unitarity := patchScatteringUnitarityCertificate_holds }
  phase7 := cosmologicalPerturbationCertificate_holds
  strong_bridge := gluonSieversHopfBridgeCertificate_holds

end Hqiv.Physics
