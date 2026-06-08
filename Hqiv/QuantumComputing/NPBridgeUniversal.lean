import Hqiv.QuantumComputing.NPBridgeDecision
import Hqiv.QuantumComputing.CertificateDomainCover

/-!
# Universal NP-bridge composition theorem (conditional, zero-axiom)

This module closes the **composition** gap: given an abstract NP-style language, a polynomial
HQIV encoder that exports `acceptedPolynomial` certificates at every instance size, and optional
measurement/readout soundness witnesses, the combined simulate-then-readout procedure is
polynomially bounded and each encoded circuit family is in
`ClassicalPolynomialSimulableByDomainCover`.

**This does not prove NP = P unconditionally.** All load-bearing assumptions are explicit
structures below; concrete SAT/ATSP benchmarks instantiate them via generated witnesses.
-/

namespace Hqiv.QuantumComputing.NPBridgeUniversal

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.NPBridgeDecision

/-- Abstract NP-style language over instance type `I`. -/
structure NPLanguageModel (I : Type) where
  instanceSize : I → Nat
  member : I → Prop

/-- Polynomial HQIV encoder: every instance maps to an accepted frequency certificate. -/
structure HQIVNPEncoder (I : Type) where
  cert : I → FrequencyPolynomialCertificate
  n : I → Nat
  size_ge_one : ∀ i, 1 ≤ n i
  accepted : ∀ i, (cert i).acceptedPolynomial (n i)

/-- Readout soundness: threshold-exceeding measurement witnesses certify membership. -/
structure HQIVNPReadoutSound (I : Type) (L : NPLanguageModel I) where
  witness : I → MeasurementOutcomeWitness
  soundPositive : ∀ i, (witness i).thresholdMet → L.member i

/-- Bundled universal discharge for one encoded instance family. -/
structure UniversalNPBridgeDischarge (I : Type) (L : NPLanguageModel I) (E : HQIVNPEncoder I) where
  search : ∀ i, NPSearchDischarge (E.cert i) (E.n i)
  domainCover : ∀ i, ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert (E.cert i))

namespace HQIVNPEncoder

/-- Every encoded instance has polynomial simulate-then-readout cost. -/
theorem search_poly {I : Type} (E : HQIVNPEncoder I) (i : I) :
    NPSearchDischarge (E.cert i) (E.n i) :=
  NPSearchDischarge.of_acceptedPolynomial (E.cert i) (E.n i) (E.size_ge_one i) (E.accepted i)

/-- Every encoded instance is classically polynomial-simulable by domain cover. -/
theorem domain_cover {I : Type} (E : HQIVNPEncoder I) (i : I) :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert (E.cert i)) :=
  frequency_cert_acceptedPolynomial_in_P (E.cert i) (E.n i) (E.size_ge_one i) (E.accepted i)

/-- Assemble the bundled universal discharge from encoder acceptance alone. -/
def universalDischarge {I : Type} (_L : NPLanguageModel I) (E : HQIVNPEncoder I) :
    UniversalNPBridgeDischarge I _L E where
  search := fun i => search_poly E i
  domainCover := fun i => domain_cover E i

end HQIVNPEncoder

/--
**Universal search/readout polynomiality.** Accepted certificates at every encoded size
imply `NPSearchDischarge` for every instance.
-/
theorem universal_np_bridge_search_poly {I : Type} (E : HQIVNPEncoder I) (i : I) :
    NPSearchDischarge (E.cert i) (E.n i) :=
  HQIVNPEncoder.search_poly E i

/--
**Universal domain-cover simulation.** Accepted certificates imply
`ClassicalPolynomialSimulableByDomainCover` for every encoded circuit family.
-/
theorem universal_np_bridge_domain_cover {I : Type} (E : HQIVNPEncoder I) (i : I) :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert (E.cert i)) :=
  HQIVNPEncoder.domain_cover E i

/--
**Universal bundled discharge.** Combines search/readout polynomiality and domain-cover
simulation for the full encoded instance family.
-/
theorem universal_np_bridge_discharge {I : Type} (L : NPLanguageModel I) (E : HQIVNPEncoder I) :
    UniversalNPBridgeDischarge I L E :=
  HQIVNPEncoder.universalDischarge L E

/--
**Decision soundness (conditional).** When readout witnesses exceed threshold and soundness
holds, every such witness certifies language membership.
-/
theorem universal_np_bridge_decision_sound {I : Type}
    (L : NPLanguageModel I) (R : HQIVNPReadoutSound I L) (i : I)
    (hw : (R.witness i).thresholdMet) : L.member i :=
  R.soundPositive i hw

/--
**Full conditional bridge.** Encoder acceptance + readout soundness gives both polynomial
HQIV discharge and certified positive decisions.
-/
structure FullNPBridge (I : Type) (L : NPLanguageModel I) where
  encoder : HQIVNPEncoder I
  readout : HQIVNPReadoutSound I L
  discharge : UniversalNPBridgeDischarge I L encoder

def FullNPBridge.ofEncoder {I : Type} (L : NPLanguageModel I) (E : HQIVNPEncoder I)
    (R : HQIVNPReadoutSound I L) : FullNPBridge I L where
  encoder := E
  readout := R
  discharge := universal_np_bridge_discharge L E

end Hqiv.QuantumComputing.NPBridgeUniversal
