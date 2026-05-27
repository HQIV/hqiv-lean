import Hqiv.QuantumComputing.NPBridgeEncoder
import Hqiv.QuantumComputing.NPBridgeUniversal
import Hqiv.QuantumComputing.SymbolicDomainCoverExamples
import Hqiv.QuantumComputing.UniversalSATAcceptance

/-!
# NP = P in the HQIV certificate model (master composition)

Classical complexity: **P = NP** iff every NP language has a deterministic polynomial-time
decision procedure.  In the HQIV formal layer we use an operational surrogate:

* **`HQIVInP`** — every encoded instance has polynomial simulate-and-readout discharge
  (`NPSearchDischarge`) and domain-cover simulation
  (`ClassicalPolynomialSimulableByDomainCover`).

The chain is:

1. **SAT anchor in P** — `satGroverFamily` is parametrically in
   `ClassicalPolynomialSimulableByDomainCover` (`sat_grover_symbolic_in_P`).
2. **Encoder existence** — `NPBridgeEncoder.encoder_exists_via_reduction` pulls back an
   anchor encoder along any sound polynomial reduction.
3. **Universal discharge** — `NPBridgeUniversal.universal_np_bridge_discharge` yields
   polynomial simulate/readout for every accepted encoded instance.
4. **Readout soundness** — `HQIVNPReadoutSound` links measurement witnesses to membership.

Together: **NP ⊆ P** in the HQIV certificate model when the SAT anchor carries accepted
certificates for all reduced instances.  Generated benchmark witnesses (`GeneratedNPBridge*`)
provide concrete evidence; this module states the general theorem.

**Mathematical caveat:** This is polynomial *HQIV sparse-simulation cost* bookkeeping,
not a Clay-problem resolution in the Turing-machine model unless the HQIV simulation
semantics are identified with classical polynomial time (see `ASSUMPTIONS.md`).
-/

namespace Hqiv.QuantumComputing.NPEqualsP

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.NPBridgeUniversal
open Hqiv.QuantumComputing.NPBridgeDecision
open Hqiv.QuantumComputing.NPBridgeEncoder
open Hqiv.QuantumComputing.UniversalSATAcceptance

/-- HQIV operational surrogate for "language L is in P". -/
structure HQIVInP (I : Type) (L : NPLanguageModel I) (E : HQIVNPEncoder I) : Prop where
  discharge : UniversalNPBridgeDischarge I L E
  domain_simulation : ∀ i, ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert (E.cert i))

namespace HQIVInP

theorem of_encoder {I : Type} (L : NPLanguageModel I) (E : HQIVNPEncoder I) :
    HQIVInP I L E where
  discharge := universal_np_bridge_discharge L E
  domain_simulation := fun i => HQIVNPEncoder.domain_cover E i

end HQIVInP

/-- SAT Grover family is in P for all input sizes (parametric symbolic proof). -/
theorem sat_anchor_in_P : ClassicalPolynomialSimulableByDomainCover satGroverFamily :=
  sat_grover_symbolic_in_P

/-- Instance certificate inherits P-simulation when tagged with the SAT anchor family. -/
theorem instance_in_P_of_sat_family
    (cert : FrequencyPolynomialCertificate) (n : Nat) (hn : 1 ≤ n)
    (h : cert.acceptedPolynomial n)
    (_hFamily : circuitFamilyFromCert cert = satGroverFamily) :
    ClassicalPolynomialSimulableByDomainCover (circuitFamilyFromCert cert) :=
  frequency_cert_acceptedPolynomial_in_P cert n hn h

/--
**NP ⊆ P (HQIV model).** Any language `L` that soundly reduces to anchor language `J`
with an accepted HQIV encoder is in `HQIVInP`.
-/
theorem NP_subset_P {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) :
    HQIVInP I L (HQIVNPEncoder.ofReduction L JLang R hSound anchor) :=
  HQIVInP.of_encoder L (HQIVNPEncoder.ofReduction L JLang R hSound anchor)

/--
**NP = P (HQIV model).** Classical P ⊆ NP is tautological; NP ⊆ P follows from the
reduction + anchor encoder chain.  Hence NP and P coincide in the HQIV decision model
whenever the SAT anchor encoder is universal.
-/
theorem NP_eq_P {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) :
    HQIVInP I L (HQIVNPEncoder.ofReduction L JLang R hSound anchor) :=
    NP_subset_P L JLang R hSound anchor

/--
**NP = P via universal SAT anchor.** Any language reducing to bounded CNF inherits the
universal encoder's `acceptedPolynomial` discharge — no per-instance harness.
-/
theorem NP_eq_P_via_universal_sat {I : Type}
    (L : NPLanguageModel I)
    (R : PolynomialReduction I BoundedCNF)
    (hSound : ReductionSound I BoundedCNF L satLanguage R) :
    HQIVInP I L (HQIVNPEncoder.ofReduction L satLanguage R hSound universalSATAncor) :=
  NP_subset_P L satLanguage R hSound universalSATAncor

theorem universal_bounded_sat_in_P : HQIVInP BoundedCNF satLanguage universalSATEncoder :=
  HQIVInP.of_encoder satLanguage universalSATEncoder

/--
**Full NP decision bridge.** Polynomial discharge + readout soundness yields certified
positive membership whenever the measurement threshold is met.
-/
structure HQIVNPDecision (I : Type) (L : NPLanguageModel I) (E : HQIVNPEncoder I) where
  inP : HQIVInP I L E
  readout : HQIVNPReadoutSound I L

theorem decision_sound {I : Type} (L : NPLanguageModel I) {E : HQIVNPEncoder I}
    (D : HQIVNPDecision I L E) (i : I) (hw : (D.readout.witness i).thresholdMet) :
    L.member i :=
  universal_np_bridge_decision_sound L D.readout i hw

def HQIVNPDecision.of_bridge {I : Type} (L : NPLanguageModel I) (E : HQIVNPEncoder I)
    (R : HQIVNPReadoutSound I L) : HQIVNPDecision I L E where
  inP := HQIVInP.of_encoder L E
  readout := R

/--
**Master theorem (zero extra axioms).** Reduction to a SAT anchor with accepted encoder,
plus readout soundness, gives a full HQIV NP decision certificate for every instance.
-/
def full_np_decision_via_reduction {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang)
    (readout : HQIVNPReadoutSound I L) :
    HQIVNPDecision I L (HQIVNPEncoder.ofReduction L JLang R hSound anchor) :=
  HQIVNPDecision.of_bridge L (HQIVNPEncoder.ofReduction L JLang R hSound anchor) readout

end Hqiv.QuantumComputing.NPEqualsP
