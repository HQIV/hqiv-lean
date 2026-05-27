import Hqiv.QuantumComputing.CertificateDomainCover
import Hqiv.QuantumComputing.SparseScheduleCost
import Hqiv.QuantumComputing.FrequencyCertificate

/-!
# NP-bridge decision discharge layer

Closes the operational gap between:
1. **Polynomial HQIV schedule simulation** (`scheduleCost_polynomial_of_acceptedPolynomial`), and
2. **Classical marginal readout** on a sparse embedded register (linear in `maxSupport`).

This does **not** claim NP = P in the abstract: it states that when an exported
`FrequencyPolynomialCertificate` is `acceptedPolynomial` at size `n`, the combined
simulate-then-readout bookkeeping is polynomially bounded under the certificate model.
Python SAT/ATSP harnesses supply the empirical measurement witness separately.
-/

namespace Hqiv.QuantumComputing.NPBridgeDecision

open Hqiv.QuantumComputing

/-- Cost of extracting one marginal probability from a sparse support of size `s`. -/
def marginalReadoutCost (support : Nat) : Nat := support

/-- Combined simulate + single marginal readout cost. -/
def simulateAndReadoutCost (depth maxSupport maxChiFrequencyBand : Nat) : Nat :=
  scheduleCost depth maxSupport maxChiFrequencyBand + marginalReadoutCost maxSupport

theorem marginalReadoutCost_le_support (s : Nat) :
    marginalReadoutCost s ≤ s + 1 := by
  unfold marginalReadoutCost
  omega

theorem simulateAndReadoutCost_le_schedule_plus_support
    (depth maxSupport maxChiFrequencyBand : Nat) :
    simulateAndReadoutCost depth maxSupport maxChiFrequencyBand ≤
      scheduleCost depth maxSupport maxChiFrequencyBand + maxSupport + 1 := by
  unfold simulateAndReadoutCost
  exact Nat.add_le_add_left (marginalReadoutCost_le_support maxSupport) _

private theorem polyEnvelope_degree_mono {n a b : Nat} (hn : 1 ≤ n) (hab : a ≤ b) :
    polyEnvelope n a ≤ polyEnvelope n b := by
  unfold polyEnvelope
  exact Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.add_le_add_right hab 1)

private theorem two_mul_pow_le_pow_add_two {n d : Nat} (hn : 1 ≤ n) :
    2 * (n + 1) ^ (d + 1) ≤ (n + 1) ^ (d + 3) := by
  have hn2 : 2 ≤ (n + 1) * (n + 1) := by
    have : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  calc
    2 * (n + 1) ^ (d + 1) = (n + 1) ^ (d + 1) * 2 := Nat.mul_comm _ _
    _ ≤ (n + 1) ^ (d + 1) * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left _ hn2
    _ = (n + 1) ^ (d + 3) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
      ring_nf

/--
**Discharge theorem (certificate layer).** Accepted polynomial obligations imply
polynomial bounds on simulate-then-readout cost at size `n`.
-/
theorem simulateAndReadout_polynomial_of_acceptedPolynomial
    (cert : FrequencyPolynomialCertificate) (n : Nat)
    (hn : 1 ≤ n)
    (h : cert.acceptedPolynomial n) :
    ∃ d,
      simulateAndReadoutCost cert.obligations.depth cert.obligations.maxSupport
          cert.obligations.maxChiFrequencyBand ≤ polyEnvelope n d := by
  let w := cert.witness
  let dInner := schedulePolyDegree w
  refine ⟨dInner + 2, ?_⟩
  have hpoly := FrequencyPolynomialCertificate.polyBoundedAt_of_acceptedPolynomial h
  have hsched :
      scheduleCost cert.obligations.depth cert.obligations.maxSupport
          cert.obligations.maxChiFrequencyBand ≤ polyEnvelope n dInner :=
    scheduleCost_le_polyEnvelope_of_bounds w n cert.obligations.depth
      cert.obligations.maxSupport cert.obligations.maxChiFrequencyBand hn
      hpoly.2.2 hpoly.1 hpoly.2.1
  have hdeg : w.polyDegreeSupport ≤ schedulePolyDegree w := by
    unfold schedulePolyDegree
    omega
  have hread : marginalReadoutCost cert.obligations.maxSupport ≤ polyEnvelope n dInner := by
    unfold marginalReadoutCost
    exact le_trans hpoly.1 (polyEnvelope_degree_mono hn hdeg)
  have hsum :
      scheduleCost cert.obligations.depth cert.obligations.maxSupport
          cert.obligations.maxChiFrequencyBand +
        marginalReadoutCost cert.obligations.maxSupport ≤
        polyEnvelope n dInner + polyEnvelope n dInner :=
    Nat.add_le_add hsched hread
  have hdouble : polyEnvelope n dInner + polyEnvelope n dInner ≤ polyEnvelope n (dInner + 2) := by
    unfold polyEnvelope
    have h2 := @two_mul_pow_le_pow_add_two n dInner hn
    nlinarith
  unfold simulateAndReadoutCost
  exact le_trans hsum hdouble

/-- Frequency-band χ used in Lean witnesses is the authoritative bond proxy (not RDM χ). -/
theorem acceptedPolynomial_frequency_chi_authoritative
    {cert : FrequencyPolynomialCertificate} {n : Nat}
    (h : cert.acceptedPolynomial n) :
    cert.obligations.maxChiFrequencyBand ≤ cert.obligations.maxChiBound :=
  acceptedPolynomial_frequency_chi_le_global h

/-- A classical measurement outcome witness (rational threshold vs observed probability). -/
structure MeasurementOutcomeWitness where
  thresholdNumer : Nat
  thresholdDenom : Nat
  observedNumer : Nat
  observedDenom : Nat
  deriving Repr

namespace MeasurementOutcomeWitness

/-- Observed success probability meets the configured threshold. -/
def thresholdMet (w : MeasurementOutcomeWitness) : Prop :=
  w.observedNumer * w.thresholdDenom ≥ w.thresholdNumer * w.observedDenom

def ofRationals (thresholdNumer thresholdDenom observedNumer observedDenom : Nat) :
    MeasurementOutcomeWitness :=
  { thresholdNumer := thresholdNumer
  , thresholdDenom := thresholdDenom
  , observedNumer := observedNumer
  , observedDenom := observedDenom }

end MeasurementOutcomeWitness

/-- Operational SAT/ATSP success is discharged when simulation is poly and readout exceeds threshold. -/
structure NPSearchDischarge (cert : FrequencyPolynomialCertificate) (n : Nat) where
  hn : 1 ≤ n
  accepted : cert.acceptedPolynomial n
  schedulePoly :
    ∃ d, scheduleCost cert.obligations.depth cert.obligations.maxSupport
        cert.obligations.maxChiFrequencyBand ≤ polyEnvelope n d
  readoutPoly :
    ∃ d, simulateAndReadoutCost cert.obligations.depth cert.obligations.maxSupport
        cert.obligations.maxChiFrequencyBand ≤ polyEnvelope n d

def NPSearchDischarge.of_acceptedPolynomial
    (cert : FrequencyPolynomialCertificate) (n : Nat)
    (hn : 1 ≤ n) (h : cert.acceptedPolynomial n) : NPSearchDischarge cert n where
  hn := hn
  accepted := h
  schedulePoly := scheduleCost_polynomial_of_acceptedPolynomial cert n hn h
  readoutPoly := simulateAndReadout_polynomial_of_acceptedPolynomial cert n hn h

end Hqiv.QuantumComputing.NPBridgeDecision
