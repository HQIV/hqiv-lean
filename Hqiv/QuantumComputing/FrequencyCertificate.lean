import Hqiv.QuantumComputing.OSHoracle

/-!
# Frequency-domain certificate obligations and polynomial witnesses

Lean-side consumer for Python `hqiv-obligation-certificate/lean/v1` exports.  Checks finite
schema-stable obligations (parity, no dense fallback, frequency χ bound) and optional
polynomial witnesses for support / frequency-χ / route depth.

Generated witness files instantiate `FrequencyPolynomialCertificate` and discharge
`acceptedPolynomial`.
-/

namespace Hqiv.QuantumComputing

/-- Frequency basis tag mirrored from Python certificates. -/
inductive FrequencyBasis where
  | harmonic
  | walshHadamard
  | fourierLike
  | custom
  deriving DecidableEq, Repr

/-- Monotone polynomial envelope `O(n^{d+1})` used for certificate witnesses. -/
def polyEnvelope (n d : Nat) : Nat :=
  (n + 1) ^ (d + 1)

theorem polyEnvelope_mono_n {n m d : Nat} (h : n ≤ m) : polyEnvelope n d ≤ polyEnvelope m d := by
  unfold polyEnvelope
  exact Nat.pow_le_pow_left (Nat.add_le_add_right h 1) (d + 1)

theorem polyEnvelope_zero (d : Nat) : polyEnvelope 0 d = 1 := by
  simp [polyEnvelope]

theorem one_le_polyEnvelope (n d : Nat) : 1 ≤ polyEnvelope n d := by
  unfold polyEnvelope
  have hp : 0 < (n + 1) ^ (d + 1) := by positivity
  exact Nat.succ_le_of_lt hp

/-- Witness degree chosen at `n₀ = 1` bounds a value at every `n ≥ 1`. -/
theorem polyEnvelope_witness_degree_sound {value d n : Nat} (hn : 1 ≤ n)
    (hdeg : value ≤ polyEnvelope 1 d) :
    value ≤ polyEnvelope n d := by
  unfold polyEnvelope at hdeg ⊢
  have h2 : 2 ≤ n + 1 := by omega
  have hpow : 2 ^ (d + 1) ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_left h2 (d + 1)
  calc
    value ≤ 2 ^ (d + 1) := by simpa [polyEnvelope] using hdeg
    _ ≤ (n + 1) ^ (d + 1) := hpow

/-- Exported polynomial degree witnesses (Python fits power-law exponents → ceil + margin). -/
structure PolynomialWitness where
  polyDegreeSupport : Nat
  polyDegreeFrequencyChi : Nat
  polyDegreeRouteCount : Nat
  deriving Repr

namespace PolynomialWitness

def default : PolynomialWitness :=
  { polyDegreeSupport := 2
  , polyDegreeFrequencyChi := 2
  , polyDegreeRouteCount := 1 }

end PolynomialWitness

/-- Lean-facing obligations from one frequency-aware certificate. -/
structure FrequencyObligations where
  circuitId : String
  nQubits : Nat
  depth : Nat
  maxChiBound : Nat
  maxChiFrequencyBand : Nat
  maxSupport : Nat
  denseFallbackCount : Nat
  parityOk : Bool
  frequencyCutUsed : Bool
  frequencyBasis : FrequencyBasis
  deriving Repr

/-- Acceptance predicate for the current Python frequency certificate export. -/
def FrequencyObligations.accepted (c : FrequencyObligations) : Prop :=
  c.parityOk = true ∧
  c.denseFallbackCount = 0 ∧
  c.maxChiFrequencyBand ≤ c.maxChiBound ∧
  c.maxSupport > 0 ∧
  c.depth > 0

/-- Polynomial bound at problem size `n` (typically `nQubits`). -/
def FrequencyObligations.polyBoundedAt (c : FrequencyObligations) (w : PolynomialWitness)
    (n : Nat) : Prop :=
  c.maxSupport ≤ polyEnvelope n w.polyDegreeSupport ∧
  c.maxChiFrequencyBand ≤ polyEnvelope n w.polyDegreeFrequencyChi ∧
  c.depth ≤ polyEnvelope n w.polyDegreeRouteCount

/-- Obligations + witness bundle consumed by generated Lean files. -/
structure FrequencyPolynomialCertificate where
  obligations : FrequencyObligations
  witness : PolynomialWitness
  deriving Repr

/-- Accepted certificate with explicit polynomial witnesses at size `n`. -/
def FrequencyPolynomialCertificate.acceptedPolynomial
    (cert : FrequencyPolynomialCertificate) (n : Nat) : Prop :=
  cert.obligations.accepted ∧
  cert.obligations.polyBoundedAt cert.witness n

theorem FrequencyObligations.accepted_parity
    {c : FrequencyObligations} (h : c.accepted) :
    c.parityOk = true :=
  h.1

theorem FrequencyObligations.accepted_no_dense_fallback
    {c : FrequencyObligations} (h : c.accepted) :
    c.denseFallbackCount = 0 :=
  h.2.1

theorem FrequencyObligations.accepted_frequency_chi_le_global
    {c : FrequencyObligations} (h : c.accepted) :
    c.maxChiFrequencyBand ≤ c.maxChiBound :=
  h.2.2.1

theorem FrequencyObligations.accepted_nonzero_support
    {c : FrequencyObligations} (h : c.accepted) :
    c.maxSupport > 0 :=
  h.2.2.2.1

theorem FrequencyObligations.accepted_positive_depth
    {c : FrequencyObligations} (h : c.accepted) :
    c.depth > 0 :=
  h.2.2.2.2

theorem FrequencyPolynomialCertificate.accepted_of_acceptedPolynomial
    {cert : FrequencyPolynomialCertificate} {n : Nat}
    (h : cert.acceptedPolynomial n) : cert.obligations.accepted :=
  h.1

theorem FrequencyPolynomialCertificate.polyBoundedAt_of_acceptedPolynomial
    {cert : FrequencyPolynomialCertificate} {n : Nat}
    (h : cert.acceptedPolynomial n) :
    cert.obligations.polyBoundedAt cert.witness n :=
  h.2

/-- Structural polynomial bound from a witness checked at `n = 1`. -/
theorem FrequencyObligations.polyBoundedAt_all_of_witness_at_one
    {c : FrequencyObligations} {w : PolynomialWitness} {n : Nat} (hn : 1 ≤ n)
    (hs : c.maxSupport ≤ polyEnvelope 1 w.polyDegreeSupport)
    (hchi : c.maxChiFrequencyBand ≤ polyEnvelope 1 w.polyDegreeFrequencyChi)
    (hdepth : c.depth ≤ polyEnvelope 1 w.polyDegreeRouteCount) :
    c.polyBoundedAt w n :=
  ⟨polyEnvelope_witness_degree_sound hn hs,
    polyEnvelope_witness_degree_sound hn hchi,
    polyEnvelope_witness_degree_sound hn hdepth⟩

theorem FrequencyPolynomialCertificate.acceptedPolynomial_of_obligations_and_witness_at_one
    {cert : FrequencyPolynomialCertificate} {n : Nat} (hn : 1 ≤ n)
    (hacc : cert.obligations.accepted)
    (hs : cert.obligations.maxSupport ≤ polyEnvelope 1 cert.witness.polyDegreeSupport)
    (hchi : cert.obligations.maxChiFrequencyBand ≤ polyEnvelope 1 cert.witness.polyDegreeFrequencyChi)
    (hdepth : cert.obligations.depth ≤ polyEnvelope 1 cert.witness.polyDegreeRouteCount) :
    cert.acceptedPolynomial n :=
  ⟨hacc, FrequencyObligations.polyBoundedAt_all_of_witness_at_one hn hs hchi hdepth⟩

theorem FrequencyObligations.polyBounded_support
    {c : FrequencyObligations} {w : PolynomialWitness} {n : Nat}
    (h : c.polyBoundedAt w n) : c.maxSupport ≤ polyEnvelope n w.polyDegreeSupport :=
  h.1

theorem FrequencyObligations.polyBounded_frequency_chi
    {c : FrequencyObligations} {w : PolynomialWitness} {n : Nat}
    (h : c.polyBoundedAt w n) :
    c.maxChiFrequencyBand ≤ polyEnvelope n w.polyDegreeFrequencyChi :=
  h.2.1

theorem FrequencyObligations.polyBounded_route_count
    {c : FrequencyObligations} {w : PolynomialWitness} {n : Nat}
    (h : c.polyBoundedAt w n) : c.depth ≤ polyEnvelope n w.polyDegreeRouteCount :=
  h.2.2

/-- Storage/work proxy: support times frequency χ (used by the schedule cost model). -/
def certificateWorkBound (c : FrequencyObligations) : Nat :=
  c.maxSupport * c.maxChiFrequencyBand + c.maxSupport

theorem certificateWorkBound_le_envelope
    {c : FrequencyObligations} {w : PolynomialWitness} {n : Nat}
    (h : c.polyBoundedAt w n) :
    certificateWorkBound c ≤
      polyEnvelope n w.polyDegreeSupport * polyEnvelope n w.polyDegreeFrequencyChi +
        polyEnvelope n w.polyDegreeSupport := by
  dsimp [certificateWorkBound]
  have hs := h.1
  have hchi := h.2.1
  exact Nat.add_le_add (Nat.mul_le_mul hs hchi) hs

end Hqiv.QuantumComputing
