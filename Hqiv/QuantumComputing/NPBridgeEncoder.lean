import Hqiv.QuantumComputing.NPBridgeUniversal
import Hqiv.QuantumComputing.NPBridgeDecision
import Hqiv.QuantumComputing.FrequencyCertificate

/-!
# NP-complete encoder existence via polynomial reduction

Classical NP-completeness: if language `J` is NP-complete and `L` reduces to `J` in
polynomial time, then every instance of `L` encodes to an instance of `J` whose size is
polynomially bounded.

This module lifts that to the HQIV certificate layer: a polynomial reduction plus an
accepted-certificate encoder for the anchor language yields an encoder for the source
language by composing `reduce` with the anchor encoder.

**This does not prove NP = P.** It proves encoder *existence* is closed under reduction
once a SAT (or other NP-complete anchor) encoder is available.
-/

namespace Hqiv.QuantumComputing.NPBridgeEncoder

open Hqiv.QuantumComputing
open Hqiv.QuantumComputing.NPBridgeUniversal
open Hqiv.QuantumComputing.NPBridgeDecision

/-- Polynomial size bound: `bound n d = (n+1)^(d+1)` matches certificate `polyEnvelope`. -/
def polySizeBound (n d : Nat) : Nat := polyEnvelope n d

theorem polySizeBound_mono {n m d : Nat} (h : n ≤ m) :
    polySizeBound n d ≤ polySizeBound m d :=
  polyEnvelope_mono_n h

/-- A many-one reduction with an explicit polynomial size witness. -/
structure PolynomialReduction (I J : Type) where
  sourceSize : I → Nat
  targetSize : J → Nat
  reduce : I → J
  sizeDegree : Nat
  size_bound : ∀ i, targetSize (reduce i) ≤ polySizeBound (sourceSize i) sizeDegree

namespace PolynomialReduction

theorem reduced_size_le {I J : Type} (R : PolynomialReduction I J) (i : I) :
    R.targetSize (R.reduce i) ≤ polySizeBound (R.sourceSize i) R.sizeDegree :=
  R.size_bound i

end PolynomialReduction

/-- Reduction preserves membership (correctness of the NP reduction). -/
structure ReductionSound (I J : Type) (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) where
  preserves_membership : ∀ i, L.member i ↔ JLang.member (R.reduce i)

/-- SAT / NP-complete anchor: language + accepted HQIV encoder. -/
structure NPCompleteAnchor (J : Type) (JLang : NPLanguageModel J) where
  encoder : HQIVNPEncoder J

/--
**Encoder existence via reduction.** If `L` polynomially reduces to anchor language `J`
with membership preservation, and `J` has an accepted HQIV encoder, then `L` has an
HQIV encoder obtained by composing reduction with the anchor map.
-/
def HQIVNPEncoder.ofReduction {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (_hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) : HQIVNPEncoder I where
  cert := fun i => anchor.encoder.cert (R.reduce i)
  n := fun i => anchor.encoder.n (R.reduce i)
  size_ge_one := fun i => anchor.encoder.size_ge_one (R.reduce i)
  accepted := fun i => anchor.encoder.accepted (R.reduce i)

theorem encoder_exists_via_reduction {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) :
    Nonempty (HQIVNPEncoder I) :=
  ⟨HQIVNPEncoder.ofReduction L JLang R hSound anchor⟩

/--
**Full bridge via reduction.** Polynomial reduction + anchor encoder + readout on the
reduced instance yields universal discharge on the source language (pullback certificates).
-/
theorem full_bridge_via_reduction {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) :
    UniversalNPBridgeDischarge I L (HQIVNPEncoder.ofReduction L JLang R hSound anchor) :=
  universal_np_bridge_discharge L (HQIVNPEncoder.ofReduction L JLang R hSound anchor)

/-- Reduced instance inherits polynomial simulate/readout discharge. -/
theorem search_discharge_via_reduction {I J : Type}
    (L : NPLanguageModel I) (JLang : NPLanguageModel J)
    (R : PolynomialReduction I J) (hSound : ReductionSound I J L JLang R)
    (anchor : NPCompleteAnchor J JLang) (i : I) :
    NPSearchDischarge (anchor.encoder.cert (R.reduce i)) (anchor.encoder.n (R.reduce i)) :=
  HQIVNPEncoder.search_poly (HQIVNPEncoder.ofReduction L JLang R hSound anchor) i

end Hqiv.QuantumComputing.NPBridgeEncoder
