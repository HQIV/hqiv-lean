import Hqiv.QuantumComputing.SymbolicDomainCover
import Hqiv.QuantumComputing.DomainCoverFromFrequencySlice
import Hqiv.QuantumComputing.FrequencyCertificate

/-!
# Parametric symbolic families

A **`ParametricFamilySpec`** is a small constants record that completely determines a
`DomainCoverToP` certificate: a single canonical route per size, with shell/frequency/hybrid
domain selection, and polynomial envelope degrees for `maxSupport`, `maxChi`, and `routeCount`.

The point of this builder is to make adding a new symbolic family (GHZ, QAOA, QPE, quantum walk,
Clifford+T, ...) a one-liner.  Each family becomes:

```
def fooSpec : ParametricFamilySpec := { ... }
def fooFamily := fooSpec.family
theorem foo_symbolic_in_P : ClassicalPolynomialSimulableByDomainCover fooFamily :=
  fooSpec.symbolic_in_P
```
-/

namespace Hqiv.QuantumComputing

open SymbolicDomainCover

/-- Constants record describing one canonical route + envelope degrees for a family. -/
structure ParametricFamilySpec where
  /-- Family identifier exported into the Lean / Python certificate stream. -/
  name : String
  /-- Domain of the canonical route. -/
  domain : DecompositionDomain
  /-- Support of the canonical route (constant in `n`).  Must be ≥ 1. -/
  routeSupport : Nat
  /-- Frequency χ of the canonical route (constant in `n`).  Must be ≥ 1. -/
  routeChi : Nat
  /-- Shell-local support projection of the canonical route. -/
  routeShellSupport : Nat
  /-- Frequency-local χ projection of the canonical route. -/
  routeFrequencyChi : Nat
  /-- Polynomial envelope degree for `maxSupport`. -/
  supportDegree : Nat
  /-- Polynomial envelope degree for `maxChi`. -/
  chiDegree : Nat
  /-- Polynomial envelope degree for `routeCount`. -/
  routeCountDegree : Nat
  /-- Positivity of the canonical route's support. -/
  routeSupport_pos : 1 ≤ routeSupport
  /-- Positivity of the canonical route's χ. -/
  routeChi_pos : 1 ≤ routeChi
  /-- Coverage compatibility for the chosen domain (the lone non-trivial obligation). -/
  domainProof :
    (domain = DecompositionDomain.shell ∧ routeSupport = routeShellSupport)
    ∨ (domain = DecompositionDomain.frequency ∧ routeChi = routeFrequencyChi)
    ∨ (domain = DecompositionDomain.hybrid
        ∧ 0 < routeShellSupport ∧ 0 < routeFrequencyChi
        ∧ routeShellSupport ≤ routeSupport ∧ routeFrequencyChi ≤ routeChi)
  /-- The support envelope at n=1 covers the canonical route's support. -/
  supportFitsAtOne : routeSupport ≤ polyEnvelope 1 supportDegree
  /-- The χ envelope at n=1 covers the canonical route's χ. -/
  chiFitsAtOne : routeChi ≤ polyEnvelope 1 chiDegree

namespace ParametricFamilySpec

/-- Underlying `CircuitFamily`. -/
def family (s : ParametricFamilySpec) : CircuitFamily := { name := s.name }

/-- The single canonical `RouteObligation` for the family. -/
def canonicalRoute (s : ParametricFamilySpec) : RouteObligation :=
  { domain := s.domain
  , support := s.routeSupport
  , chi := s.routeChi
  , shellSupport := s.routeShellSupport
  , frequencyChi := s.routeFrequencyChi
  , gateSemanticsCovered := True }

/-- The canonical route is shell/frequency/hybrid-covered by the supplied `domainProof`. -/
theorem canonicalRoute_covered (s : ParametricFamilySpec) :
    s.canonicalRoute.CoveredByPDomain := by
  rcases s.domainProof with hshell | hfreq | hhybrid
  · exact RouteObligation.shell_local_covered s.canonicalRoute hshell.1 hshell.2 trivial
  · exact RouteObligation.frequency_local_covered s.canonicalRoute hfreq.1 hfreq.2 trivial
  · exact RouteObligation.hybrid_covered s.canonicalRoute hhybrid.1
      hhybrid.2.1 hhybrid.2.2.1 hhybrid.2.2.2.1 hhybrid.2.2.2.2 trivial

/-- The induced symbolic domain cover. -/
def domainCover (s : ParametricFamilySpec) : SymbolicDomainCover s.family :=
  { routes := fun _ => [s.canonicalRoute]
  , maxSupport := fun n => polyEnvelope n s.supportDegree
  , maxChi := fun n => polyEnvelope n s.chiDegree
  , routeCount := fun n => polyEnvelope n s.routeCountDegree
  , parityOk := fun _ => true
  , denseFallbackCount := fun _ => 0 }

/-- Acceptance of the parametric domain cover at every `n ≥ 1`. -/
theorem domainCover_accepted (s : ParametricFamilySpec) (n : Nat) (hn : 1 ≤ n) :
    s.domainCover.acceptedAt n :=
  acceptedAt_of_static_routes s.domainCover [s.canonicalRoute]
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro r hr; simp at hr; subst hr; exact s.canonicalRoute_covered)
    (by
      intro m _hm
      simp [domainCover]
      exact one_le_polyEnvelope m s.routeCountDegree)
    (by
      intro m hm r hr
      simp [canonicalRoute] at hr
      subst hr
      refine ⟨?_, ?_⟩
      · exact polyEnvelope_witness_degree_sound hm s.supportFitsAtOne
      · exact polyEnvelope_witness_degree_sound hm s.chiFitsAtOne) n hn

/-- Polynomial witness for the parametric domain cover. -/
def domainCoverWitness (s : ParametricFamilySpec) :
    DomainCoverPolynomialWitness s.domainCover :=
  { witness :=
      { polyDegreeSupport := s.supportDegree
      , polyDegreeFrequencyChi := s.chiDegree
      , polyDegreeRouteCount := s.routeCountDegree }
  , supportBound := by intro n _hn; rfl
  , chiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

/-- The parametric `DomainCoverToP` certificate. -/
def domainCoverToP (s : ParametricFamilySpec) : DomainCoverToP s.family :=
  { cover := s.domainCover
  , acceptedAll := s.domainCover_accepted
  , polynomialWitness := s.domainCoverWitness }

/-- Main one-shot theorem: every parametric family is in P. -/
theorem symbolic_in_P (s : ParametricFamilySpec) :
    ClassicalPolynomialSimulableByDomainCover s.family :=
  shell_or_frequency_coverage_to_P s.domainCoverToP

/-- The route-list cost is bounded by the aggregate schedule cost at every accepted size. -/
theorem routeListCost_le (s : ParametricFamilySpec) (n : Nat) (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (s.domainCover.routes n) ≤ s.domainCover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt s.domainCover n (s.domainCover_accepted n hn)

end ParametricFamilySpec

/-! ## Smart constructors

These build the `domainProof` field automatically for each domain. They are the
recommended entry points: only positivity / projection-equality obligations remain
visible to the user. -/

/-- Build a shell-local parametric spec.  `routeSupport = routeShellSupport` is enforced. -/
def mkShellLocalFamily
    (name : String)
    (routeSupport routeChi : Nat)
    (supportDegree chiDegree routeCountDegree : Nat)
    (hsup : 1 ≤ routeSupport) (hchi : 1 ≤ routeChi)
    (hsupFits : routeSupport ≤ polyEnvelope 1 supportDegree)
    (hchiFits : routeChi ≤ polyEnvelope 1 chiDegree) :
    ParametricFamilySpec :=
  { name := name
  , domain := DecompositionDomain.shell
  , routeSupport := routeSupport
  , routeChi := routeChi
  , routeShellSupport := routeSupport
  , routeFrequencyChi := routeChi
  , supportDegree := supportDegree
  , chiDegree := chiDegree
  , routeCountDegree := routeCountDegree
  , routeSupport_pos := hsup
  , routeChi_pos := hchi
  , domainProof := Or.inl ⟨rfl, rfl⟩
  , supportFitsAtOne := hsupFits
  , chiFitsAtOne := hchiFits }

/-- Build a frequency-local parametric spec.  `routeChi = routeFrequencyChi` is enforced. -/
def mkFrequencyLocalFamily
    (name : String)
    (routeSupport routeChi : Nat)
    (supportDegree chiDegree routeCountDegree : Nat)
    (hsup : 1 ≤ routeSupport) (hchi : 1 ≤ routeChi)
    (hsupFits : routeSupport ≤ polyEnvelope 1 supportDegree)
    (hchiFits : routeChi ≤ polyEnvelope 1 chiDegree) :
    ParametricFamilySpec :=
  { name := name
  , domain := DecompositionDomain.frequency
  , routeSupport := routeSupport
  , routeChi := routeChi
  , routeShellSupport := routeSupport
  , routeFrequencyChi := routeChi
  , supportDegree := supportDegree
  , chiDegree := chiDegree
  , routeCountDegree := routeCountDegree
  , routeSupport_pos := hsup
  , routeChi_pos := hchi
  , domainProof := Or.inr (Or.inl ⟨rfl, rfl⟩)
  , supportFitsAtOne := hsupFits
  , chiFitsAtOne := hchiFits }

/-- Build a hybrid parametric spec with explicit shell/frequency projections. -/
def mkHybridFamily
    (name : String)
    (routeSupport routeChi routeShellSupport routeFrequencyChi : Nat)
    (supportDegree chiDegree routeCountDegree : Nat)
    (hsup : 1 ≤ routeSupport) (hchi : 1 ≤ routeChi)
    (hshell_pos : 0 < routeShellSupport) (hfreq_pos : 0 < routeFrequencyChi)
    (hshell_le : routeShellSupport ≤ routeSupport)
    (hfreq_le : routeFrequencyChi ≤ routeChi)
    (hsupFits : routeSupport ≤ polyEnvelope 1 supportDegree)
    (hchiFits : routeChi ≤ polyEnvelope 1 chiDegree) :
    ParametricFamilySpec :=
  { name := name
  , domain := DecompositionDomain.hybrid
  , routeSupport := routeSupport
  , routeChi := routeChi
  , routeShellSupport := routeShellSupport
  , routeFrequencyChi := routeFrequencyChi
  , supportDegree := supportDegree
  , chiDegree := chiDegree
  , routeCountDegree := routeCountDegree
  , routeSupport_pos := hsup
  , routeChi_pos := hchi
  , domainProof := Or.inr (Or.inr ⟨rfl, hshell_pos, hfreq_pos, hshell_le, hfreq_le⟩)
  , supportFitsAtOne := hsupFits
  , chiFitsAtOne := hchiFits }

end Hqiv.QuantumComputing
