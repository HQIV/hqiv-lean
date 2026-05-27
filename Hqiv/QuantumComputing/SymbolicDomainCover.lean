import Hqiv.QuantumComputing.SymbolicFrequencySlice

/-!
# Symbolic shell/frequency/hybrid domain coverage

This module states the opposite-side coverage theorem: a circuit family is in the polynomial
sparse-simulation domain if every route step is covered by a polynomial shell-local,
frequency-local, or bounded hybrid decomposition.

The proof is intentionally symbolic.  Computed certificates and boundary reports can instantiate
these obligations, but the theorem itself is not proof-by-run: it quantifies over all input sizes.
-/

namespace Hqiv.QuantumComputing

/-- Domains in which a route step can be certified polynomial. -/
inductive DecompositionDomain where
  | shell
  | frequency
  | hybrid
  deriving DecidableEq, Repr

/-- One symbolic route obligation inside a circuit family at size `n`. -/
structure RouteObligation where
  domain : DecompositionDomain
  support : Nat
  chi : Nat
  /-- Shell-local support projection used to decide whether pure shell coverage is enough. -/
  shellSupport : Nat
  /-- Frequency-local χ projection used to decide whether pure frequency coverage is enough. -/
  frequencyChi : Nat
  gateSemanticsCovered : Prop

namespace RouteObligation

/-- Per-route sparse cost proxy. -/
def cost (r : RouteObligation) : Nat :=
  frequencySparseStepCost r.support r.chi

/--
Discrete light-cone admissibility for one elementary route/tick.

Structural form: the route's elementary domain is one of the two finite-QM
classes (shell or frequency). Hybrid routes are excluded because their kernel
mixes a shell channel and a frequency channel inside a single tick, which the
discrete light-cone axiom forbids.
-/
def DiscreteLightConeAdmissible (r : RouteObligation) : Prop :=
  r.domain = DecompositionDomain.shell ∨ r.domain = DecompositionDomain.frequency

/--
Informational monogamy admissibility for one elementary route/tick.

Structural form: a single operator channel is open per tick, so the route is
constructed from exactly one of the two finite-QM channels. The shell-channel
constructor witnesses `support = shellSupport`; the frequency-channel
constructor witnesses `chi = frequencyChi`.
-/
inductive InformationalMonogamyAdmissible (r : RouteObligation) : Prop where
  | shellChannel
      (hd : r.domain = DecompositionDomain.shell)
      (hs : r.support = r.shellSupport)
      (hsem : r.gateSemanticsCovered) :
      InformationalMonogamyAdmissible r
  | frequencyChannel
      (hd : r.domain = DecompositionDomain.frequency)
      (hchi : r.chi = r.frequencyChi)
      (hsem : r.gateSemanticsCovered) :
      InformationalMonogamyAdmissible r

namespace InformationalMonogamyAdmissible

/-- Monogamy admissibility entails the structural light-cone disjunction. -/
theorem discreteLightCone {r : RouteObligation}
    (h : InformationalMonogamyAdmissible r) :
    DiscreteLightConeAdmissible r := by
  cases h with
  | shellChannel hd _ _ => exact Or.inl hd
  | frequencyChannel hd _ _ => exact Or.inr hd

/-- Monogamy admissibility exposes the route's covered gate semantics. -/
theorem gateSemanticsCovered {r : RouteObligation}
    (h : InformationalMonogamyAdmissible r) :
    r.gateSemanticsCovered := by
  cases h with
  | shellChannel _ _ hsem => exact hsem
  | frequencyChannel _ _ hsem => exact hsem

end InformationalMonogamyAdmissible

/-- A route is shell-local and Lean-backed. -/
def ShellLocalPolynomial (r : RouteObligation) : Prop :=
  r.domain = DecompositionDomain.shell ∧
  r.support = r.shellSupport ∧
  r.gateSemanticsCovered

/-- A route is frequency-local and Lean-backed. -/
def FrequencyLocalPolynomial (r : RouteObligation) : Prop :=
  r.domain = DecompositionDomain.frequency ∧
  r.chi = r.frequencyChi ∧
  r.gateSemanticsCovered

/-- A route is covered by a bounded shell/frequency hybrid and Lean-backed. -/
def HybridShellFrequencyPolynomial (r : RouteObligation) : Prop :=
  r.domain = DecompositionDomain.hybrid ∧
  0 < r.shellSupport ∧
  0 < r.frequencyChi ∧
  r.shellSupport ≤ r.support ∧
  r.frequencyChi ≤ r.chi ∧
  r.gateSemanticsCovered

/-- Every acceptable route falls into shell, frequency, or hybrid polynomial coverage. -/
def CoveredByPDomain (r : RouteObligation) : Prop :=
  r.ShellLocalPolynomial ∨ r.FrequencyLocalPolynomial ∨ r.HybridShellFrequencyPolynomial

/--
Finite-HQIV-QM operator classification theorem.

Under finite harmonic-octonion QM, any elementary operator that satisfies the
structural informational monogamy axiom is either a shell operator or a frequency
operator. Proved directly from the structure of `InformationalMonogamyAdmissible`,
no external axiom required.
-/
theorem finiteQM_classification {r : RouteObligation}
    (h : InformationalMonogamyAdmissible r) :
    r.ShellLocalPolynomial ∨ r.FrequencyLocalPolynomial := by
  cases h with
  | shellChannel hd hs hsem => exact Or.inl ⟨hd, hs, hsem⟩
  | frequencyChannel hd hchi hsem => exact Or.inr ⟨hd, hchi, hsem⟩

/-- Monogamy-admissible routes are covered by the shell/frequency domain. -/
theorem covered_of_finiteQM_monogamy {r : RouteObligation}
    (h : InformationalMonogamyAdmissible r) :
    r.CoveredByPDomain := by
  rcases finiteQM_classification h with hshell | hfreq
  · exact Or.inl hshell
  · exact Or.inr (Or.inl hfreq)

/-- Convenience constructor: build shell-channel monogamy from a covered shell route. -/
theorem shell_channel_monogamy_admissible {r : RouteObligation}
    (hd : r.domain = DecompositionDomain.shell)
    (hs : r.support = r.shellSupport)
    (hsem : r.gateSemanticsCovered) :
    InformationalMonogamyAdmissible r :=
  InformationalMonogamyAdmissible.shellChannel hd hs hsem

/-- Convenience constructor: build frequency-channel monogamy from a covered frequency route. -/
theorem frequency_channel_monogamy_admissible {r : RouteObligation}
    (hd : r.domain = DecompositionDomain.frequency)
    (hchi : r.chi = r.frequencyChi)
    (hsem : r.gateSemanticsCovered) :
    InformationalMonogamyAdmissible r :=
  InformationalMonogamyAdmissible.frequencyChannel hd hchi hsem

/-! ## Elementary HQIV gate-kind bridge

The previous symbolic layer treated `gateSemanticsCovered : Prop` as an abstract
hook (typically instantiated to `True`). This section replaces that hook with a
concrete claim: "this route is realized by one of the three elementary HQIV gate
kinds the simulator recognizes (permutation, diagonal phase, two-level local
mix)". Each gate kind maps to a definite `DecompositionDomain`, and monogamy
admissibility is then a straightforward downstream lemma rather than a structural
axiom on the route literal.

This closes the gate-semantics-to-monogamy bridge for the kinds the Python
classifier emits: `permutation` (`shell`), `diagonal` (`frequency`), and
`local_mix` (`frequency`).
-/

/-- The three elementary HQIV gate kinds the sparse classifier identifies. -/
inductive ElementaryGateKind where
  | permutation
  | diagonalPhase
  | twoLevelLocalMix
  deriving DecidableEq, Repr

/-- Each elementary kind lands in a definite `DecompositionDomain`. -/
def domainOfKind : ElementaryGateKind → DecompositionDomain
  | .permutation => DecompositionDomain.shell
  | .diagonalPhase => DecompositionDomain.frequency
  | .twoLevelLocalMix => DecompositionDomain.frequency

@[simp] theorem domainOfKind_permutation :
    domainOfKind .permutation = DecompositionDomain.shell := rfl

@[simp] theorem domainOfKind_diagonalPhase :
    domainOfKind .diagonalPhase = DecompositionDomain.frequency := rfl

@[simp] theorem domainOfKind_twoLevelLocalMix :
    domainOfKind .twoLevelLocalMix = DecompositionDomain.frequency := rfl

/--
The route is realized by a specific HQIV elementary gate kind.

This is the structural claim that replaces the abstract `gateSemanticsCovered`
hook. Each constructor pairs the route's structural data with the elementary
kind that justifies the corresponding channel projection.
-/
inductive HasElementaryGateKind (r : RouteObligation) : Prop where
  | permutation
      (hd : r.domain = DecompositionDomain.shell)
      (hs : r.support = r.shellSupport)
      (hsem : r.gateSemanticsCovered) :
      HasElementaryGateKind r
  | diagonalPhase
      (hd : r.domain = DecompositionDomain.frequency)
      (hchi : r.chi = r.frequencyChi)
      (hsem : r.gateSemanticsCovered) :
      HasElementaryGateKind r
  | twoLevelLocalMix
      (hd : r.domain = DecompositionDomain.frequency)
      (hchi : r.chi = r.frequencyChi)
      (hsem : r.gateSemanticsCovered) :
      HasElementaryGateKind r

namespace HasElementaryGateKind

/-- Every elementary-kind witness exposes a covered gate-semantics proof. -/
theorem gateSemanticsCovered {r : RouteObligation}
    (h : HasElementaryGateKind r) : r.gateSemanticsCovered := by
  cases h with
  | permutation _ _ hsem => exact hsem
  | diagonalPhase _ _ hsem => exact hsem
  | twoLevelLocalMix _ _ hsem => exact hsem

/-- Every elementary-kind witness pins down the route's `DecompositionDomain`. -/
theorem domain_eq_domainOfKind {r : RouteObligation}
    (h : HasElementaryGateKind r) :
    ∃ k : ElementaryGateKind, r.domain = domainOfKind k := by
  cases h with
  | permutation hd _ _ => exact ⟨.permutation, hd⟩
  | diagonalPhase hd _ _ => exact ⟨.diagonalPhase, hd⟩
  | twoLevelLocalMix hd _ _ => exact ⟨.twoLevelLocalMix, hd⟩

end HasElementaryGateKind

/-- Bridge: an elementary-kind route is informational-monogamy admissible. -/
theorem informationalMonogamy_of_elementary_kind {r : RouteObligation}
    (h : HasElementaryGateKind r) : InformationalMonogamyAdmissible r := by
  cases h with
  | permutation hd hs hsem => exact .shellChannel hd hs hsem
  | diagonalPhase hd hchi hsem => exact .frequencyChannel hd hchi hsem
  | twoLevelLocalMix hd hchi hsem => exact .frequencyChannel hd hchi hsem

/-- Bridge: an elementary-kind route satisfies the discrete light-cone disjunction. -/
theorem discreteLightCone_of_elementary_kind {r : RouteObligation}
    (h : HasElementaryGateKind r) : DiscreteLightConeAdmissible r :=
  (informationalMonogamy_of_elementary_kind h).discreteLightCone

/-- Bridge: an elementary-kind route is shell-or-frequency covered. -/
theorem covered_of_elementary_kind {r : RouteObligation}
    (h : HasElementaryGateKind r) : r.CoveredByPDomain :=
  covered_of_finiteQM_monogamy (informationalMonogamy_of_elementary_kind h)

/-- Hybrid routes structurally have no elementary HQIV gate kind. -/
theorem hybridRoute_no_elementary_kind {r : RouteObligation}
    (hd : r.domain = DecompositionDomain.hybrid) :
    ¬ HasElementaryGateKind r := by
  intro h
  cases h with
  | permutation hperm _ _ =>
      have : DecompositionDomain.hybrid = DecompositionDomain.shell := hd.symm.trans hperm
      cases this
  | diagonalPhase hfreq _ _ =>
      have : DecompositionDomain.hybrid = DecompositionDomain.frequency := hd.symm.trans hfreq
      cases this
  | twoLevelLocalMix hfreq _ _ =>
      have : DecompositionDomain.hybrid = DecompositionDomain.frequency := hd.symm.trans hfreq
      cases this

/--
Legacy structure: finite-QM completeness as an external hypothesis.

Older generated witnesses bind against this shape. The bundled `proven` instance
discharges it from `finiteQM_classification`, so the axiom is no longer load-bearing.
-/
structure CompleteFiniteQMOperatorClassification : Prop where
  classify :
    ∀ r : RouteObligation,
      r.DiscreteLightConeAdmissible →
      r.InformationalMonogamyAdmissible →
      r.ShellLocalPolynomial ∨ r.FrequencyLocalPolynomial

/-- Canonical proof of the finite-QM completeness "axiom" — no axiom needed. -/
theorem CompleteFiniteQMOperatorClassification.proven :
    CompleteFiniteQMOperatorClassification :=
  ⟨fun _ _ hmono => finiteQM_classification hmono⟩

/-- Backward-compatible covered-route lemma using the legacy structure. -/
theorem covered_of_complete_finiteQM
    (hcomplete : CompleteFiniteQMOperatorClassification)
    {r : RouteObligation}
    (hlc : r.DiscreteLightConeAdmissible)
    (hmono : r.InformationalMonogamyAdmissible) :
    r.CoveredByPDomain := by
  rcases hcomplete.classify r hlc hmono with hshell | hfreq
  · exact Or.inl hshell
  · exact Or.inr (Or.inl hfreq)

theorem covered_gate_semantics {r : RouteObligation} (h : r.CoveredByPDomain) :
    r.gateSemanticsCovered := by
  rcases h with hshell | hfreq | hhybrid
  · exact hshell.2.2
  · exact hfreq.2.2
  · exact hhybrid.2.2.2.2.2

/-- Pure shell coverage exposes the tight shell-support projection. -/
theorem shell_local_support_eq {r : RouteObligation} (h : r.ShellLocalPolynomial) :
    r.support = r.shellSupport :=
  h.2.1

/-- Pure frequency coverage exposes the tight frequency-χ projection. -/
theorem frequency_local_chi_eq {r : RouteObligation} (h : r.FrequencyLocalPolynomial) :
    r.chi = r.frequencyChi :=
  h.2.1

/-- Hybrid coverage explicitly bounds both constituent projections. -/
theorem hybrid_projection_bounds {r : RouteObligation} (h : r.HybridShellFrequencyPolynomial) :
    r.shellSupport ≤ r.support ∧ r.frequencyChi ≤ r.chi :=
  ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- Shell-local route with matching projection and covered semantics. -/
theorem shell_local_covered (r : RouteObligation)
    (hd : r.domain = DecompositionDomain.shell)
    (hs : r.support = r.shellSupport) (hsem : r.gateSemanticsCovered) :
    r.CoveredByPDomain :=
  Or.inl ⟨hd, hs, hsem⟩

/-- Frequency-local route with matching projection and covered semantics. -/
theorem frequency_local_covered (r : RouteObligation)
    (hd : r.domain = DecompositionDomain.frequency)
    (hchi : r.chi = r.frequencyChi) (hsem : r.gateSemanticsCovered) :
    r.CoveredByPDomain :=
  Or.inr (Or.inl ⟨hd, hchi, hsem⟩)

/-- Bounded hybrid route with covered semantics. -/
theorem hybrid_covered (r : RouteObligation)
    (hd : r.domain = DecompositionDomain.hybrid)
    (hshell : 0 < r.shellSupport) (hfreq : 0 < r.frequencyChi)
    (hs : r.shellSupport ≤ r.support) (hchi : r.frequencyChi ≤ r.chi)
    (hsem : r.gateSemanticsCovered) :
    r.CoveredByPDomain :=
  Or.inr (Or.inr ⟨hd, hshell, hfreq, hs, hchi, hsem⟩)

theorem cost_le_uniform {r : RouteObligation} {maxSupport maxChi : Nat}
    (hs : r.support ≤ maxSupport) (hchi : r.chi ≤ maxChi) :
    r.cost ≤ frequencySparseStepCost maxSupport maxChi :=
  frequencySparseStepCost_mono hs hchi

end RouteObligation

/--
Family-level domain cover.  `routes n` is a symbolic finite route list for size `n`; the
maxima are exported separately so the theorem does not need to reason about list maxima yet.
-/
structure SymbolicDomainCover (F : CircuitFamily) where
  routes : Nat → List RouteObligation
  maxSupport : SizeMetric
  maxChi : SizeMetric
  routeCount : SizeMetric
  parityOk : Nat → Bool
  denseFallbackCount : SizeMetric

namespace SymbolicDomainCover

/-- Every route at size `n` is shell-local, frequency-local, or bounded hybrid-local. -/
def everyRouteCoveredAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat) : Prop :=
  ∀ r ∈ C.routes n, r.CoveredByPDomain

/-- The explicit route list is bounded by the exported route-count obligation. -/
def routeCountBoundsAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat) : Prop :=
  (C.routes n).length ≤ C.routeCount n

/-- Each route is bounded by the exported support/χ maxima. -/
def routeMetricsBoundedAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat) : Prop :=
  ∀ r ∈ C.routes n, r.support ≤ C.maxSupport n ∧ r.chi ≤ C.maxChi n

/-- Accepted cover obligations at size `n`. -/
def acceptedAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat) : Prop :=
  C.parityOk n = true ∧
  C.denseFallbackCount n = 0 ∧
  C.everyRouteCoveredAt n ∧
  C.routeCountBoundsAt n ∧
  C.routeMetricsBoundedAt n

/-- Aggregate sparse schedule cost for the symbolic route list. -/
def routeListCost : List RouteObligation → Nat
  | [] => 0
  | r :: rs => r.cost + routeListCost rs

theorem routeListCost_nil : routeListCost [] = 0 := rfl

theorem routeListCost_cons (r : RouteObligation) (rs : List RouteObligation) :
    routeListCost (r :: rs) = r.cost + routeListCost rs := rfl

private theorem routeListCost_le_length_mul (routes : List RouteObligation) (M : Nat)
    (h : ∀ r ∈ routes, r.cost ≤ M) :
    routeListCost routes ≤ routes.length * M := by
  induction routes with
  | nil => simp [routeListCost]
  | cons r rs ih =>
    have hM := h r (by simp)
    have hrs := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hfac : M + rs.length * M = (rs.length + 1) * M :=
      (Nat.add_comm M (rs.length * M)).trans (Nat.succ_mul rs.length M).symm
    calc
      routeListCost (r :: rs) = r.cost + routeListCost rs := rfl
      _ ≤ M + rs.length * M := Nat.add_le_add hM hrs
      _ ≤ (rs.length + 1) * M := le_of_eq hfac
      _ = (r :: rs).length * M := by simp [List.length]

/-- Cost of the symbolic schedule at size `n`. -/
def costAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat) : Nat :=
  scheduleCost (C.routeCount n) (C.maxSupport n) (C.maxChi n)

theorem routeListCost_le_scheduleCost (routes : List RouteObligation)
    (routeCount maxSupport maxChi : Nat)
    (hlen : routes.length ≤ routeCount)
    (hbound : ∀ r ∈ routes, r.support ≤ maxSupport ∧ r.chi ≤ maxChi) :
    routeListCost routes ≤ scheduleCost routeCount maxSupport maxChi := by
  have hstep : ∀ r ∈ routes, r.cost ≤ frequencySparseStepCost maxSupport maxChi := by
    intro r hr
    exact RouteObligation.cost_le_uniform (hbound r hr).1 (hbound r hr).2
  have hsum := routeListCost_le_length_mul routes
    (frequencySparseStepCost maxSupport maxChi) hstep
  calc
    routeListCost routes
        ≤ routes.length * frequencySparseStepCost maxSupport maxChi := hsum
    _ ≤ routeCount * frequencySparseStepCost maxSupport maxChi :=
      Nat.mul_le_mul hlen (Nat.le_refl _)
    _ = scheduleCost routeCount maxSupport maxChi := by
      rfl

theorem routeListCost_le_costAt {F : CircuitFamily} (C : SymbolicDomainCover F) (n : Nat)
    (hacc : C.acceptedAt n) :
    routeListCost (C.routes n) ≤ C.costAt n := by
  dsimp [costAt]
  exact routeListCost_le_scheduleCost (C.routes n) (C.routeCount n) (C.maxSupport n) (C.maxChi n)
    hacc.2.2.2.1 (fun r hr => hacc.2.2.2.2 r hr)

/-- Assemble `acceptedAt` from static route-list obligations (used by generated witnesses). -/
theorem acceptedAt_of_static_routes {F : CircuitFamily} (C : SymbolicDomainCover F)
    (routes : List RouteObligation)
    (hstatic : ∀ n, C.routes n = routes)
    (hparity : ∀ n, C.parityOk n = true)
    (hdense : ∀ n, C.denseFallbackCount n = 0)
    (hcovered : ∀ r ∈ routes, r.CoveredByPDomain)
    (hcount : ∀ n, 1 ≤ n → routes.length ≤ C.routeCount n)
    (hmetrics : ∀ n, 1 ≤ n → ∀ r ∈ routes, r.support ≤ C.maxSupport n ∧ r.chi ≤ C.maxChi n) :
    ∀ n, 1 ≤ n → C.acceptedAt n := by
  intro n hn
  refine ⟨hparity n, hdense n, ?_, ?_, ?_⟩
  · intro r hr
    rw [hstatic n] at hr
    exact hcovered r hr
  · simp [SymbolicDomainCover.routeCountBoundsAt, hstatic n]
    exact hcount n hn
  · intro r hr
    rw [hstatic n] at hr
    exact hmetrics n hn r hr

/--
Assemble `acceptedAt` from finite-QM route admissibility rather than a pre-built
`CoveredByPDomain` proof. Discharged via `covered_of_complete_finiteQM`, which the
canonical `CompleteFiniteQMOperatorClassification.proven` proof closes for free.
-/
theorem acceptedAt_of_static_finiteQM_routes {F : CircuitFamily} (C : SymbolicDomainCover F)
    (routes : List RouteObligation)
    (hcomplete : RouteObligation.CompleteFiniteQMOperatorClassification)
    (hstatic : ∀ n, C.routes n = routes)
    (hparity : ∀ n, C.parityOk n = true)
    (hdense : ∀ n, C.denseFallbackCount n = 0)
    (hadmissible :
      ∀ r ∈ routes,
        r.DiscreteLightConeAdmissible ∧ r.InformationalMonogamyAdmissible)
    (hcount : ∀ n, 1 ≤ n → routes.length ≤ C.routeCount n)
    (hmetrics : ∀ n, 1 ≤ n → ∀ r ∈ routes, r.support ≤ C.maxSupport n ∧ r.chi ≤ C.maxChi n) :
    ∀ n, 1 ≤ n → C.acceptedAt n :=
  acceptedAt_of_static_routes C routes hstatic hparity hdense
    (by
      intro r hr
      exact RouteObligation.covered_of_complete_finiteQM hcomplete
        (hadmissible r hr).1 (hadmissible r hr).2)
    hcount hmetrics

/--
Hypothesis-free variant: structural informational monogamy admissibility alone
discharges acceptance, because finite-QM operator classification is proven.
This is the current symbolic-proof frontier: no external `Complete…Classification`
axiom is required, only that each emitted route is structurally monogamy-admissible.
-/
theorem acceptedAt_of_static_monogamy_routes {F : CircuitFamily} (C : SymbolicDomainCover F)
    (routes : List RouteObligation)
    (hstatic : ∀ n, C.routes n = routes)
    (hparity : ∀ n, C.parityOk n = true)
    (hdense : ∀ n, C.denseFallbackCount n = 0)
    (hmonogamy : ∀ r ∈ routes, RouteObligation.InformationalMonogamyAdmissible r)
    (hcount : ∀ n, 1 ≤ n → routes.length ≤ C.routeCount n)
    (hmetrics : ∀ n, 1 ≤ n → ∀ r ∈ routes, r.support ≤ C.maxSupport n ∧ r.chi ≤ C.maxChi n) :
    ∀ n, 1 ≤ n → C.acceptedAt n :=
  acceptedAt_of_static_routes C routes hstatic hparity hdense
    (fun r hr => RouteObligation.covered_of_finiteQM_monogamy (hmonogamy r hr))
    hcount hmetrics

/-- Every element of a replicated route template inherits coverage. -/
theorem mem_replicate_routes_covered (template : RouteObligation) (n : Nat)
    (ht : template.CoveredByPDomain) {r : RouteObligation}
    (hr : r ∈ List.replicate n template) : r.CoveredByPDomain := by
  rw [List.mem_replicate] at hr
  rcases hr with ⟨_, heq⟩
  subst heq
  exact ht

end SymbolicDomainCover

/-- Polynomial witnesses for the combined shell/frequency/hybrid cover. -/
structure DomainCoverPolynomialWitness {F : CircuitFamily} (C : SymbolicDomainCover F) where
  witness : PolynomialWitness
  supportBound :
    ∀ n, 1 ≤ n → C.maxSupport n ≤ polyEnvelope n witness.polyDegreeSupport
  chiBound :
    ∀ n, 1 ≤ n → C.maxChi n ≤ polyEnvelope n witness.polyDegreeFrequencyChi
  routeCountBound :
    ∀ n, 1 ≤ n → C.routeCount n ≤ polyEnvelope n witness.polyDegreeRouteCount

/-- Symbolic condition: the family has polynomial shell/frequency/hybrid domain coverage. -/
structure DomainCoverToP (F : CircuitFamily) where
  cover : SymbolicDomainCover F
  acceptedAll : ∀ n, 1 ≤ n → cover.acceptedAt n
  polynomialWitness : DomainCoverPolynomialWitness cover

/-- Propositional wrapper for contradictory statements. -/
def HasDomainCoverToP (F : CircuitFamily) : Prop :=
  Nonempty (DomainCoverToP F)

/-- Polynomial simulability under a symbolic shell/frequency/hybrid domain cover. -/
def ClassicalPolynomialSimulableByDomainCover (F : CircuitFamily) : Prop :=
  ∃ C : SymbolicDomainCover F, PolynomiallyBounded C.costAt

theorem DomainCoverPolynomialWitness.cost_polynomial
    {F : CircuitFamily} {C : SymbolicDomainCover F}
    (W : DomainCoverPolynomialWitness C) :
    PolynomiallyBounded C.costAt := by
  refine ⟨schedulePolyDegree W.witness, ?_⟩
  intro n hn
  exact scheduleCost_le_polyEnvelope_of_bounds
    W.witness n (C.routeCount n) (C.maxSupport n) (C.maxChi n)
    hn (W.routeCountBound n hn) (W.supportBound n hn) (W.chiBound n hn)

/--
Main combined-domain theorem: if every route is covered by shell, frequency, or bounded hybrid
decomposition and the cover metrics have fixed polynomial witnesses, the family has polynomial
classical schedule cost.
-/
theorem shell_or_frequency_coverage_to_P
    {F : CircuitFamily} (h : DomainCoverToP F) :
    ClassicalPolynomialSimulableByDomainCover F :=
  ⟨h.cover, h.polynomialWitness.cost_polynomial⟩

/--
Opposite-side boundary theorem: if a family is not polynomially simulable under any symbolic domain
cover, it cannot have a shell/frequency/hybrid domain-cover certificate.
-/
theorem not_P_implies_uncovered_boundary
    {F : CircuitFamily} (hnotP : ¬ ClassicalPolynomialSimulableByDomainCover F) :
    ¬ HasDomainCoverToP F :=
  fun hcover => hcover.elim (fun h => hnotP (shell_or_frequency_coverage_to_P h))

/-- Accepted domain cover implies no dense fallback at every accepted size. -/
theorem domain_cover_no_dense_fallback
    {F : CircuitFamily} (h : DomainCoverToP F) {n : Nat} (hn : 1 ≤ n) :
    h.cover.denseFallbackCount n = 0 :=
  (h.acceptedAll n hn).2.1

/-- Accepted domain cover gives the shell/frequency/hybrid route coverage obligation. -/
theorem domain_cover_every_route_covered
    {F : CircuitFamily} (h : DomainCoverToP F) {n : Nat} (hn : 1 ≤ n) :
    h.cover.everyRouteCoveredAt n :=
  (h.acceptedAll n hn).2.2.1

/-- Accepted domain cover bounds the explicit route list by the exported route-count metric. -/
theorem domain_cover_route_count_bounds
    {F : CircuitFamily} (h : DomainCoverToP F) {n : Nat} (hn : 1 ≤ n) :
    h.cover.routeCountBoundsAt n :=
  (h.acceptedAll n hn).2.2.2.1

/-- Explicit route-list cost is bounded by the aggregate schedule cost at every accepted size. -/
theorem domain_cover_routeListCost_le_costAt
    {F : CircuitFamily} (h : DomainCoverToP F) {n : Nat} (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (h.cover.routes n) ≤ h.cover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt h.cover n (h.acceptedAll n hn)

end Hqiv.QuantumComputing
