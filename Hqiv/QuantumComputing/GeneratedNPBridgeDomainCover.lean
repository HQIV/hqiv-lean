import Hqiv.QuantumComputing.FrequencyCertificate
import Hqiv.QuantumComputing.SymbolicDomainCover

/-!
Auto-generated symbolic domain-cover certificates
(`hqiv-obligation-certificate/lean-domain-cover-witness/v1`).
Do not edit by hand; regenerate from Python certificate export.
-/

namespace HQIVNPBridgeDomainCover

open Hqiv.QuantumComputing


def sat_n7_qasmbench_domainFamily : CircuitFamily :=
  { name := "sat_n7_qasmbench" }

def sat_n7_qasmbench_routes : List RouteObligation := [
    { domain := DecompositionDomain.frequency, support := 2, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 4, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 4, chi := 1, shellSupport := 4, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 5, chi := 1, shellSupport := 5, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 8, chi := 1, shellSupport := 8, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True }
  ]


theorem sat_n7_qasmbench_routes_covered : ∀ r ∈ sat_n7_qasmbench_routes, r.CoveredByPDomain :=
  (by
      intro r hr
      simp only [sat_n7_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial)

theorem sat_n7_qasmbench_finiteQM_classification_proven :
    RouteObligation.CompleteFiniteQMOperatorClassification :=
  RouteObligation.CompleteFiniteQMOperatorClassification.proven

theorem sat_n7_qasmbench_routes_hasElementaryGateKind :
    ∀ r ∈ sat_n7_qasmbench_routes, RouteObligation.HasElementaryGateKind r :=
  (by
      intro r hr
      simp only [sat_n7_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial)

theorem sat_n7_qasmbench_routes_gateSemanticsCovered_via_kind :
    ∀ r ∈ sat_n7_qasmbench_routes, r.gateSemanticsCovered := by
  intro r hr
  exact RouteObligation.HasElementaryGateKind.gateSemanticsCovered
    (sat_n7_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n7_qasmbench_routes_monogamy_admissible :
    ∀ r ∈ sat_n7_qasmbench_routes, RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  exact RouteObligation.informationalMonogamy_of_elementary_kind
    (sat_n7_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n7_qasmbench_routes_covered_from_monogamy :
    ∀ r ∈ sat_n7_qasmbench_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_elementary_kind (sat_n7_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n7_qasmbench_routes_finiteQM_admissible :
    ∀ r ∈ sat_n7_qasmbench_routes,
      RouteObligation.DiscreteLightConeAdmissible r ∧
        RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  refine ⟨?_, sat_n7_qasmbench_routes_monogamy_admissible r hr⟩
  exact RouteObligation.InformationalMonogamyAdmissible.discreteLightCone
    (sat_n7_qasmbench_routes_monogamy_admissible r hr)

theorem sat_n7_qasmbench_routes_covered_from_finiteQM
    (hcomplete : RouteObligation.CompleteFiniteQMOperatorClassification) :
    ∀ r ∈ sat_n7_qasmbench_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_complete_finiteQM hcomplete
    (sat_n7_qasmbench_routes_finiteQM_admissible r hr).1 (sat_n7_qasmbench_routes_finiteQM_admissible r hr).2


def sat_n7_qasmbench_domainCover : SymbolicDomainCover sat_n7_qasmbench_domainFamily :=
  { routes := fun _ => sat_n7_qasmbench_routes
  , maxSupport := fun n => polyEnvelope n 5
  , maxChi := fun n => polyEnvelope n 1
  , routeCount := fun n => polyEnvelope n 6
  , parityOk := fun _ => true
  , denseFallbackCount := fun _ => 0 }

def sat_n7_qasmbench_domainCoverWitness : DomainCoverPolynomialWitness sat_n7_qasmbench_domainCover :=
  { witness :=
      { polyDegreeSupport := 5
      , polyDegreeFrequencyChi := 1
      , polyDegreeRouteCount := 6 }
  , supportBound := by intro n _hn; rfl
  , chiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

theorem sat_n7_qasmbench_domainCover_accepted (n : Nat) (hn : 1 ≤ n) :
    sat_n7_qasmbench_domainCover.acceptedAt n :=
  SymbolicDomainCover.acceptedAt_of_static_routes sat_n7_qasmbench_domainCover sat_n7_qasmbench_routes
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro _; rfl)
    sat_n7_qasmbench_routes_covered
    (by
      intro n hn
      simp [sat_n7_qasmbench_domainCover, sat_n7_qasmbench_routes, polyEnvelope]
      have hRouteCount : 40 ≤ polyEnvelope 1 6 := by decide
      exact polyEnvelope_witness_degree_sound hn hRouteCount)
    (by
      intro n hn r hr
      simp only [sat_n7_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨?_, ?_⟩
        · have hSupport0 : 2 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport0
        · have hChi0 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi0
      · refine ⟨?_, ?_⟩
        · have hSupport1 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport1
        · have hChi1 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi1
      · refine ⟨?_, ?_⟩
        · have hSupport2 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport2
        · have hChi2 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi2
      · refine ⟨?_, ?_⟩
        · have hSupport3 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport3
        · have hChi3 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi3
      · refine ⟨?_, ?_⟩
        · have hSupport4 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport4
        · have hChi4 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi4
      · refine ⟨?_, ?_⟩
        · have hSupport5 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport5
        · have hChi5 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi5
      · refine ⟨?_, ?_⟩
        · have hSupport6 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport6
        · have hChi6 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi6
      · refine ⟨?_, ?_⟩
        · have hSupport7 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport7
        · have hChi7 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi7
      · refine ⟨?_, ?_⟩
        · have hSupport8 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport8
        · have hChi8 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi8
      · refine ⟨?_, ?_⟩
        · have hSupport9 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport9
        · have hChi9 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi9
      · refine ⟨?_, ?_⟩
        · have hSupport10 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport10
        · have hChi10 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi10
      · refine ⟨?_, ?_⟩
        · have hSupport11 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport11
        · have hChi11 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi11
      · refine ⟨?_, ?_⟩
        · have hSupport12 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport12
        · have hChi12 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi12
      · refine ⟨?_, ?_⟩
        · have hSupport13 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport13
        · have hChi13 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi13
      · refine ⟨?_, ?_⟩
        · have hSupport14 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport14
        · have hChi14 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi14
      · refine ⟨?_, ?_⟩
        · have hSupport15 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport15
        · have hChi15 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi15
      · refine ⟨?_, ?_⟩
        · have hSupport16 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport16
        · have hChi16 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi16
      · refine ⟨?_, ?_⟩
        · have hSupport17 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport17
        · have hChi17 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi17
      · refine ⟨?_, ?_⟩
        · have hSupport18 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport18
        · have hChi18 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi18
      · refine ⟨?_, ?_⟩
        · have hSupport19 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport19
        · have hChi19 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi19
      · refine ⟨?_, ?_⟩
        · have hSupport20 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport20
        · have hChi20 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi20
      · refine ⟨?_, ?_⟩
        · have hSupport21 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport21
        · have hChi21 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi21
      · refine ⟨?_, ?_⟩
        · have hSupport22 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport22
        · have hChi22 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi22
      · refine ⟨?_, ?_⟩
        · have hSupport23 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport23
        · have hChi23 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi23
      · refine ⟨?_, ?_⟩
        · have hSupport24 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport24
        · have hChi24 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi24
      · refine ⟨?_, ?_⟩
        · have hSupport25 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport25
        · have hChi25 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi25
      · refine ⟨?_, ?_⟩
        · have hSupport26 : 5 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport26
        · have hChi26 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi26
      · refine ⟨?_, ?_⟩
        · have hSupport27 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport27
        · have hChi27 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi27
      · refine ⟨?_, ?_⟩
        · have hSupport28 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport28
        · have hChi28 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi28
      · refine ⟨?_, ?_⟩
        · have hSupport29 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport29
        · have hChi29 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi29
      · refine ⟨?_, ?_⟩
        · have hSupport30 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport30
        · have hChi30 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi30
      · refine ⟨?_, ?_⟩
        · have hSupport31 : 5 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport31
        · have hChi31 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi31
      · refine ⟨?_, ?_⟩
        · have hSupport32 : 5 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport32
        · have hChi32 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi32
      · refine ⟨?_, ?_⟩
        · have hSupport33 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport33
        · have hChi33 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi33
      · refine ⟨?_, ?_⟩
        · have hSupport34 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport34
        · have hChi34 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi34
      · refine ⟨?_, ?_⟩
        · have hSupport35 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport35
        · have hChi35 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi35
      · refine ⟨?_, ?_⟩
        · have hSupport36 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport36
        · have hChi36 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi36
      · refine ⟨?_, ?_⟩
        · have hSupport37 : 5 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport37
        · have hChi37 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi37
      · refine ⟨?_, ?_⟩
        · have hSupport38 : 5 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport38
        · have hChi38 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi38
      · refine ⟨?_, ?_⟩
        · have hSupport39 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport39
        · have hChi39 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi39) n hn

def sat_n7_qasmbench_domainCoverToP : DomainCoverToP sat_n7_qasmbench_domainFamily :=
  { cover := sat_n7_qasmbench_domainCover
  , acceptedAll := sat_n7_qasmbench_domainCover_accepted
  , polynomialWitness := sat_n7_qasmbench_domainCoverWitness }

theorem sat_n7_qasmbench_symbolic_in_P : ClassicalPolynomialSimulableByDomainCover sat_n7_qasmbench_domainFamily :=
  shell_or_frequency_coverage_to_P sat_n7_qasmbench_domainCoverToP

theorem sat_n7_qasmbench_routeListCost_le_costAt (n : Nat) (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (sat_n7_qasmbench_domainCover.routes n) ≤ sat_n7_qasmbench_domainCover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt sat_n7_qasmbench_domainCover n (sat_n7_qasmbench_domainCover_accepted n hn)

def sat_n11_qasmbench_domainFamily : CircuitFamily :=
  { name := "sat_n11_qasmbench" }

def sat_n11_qasmbench_routes : List RouteObligation := [
    { domain := DecompositionDomain.frequency, support := 2, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 4, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 16, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 16, chi := 1, shellSupport := 16, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 14, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 21, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 32, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 21, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 13, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 13, chi := 1, shellSupport := 13, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 13, chi := 1, shellSupport := 13, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 13, chi := 1, shellSupport := 13, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 13, chi := 1, shellSupport := 13, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 13, chi := 1, shellSupport := 13, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 21, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.shell, support := 21, chi := 1, shellSupport := 21, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 13, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 20, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 22, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 31, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 32, chi := 1, shellSupport := 1, frequencyChi := 1, gateSemanticsCovered := True }
  ]


theorem sat_n11_qasmbench_routes_covered : ∀ r ∈ sat_n11_qasmbench_routes, r.CoveredByPDomain :=
  (by
      intro r hr
      simp only [sat_n11_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.shell_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial)

theorem sat_n11_qasmbench_finiteQM_classification_proven :
    RouteObligation.CompleteFiniteQMOperatorClassification :=
  RouteObligation.CompleteFiniteQMOperatorClassification.proven

theorem sat_n11_qasmbench_routes_hasElementaryGateKind :
    ∀ r ∈ sat_n11_qasmbench_routes, RouteObligation.HasElementaryGateKind r :=
  (by
      intro r hr
      simp only [sat_n11_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.permutation rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial)

theorem sat_n11_qasmbench_routes_gateSemanticsCovered_via_kind :
    ∀ r ∈ sat_n11_qasmbench_routes, r.gateSemanticsCovered := by
  intro r hr
  exact RouteObligation.HasElementaryGateKind.gateSemanticsCovered
    (sat_n11_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n11_qasmbench_routes_monogamy_admissible :
    ∀ r ∈ sat_n11_qasmbench_routes, RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  exact RouteObligation.informationalMonogamy_of_elementary_kind
    (sat_n11_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n11_qasmbench_routes_covered_from_monogamy :
    ∀ r ∈ sat_n11_qasmbench_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_elementary_kind (sat_n11_qasmbench_routes_hasElementaryGateKind r hr)

theorem sat_n11_qasmbench_routes_finiteQM_admissible :
    ∀ r ∈ sat_n11_qasmbench_routes,
      RouteObligation.DiscreteLightConeAdmissible r ∧
        RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  refine ⟨?_, sat_n11_qasmbench_routes_monogamy_admissible r hr⟩
  exact RouteObligation.InformationalMonogamyAdmissible.discreteLightCone
    (sat_n11_qasmbench_routes_monogamy_admissible r hr)

theorem sat_n11_qasmbench_routes_covered_from_finiteQM
    (hcomplete : RouteObligation.CompleteFiniteQMOperatorClassification) :
    ∀ r ∈ sat_n11_qasmbench_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_complete_finiteQM hcomplete
    (sat_n11_qasmbench_routes_finiteQM_admissible r hr).1 (sat_n11_qasmbench_routes_finiteQM_admissible r hr).2


def sat_n11_qasmbench_domainCover : SymbolicDomainCover sat_n11_qasmbench_domainFamily :=
  { routes := fun _ => sat_n11_qasmbench_routes
  , maxSupport := fun n => polyEnvelope n 5
  , maxChi := fun n => polyEnvelope n 1
  , routeCount := fun n => polyEnvelope n 6
  , parityOk := fun _ => true
  , denseFallbackCount := fun _ => 0 }

def sat_n11_qasmbench_domainCoverWitness : DomainCoverPolynomialWitness sat_n11_qasmbench_domainCover :=
  { witness :=
      { polyDegreeSupport := 5
      , polyDegreeFrequencyChi := 1
      , polyDegreeRouteCount := 6 }
  , supportBound := by intro n _hn; rfl
  , chiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

theorem sat_n11_qasmbench_domainCover_accepted (n : Nat) (hn : 1 ≤ n) :
    sat_n11_qasmbench_domainCover.acceptedAt n :=
  SymbolicDomainCover.acceptedAt_of_static_routes sat_n11_qasmbench_domainCover sat_n11_qasmbench_routes
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro _; rfl)
    sat_n11_qasmbench_routes_covered
    (by
      intro n hn
      simp [sat_n11_qasmbench_domainCover, sat_n11_qasmbench_routes, polyEnvelope]
      have hRouteCount : 91 ≤ polyEnvelope 1 6 := by decide
      exact polyEnvelope_witness_degree_sound hn hRouteCount)
    (by
      intro n hn r hr
      simp only [sat_n11_qasmbench_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨?_, ?_⟩
        · have hSupport0 : 2 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport0
        · have hChi0 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi0
      · refine ⟨?_, ?_⟩
        · have hSupport1 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport1
        · have hChi1 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi1
      · refine ⟨?_, ?_⟩
        · have hSupport2 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport2
        · have hChi2 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi2
      · refine ⟨?_, ?_⟩
        · have hSupport3 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport3
        · have hChi3 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi3
      · refine ⟨?_, ?_⟩
        · have hSupport4 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport4
        · have hChi4 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi4
      · refine ⟨?_, ?_⟩
        · have hSupport5 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport5
        · have hChi5 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi5
      · refine ⟨?_, ?_⟩
        · have hSupport6 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport6
        · have hChi6 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi6
      · refine ⟨?_, ?_⟩
        · have hSupport7 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport7
        · have hChi7 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi7
      · refine ⟨?_, ?_⟩
        · have hSupport8 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport8
        · have hChi8 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi8
      · refine ⟨?_, ?_⟩
        · have hSupport9 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport9
        · have hChi9 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi9
      · refine ⟨?_, ?_⟩
        · have hSupport10 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport10
        · have hChi10 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi10
      · refine ⟨?_, ?_⟩
        · have hSupport11 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport11
        · have hChi11 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi11
      · refine ⟨?_, ?_⟩
        · have hSupport12 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport12
        · have hChi12 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi12
      · refine ⟨?_, ?_⟩
        · have hSupport13 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport13
        · have hChi13 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi13
      · refine ⟨?_, ?_⟩
        · have hSupport14 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport14
        · have hChi14 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi14
      · refine ⟨?_, ?_⟩
        · have hSupport15 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport15
        · have hChi15 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi15
      · refine ⟨?_, ?_⟩
        · have hSupport16 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport16
        · have hChi16 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi16
      · refine ⟨?_, ?_⟩
        · have hSupport17 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport17
        · have hChi17 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi17
      · refine ⟨?_, ?_⟩
        · have hSupport18 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport18
        · have hChi18 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi18
      · refine ⟨?_, ?_⟩
        · have hSupport19 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport19
        · have hChi19 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi19
      · refine ⟨?_, ?_⟩
        · have hSupport20 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport20
        · have hChi20 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi20
      · refine ⟨?_, ?_⟩
        · have hSupport21 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport21
        · have hChi21 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi21
      · refine ⟨?_, ?_⟩
        · have hSupport22 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport22
        · have hChi22 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi22
      · refine ⟨?_, ?_⟩
        · have hSupport23 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport23
        · have hChi23 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi23
      · refine ⟨?_, ?_⟩
        · have hSupport24 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport24
        · have hChi24 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi24
      · refine ⟨?_, ?_⟩
        · have hSupport25 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport25
        · have hChi25 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi25
      · refine ⟨?_, ?_⟩
        · have hSupport26 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport26
        · have hChi26 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi26
      · refine ⟨?_, ?_⟩
        · have hSupport27 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport27
        · have hChi27 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi27
      · refine ⟨?_, ?_⟩
        · have hSupport28 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport28
        · have hChi28 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi28
      · refine ⟨?_, ?_⟩
        · have hSupport29 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport29
        · have hChi29 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi29
      · refine ⟨?_, ?_⟩
        · have hSupport30 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport30
        · have hChi30 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi30
      · refine ⟨?_, ?_⟩
        · have hSupport31 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport31
        · have hChi31 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi31
      · refine ⟨?_, ?_⟩
        · have hSupport32 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport32
        · have hChi32 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi32
      · refine ⟨?_, ?_⟩
        · have hSupport33 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport33
        · have hChi33 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi33
      · refine ⟨?_, ?_⟩
        · have hSupport34 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport34
        · have hChi34 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi34
      · refine ⟨?_, ?_⟩
        · have hSupport35 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport35
        · have hChi35 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi35
      · refine ⟨?_, ?_⟩
        · have hSupport36 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport36
        · have hChi36 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi36
      · refine ⟨?_, ?_⟩
        · have hSupport37 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport37
        · have hChi37 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi37
      · refine ⟨?_, ?_⟩
        · have hSupport38 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport38
        · have hChi38 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi38
      · refine ⟨?_, ?_⟩
        · have hSupport39 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport39
        · have hChi39 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi39
      · refine ⟨?_, ?_⟩
        · have hSupport40 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport40
        · have hChi40 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi40
      · refine ⟨?_, ?_⟩
        · have hSupport41 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport41
        · have hChi41 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi41
      · refine ⟨?_, ?_⟩
        · have hSupport42 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport42
        · have hChi42 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi42
      · refine ⟨?_, ?_⟩
        · have hSupport43 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport43
        · have hChi43 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi43
      · refine ⟨?_, ?_⟩
        · have hSupport44 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport44
        · have hChi44 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi44
      · refine ⟨?_, ?_⟩
        · have hSupport45 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport45
        · have hChi45 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi45
      · refine ⟨?_, ?_⟩
        · have hSupport46 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport46
        · have hChi46 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi46
      · refine ⟨?_, ?_⟩
        · have hSupport47 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport47
        · have hChi47 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi47
      · refine ⟨?_, ?_⟩
        · have hSupport48 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport48
        · have hChi48 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi48
      · refine ⟨?_, ?_⟩
        · have hSupport49 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport49
        · have hChi49 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi49
      · refine ⟨?_, ?_⟩
        · have hSupport50 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport50
        · have hChi50 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi50
      · refine ⟨?_, ?_⟩
        · have hSupport51 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport51
        · have hChi51 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi51
      · refine ⟨?_, ?_⟩
        · have hSupport52 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport52
        · have hChi52 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi52
      · refine ⟨?_, ?_⟩
        · have hSupport53 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport53
        · have hChi53 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi53
      · refine ⟨?_, ?_⟩
        · have hSupport54 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport54
        · have hChi54 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi54
      · refine ⟨?_, ?_⟩
        · have hSupport55 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport55
        · have hChi55 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi55
      · refine ⟨?_, ?_⟩
        · have hSupport56 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport56
        · have hChi56 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi56
      · refine ⟨?_, ?_⟩
        · have hSupport57 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport57
        · have hChi57 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi57
      · refine ⟨?_, ?_⟩
        · have hSupport58 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport58
        · have hChi58 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi58
      · refine ⟨?_, ?_⟩
        · have hSupport59 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport59
        · have hChi59 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi59
      · refine ⟨?_, ?_⟩
        · have hSupport60 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport60
        · have hChi60 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi60
      · refine ⟨?_, ?_⟩
        · have hSupport61 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport61
        · have hChi61 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi61
      · refine ⟨?_, ?_⟩
        · have hSupport62 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport62
        · have hChi62 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi62
      · refine ⟨?_, ?_⟩
        · have hSupport63 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport63
        · have hChi63 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi63
      · refine ⟨?_, ?_⟩
        · have hSupport64 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport64
        · have hChi64 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi64
      · refine ⟨?_, ?_⟩
        · have hSupport65 : 14 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport65
        · have hChi65 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi65
      · refine ⟨?_, ?_⟩
        · have hSupport66 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport66
        · have hChi66 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi66
      · refine ⟨?_, ?_⟩
        · have hSupport67 : 32 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport67
        · have hChi67 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi67
      · refine ⟨?_, ?_⟩
        · have hSupport68 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport68
        · have hChi68 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi68
      · refine ⟨?_, ?_⟩
        · have hSupport69 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport69
        · have hChi69 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi69
      · refine ⟨?_, ?_⟩
        · have hSupport70 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport70
        · have hChi70 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi70
      · refine ⟨?_, ?_⟩
        · have hSupport71 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport71
        · have hChi71 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi71
      · refine ⟨?_, ?_⟩
        · have hSupport72 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport72
        · have hChi72 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi72
      · refine ⟨?_, ?_⟩
        · have hSupport73 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport73
        · have hChi73 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi73
      · refine ⟨?_, ?_⟩
        · have hSupport74 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport74
        · have hChi74 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi74
      · refine ⟨?_, ?_⟩
        · have hSupport75 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport75
        · have hChi75 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi75
      · refine ⟨?_, ?_⟩
        · have hSupport76 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport76
        · have hChi76 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi76
      · refine ⟨?_, ?_⟩
        · have hSupport77 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport77
        · have hChi77 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi77
      · refine ⟨?_, ?_⟩
        · have hSupport78 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport78
        · have hChi78 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi78
      · refine ⟨?_, ?_⟩
        · have hSupport79 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport79
        · have hChi79 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi79
      · refine ⟨?_, ?_⟩
        · have hSupport80 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport80
        · have hChi80 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi80
      · refine ⟨?_, ?_⟩
        · have hSupport81 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport81
        · have hChi81 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi81
      · refine ⟨?_, ?_⟩
        · have hSupport82 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport82
        · have hChi82 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi82
      · refine ⟨?_, ?_⟩
        · have hSupport83 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport83
        · have hChi83 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi83
      · refine ⟨?_, ?_⟩
        · have hSupport84 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport84
        · have hChi84 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi84
      · refine ⟨?_, ?_⟩
        · have hSupport85 : 21 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport85
        · have hChi85 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi85
      · refine ⟨?_, ?_⟩
        · have hSupport86 : 13 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport86
        · have hChi86 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi86
      · refine ⟨?_, ?_⟩
        · have hSupport87 : 20 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport87
        · have hChi87 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi87
      · refine ⟨?_, ?_⟩
        · have hSupport88 : 22 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport88
        · have hChi88 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi88
      · refine ⟨?_, ?_⟩
        · have hSupport89 : 31 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport89
        · have hChi89 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi89
      · refine ⟨?_, ?_⟩
        · have hSupport90 : 32 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport90
        · have hChi90 : 1 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi90) n hn

def sat_n11_qasmbench_domainCoverToP : DomainCoverToP sat_n11_qasmbench_domainFamily :=
  { cover := sat_n11_qasmbench_domainCover
  , acceptedAll := sat_n11_qasmbench_domainCover_accepted
  , polynomialWitness := sat_n11_qasmbench_domainCoverWitness }

theorem sat_n11_qasmbench_symbolic_in_P : ClassicalPolynomialSimulableByDomainCover sat_n11_qasmbench_domainFamily :=
  shell_or_frequency_coverage_to_P sat_n11_qasmbench_domainCoverToP

theorem sat_n11_qasmbench_routeListCost_le_costAt (n : Nat) (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (sat_n11_qasmbench_domainCover.routes n) ≤ sat_n11_qasmbench_domainCover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt sat_n11_qasmbench_domainCover n (sat_n11_qasmbench_domainCover_accepted n hn)

def atsp_demo_n3_grover_i2_domainFamily : CircuitFamily :=
  { name := "atsp_demo_n3_grover_i2" }

def atsp_demo_n3_grover_i2_routes : List RouteObligation := [
    { domain := DecompositionDomain.frequency, support := 2, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 4, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 4, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 6, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 5, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 2, shellSupport := 1, frequencyChi := 2, gateSemanticsCovered := True }
  ]


theorem atsp_demo_n3_grover_i2_routes_covered : ∀ r ∈ atsp_demo_n3_grover_i2_routes, r.CoveredByPDomain :=
  (by
      intro r hr
      simp only [atsp_demo_n3_grover_i2_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial)

theorem atsp_demo_n3_grover_i2_finiteQM_classification_proven :
    RouteObligation.CompleteFiniteQMOperatorClassification :=
  RouteObligation.CompleteFiniteQMOperatorClassification.proven

theorem atsp_demo_n3_grover_i2_routes_hasElementaryGateKind :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes, RouteObligation.HasElementaryGateKind r :=
  (by
      intro r hr
      simp only [atsp_demo_n3_grover_i2_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial)

theorem atsp_demo_n3_grover_i2_routes_gateSemanticsCovered_via_kind :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes, r.gateSemanticsCovered := by
  intro r hr
  exact RouteObligation.HasElementaryGateKind.gateSemanticsCovered
    (atsp_demo_n3_grover_i2_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_grover_i2_routes_monogamy_admissible :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes, RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  exact RouteObligation.informationalMonogamy_of_elementary_kind
    (atsp_demo_n3_grover_i2_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_grover_i2_routes_covered_from_monogamy :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_elementary_kind (atsp_demo_n3_grover_i2_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_grover_i2_routes_finiteQM_admissible :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes,
      RouteObligation.DiscreteLightConeAdmissible r ∧
        RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  refine ⟨?_, atsp_demo_n3_grover_i2_routes_monogamy_admissible r hr⟩
  exact RouteObligation.InformationalMonogamyAdmissible.discreteLightCone
    (atsp_demo_n3_grover_i2_routes_monogamy_admissible r hr)

theorem atsp_demo_n3_grover_i2_routes_covered_from_finiteQM
    (hcomplete : RouteObligation.CompleteFiniteQMOperatorClassification) :
    ∀ r ∈ atsp_demo_n3_grover_i2_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_complete_finiteQM hcomplete
    (atsp_demo_n3_grover_i2_routes_finiteQM_admissible r hr).1 (atsp_demo_n3_grover_i2_routes_finiteQM_admissible r hr).2


def atsp_demo_n3_grover_i2_domainCover : SymbolicDomainCover atsp_demo_n3_grover_i2_domainFamily :=
  { routes := fun _ => atsp_demo_n3_grover_i2_routes
  , maxSupport := fun n => polyEnvelope n 2
  , maxChi := fun n => polyEnvelope n 0
  , routeCount := fun n => polyEnvelope n 5
  , parityOk := fun _ => true
  , denseFallbackCount := fun _ => 0 }

def atsp_demo_n3_grover_i2_domainCoverWitness : DomainCoverPolynomialWitness atsp_demo_n3_grover_i2_domainCover :=
  { witness :=
      { polyDegreeSupport := 2
      , polyDegreeFrequencyChi := 0
      , polyDegreeRouteCount := 5 }
  , supportBound := by intro n _hn; rfl
  , chiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

theorem atsp_demo_n3_grover_i2_domainCover_accepted (n : Nat) (hn : 1 ≤ n) :
    atsp_demo_n3_grover_i2_domainCover.acceptedAt n :=
  SymbolicDomainCover.acceptedAt_of_static_routes atsp_demo_n3_grover_i2_domainCover atsp_demo_n3_grover_i2_routes
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro _; rfl)
    atsp_demo_n3_grover_i2_routes_covered
    (by
      intro n hn
      simp [atsp_demo_n3_grover_i2_domainCover, atsp_demo_n3_grover_i2_routes, polyEnvelope]
      have hRouteCount : 43 ≤ polyEnvelope 1 5 := by decide
      exact polyEnvelope_witness_degree_sound hn hRouteCount)
    (by
      intro n hn r hr
      simp only [atsp_demo_n3_grover_i2_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨?_, ?_⟩
        · have hSupport0 : 2 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport0
        · have hChi0 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi0
      · refine ⟨?_, ?_⟩
        · have hSupport1 : 4 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport1
        · have hChi1 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi1
      · refine ⟨?_, ?_⟩
        · have hSupport2 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport2
        · have hChi2 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi2
      · refine ⟨?_, ?_⟩
        · have hSupport3 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport3
        · have hChi3 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi3
      · refine ⟨?_, ?_⟩
        · have hSupport4 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport4
        · have hChi4 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi4
      · refine ⟨?_, ?_⟩
        · have hSupport5 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport5
        · have hChi5 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi5
      · refine ⟨?_, ?_⟩
        · have hSupport6 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport6
        · have hChi6 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi6
      · refine ⟨?_, ?_⟩
        · have hSupport7 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport7
        · have hChi7 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi7
      · refine ⟨?_, ?_⟩
        · have hSupport8 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport8
        · have hChi8 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi8
      · refine ⟨?_, ?_⟩
        · have hSupport9 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport9
        · have hChi9 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi9
      · refine ⟨?_, ?_⟩
        · have hSupport10 : 4 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport10
        · have hChi10 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi10
      · refine ⟨?_, ?_⟩
        · have hSupport11 : 5 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport11
        · have hChi11 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi11
      · refine ⟨?_, ?_⟩
        · have hSupport12 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport12
        · have hChi12 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi12
      · refine ⟨?_, ?_⟩
        · have hSupport13 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport13
        · have hChi13 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi13
      · refine ⟨?_, ?_⟩
        · have hSupport14 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport14
        · have hChi14 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi14
      · refine ⟨?_, ?_⟩
        · have hSupport15 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport15
        · have hChi15 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi15
      · refine ⟨?_, ?_⟩
        · have hSupport16 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport16
        · have hChi16 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi16
      · refine ⟨?_, ?_⟩
        · have hSupport17 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport17
        · have hChi17 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi17
      · refine ⟨?_, ?_⟩
        · have hSupport18 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport18
        · have hChi18 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi18
      · refine ⟨?_, ?_⟩
        · have hSupport19 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport19
        · have hChi19 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi19
      · refine ⟨?_, ?_⟩
        · have hSupport20 : 5 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport20
        · have hChi20 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi20
      · refine ⟨?_, ?_⟩
        · have hSupport21 : 5 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport21
        · have hChi21 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi21
      · refine ⟨?_, ?_⟩
        · have hSupport22 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport22
        · have hChi22 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi22
      · refine ⟨?_, ?_⟩
        · have hSupport23 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport23
        · have hChi23 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi23
      · refine ⟨?_, ?_⟩
        · have hSupport24 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport24
        · have hChi24 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi24
      · refine ⟨?_, ?_⟩
        · have hSupport25 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport25
        · have hChi25 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi25
      · refine ⟨?_, ?_⟩
        · have hSupport26 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport26
        · have hChi26 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi26
      · refine ⟨?_, ?_⟩
        · have hSupport27 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport27
        · have hChi27 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi27
      · refine ⟨?_, ?_⟩
        · have hSupport28 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport28
        · have hChi28 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi28
      · refine ⟨?_, ?_⟩
        · have hSupport29 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport29
        · have hChi29 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi29
      · refine ⟨?_, ?_⟩
        · have hSupport30 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport30
        · have hChi30 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi30
      · refine ⟨?_, ?_⟩
        · have hSupport31 : 6 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport31
        · have hChi31 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi31
      · refine ⟨?_, ?_⟩
        · have hSupport32 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport32
        · have hChi32 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi32
      · refine ⟨?_, ?_⟩
        · have hSupport33 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport33
        · have hChi33 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi33
      · refine ⟨?_, ?_⟩
        · have hSupport34 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport34
        · have hChi34 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi34
      · refine ⟨?_, ?_⟩
        · have hSupport35 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport35
        · have hChi35 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi35
      · refine ⟨?_, ?_⟩
        · have hSupport36 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport36
        · have hChi36 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi36
      · refine ⟨?_, ?_⟩
        · have hSupport37 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport37
        · have hChi37 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi37
      · refine ⟨?_, ?_⟩
        · have hSupport38 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport38
        · have hChi38 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi38
      · refine ⟨?_, ?_⟩
        · have hSupport39 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport39
        · have hChi39 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi39
      · refine ⟨?_, ?_⟩
        · have hSupport40 : 5 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport40
        · have hChi40 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi40
      · refine ⟨?_, ?_⟩
        · have hSupport41 : 5 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport41
        · have hChi41 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi41
      · refine ⟨?_, ?_⟩
        · have hSupport42 : 8 ≤ polyEnvelope 1 2 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport42
        · have hChi42 : 2 ≤ polyEnvelope 1 0 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi42) n hn

def atsp_demo_n3_grover_i2_domainCoverToP : DomainCoverToP atsp_demo_n3_grover_i2_domainFamily :=
  { cover := atsp_demo_n3_grover_i2_domainCover
  , acceptedAll := atsp_demo_n3_grover_i2_domainCover_accepted
  , polynomialWitness := atsp_demo_n3_grover_i2_domainCoverWitness }

theorem atsp_demo_n3_grover_i2_symbolic_in_P : ClassicalPolynomialSimulableByDomainCover atsp_demo_n3_grover_i2_domainFamily :=
  shell_or_frequency_coverage_to_P atsp_demo_n3_grover_i2_domainCoverToP

theorem atsp_demo_n3_grover_i2_routeListCost_le_costAt (n : Nat) (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (atsp_demo_n3_grover_i2_domainCover.routes n) ≤ atsp_demo_n3_grover_i2_domainCover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt atsp_demo_n3_grover_i2_domainCover n (atsp_demo_n3_grover_i2_domainCover_accepted n hn)

def atsp_demo_n3_via_sat_domainFamily : CircuitFamily :=
  { name := "atsp_demo_n3_via_sat" }

def atsp_demo_n3_via_sat_routes : List RouteObligation := [
    { domain := DecompositionDomain.frequency, support := 2, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 4, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 8, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 16, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 32, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 32, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 25, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 18, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 26, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 48, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 36, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 33, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 47, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 55, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 60, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 60, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 46, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 35, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 52, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 57, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 60, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 59, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 55, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 60, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True },
    { domain := DecompositionDomain.frequency, support := 64, chi := 3, shellSupport := 1, frequencyChi := 3, gateSemanticsCovered := True }
  ]


theorem atsp_demo_n3_via_sat_routes_covered : ∀ r ∈ atsp_demo_n3_via_sat_routes, r.CoveredByPDomain :=
  (by
      intro r hr
      simp only [atsp_demo_n3_via_sat_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial
      · exact RouteObligation.frequency_local_covered _ rfl rfl trivial)

theorem atsp_demo_n3_via_sat_finiteQM_classification_proven :
    RouteObligation.CompleteFiniteQMOperatorClassification :=
  RouteObligation.CompleteFiniteQMOperatorClassification.proven

theorem atsp_demo_n3_via_sat_routes_hasElementaryGateKind :
    ∀ r ∈ atsp_demo_n3_via_sat_routes, RouteObligation.HasElementaryGateKind r :=
  (by
      intro r hr
      simp only [atsp_demo_n3_via_sat_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.diagonalPhase rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial
      · exact RouteObligation.HasElementaryGateKind.twoLevelLocalMix rfl rfl trivial)

theorem atsp_demo_n3_via_sat_routes_gateSemanticsCovered_via_kind :
    ∀ r ∈ atsp_demo_n3_via_sat_routes, r.gateSemanticsCovered := by
  intro r hr
  exact RouteObligation.HasElementaryGateKind.gateSemanticsCovered
    (atsp_demo_n3_via_sat_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_via_sat_routes_monogamy_admissible :
    ∀ r ∈ atsp_demo_n3_via_sat_routes, RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  exact RouteObligation.informationalMonogamy_of_elementary_kind
    (atsp_demo_n3_via_sat_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_via_sat_routes_covered_from_monogamy :
    ∀ r ∈ atsp_demo_n3_via_sat_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_elementary_kind (atsp_demo_n3_via_sat_routes_hasElementaryGateKind r hr)

theorem atsp_demo_n3_via_sat_routes_finiteQM_admissible :
    ∀ r ∈ atsp_demo_n3_via_sat_routes,
      RouteObligation.DiscreteLightConeAdmissible r ∧
        RouteObligation.InformationalMonogamyAdmissible r := by
  intro r hr
  refine ⟨?_, atsp_demo_n3_via_sat_routes_monogamy_admissible r hr⟩
  exact RouteObligation.InformationalMonogamyAdmissible.discreteLightCone
    (atsp_demo_n3_via_sat_routes_monogamy_admissible r hr)

theorem atsp_demo_n3_via_sat_routes_covered_from_finiteQM
    (hcomplete : RouteObligation.CompleteFiniteQMOperatorClassification) :
    ∀ r ∈ atsp_demo_n3_via_sat_routes, r.CoveredByPDomain := by
  intro r hr
  exact RouteObligation.covered_of_complete_finiteQM hcomplete
    (atsp_demo_n3_via_sat_routes_finiteQM_admissible r hr).1 (atsp_demo_n3_via_sat_routes_finiteQM_admissible r hr).2


def atsp_demo_n3_via_sat_domainCover : SymbolicDomainCover atsp_demo_n3_via_sat_domainFamily :=
  { routes := fun _ => atsp_demo_n3_via_sat_routes
  , maxSupport := fun n => polyEnvelope n 5
  , maxChi := fun n => polyEnvelope n 1
  , routeCount := fun n => polyEnvelope n 6
  , parityOk := fun _ => true
  , denseFallbackCount := fun _ => 0 }

def atsp_demo_n3_via_sat_domainCoverWitness : DomainCoverPolynomialWitness atsp_demo_n3_via_sat_domainCover :=
  { witness :=
      { polyDegreeSupport := 5
      , polyDegreeFrequencyChi := 1
      , polyDegreeRouteCount := 6 }
  , supportBound := by intro n _hn; rfl
  , chiBound := by intro n _hn; rfl
  , routeCountBound := by intro n _hn; rfl }

theorem atsp_demo_n3_via_sat_domainCover_accepted (n : Nat) (hn : 1 ≤ n) :
    atsp_demo_n3_via_sat_domainCover.acceptedAt n :=
  SymbolicDomainCover.acceptedAt_of_static_routes atsp_demo_n3_via_sat_domainCover atsp_demo_n3_via_sat_routes
    (by intro _; rfl)
    (by intro _; rfl)
    (by intro _; rfl)
    atsp_demo_n3_via_sat_routes_covered
    (by
      intro n hn
      simp [atsp_demo_n3_via_sat_domainCover, atsp_demo_n3_via_sat_routes, polyEnvelope]
      have hRouteCount : 122 ≤ polyEnvelope 1 6 := by decide
      exact polyEnvelope_witness_degree_sound hn hRouteCount)
    (by
      intro n hn r hr
      simp only [atsp_demo_n3_via_sat_routes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨?_, ?_⟩
        · have hSupport0 : 2 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport0
        · have hChi0 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi0
      · refine ⟨?_, ?_⟩
        · have hSupport1 : 4 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport1
        · have hChi1 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi1
      · refine ⟨?_, ?_⟩
        · have hSupport2 : 8 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport2
        · have hChi2 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi2
      · refine ⟨?_, ?_⟩
        · have hSupport3 : 16 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport3
        · have hChi3 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi3
      · refine ⟨?_, ?_⟩
        · have hSupport4 : 32 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport4
        · have hChi4 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi4
      · refine ⟨?_, ?_⟩
        · have hSupport5 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport5
        · have hChi5 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi5
      · refine ⟨?_, ?_⟩
        · have hSupport6 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport6
        · have hChi6 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi6
      · refine ⟨?_, ?_⟩
        · have hSupport7 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport7
        · have hChi7 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi7
      · refine ⟨?_, ?_⟩
        · have hSupport8 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport8
        · have hChi8 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi8
      · refine ⟨?_, ?_⟩
        · have hSupport9 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport9
        · have hChi9 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi9
      · refine ⟨?_, ?_⟩
        · have hSupport10 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport10
        · have hChi10 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi10
      · refine ⟨?_, ?_⟩
        · have hSupport11 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport11
        · have hChi11 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi11
      · refine ⟨?_, ?_⟩
        · have hSupport12 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport12
        · have hChi12 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi12
      · refine ⟨?_, ?_⟩
        · have hSupport13 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport13
        · have hChi13 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi13
      · refine ⟨?_, ?_⟩
        · have hSupport14 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport14
        · have hChi14 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi14
      · refine ⟨?_, ?_⟩
        · have hSupport15 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport15
        · have hChi15 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi15
      · refine ⟨?_, ?_⟩
        · have hSupport16 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport16
        · have hChi16 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi16
      · refine ⟨?_, ?_⟩
        · have hSupport17 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport17
        · have hChi17 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi17
      · refine ⟨?_, ?_⟩
        · have hSupport18 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport18
        · have hChi18 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi18
      · refine ⟨?_, ?_⟩
        · have hSupport19 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport19
        · have hChi19 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi19
      · refine ⟨?_, ?_⟩
        · have hSupport20 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport20
        · have hChi20 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi20
      · refine ⟨?_, ?_⟩
        · have hSupport21 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport21
        · have hChi21 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi21
      · refine ⟨?_, ?_⟩
        · have hSupport22 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport22
        · have hChi22 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi22
      · refine ⟨?_, ?_⟩
        · have hSupport23 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport23
        · have hChi23 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi23
      · refine ⟨?_, ?_⟩
        · have hSupport24 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport24
        · have hChi24 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi24
      · refine ⟨?_, ?_⟩
        · have hSupport25 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport25
        · have hChi25 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi25
      · refine ⟨?_, ?_⟩
        · have hSupport26 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport26
        · have hChi26 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi26
      · refine ⟨?_, ?_⟩
        · have hSupport27 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport27
        · have hChi27 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi27
      · refine ⟨?_, ?_⟩
        · have hSupport28 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport28
        · have hChi28 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi28
      · refine ⟨?_, ?_⟩
        · have hSupport29 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport29
        · have hChi29 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi29
      · refine ⟨?_, ?_⟩
        · have hSupport30 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport30
        · have hChi30 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi30
      · refine ⟨?_, ?_⟩
        · have hSupport31 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport31
        · have hChi31 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi31
      · refine ⟨?_, ?_⟩
        · have hSupport32 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport32
        · have hChi32 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi32
      · refine ⟨?_, ?_⟩
        · have hSupport33 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport33
        · have hChi33 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi33
      · refine ⟨?_, ?_⟩
        · have hSupport34 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport34
        · have hChi34 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi34
      · refine ⟨?_, ?_⟩
        · have hSupport35 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport35
        · have hChi35 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi35
      · refine ⟨?_, ?_⟩
        · have hSupport36 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport36
        · have hChi36 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi36
      · refine ⟨?_, ?_⟩
        · have hSupport37 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport37
        · have hChi37 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi37
      · refine ⟨?_, ?_⟩
        · have hSupport38 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport38
        · have hChi38 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi38
      · refine ⟨?_, ?_⟩
        · have hSupport39 : 32 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport39
        · have hChi39 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi39
      · refine ⟨?_, ?_⟩
        · have hSupport40 : 25 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport40
        · have hChi40 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi40
      · refine ⟨?_, ?_⟩
        · have hSupport41 : 18 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport41
        · have hChi41 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi41
      · refine ⟨?_, ?_⟩
        · have hSupport42 : 26 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport42
        · have hChi42 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi42
      · refine ⟨?_, ?_⟩
        · have hSupport43 : 48 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport43
        · have hChi43 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi43
      · refine ⟨?_, ?_⟩
        · have hSupport44 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport44
        · have hChi44 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi44
      · refine ⟨?_, ?_⟩
        · have hSupport45 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport45
        · have hChi45 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi45
      · refine ⟨?_, ?_⟩
        · have hSupport46 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport46
        · have hChi46 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi46
      · refine ⟨?_, ?_⟩
        · have hSupport47 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport47
        · have hChi47 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi47
      · refine ⟨?_, ?_⟩
        · have hSupport48 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport48
        · have hChi48 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi48
      · refine ⟨?_, ?_⟩
        · have hSupport49 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport49
        · have hChi49 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi49
      · refine ⟨?_, ?_⟩
        · have hSupport50 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport50
        · have hChi50 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi50
      · refine ⟨?_, ?_⟩
        · have hSupport51 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport51
        · have hChi51 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi51
      · refine ⟨?_, ?_⟩
        · have hSupport52 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport52
        · have hChi52 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi52
      · refine ⟨?_, ?_⟩
        · have hSupport53 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport53
        · have hChi53 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi53
      · refine ⟨?_, ?_⟩
        · have hSupport54 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport54
        · have hChi54 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi54
      · refine ⟨?_, ?_⟩
        · have hSupport55 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport55
        · have hChi55 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi55
      · refine ⟨?_, ?_⟩
        · have hSupport56 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport56
        · have hChi56 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi56
      · refine ⟨?_, ?_⟩
        · have hSupport57 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport57
        · have hChi57 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi57
      · refine ⟨?_, ?_⟩
        · have hSupport58 : 36 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport58
        · have hChi58 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi58
      · refine ⟨?_, ?_⟩
        · have hSupport59 : 33 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport59
        · have hChi59 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi59
      · refine ⟨?_, ?_⟩
        · have hSupport60 : 47 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport60
        · have hChi60 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi60
      · refine ⟨?_, ?_⟩
        · have hSupport61 : 55 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport61
        · have hChi61 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi61
      · refine ⟨?_, ?_⟩
        · have hSupport62 : 60 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport62
        · have hChi62 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi62
      · refine ⟨?_, ?_⟩
        · have hSupport63 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport63
        · have hChi63 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi63
      · refine ⟨?_, ?_⟩
        · have hSupport64 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport64
        · have hChi64 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi64
      · refine ⟨?_, ?_⟩
        · have hSupport65 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport65
        · have hChi65 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi65
      · refine ⟨?_, ?_⟩
        · have hSupport66 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport66
        · have hChi66 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi66
      · refine ⟨?_, ?_⟩
        · have hSupport67 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport67
        · have hChi67 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi67
      · refine ⟨?_, ?_⟩
        · have hSupport68 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport68
        · have hChi68 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi68
      · refine ⟨?_, ?_⟩
        · have hSupport69 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport69
        · have hChi69 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi69
      · refine ⟨?_, ?_⟩
        · have hSupport70 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport70
        · have hChi70 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi70
      · refine ⟨?_, ?_⟩
        · have hSupport71 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport71
        · have hChi71 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi71
      · refine ⟨?_, ?_⟩
        · have hSupport72 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport72
        · have hChi72 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi72
      · refine ⟨?_, ?_⟩
        · have hSupport73 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport73
        · have hChi73 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi73
      · refine ⟨?_, ?_⟩
        · have hSupport74 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport74
        · have hChi74 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi74
      · refine ⟨?_, ?_⟩
        · have hSupport75 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport75
        · have hChi75 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi75
      · refine ⟨?_, ?_⟩
        · have hSupport76 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport76
        · have hChi76 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi76
      · refine ⟨?_, ?_⟩
        · have hSupport77 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport77
        · have hChi77 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi77
      · refine ⟨?_, ?_⟩
        · have hSupport78 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport78
        · have hChi78 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi78
      · refine ⟨?_, ?_⟩
        · have hSupport79 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport79
        · have hChi79 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi79
      · refine ⟨?_, ?_⟩
        · have hSupport80 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport80
        · have hChi80 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi80
      · refine ⟨?_, ?_⟩
        · have hSupport81 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport81
        · have hChi81 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi81
      · refine ⟨?_, ?_⟩
        · have hSupport82 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport82
        · have hChi82 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi82
      · refine ⟨?_, ?_⟩
        · have hSupport83 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport83
        · have hChi83 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi83
      · refine ⟨?_, ?_⟩
        · have hSupport84 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport84
        · have hChi84 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi84
      · refine ⟨?_, ?_⟩
        · have hSupport85 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport85
        · have hChi85 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi85
      · refine ⟨?_, ?_⟩
        · have hSupport86 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport86
        · have hChi86 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi86
      · refine ⟨?_, ?_⟩
        · have hSupport87 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport87
        · have hChi87 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi87
      · refine ⟨?_, ?_⟩
        · have hSupport88 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport88
        · have hChi88 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi88
      · refine ⟨?_, ?_⟩
        · have hSupport89 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport89
        · have hChi89 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi89
      · refine ⟨?_, ?_⟩
        · have hSupport90 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport90
        · have hChi90 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi90
      · refine ⟨?_, ?_⟩
        · have hSupport91 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport91
        · have hChi91 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi91
      · refine ⟨?_, ?_⟩
        · have hSupport92 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport92
        · have hChi92 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi92
      · refine ⟨?_, ?_⟩
        · have hSupport93 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport93
        · have hChi93 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi93
      · refine ⟨?_, ?_⟩
        · have hSupport94 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport94
        · have hChi94 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi94
      · refine ⟨?_, ?_⟩
        · have hSupport95 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport95
        · have hChi95 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi95
      · refine ⟨?_, ?_⟩
        · have hSupport96 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport96
        · have hChi96 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi96
      · refine ⟨?_, ?_⟩
        · have hSupport97 : 60 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport97
        · have hChi97 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi97
      · refine ⟨?_, ?_⟩
        · have hSupport98 : 46 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport98
        · have hChi98 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi98
      · refine ⟨?_, ?_⟩
        · have hSupport99 : 35 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport99
        · have hChi99 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi99
      · refine ⟨?_, ?_⟩
        · have hSupport100 : 52 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport100
        · have hChi100 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi100
      · refine ⟨?_, ?_⟩
        · have hSupport101 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport101
        · have hChi101 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi101
      · refine ⟨?_, ?_⟩
        · have hSupport102 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport102
        · have hChi102 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi102
      · refine ⟨?_, ?_⟩
        · have hSupport103 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport103
        · have hChi103 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi103
      · refine ⟨?_, ?_⟩
        · have hSupport104 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport104
        · have hChi104 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi104
      · refine ⟨?_, ?_⟩
        · have hSupport105 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport105
        · have hChi105 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi105
      · refine ⟨?_, ?_⟩
        · have hSupport106 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport106
        · have hChi106 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi106
      · refine ⟨?_, ?_⟩
        · have hSupport107 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport107
        · have hChi107 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi107
      · refine ⟨?_, ?_⟩
        · have hSupport108 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport108
        · have hChi108 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi108
      · refine ⟨?_, ?_⟩
        · have hSupport109 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport109
        · have hChi109 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi109
      · refine ⟨?_, ?_⟩
        · have hSupport110 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport110
        · have hChi110 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi110
      · refine ⟨?_, ?_⟩
        · have hSupport111 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport111
        · have hChi111 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi111
      · refine ⟨?_, ?_⟩
        · have hSupport112 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport112
        · have hChi112 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi112
      · refine ⟨?_, ?_⟩
        · have hSupport113 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport113
        · have hChi113 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi113
      · refine ⟨?_, ?_⟩
        · have hSupport114 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport114
        · have hChi114 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi114
      · refine ⟨?_, ?_⟩
        · have hSupport115 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport115
        · have hChi115 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi115
      · refine ⟨?_, ?_⟩
        · have hSupport116 : 57 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport116
        · have hChi116 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi116
      · refine ⟨?_, ?_⟩
        · have hSupport117 : 60 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport117
        · have hChi117 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi117
      · refine ⟨?_, ?_⟩
        · have hSupport118 : 59 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport118
        · have hChi118 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi118
      · refine ⟨?_, ?_⟩
        · have hSupport119 : 55 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport119
        · have hChi119 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi119
      · refine ⟨?_, ?_⟩
        · have hSupport120 : 60 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport120
        · have hChi120 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi120
      · refine ⟨?_, ?_⟩
        · have hSupport121 : 64 ≤ polyEnvelope 1 5 := by decide
          exact polyEnvelope_witness_degree_sound hn hSupport121
        · have hChi121 : 3 ≤ polyEnvelope 1 1 := by decide
          exact polyEnvelope_witness_degree_sound hn hChi121) n hn

def atsp_demo_n3_via_sat_domainCoverToP : DomainCoverToP atsp_demo_n3_via_sat_domainFamily :=
  { cover := atsp_demo_n3_via_sat_domainCover
  , acceptedAll := atsp_demo_n3_via_sat_domainCover_accepted
  , polynomialWitness := atsp_demo_n3_via_sat_domainCoverWitness }

theorem atsp_demo_n3_via_sat_symbolic_in_P : ClassicalPolynomialSimulableByDomainCover atsp_demo_n3_via_sat_domainFamily :=
  shell_or_frequency_coverage_to_P atsp_demo_n3_via_sat_domainCoverToP

theorem atsp_demo_n3_via_sat_routeListCost_le_costAt (n : Nat) (hn : 1 ≤ n) :
    SymbolicDomainCover.routeListCost (atsp_demo_n3_via_sat_domainCover.routes n) ≤ atsp_demo_n3_via_sat_domainCover.costAt n :=
  SymbolicDomainCover.routeListCost_le_costAt atsp_demo_n3_via_sat_domainCover n (atsp_demo_n3_via_sat_domainCover_accepted n hn)

end HQIVNPBridgeDomainCover
