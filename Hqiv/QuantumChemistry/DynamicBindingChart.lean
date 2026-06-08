import Hqiv.QuantumChemistry.LiH
import Hqiv.QuantumChemistry.LiHDerivation
import Hqiv.Geometry.BondedHorizonCasimir
import Hqiv.Physics.TuftShellChart
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.ContinuousXiCoupling

/-!
# Dynamic binding chart (general finite-site readout)

Parameter-free packaging of the post-T12/T13 dynamic binding formula for an
arbitrary bonded surplus and Compton triplet:

`E_bind = η_p · surplus_dimless · geomean(tuftVevFactorNetworkedAtCluster) ·
dynamicBindingCurvatureFeedbackAtXi(ξ) · EV_per_λ` with `κ(ξ) = γ·(4/8)·ω_K(ξ)/ω_K(ξ_lock)`.

Bare `tuftVevFactorAtXi` on fixed shells is the ladder chart; the networked factor dresses ξ by
per-nucleon cluster mass ``(A·m_p − B)/A`` so bound D/T/He deficits propagate into heavier readouts.

LiH is the worked example (`lihDynamicBindingCoreDimless`); this module states the
**generic** factorization used by the Python GMTKN55 chart (`hqiv_dynamic_binding_chart.py`).

Structural theorems only — no numeric fit to experiment.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Hqiv.Geometry
open scoped BigOperators

noncomputable section

/-- Binding readout kind on the finite-site chart. -/
inductive DynamicBindingKind
  | dissociation
  | atomization
  deriving DecidableEq, Repr

/-- Parameter-free Compton triplet scaffold (shell indices `m`, not `ξ = m+1`). -/
structure DynamicComptonTriplet where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  deriving Repr

def dynamicComptonTripletH2 : DynamicComptonTriplet := ⟨1, 1, 1⟩

/-- Heavy-hydride triplet from TUFT chart rows + proton-anchor hydrogen `1`. -/
def dynamicComptonTripletHeavyHydride : DynamicComptonTriplet :=
  ⟨tuftHeavyChartShell, tuftStrongChartShell, 1⟩

def dynamicComptonTripletHomonuclearPeriod2 : DynamicComptonTriplet := ⟨4, 4, 4⟩

def DynamicComptonTriplet.shellAt (t : DynamicComptonTriplet) : Fin 3 → ℕ
  | 0 => t.m0
  | 1 => t.m1
  | 2 => t.m2

def DynamicComptonTriplet.xiAt (t : DynamicComptonTriplet) : Fin 3 → ℝ
  | i => xiOfShell (t.shellAt i)

/-- Temperature-relative TUFT vev factor: `heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5`. -/
noncomputable def tuftVevFactorAtXi (ξ : ℝ) : ℝ :=
  heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5

theorem tuftVevFactorAtXi_lockin :
    tuftVevFactorAtXi 5 = 1 := by
  unfold tuftVevFactorAtXi
  have h0 : heavy_lepton_gap_at_xi 5 ≠ 0 := by
    rw [heavy_lepton_gap_at_lockin_eq_four_fifths]
    norm_num
  field_simp [h0]

/-- Geometric mean of `tuftVevFactorAtXi` on a Compton triplet. -/
noncomputable def dynamicComptonTuftVevGeometricMean (t : DynamicComptonTriplet) : ℝ :=
  Real.rpow (
    tuftVevFactorAtXi (t.xiAt 0) *
      tuftVevFactorAtXi (t.xiAt 1) *
      tuftVevFactorAtXi (t.xiAt 2)) (1 / 3)

/-- Per-nucleon cluster mass after BBN/valley binding (same spine as `bbnClusterMass`). -/
noncomputable def clusterMassMeV (m A : ℕ) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * derivedProtonMass - bbnClusterBinding m A c

/-- Mass-networked TUFT vev: ξ_eff = ξ_lock · (clusterMass / A / m_p). -/
noncomputable def tuftVevFactorNetworkedAtCluster (m A : ℕ) (c : ℝ := 1) : ℝ :=
  let mEff := clusterMassMeV m A c / (A : ℝ)
  tuftVevFactorAtXi (xiLockin * (mEff / derivedProtonMass))

/-- BBN-valley networked geomean over ``a = 1, …, A``. -/
noncomputable def valleyNetworkTuftVevGeometricMean (A : ℕ) (c : ℝ := 1) : ℝ :=
  Real.rpow (∏ a ∈ Finset.Icc 1 A, tuftVevFactorNetworkedAtCluster (referenceM) a c) (1 / (A : ℝ))

/-- Peripheral H on a heavy centre: repulsive contacts per H (CH₄: two each). -/
def peripheralHHRepulsiveContactsPerHydrogen (nH : ℕ) : ℕ :=
  if nH < 2 then 0 else if 4 ≤ nH then 2 else if nH = 3 then 2 else 1

/-- Undirected H–H repulsive contact points (CH₄: four). -/
def peripheralHHRepulsiveContactPoints (nH : ℕ) : ℕ :=
  nH * peripheralHHRepulsiveContactsPerHydrogen nH / 2

/-- Mean ξ over a Compton triplet (contact readout). -/
noncomputable def dynamicComptonXiMean (t : DynamicComptonTriplet) : ℝ :=
  (t.xiAt 0 + t.xiAt 1 + t.xiAt 2) / 3

/-- Dynamic κ(ξ) = γ · (4/8) · ω_K chart ratio (replaces fixed κ_bind). -/
noncomputable def dynamicBindingCurvatureCouplingAtXi (xi : ℝ) : ℝ :=
  gamma_HQIV * strongChannelFraction * omegaKContinuous xi xiLockin

/-- Dimensionless cluster-binding contrast (B_lock − B_qcd) / B_lock. -/
noncomputable def clusterBindingContrastRelative : ℝ :=
  (bbnClusterBinding m_lockin 4 - bbnClusterBinding m_QCD 4) / bbnClusterBinding m_lockin 4

/-- Binding-curvature correction at contact ξ (dimensionless). -/
noncomputable def dynamicBindingCurvatureCorrectionAtXi (xi : ℝ) : ℝ :=
  dynamicBindingCurvatureCouplingAtXi xi * clusterBindingContrastRelative

/-- First-order binding feedback at ξ. -/
noncomputable def dynamicBindingCurvatureFeedbackAtXi (xi : ℝ) : ℝ :=
  1 + dynamicBindingCurvatureCorrectionAtXi xi

/-- p-slot active on a Compton triplet (heavy-centre hydride / polyatomic pattern). -/
def dynamicComptonPShellActive (t : DynamicComptonTriplet) : Bool :=
  t.m1 > 1 ∧ t.m0 ≠ t.m1

/--
Second-order Compton participation on the p shell:

`η → η + (4/8) · η²` when the p slot is active (LiH valence trace / shared-p channel).
Inactive for `(1,1,1)` homonuclear H₂.
-/
noncomputable def dynamicComptonEtaSecondOrder (ηp : ℝ) (hasPShell : Bool) : ℝ :=
  if hasPShell then ηp + strongChannelFraction * ηp ^ 2 else ηp

/--
Second-order binding feedback: first-order κ(ξ) contrast times lapse concentration
`C₂(ξ)/C₂(ξ_lock)` from `tuftHopfKappa6AtXi` (Hopf / BBN mass geometry).
-/
noncomputable def dynamicBindingCurvatureFeedbackSecondOrderAtXi (xi : ℝ) : ℝ :=
  dynamicBindingCurvatureFeedbackAtXi xi *
    (tuftLapseConcentrationAtXi xi 0 0 / tuftLapseConcentrationAtXi xiLockin 0 0)

/--
Generic dimless dynamic binding core on the post-lock-in shell chart.

`surplus` is either a diatomic bonded-horizon surplus or a polyatomic atomization
surplus supplied by the caller; this module does not fix which physics map is used.
-/
noncomputable def dynamicBindingCoreDimlessAtXi (ηp surplus vevGeom xi : ℝ) : ℝ :=
  ηp * surplus * vevGeom * dynamicBindingCurvatureFeedbackAtXi xi

theorem dynamicBindingCoreDimlessAtXi_eq
    (ηp surplus vevGeom xi : ℝ) :
    dynamicBindingCoreDimlessAtXi ηp surplus vevGeom xi =
      ηp * surplus * vevGeom * dynamicBindingCurvatureFeedbackAtXi xi := rfl

/--
Dimless core with second-order η_p (p shell) and optional lapse-dressed feedback.

Default GMTKN55 chart uses the η second-order factor; C₂ dressing is available for
bulk / BBN-aligned readouts via `dynamicBindingCurvatureFeedbackSecondOrderAtXi`.
-/
noncomputable def dynamicBindingCoreDimlessSecondOrderAtXi
    (ηp surplus vevGeom xi : ℝ) (t : DynamicComptonTriplet) : ℝ :=
  dynamicComptonEtaSecondOrder ηp (dynamicComptonPShellActive t) * surplus * vevGeom *
    dynamicBindingCurvatureFeedbackAtXi xi

noncomputable def dynamicBindingCoreDimless
    (ηp surplus vevGeom : ℝ) (t : DynamicComptonTriplet) : ℝ :=
  dynamicBindingCoreDimlessAtXi ηp surplus vevGeom (dynamicComptonXiMean t)

/-- Chemist-convention binding energy in eV from the generic dimless core. -/
noncomputable def dynamicBindingEnergyEv (core : ℝ) : ℝ :=
  core * eVPerLambdaUnit_S7HydrogenAnchor

theorem dynamicBindingCoreDimlessAtXi_pos
    (ηp surplus vevGeom xi : ℝ)
    (hηp : 0 < ηp) (hsur : 0 < surplus) (hvev : 0 < vevGeom)
    (hfb : 0 < dynamicBindingCurvatureFeedbackAtXi xi) :
    0 < dynamicBindingCoreDimlessAtXi ηp surplus vevGeom xi := by
  unfold dynamicBindingCoreDimlessAtXi
  exact mul_pos (mul_pos (mul_pos hηp hsur) hvev) hfb

theorem dynamicBindingEnergyEv_pos_of_core_pos (core : ℝ) (hcore : 0 < core) :
    0 < dynamicBindingEnergyEv core := by
  unfold dynamicBindingEnergyEv
  exact mul_pos hcore (by unfold eVPerLambdaUnit_S7HydrogenAnchor hydrogenGroundIP_eV; norm_num)

/-- Dissociation surplus alias for a two-fragment bonded horizon (electron counts as naturals). -/
noncomputable def diatomicBondSurplusDimless
    (nTotal nFrag1 nFrag2 : ℕ)
    (cfg : NuclearTorusConfig := defaultNuclearTorus) : ℝ :=
  bondHorizonSurplusDimless nTotal nFrag1 nFrag2 cfg

/-- Per-nucleon composite-trace binding at shell `m` (BBN / hadron network spine). -/
noncomputable def perNucleonTraceBindingMeV (m : ℕ) (c : ℝ := 1) : ℝ :=
  bbnNucleonTraceBinding m c

theorem perNucleonTraceBindingMeV_eq_bbn (m : ℕ) (c : ℝ) :
    perNucleonTraceBindingMeV m c = bbnNucleonTraceBinding m c := rfl

/-- Cluster binding per nucleon at mass number `A` and shell `m`. -/
noncomputable def perNucleonClusterBindingMeV (m A : ℕ) (c : ℝ := 1) : ℝ :=
  bbnClusterBinding m A c / (A : ℝ)

theorem perNucleonClusterBindingMeV_eq (m A : ℕ) (c : ℝ) :
    perNucleonClusterBindingMeV m A c = bbnClusterBinding m A c / (A : ℝ) := rfl

end

end Hqiv.QuantumChemistry
