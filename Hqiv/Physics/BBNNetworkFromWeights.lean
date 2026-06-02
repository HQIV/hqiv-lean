import Hqiv.Physics.BoundStates
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.PostAlphaBindingGeometry
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric

/-!
# BBN light-element network from HQIV 8×8 weights

Reactions and abundances are driven by the **same** composite-trace spine as hadron mass:

* `E_bind_from_composite_trace` / `networkWeightFromCompositeTrace` (`BoundStates`)
* isotope-ladder **valley** bookkeeping (`HQIVNuclei`: deuteron → ³He → ⁴He)
* lock-in nucleon masses and `derivedDeltaM` (`DerivedNucleonMass`)
* baryon asymmetry `η` at lock-in (`BaryogenesisWitness`)

**Not used as inputs:** Coc et al. semi-analytic fits (those live in `BigBangNucleosynthesis` as a
comparison layer only). **Not claimed:** full 400-reaction PRIMAT integration or Li-problem solution.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Planck temperature in MeV (shell-index map for the BBN epoch). -/
def T_Pl_MeV : ℝ := 1.2209e19 * 1000

/-- BBN temperature bracket (MeV). -/
def bbnTemperatureLowMeV : ℝ := 0.01
def bbnTemperatureHighMeV : ℝ := 1.0

/-- Real shell index on the HQIV ladder: `m + 1 = T_Pl_MeV / T_MeV`. -/
noncomputable def bbnShellIndexFromMeV (T_MeV : ℝ) : ℝ :=
  T_Pl_MeV / T_MeV - 1

/-- Strong-channel fraction of the octonion carrier (4/8). Re-exports the single source of truth
from `HQIVNuclei.strongChannelFraction` for BBN weighting. -/
def bbnStrongChannelFraction : ℝ := Hqiv.Physics.strongChannelFraction

theorem bbnStrongChannelFraction_eq_strong_channel : bbnStrongChannelFraction = strongChannelFraction := rfl

/-- HQIV damping of horizon overlap at shell `m` (→ 0 at BBN). -/
noncomputable def gammaEffAtShell (m : ℕ) : ℝ :=
  gamma_HQIV * T m

/-- Phase-horizon weak-rate factor `T/T_Pl` at shell `m`. -/
noncomputable def phaseHorizonWeakRateFactor (m : ℕ) : ℝ :=
  T m / T_Pl

/-- Valley count on the constructive isotope ladder (matches `HQIVNuclei`). -/
def bbnValleyCount : ℕ → ℕ
  | 1 => 0
  | 2 => valleyCount deuteron
  | 3 => valleyCount helium3
  | 4 => valleyCount helium4
  | _ => 0

theorem bbnValleyCount_two : bbnValleyCount 2 = 2 := rfl
theorem bbnValleyCount_three : bbnValleyCount 3 = 4 := rfl
theorem bbnValleyCount_four : bbnValleyCount 4 = 6 := helium4_valleyCount

/-- Reference shell for light-nucleus binding (lock-in / proton anchor). -/
def bbnBindingShell : ℕ := referenceM

/-- Per-nucleon composite-trace binding at shell `m` (MeV-scale witness units). -/
noncomputable def bbnNucleonTraceBinding (m : ℕ) (c : ℝ := 1) : ℝ :=
  E_bind_from_composite_trace m nucleonTraceDiagonal nucleonTraceState c

/-- Toroidal-valley enhancement: constructive through ⁴He; post-α facet touches spin-gated. -/
noncomputable def bbnValleyBindingFactor (A : ℕ) (Z : ℕ := 0) : ℝ :=
  if A ≤ 4 then
    1 + (bbnValleyCount A : ℝ) / (bbnValleyCount 4 : ℝ)
  else
    let cap := (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ)
    let touch :=
      (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) / (bbnValleyCount 4 : ℝ) *
        spinStabilityParticipation A Z
    let far := farNeutronWeightedContactSum A Z / (bbnValleyCount 4 : ℝ)
    1 + cap + touch + far

/-- Cluster binding from the 8×8 network at shell `m` (specify `Z` when `A > 4`). -/
noncomputable def bbnClusterBinding (m A : ℕ) (c : ℝ := 1) (Z : ℕ := 0) : ℝ :=
  (A : ℝ) * bbnNucleonTraceBinding m c * bbnValleyBindingFactor A Z

/-!
### Geometric binding hook (future wiring point)

`bbnValleyBindingFactor` is a **normalized contact-count proxy** derived from the isotope ladder
and post-α sphere-touch geometry in `HQIVNuclei`. The underlying geometric currency is the
`valleyPotential` (negative Fresnel-caustic overlap) and the sphere-touch contact energies
(`sphereTouchContactEnergy`, `facetProtonContactSetEnergy`).

The hook below is the intended future home for a direct sum of valley-potential contributions
along a concrete packing of Fresnel caustics. Currently it delegates to the count-based factor
so that all downstream BBN readouts remain unchanged while the geometric derivation is developed.
-/

/-- Cluster binding from sphere-touch geometry when `A > 4`; ladder valley factor when `A ≤ 4`. -/
noncomputable def bbnClusterBindingFromCausticGeometry (m A : ℕ) (c : ℝ := 1) (Z : ℕ := 0) : ℝ :=
  if A ≤ 4 then bbnClusterBinding m A c Z
  else postAlphaClusterBindingWithNetwork m A Z c

theorem bbnClusterBindingFromCausticGeometry_le_four (m A : ℕ) (c : ℝ := 1) (Z : ℕ := 0)
    (hA : A ≤ 4) :
    bbnClusterBindingFromCausticGeometry m A c Z = bbnClusterBinding m A c Z := by
  unfold bbnClusterBindingFromCausticGeometry
  simp [hA]

theorem bbnClusterBindingFromCausticGeometry_gt_four (m A : ℕ) (c : ℝ := 1) (Z : ℕ := 0)
    (hA : 4 < A) :
    bbnClusterBindingFromCausticGeometry m A c Z =
      postAlphaClusterBindingWithNetwork m A Z c := by
  unfold bbnClusterBindingFromCausticGeometry
  simp [hA]

/-- Cluster mass from constituent nucleon mass minus network binding. -/
noncomputable def bbnClusterMass (m A : ℕ) (m_nucleon : ℝ) (c : ℝ := 1) (Z : ℕ := 0) : ℝ :=
  (A : ℝ) * m_nucleon - bbnClusterBinding m A c Z

/-- Deuteron mass from the network at the binding shell. -/
noncomputable def bbnDeuteronMass (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnClusterMass bbnBindingShell 2 m_nucleon c

/-- ⁴He mass from the network at the binding shell. -/
noncomputable def bbnHelium4Mass (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnClusterMass bbnBindingShell 4 m_nucleon c

/-- D + γ binding Q from network masses (MeV). -/
noncomputable def bbnDeuteronBindingQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  2 * m_nucleon - bbnDeuteronMass m_nucleon c

/-- ⁴He + γ binding Q from network masses (MeV). -/
noncomputable def bbnHelium4BindingQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  4 * m_nucleon - bbnHelium4Mass m_nucleon c

/-- n/p equilibrium factor at temperature `T_MeV` with HQIV mass gap `Q_np`. -/
noncomputable def bbnNeutronProtonRatio (T_MeV Q_np : ℝ) : ℝ :=
  Real.exp (-Q_np / T_MeV) / (1 + Real.exp (-Q_np / T_MeV))

/-- ⁴He mass fraction from captured neutrons before decay (network-lite). -/
noncomputable def bbnYpFromNeutronFraction (x_n : ℝ) : ℝ :=
  2 * x_n / (1 + x_n)

/-- HQIV n–p gap for weak equilibrium (derived nucleon split). -/
noncomputable def bbnNeutronProtonGap : ℝ := derivedDeltaM

/-- Freeze-out n/p ratio using `derivedDeltaM` at `T_MeV`. -/
noncomputable def bbnNeutronFractionAt (T_MeV : ℝ) : ℝ :=
  bbnNeutronProtonRatio T_MeV bbnNeutronProtonGap

/-- ⁴He mass fraction from the weight-derived freeze-out factor. -/
noncomputable def bbnYpFromNetworkAt (T_MeV : ℝ) : ℝ :=
  bbnYpFromNeutronFraction (bbnNeutronFractionAt T_MeV)

/-- Boltzmann weight `exp(Q/T)` for a cluster channel (dimensionless). -/
noncomputable def bbnBoltzmannWeight (Q T_MeV : ℝ) : ℝ :=
  Real.exp (Q / T_MeV)

/-- η₁₀ = 10¹⁰ η (baryon-to-photon ratio in BBN convention). -/
noncomputable def eta10 (η : ℝ) : ℝ := η * 10^10

/-- η₁₀ exponent for D/H: \(-(Q_\alpha - Q_D)/Q_{np}\) from binding gaps over the HQIV weak scale. -/
noncomputable def bbnDH_etaExponent (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  -((bbnHelium4BindingQ m_nucleon c - bbnDeuteronBindingQ m_nucleon c) / bbnNeutronProtonGap)

/-- ³He/H η exponent from trimer vs deuteron binding gap. -/
noncomputable def bbnHe3_etaExponent (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  -((bbnClusterBinding bbnBindingShell 3 c - bbnDeuteronBindingQ m_nucleon c) / bbnNeutronProtonGap)

/-- ⁷Be (`A = 7`, `Z = 4`): α core + two extra protons × three contacts each. -/
noncomputable def bbnBe7BindingQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnClusterBinding bbnBindingShell 7 c (Z := 4)

/-- ⁷Li (`A = 7`, `Z = 3`): one facet proton + far-neutron touches at `(4/8)` weight. -/
noncomputable def bbnLi7ClusterBindingQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnClusterBinding bbnBindingShell 7 c (Z := 3)

/-- ⁷Be → ⁷Li capture Q from cluster-well depth difference (daughter far-neutron well). -/
noncomputable def bbnBe7ToLi7CaptureQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  gamma_HQIV * bbnStrongChannelFraction *
    max 0 (bbnBe7BindingQ m_nucleon c - bbnLi7ClusterBindingQ m_nucleon c)

/-- ³He + ⁴He → ⁷Be reaction Q from network binding gaps. -/
noncomputable def bbnBe7FormationQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnBe7BindingQ m_nucleon c - bbnClusterBinding bbnBindingShell 3 c - bbnHelium4BindingQ m_nucleon c

/-- ⁷Be electron-capture scale: weak-channel fraction × n–p gap (no fitted ec Q). -/
noncomputable def bbnBe7ElectronCaptureQ : ℝ :=
  gamma_HQIV * bbnStrongChannelFraction * bbnNeutronProtonGap

/-- ⁷Li/H η exponent (seventh-order valley proxy on α vs deuteron gap). -/
noncomputable def bbnLi7_etaExponent (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  -(((7 / 4 : ℝ) * bbnHelium4BindingQ m_nucleon c - bbnDeuteronBindingQ m_nucleon c) / bbnNeutronProtonGap)

/-!
### Lithium-7 channel: explicit illustrative scaffold

The current `bbnLi7*` formulas are **scaffold illustrations** that demonstrate how a valley-weighted
network readout would propagate to A=7. At mid-epoch and in window-integrated witnesses the
resulting ⁷Li/H can be astronomically large (Boltzmann exponents driven by the 7/4 proxy and
the gap to ⁴He). This is **not claimed** to match observational bounds. The Li channels serve
as a template for future nuclear-network upgrades (dynamic C₂ lapse suppression, full reaction
graph, post-BBN depletion). See the BBN paper §"Honesty on lithium".
-/

/-- Marker proposition: the Li7 abundance formulas are illustrative scaffold readouts whose
numeric magnitude at BBN-epoch temperatures is not asserted to lie near observational values. -/
def bbnLi7_is_illustrative_scaffold : Prop := True

theorem bbnLi7_is_illustrative_scaffold_holds : bbnLi7_is_illustrative_scaffold := trivial

/-- Thermal factor exp((Q_light − Q_α)/T) at partition temperature. -/
noncomputable def bbnThermalSinkFactor (Q_light Q_alpha T_MeV : ℝ) : ℝ :=
  bbnBoltzmannWeight (Q_light - Q_alpha) T_MeV

/-- Internal BBN temperature from the weak gap and η₁₀ anchor: `T = Q_np / log(η₁₀)`. -/
noncomputable def bbnInternalTemperatureMeV (η Q_np : ℝ) : ℝ :=
  Q_np / Real.log (eta10 η)

/-- D/H from network weights: `η₁₀^exponent × exp((Q_D−Q_α)/T_bbn)`. -/
noncomputable def bbnDHNumberRatio (η : ℝ) (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  (eta10 η) ^ bbnDH_etaExponent m_nucleon c *
    bbnThermalSinkFactor (bbnDeuteronBindingQ m_nucleon c) (bbnHelium4BindingQ m_nucleon c)
      (bbnInternalTemperatureMeV η bbnNeutronProtonGap)

noncomputable def bbnHe3HNumberRatio (η : ℝ) (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  (eta10 η) ^ bbnHe3_etaExponent m_nucleon c *
    bbnThermalSinkFactor (bbnClusterBinding bbnBindingShell 3 c) (bbnHelium4BindingQ m_nucleon c)
      (bbnInternalTemperatureMeV η bbnNeutronProtonGap)

noncomputable def bbnLi7HNumberRatio (η : ℝ) (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  (eta10 η) ^ bbnLi7_etaExponent m_nucleon c *
    bbnThermalSinkFactor (bbnHelium4BindingQ m_nucleon c * (7 / 4 : ℝ)) (bbnHelium4BindingQ m_nucleon c)
      (bbnInternalTemperatureMeV η bbnNeutronProtonGap)

structure BBNNetworkReadout where
  eta : ℝ
  T_MeV : ℝ
  Yp : ℝ
  DH : ℝ
  He3H : ℝ
  Li7H : ℝ
  deuteronQ : ℝ
  helium4Q : ℝ

/-- Network readout at lock-in η and a chosen BBN temperature. -/
noncomputable def bbnNetworkReadoutAt (η T_MeV : ℝ) (c : ℝ := 1) : BBNNetworkReadout where
  eta := η
  T_MeV := T_MeV
  Yp := bbnYpFromNetworkAt T_MeV
  DH := bbnDHNumberRatio η derivedProtonMass c
  He3H := bbnHe3HNumberRatio η derivedProtonMass c
  Li7H := bbnLi7HNumberRatio η derivedProtonMass c
  deuteronQ := bbnDeuteronBindingQ derivedProtonMass c
  helium4Q := bbnHelium4BindingQ derivedProtonMass c

/-- Default BBN temperature for the partition (0.1 MeV, mid-epoch). -/
def bbnPartitionTemperatureMeV : ℝ := 1 / 10

noncomputable def bbnNetworkReadoutAtLockin : BBNNetworkReadout :=
  bbnNetworkReadoutAt eta_paper bbnPartitionTemperatureMeV

theorem bbnNetworkReadoutAtLockin_eta : bbnNetworkReadoutAtLockin.eta = eta_paper := rfl

theorem bbnBindingShell_eq_referenceM : bbnBindingShell = referenceM := rfl

theorem bbnNeutronProtonGap_eq_derivedDeltaM : bbnNeutronProtonGap = derivedDeltaM := rfl

theorem eta10_eta_paper_gt_one : 1 < eta10 eta_paper := by
  rw [eta10, eta_paper_eq_div]
  norm_num

theorem bbnBoltzmannWeight_pos (Q T_MeV : ℝ) : 0 < bbnBoltzmannWeight Q T_MeV := by
  unfold bbnBoltzmannWeight
  exact Real.exp_pos _

theorem bbnValleyBindingFactor_pos (A : ℕ) (Z : ℕ := 0) : 0 < bbnValleyBindingFactor A Z := by
  unfold bbnValleyBindingFactor
  split_ifs with hle
  · have h4 : 0 < (bbnValleyCount 4 : ℝ) := by norm_num [bbnValleyCount_four]
    positivity
  · have hcapPos : 0 < (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ) := by
      rw [constructiveValleyCap_eq_six, bbnValleyCount_four]
      norm_num
    have hspin := spinStabilityParticipation_nonneg A Z
    have hfar := farNeutronWeightedContactSum_nonneg A Z
    have htouch : 0 ≤ (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) := by
      norm_cast
      exact Nat.zero_le _
    have hbase : (1 : ℝ) < 1 + (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ) := by linarith
    have hvalley : 0 < (bbnValleyCount 4 : ℝ) := by norm_num [bbnValleyCount_four]
    have htouchDiv :
        0 ≤ (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) / (bbnValleyCount 4 : ℝ) *
          spinStabilityParticipation A Z :=
      mul_nonneg (div_nonneg htouch (le_of_lt hvalley)) hspin
    have hfarDiv : 0 ≤ farNeutronWeightedContactSum A Z / (bbnValleyCount 4 : ℝ) :=
      div_nonneg hfar (le_of_lt hvalley)
    have hfull :
        1 + (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ) ≤
          1 + (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ) +
            (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) / (bbnValleyCount 4 : ℝ) *
              spinStabilityParticipation A Z +
            farNeutronWeightedContactSum A Z / (bbnValleyCount 4 : ℝ) := by
      linarith
    have hpos : (0 : ℝ) < 1 + (constructiveValleyCap : ℝ) / (bbnValleyCount 4 : ℝ) :=
      lt_trans zero_lt_one hbase
    exact lt_of_lt_of_le hpos hfull

theorem bbnDeuteronBindingQ_eq_clusterBinding (m_nucleon : ℝ) (c : ℝ := 1) :
    bbnDeuteronBindingQ m_nucleon c = bbnClusterBinding bbnBindingShell 2 c := by
  unfold bbnDeuteronBindingQ bbnDeuteronMass bbnClusterMass
  ring

/-- For A ≤ 4 the valley binding factor is exactly 1 + (valleyCount A) / 6, i.e. the normalized
constructive ladder count. This matches the tetrahedral edge accounting in HQIVNuclei
(`valleyCount helium4 = tetrahedralEdgeCount = 6`). -/
theorem bbnValleyBindingFactor_eq_ladder_for_A_le_4 (A : ℕ) (hA : A ≤ 4) :
    bbnValleyBindingFactor A 0 = 1 + (bbnValleyCount A : ℝ) / (bbnValleyCount 4 : ℝ) := by
  unfold bbnValleyBindingFactor
  simp [hA]

theorem bbnValleyBindingFactor_A4_eq_2 : bbnValleyBindingFactor 4 0 = 2 := by
  unfold bbnValleyBindingFactor bbnValleyCount
  simp [helium4_valleyCount]
  norm_num

/-- The BBN strong-channel fraction is identical to the HQIVNuclei source of truth. -/
theorem bbnStrongChannelFraction_is_HQIVNuclei_strong :
    bbnStrongChannelFraction = Hqiv.Physics.strongChannelFraction := rfl

theorem bbnHelium4BindingQ_eq_clusterBinding (m_nucleon : ℝ) (c : ℝ := 1) :
    bbnHelium4BindingQ m_nucleon c = bbnClusterBinding bbnBindingShell 4 c := by
  unfold bbnHelium4BindingQ bbnHelium4Mass bbnClusterMass
  ring

/-- 2D → ⁴He reaction Q from lock-in composite trace: `Q_α − 2 Q_D`. -/
noncomputable def bbnDDReactionQ (m_nucleon : ℝ) (c : ℝ := 1) : ℝ :=
  bbnHelium4BindingQ m_nucleon c - 2 * bbnDeuteronBindingQ m_nucleon c

theorem bbnDDReactionQ_eq (m_nucleon : ℝ) (c : ℝ := 1) :
    bbnDDReactionQ m_nucleon c =
      bbnHelium4BindingQ m_nucleon c - 2 * bbnDeuteronBindingQ m_nucleon c := rfl

theorem bbnDDReactionQ_eq_clusterBinding (m_nucleon : ℝ) (c : ℝ := 1) :
    bbnDDReactionQ m_nucleon c =
      bbnClusterBinding bbnBindingShell 4 c - 2 * bbnClusterBinding bbnBindingShell 2 c := by
  simp [bbnDDReactionQ_eq, bbnHelium4BindingQ_eq_clusterBinding, bbnDeuteronBindingQ_eq_clusterBinding]

theorem bbnNeutronProtonRatio_mem_Ioo (T_MeV Q_np : ℝ) (hT : 0 < T_MeV) (hQ : 0 < Q_np) :
    bbnNeutronProtonRatio T_MeV Q_np ∈ Set.Ioo 0 1 := by
  unfold bbnNeutronProtonRatio
  set x := Real.exp (-Q_np / T_MeV)
  have hx0 : 0 < x := Real.exp_pos _
  have hneg : -Q_np / T_MeV < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr hQ) hT
  have hx1 : x < 1 := (Real.exp_lt_one_iff).mpr hneg
  constructor
  · positivity
  · rw [div_lt_one (by linarith [hx0])]
    linarith [hx1]

theorem bbnNeutronFractionAt_mem_Ioo (T_MeV : ℝ) (hT : 0 < T_MeV) (hQ : 0 < bbnNeutronProtonGap) :
    bbnNeutronFractionAt T_MeV ∈ Set.Ioo 0 1 := by
  dsimp [bbnNeutronFractionAt]
  exact bbnNeutronProtonRatio_mem_Ioo T_MeV bbnNeutronProtonGap hT hQ

theorem bbnYpFromNeutronFraction_mem_Ioo {x_n : ℝ} (hx : x_n ∈ Set.Ioo 0 1) :
    bbnYpFromNeutronFraction x_n ∈ Set.Ioo 0 1 := by
  dsimp [bbnYpFromNeutronFraction]
  constructor
  · exact div_pos (by linarith [hx.1]) (by linarith [hx.1])
  · rw [div_lt_one (by linarith [hx.1])]
    linarith [hx.2]

theorem bbnYpFromNeutronFraction_lt_one {x_n : ℝ} (hx0 : 0 < x_n) (hx1 : x_n < 1) :
    bbnYpFromNeutronFraction x_n < 1 := by
  dsimp [bbnYpFromNeutronFraction]
  rw [div_lt_one (by linarith [hx0])]
  linarith [hx1]

theorem eta_bbn_eq_eta_paper :
    eta_at_horizon m_lockin m_lockin = eta_paper :=
  eta_lockin_calibration curvature_integral_m_lockin_pos

theorem bbnYpFromNetwork_pos (T_MeV : ℝ) (hT : 0 < T_MeV) :
    0 < bbnYpFromNetworkAt T_MeV := by
  dsimp [bbnYpFromNetworkAt, bbnYpFromNeutronFraction, bbnNeutronFractionAt, bbnNeutronProtonRatio,
    bbnNeutronProtonGap]
  positivity

theorem bbnDHNumberRatio_pos (η : ℝ) (hη : 0 < η) (hη10 : 1 < eta10 η) :
    0 < bbnDHNumberRatio η derivedProtonMass := by
  unfold bbnDHNumberRatio bbnDH_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight
      bbnInternalTemperatureMeV eta10 bbnNeutronProtonGap
  have hpow : 0 < (eta10 η) ^ bbnDH_etaExponent derivedProtonMass :=
    Real.rpow_pos_of_pos (by linarith [hη10]) _
  have htherm : 0 < Real.exp
      ((bbnDeuteronBindingQ derivedProtonMass - bbnHelium4BindingQ derivedProtonMass) /
        (bbnNeutronProtonGap / Real.log (eta10 η))) :=
    Real.exp_pos _
  exact mul_pos hpow htherm

/-- The Li7/H readout is positive under the illustrative scaffold formulas (positivity only;
the concrete magnitude at BBN temperatures is not asserted to match observation). -/
theorem bbnLi7HNumberRatio_pos (η : ℝ) (hη : 0 < η) (hη10 : 1 < eta10 η) :
    0 < bbnLi7HNumberRatio η derivedProtonMass := by
  unfold bbnLi7HNumberRatio bbnLi7_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight
      bbnInternalTemperatureMeV eta10 bbnNeutronProtonGap
  have hpow : 0 < (eta10 η) ^ bbnLi7_etaExponent derivedProtonMass :=
    Real.rpow_pos_of_pos (by linarith [hη10]) _
  exact mul_pos hpow (Real.exp_pos _)

def bbn_network_vital_readout : Prop :=
  eta_at_horizon m_lockin m_lockin = eta_paper ∧
    0 < bbnNetworkReadoutAtLockin.Yp ∧
      0 < bbnNetworkReadoutAtLockin.DH ∧
        0 < bbnNetworkReadoutAtLockin.He3H ∧
          0 < bbnNetworkReadoutAtLockin.Li7H

theorem bbn_network_vital_readout_holds :
    bbn_network_vital_readout := by
  refine ⟨eta_bbn_eq_eta_paper, ?_⟩
  dsimp [bbnNetworkReadoutAtLockin, bbnNetworkReadoutAt, bbnPartitionTemperatureMeV]
  have hT : 0 < (1 / 10 : ℝ) := by norm_num
  have hη10 : 1 < eta10 eta_paper := by
    rw [eta10, eta_paper_eq_div]
    norm_num
  refine ⟨bbnYpFromNetwork_pos (1 / 10) hT,
    bbnDHNumberRatio_pos eta_paper eta_paper_pos hη10, ?_, ?_⟩
  · unfold bbnHe3HNumberRatio bbnHe3_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight
      bbnInternalTemperatureMeV eta10
    have hpow : 0 < (eta10 eta_paper) ^ bbnHe3_etaExponent derivedProtonMass :=
      Real.rpow_pos_of_pos (by linarith [hη10]) _
    exact mul_pos hpow (Real.exp_pos _)
  · unfold bbnLi7HNumberRatio bbnLi7_etaExponent bbnThermalSinkFactor bbnBoltzmannWeight
      bbnInternalTemperatureMeV eta10
    have hpow : 0 < (eta10 eta_paper) ^ bbnLi7_etaExponent derivedProtonMass :=
      Real.rpow_pos_of_pos (by linarith [hη10]) _
    exact mul_pos hpow (Real.exp_pos _)

end

end Hqiv.Physics
