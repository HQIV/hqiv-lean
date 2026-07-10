import Hqiv.QuantumChemistry.OutsideContactGeometry
import Hqiv.QuantumChemistry.PhaseAllotropeDerivation
import Hqiv.QuantumChemistry.AtomElectronicDischarge
import Mathlib.Tactic

/-!
# Crystal lattice contact geometry

Periodic solid-state nearest-neighbour targets for ionic rocksalt, metallic close-packed,
and covalent-network crystals.  Distinct from gas-phase diatomic ``r_e`` and from
one-way nested-WF covalent routes.

Python mirror: ``hqiv_lab/crystal_geometry.py``, ``scripts/hqiv_crystal_contact_geometry.py``.

No tabulated lattice constants; no comparison Å inputs; no `sorry`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Real

noncomputable section

/-- Rocksalt / ionic lattice periodic dress from coordination and HQIV rationals. -/
noncomputable def ionicRocksaltLatticeDress (nCoord : ℕ) : ℝ :=
  (1 + (nCoord : ℝ) * strongChannelFraction / 4) * (1 + gamma_HQIV / 4)

/-- Metal-hydride lattice dress ``1 + (4/8)·(γ/2)`` (anion Z=1; not rocksalt CN open). -/
noncomputable def ionicHydrideLatticeDress : ℝ :=
  1 + strongChannelFraction * (gamma_HQIV / 2)

/-- Metal-hydride melt dress ``(1+α)/γ²`` (anion Z=1); else identity. -/
noncomputable def ionicHydrideMeltDress (zAnion : ℕ) : ℝ :=
  if zAnion = 1 then (1 + alpha) / (gamma_HQIV * gamma_HQIV) else 1

theorem ionicRocksaltLatticeDress_ge_one (nCoord : ℕ) :
    1 ≤ ionicRocksaltLatticeDress nCoord := by
  unfold ionicRocksaltLatticeDress
  have hs : 0 ≤ strongChannelFraction := by unfold strongChannelFraction; norm_num
  have hγ : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  have hn : 0 ≤ (nCoord : ℝ) := by positivity
  nlinarith [mul_nonneg hn hs, mul_nonneg hγ (show 0 ≤ (1 / 4 : ℝ) by norm_num)]

theorem ionicHydrideLatticeDress_ge_one :
    1 ≤ ionicHydrideLatticeDress := by
  unfold ionicHydrideLatticeDress
  have hs : 0 ≤ strongChannelFraction := by unfold strongChannelFraction; norm_num
  have hγ : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  nlinarith [mul_nonneg hs hγ]

/-- Lattice dress: hydride (anion Z=1) → mild; else rocksalt CN dress. -/
noncomputable def ionicLatticeDress (zAnion nCoord : ℕ) : ℝ :=
  if zAnion = 1 then ionicHydrideLatticeDress else ionicRocksaltLatticeDress nCoord

/-- Ionic crystal nearest-neighbour M–X contact from outside-contact pair length × lattice dress. -/
noncomputable def ionicLatticeNearestNeighborTarget
    (m_i z_i m_j z_j nCoord : ℕ) (c : ℝ := 1) : ℝ :=
  let zA := if z_i = 1 then z_i else if z_j = 1 then z_j else max z_i z_j
  ionicOutsideContactLengthTarget m_i z_i m_j z_j c *
    ionicLatticeDress zA nCoord

/-- FCC close-packing factor ``(n_coord/2)^(1/3)`` for metallic nn contacts. -/
noncomputable def metallicFccPackingFactor (nCoord : ℕ) : ℝ :=
  ((max nCoord 1 : ℝ) / 2) ^ (1 / 3 : ℝ)

theorem metallicFccPackingFactor_pos (nCoord : ℕ) :
    0 < metallicFccPackingFactor nCoord := by
  unfold metallicFccPackingFactor
  have hn : 0 < (max nCoord 1 : ℝ) := by
    have h1 : (1 : ℕ) ≤ max nCoord 1 := Nat.le_max_right nCoord 1
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  apply Real.rpow_pos_of_pos (div_pos hn (by norm_num))

/-- Metallic lattice nn from nested-WF radius × FCC pack × period screening. -/
noncomputable def metallicLatticeNearestNeighborTarget (m z nCoord : ℕ) (c : ℝ := 1) : ℝ :=
  let period := max (chemicalPeriod z) 1
  let cap := (constructiveValleyCap : ℝ)
  2 * nestedWfCovalentRadiusBohr m z c * (1 + alpha) * metallicFccPackingFactor nCoord *
    (period ^ 2 / cap)

theorem metallicLatticeNearestNeighborTarget_pos
    (m z nCoord : ℕ) (c : ℝ) (hc : 0 ≤ c) (hz : 0 < z) :
    0 < metallicLatticeNearestNeighborTarget m z nCoord c := by
  unfold metallicLatticeNearestNeighborTarget
  have hr : 0 < nestedWfCovalentRadiusBohr m z c := nestedWfCovalentRadiusBohr_pos m z c hc hz
  have hpack : 0 < metallicFccPackingFactor nCoord := metallicFccPackingFactor_pos nCoord
  have hα : 0 < 1 + alpha := by rw [alpha_eq_3_5]; norm_num
  have hcap : 0 < (constructiveValleyCap : ℝ) := by
    rw [constructiveValleyCap_eq_six]; norm_num
  have hperiod : 0 < (max (chemicalPeriod z) 1 : ℝ) := by
    have h1 : (1 : ℕ) ≤ max (chemicalPeriod z) 1 := Nat.le_max_right _ _
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  positivity

/-- α-weighted metallic unification: ``nested^α · φ_pack^(1−α)`` (EM prefers nested). -/
noncomputable def metallicUnifiedNearestNeighborTarget
    (nnNested nnPhiPack : ℝ) : ℝ :=
  nnNested ^ alpha * nnPhiPack ^ (1 - alpha)

/-- Period channel for metallic φ branch: ``(2/P)^cap`` (period-2 → 1). -/
noncomputable def metallicPeriodChannelWeight (z : ℕ) : ℝ :=
  (2 / (max (chemicalPeriod z) 1 : ℝ)) ^ (constructiveValleyCap : ℝ)

/-- Close-pack metallic coordination reference (FCC CN=12). -/
def metallicClosePackCoord : ℕ := 12

/--
Under-coordination open dress:
``(12/CN)^{γ·(1−w)·(1−γ²·δ_BCC) + (γ²/2)·w·δ_BCC}`` (identity at CN=12 when w→1).

BCC residual ``(γ²/2)·w`` keeps period-2 alkalis from freezing the open to 1;
fade damp ``(1−γ²)`` keeps period-3 BCC from over-opening.
-/
noncomputable def metallicUndercoordOpenDress (nCoord : ℕ) (periodWeight : ℝ) : ℝ :=
  let bcc : ℝ := if nCoord = metallicClosePackCoord then 0 else 1
  let exp := gamma_HQIV * (1 - periodWeight) * (1 - gamma_HQIV * gamma_HQIV * bcc) +
    (gamma_HQIV * gamma_HQIV / 2) * periodWeight * bcc
  ((metallicClosePackCoord : ℝ) / (max nCoord 1 : ℝ)) ^ exp

theorem metallicUndercoordOpenDress_at_close_pack (periodWeight : ℝ) :
    metallicUndercoordOpenDress metallicClosePackCoord periodWeight = 1 := by
  unfold metallicUndercoordOpenDress metallicClosePackCoord
  simp [Real.one_rpow]

/--
P-block metallic valence open:
``1 + (4/8)·γ·((cap−1)/12)·(1−w)·(CN/12)`` for ``1 < cap < 4``.

Excess valence above the alkali monovalent floor opens the FCC contact.
Alkali (cap=1) and transition (cap=0) stay at identity.
-/
noncomputable def metallicPblockValenceOpenDress
    (cap nCoord : ℕ) (periodWeight : ℝ) : ℝ :=
  if 1 < cap ∧ cap < 4 then
    1 + strongChannelFraction * gamma_HQIV *
      (((cap : ℝ) - 1) / (metallicClosePackCoord : ℝ)) *
      (1 - periodWeight) *
      ((max nCoord 1 : ℝ) / (metallicClosePackCoord : ℝ))
  else
    1

/-- Coordination from bonding capacity: monovalent shed → BCC 8; else FCC 12. -/
def metallicCoordinationFromCapacity (cap valence : ℕ) : ℕ :=
  if cap = 1 ∧ valence = 1 then 8 else 12

/-- Metal predicate: shed metals ``1≤cap≤3 ∧ V=cap``, or peel metals ``cap=0``. -/
def isMetallicFromCapacity (cap valence : ℕ) : Bool :=
  if cap = 0 then true
  else if 1 ≤ cap ∧ cap ≤ 3 then decide (valence = cap)
  else false

theorem metallicCoordinationFromCapacity_alkali :
    metallicCoordinationFromCapacity 1 1 = 8 := rfl

theorem metallicCoordinationFromCapacity_pblock :
    metallicCoordinationFromCapacity 3 3 = 12 := rfl

theorem metallicCoordinationFromCapacity_transition :
    metallicCoordinationFromCapacity 0 11 = 12 := rfl

theorem isMetallicFromCapacity_alkali :
    isMetallicFromCapacity 1 1 = true := by native_decide

theorem isMetallicFromCapacity_fluorine :
    isMetallicFromCapacity 1 7 = false := by native_decide

theorem isMetallicFromCapacity_silicon :
    isMetallicFromCapacity 4 4 = false := by native_decide

theorem isMetallicFromCapacity_aluminum :
    isMetallicFromCapacity 3 3 = true := by native_decide

theorem isMetallicFromCapacity_copper :
    isMetallicFromCapacity 0 11 = true := by native_decide

theorem metallicPblockValenceOpenDress_alkali (nCoord : ℕ) (w : ℝ) :
    metallicPblockValenceOpenDress 1 nCoord w = 1 := by
  unfold metallicPblockValenceOpenDress
  simp

theorem metallicPblockValenceOpenDress_transition (nCoord : ℕ) (w : ℝ) :
    metallicPblockValenceOpenDress 0 nCoord w = 1 := by
  unfold metallicPblockValenceOpenDress
  simp

/-- Post-d d¹⁰ core elongation: ``1 + (4/8)·α·γ·(1−w)·max(osp−1, 0)``. -/
noncomputable def metallicD10CoreElongation
    (dPrev osp : ℕ) (periodWeight : ℝ) : ℝ :=
  if dPrev = 10 then
    1 + strongChannelFraction * alpha * gamma_HQIV *
      (1 - periodWeight) * max ((osp : ℝ) - 1) 0
  else
    1

/-- Continuous open-d fade: ``max(0, (10 − d)/10)`` for ``0 < d < 9``
(Fe/Ni partial; ``d=0`` main-group and Cu Madelung ``d≥9`` stay at identity). -/
noncomputable def metallicOpenDFade (dPrev : ℕ) : ℝ :=
  if 0 < dPrev ∧ dPrev < 9 then
    max 0 (((10 : ℝ) - (dPrev : ℝ)) / 10)
  else
    0

/-- Open-d peel contract: ``1 / (1 + (4/8)·α·γ·(peel/Z)·(1−w)·fade(d))``. -/
noncomputable def metallicOpenDPeelContract
    (dPrev : ℕ) (peelFrac periodWeight : ℝ) : ℝ :=
  let fade := metallicOpenDFade dPrev
  if fade = 0 then
    1
  else
    1 / (1 + strongChannelFraction * alpha * gamma_HQIV *
      peelFrac * (1 - periodWeight) * fade)

/-- Period-2 homo residual on the φ branch: ``1 + (4/8)·(γ²/8)·w``. -/
noncomputable def metallicPeriod2HomoResidual (periodWeight : ℝ) : ℝ :=
  1 + strongChannelFraction * (gamma_HQIV * gamma_HQIV / 8) * periodWeight

/-- Deep BCC open: ``1 + (4/8)·γ·max(0, P−3)/P`` at CN=8. -/
noncomputable def metallicDeepBccOpenDress (period nCoord : ℕ) : ℝ :=
  if nCoord = 8 then
    1 + strongChannelFraction * gamma_HQIV *
      (max 0 ((period : ℝ) - 3) / (max period 1 : ℝ))
  else
    1

/-- Alkaline-earth open (cap=2, no d¹⁰): ``1 + (4/8)·γ²·(1−w)/cap``. -/
noncomputable def metallicAlkalineEarthOpenDress
    (cap dPrev : ℕ) (periodWeight : ℝ) : ℝ :=
  if cap = 2 ∧ dPrev ≠ 10 then
    1 + strongChannelFraction * (gamma_HQIV * gamma_HQIV) *
      (1 - periodWeight) / (max cap 1 : ℝ)
  else
    1

/-- HCP candidate: divalent capacity without a filled d¹⁰ core (Mg-class). -/
def metallicIsHcpCandidate (cap dPrev : ℕ) : Bool :=
  decide (cap = 2 ∧ dPrev ≠ 10)

theorem metallicD10CoreElongation_open_d (osp : ℕ) (w : ℝ) :
    metallicD10CoreElongation 6 osp w = 1 := by
  unfold metallicD10CoreElongation; simp

theorem metallicOpenDFade_closed :
    metallicOpenDFade 10 = 0 := by
  unfold metallicOpenDFade; simp

theorem metallicOpenDFade_coinage :
    metallicOpenDFade 9 = 0 := by
  unfold metallicOpenDFade; simp

theorem metallicOpenDPeelContract_closed_d (peelFrac w : ℝ) :
    metallicOpenDPeelContract 10 peelFrac w = 1 := by
  unfold metallicOpenDPeelContract metallicOpenDFade; simp

theorem metallicDeepBccOpenDress_fcc (period : ℕ) :
    metallicDeepBccOpenDress period 12 = 1 := by
  unfold metallicDeepBccOpenDress; simp

theorem metallicAlkalineEarthOpenDress_d10 (w : ℝ) :
    metallicAlkalineEarthOpenDress 2 10 w = 1 := by
  unfold metallicAlkalineEarthOpenDress; simp

/-- BCC cell edge / nn: ``a = 2 r / √3``. -/
noncomputable def bccLatticeParameter (nn : ℝ) : ℝ :=
  2 * nn / Real.sqrt 3

/-- FCC cell edge / nn: ``a = √2 · r``. -/
noncomputable def fccLatticeParameter (nn : ℝ) : ℝ :=
  nn * Real.sqrt 2

/-- Atoms per conventional cell from coordination (CN=8 → BCC=2; else FCC=4). -/
def metallicAtomsPerCell (nCoord : ℕ) : ℕ :=
  if nCoord = 8 then 2 else 4

/-- Cell-edge / nn from coordination (CN=8 → BCC; else FCC). -/
noncomputable def metallicCellEdgeOverNn (nCoord : ℕ) : ℝ :=
  if nCoord = 8 then (2 / Real.sqrt 3) else Real.sqrt 2

/-- Ideal HCP atoms per hexagonal cell. -/
def metallicHcpAtomsPerCell : ℕ := 6

/-- Ideal HCP basal edge / nn (``a = r_nn``). -/
noncomputable def metallicHcpBasalEdgeOverNn : ℝ := 1

/-- Ideal HCP packing fraction equals FCC (same V/atom from nn). -/
theorem metallicHcp_packing_eq_fcc :
    (metallicHcpAtomsPerCell : ℝ) = 6 := rfl

theorem metallicAtomsPerCell_bcc :
    metallicAtomsPerCell 8 = 2 := rfl

theorem metallicAtomsPerCell_fcc :
    metallicAtomsPerCell 12 = 4 := rfl

theorem metallicIsHcpCandidate_mg :
    metallicIsHcpCandidate 2 0 = true := by
  unfold metallicIsHcpCandidate; simp

theorem metallicIsHcpCandidate_zn_d10 :
    metallicIsHcpCandidate 2 10 = false := by
  unfold metallicIsHcpCandidate; simp

/-- Default rocksalt coordination reference (``crystallineCoordinationReference .ionicLattice``). -/
theorem ionicLatticeCoordinationReference_eq_six :
    crystallineCoordinationReference .ionicLattice = 6 := rfl

/-- Default metallic coordination reference (``crystallineCoordinationReference .metallicLattice``). -/
theorem metallicLatticeCoordinationReference_eq_twelve :
    crystallineCoordinationReference .metallicLattice = 12 := rfl

/-- Period ≥ 3 homonuclear covalent-network inert-core participation (``Z / n_val``). -/
noncomputable def covalentNetworkInertCoreElongation (z : ℕ) : ℝ :=
  let nVal := max (period2ValenceElectronCount z) 1
  if z = 0 then 1
  else if max (chemicalPeriod z) 1 ≤ 2 then 1
  else (z : ℝ) / (nVal : ℝ)

/-- Covalent-network bond target = allotrope carrier length × inert-core elongation. -/
noncomputable def covalentNetworkBondLengthTarget (baseBondAng z : ℕ) : ℝ :=
  baseBondAng * covalentNetworkInertCoreElongation z

/-- Continuous period-channel weight ``(2/P)^{constructiveValleyCap}`` (no hard gate). -/
noncomputable def covalentNetworkPeriodChannelWeight (z : ℕ) : ℝ :=
  let period := max (chemicalPeriod z) 1
  (2 / (period : ℝ)) ^ (constructiveValleyCap : ℝ)

/-- Clausius–Mossotti optical participation ``(n²−1)/(n²+2)``. -/
noncomputable def clausiusMossottiOpticalWeight (nDielectric : ℝ) : ℝ :=
  let n2 := nDielectric ^ 2
  (n2 - 1) / (n2 + 2)

/--
Generic covalent-network EM/nuclear packing dress (Python
``covalent_network_em_packing_dress``):

`r = r_bare · pack^{(1−w)(2−CM)} · em^{α(w+(1−w)CM)} · open^(w²)
     / (1 + (4/8)·(γ²/8)·(1−w)·CM)`

with `w = covalentNetworkPeriodChannelWeight`, `CM = clausiusMossottiOpticalWeight`.
Open power is `w²` so period-2 keeps full open dress while deeper periods fade open
faster than the EM/nuclear blend (continuous; no hard gate).  Steric fade is
identity at period-2.
-/
noncomputable def covalentNetworkStericFadeDress
    (periodWeight cmWeight : ℝ) : ℝ :=
  1 / (1 + strongChannelFraction * (gamma_HQIV * gamma_HQIV / 8) *
    (1 - periodWeight) * cmWeight)

noncomputable def covalentNetworkEmPackingLength
    (rBare pack em openScale nDielectric : ℝ) (z : ℕ) : ℝ :=
  let w := covalentNetworkPeriodChannelWeight z
  let cm := clausiusMossottiOpticalWeight nDielectric
  let packPow := (1 - w) * (2 - cm)
  let emPow := alpha * (w + (1 - w) * cm)
  rBare * pack ^ packPow * em ^ emPow * openScale ^ (w * w) *
    covalentNetworkStericFadeDress w cm

/-- Diamond-cubic conventional cell edge ``a = 4 r / √3``. -/
noncomputable def diamondCubicLatticeParameterAng (bondAng : ℝ) : ℝ :=
  4 * bondAng / Real.sqrt 3

/-! ## Proton/neutron packing dress

Electronic nested-WF / allotrope lengths are keyed on nuclear charge ``Z``.
Nuclear volume tracks ``A^{1/3}``.  Relative to the saturated baseline ``A ≈ 2Z``
(α-pairing floor), neutron surplus ``A/(2Z)`` expands the nucleus; lattice nearest
neighbours contract as the trapped-inside packing fraction ``(2Z/A)^γ``
(monogamy complement — same ``γ`` as outer-horizon dressing).
-/

/-- Neutron surplus relative to the ``A = 2Z`` pairing floor. -/
noncomputable def neutronSurplusOverPairFloor (A Z : ℕ) : ℝ :=
  if Z = 0 then 1
  else (A : ℝ) / (2 * (Z : ℝ))

/-- Lattice nn dress ``(2Z/A)^γ`` (≤ 1 when ``A ≥ 2Z``). -/
noncomputable def nuclearPackingDress (A Z : ℕ) : ℝ :=
  if A = 0 ∨ Z = 0 then 1
  else (neutronSurplusOverPairFloor A Z) ^ (-gamma_HQIV)

/-- Partial monogamy reopen of P/N packing: ``1 + (4/8)·γ·(1 − pack)``. -/
noncomputable def nuclearPackingOpenDress (pack : ℝ) : ℝ :=
  1 + strongChannelFraction * gamma_HQIV * (1 - pack)

/-- Mild ionic-character nn contract: ``1 / (1 + (4/8)·γ·δ²)``. -/
noncomputable def ionicCharacterLatticeDress (ionicCharacter : ℝ) : ℝ :=
  1 / (1 + strongChannelFraction * gamma_HQIV / 8 * ionicCharacter)

/-- Period-channel steric nn contract: ``1 / (1 + (4/8)·α·γ/8 · w_a · w_c)``. -/
noncomputable def ionicPeriodChannelStericDress
    (periodCation periodAnion : ℕ) : ℝ :=
  let wA := (2 / (max periodAnion 1 : ℝ)) ^ (constructiveValleyCap : ℝ)
  let wC := (2 / (max periodCation 1 : ℝ)) ^ (constructiveValleyCap : ℝ)
  1 / (1 + strongChannelFraction * alpha * gamma_HQIV / 8 * wA * wC)

/-- Deep-cation nn open: ``1 + (4/8)·(γ/8)·max(0,P_c/P_a−1)·(1−w_a)``. -/
noncomputable def ionicDeepCationOpenDress
    (periodCation periodAnion : ℕ) : ℝ :=
  let wA := (2 / (max periodAnion 1 : ℝ)) ^ (constructiveValleyCap : ℝ)
  let excess := max 0 ((periodCation : ℝ) / (max periodAnion 1 : ℝ) - 1)
  1 + strongChannelFraction * (gamma_HQIV / 8) * excess * (1 - wA)

theorem nuclearPackingOpenDress_at_floor :
    nuclearPackingOpenDress 1 = 1 := by
  unfold nuclearPackingOpenDress; ring

theorem ionicCharacterLatticeDress_zero :
    ionicCharacterLatticeDress 0 = 1 := by
  unfold ionicCharacterLatticeDress; ring

theorem covalentNetworkStericFadeDress_period_two (cm : ℝ) :
    covalentNetworkStericFadeDress 1 cm = 1 := by
  unfold covalentNetworkStericFadeDress; ring

theorem ionicDeepCationOpenDress_same_period :
    ionicDeepCationOpenDress 3 3 = 1 := by
  unfold ionicDeepCationOpenDress
  simp

/-- Crystal nn dressed by Coulomb ``A(Z)`` packing × open dress (P/N bridge). -/
noncomputable def metallicLatticeNearestNeighborPacked
    (m z nCoord : ℕ) (c : ℝ := 1) : ℝ :=
  let pack := nuclearPackingDress (stableMassNumberForCharge z) z
  metallicLatticeNearestNeighborTarget m z nCoord c * pack *
    nuclearPackingOpenDress pack

noncomputable def ionicLatticeNearestNeighborPacked
    (m_i z_i m_j z_j nCoord : ℕ) (c : ℝ := 1) (ionicCharacter : ℝ := 0)
    (periodCation periodAnion : ℕ := 2) : ℝ :=
  let A_i := stableMassNumberForCharge z_i
  let A_j := stableMassNumberForCharge z_j
  let pack := Real.sqrt (
      nuclearPackingDress A_i z_i * nuclearPackingDress A_j z_j)
  ionicLatticeNearestNeighborTarget m_i z_i m_j z_j nCoord c * pack *
    nuclearPackingOpenDress pack * ionicCharacterLatticeDress ionicCharacter *
    ionicPeriodChannelStericDress periodCation periodAnion *
    ionicDeepCationOpenDress periodCation periodAnion

/-- Optional diagnostic: covalent length × packing dress (Python default leaves this off). -/
noncomputable def covalentNetworkBondLengthPacked (baseBondAng z : ℕ) : ℝ :=
  covalentNetworkBondLengthTarget baseBondAng z *
    nuclearPackingDress (stableMassNumberForCharge z) z

end

end Hqiv.QuantumChemistry
