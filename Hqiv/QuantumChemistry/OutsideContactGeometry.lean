import Hqiv.QuantumChemistry.CentreGeometryFromTuft
import Hqiv.QuantumChemistry.CurvatureBondContact
import Hqiv.QuantumChemistry.AtomElectronicDischarge
import Hqiv.Geometry.HQVMetric
import Mathlib.Tactic

/-!
# Outside-contact geometry targets for ionic and period-3 bonds

Upstream bond-length candidates for chemistry readouts where the covalent nested-WF
route alone is sub-physical (NaCl, Cl₂).  These are **geometry candidates** only:
spectroscopy constants still require a separate reliability gate.

Python mirror: ``scripts/hqiv_chemistry_tuft_dynamics.py`` (`ionic_outside_contact_*`,
`period3_halogen_open_channel_*`).

No comparison Å inputs; no new axioms; no `sorry`.
-/

namespace Hqiv.QuantumChemistry

open Hqiv
open Hqiv.Physics
open Real

noncomputable section

/-- Informational monogamy length factor ``1 − α/2 = 7/10``. -/
noncomputable def informationalMonogamyLengthFactor : ℝ := 1 - alpha / 2

theorem informationalMonogamyLengthFactor_eq_seven_tenths :
    informationalMonogamyLengthFactor = 7 / 10 := by
  unfold informationalMonogamyLengthFactor
  rw [alpha_eq_3_5]
  norm_num

/-- Nested-WF covalent radius in Bohr ladder units: ``R_m m / z``. -/
noncomputable def nestedWfCovalentRadiusBohr (m z : ℕ) (c : ℝ := 1) : ℝ :=
  dynamicContactRadiusDimless m z c * alphaEffAtShell m c

theorem nestedWfCovalentRadiusBohr_pos (m z : ℕ) (c : ℝ) (hc : 0 ≤ c) (hz : 0 < z) :
    0 < nestedWfCovalentRadiusBohr m z c := by
  unfold nestedWfCovalentRadiusBohr
  exact mul_pos (dynamicContactRadiusDimless_pos m z c hc hz) (alphaEffAtShell_pos m c hc)

/-- Charge-asymmetry slot for ionic outside contacts: ``|Z_i − Z_j| / (Z_i + Z_j)``. -/
noncomputable def ionicChargeAsymmetry (z_i z_j : ℕ) : ℝ :=
  if z_i + z_j = 0 then 0
  else |((z_i : ℝ) - (z_j : ℝ))| / ((z_i + z_j : ℝ))

theorem ionicChargeAsymmetry_nonneg (z_i z_j : ℕ) :
    0 ≤ ionicChargeAsymmetry z_i z_j := by
  unfold ionicChargeAsymmetry
  split_ifs with h
  · norm_num
  · positivity

/-- Period-3-or-heavier route predicate for outside curvature geometry. -/
def period3OrHeavier (z : ℕ) : Prop := 3 ≤ chemicalPeriod z

/-- Period-3-or-heavier participation weight: ``0`` below period 3, ``1`` at/above. -/
noncomputable def periodParticipation (z : ℕ) : ℝ :=
  if 3 ≤ chemicalPeriod z then 1 else 0

/-- Continuous ionic outside-contact route weight (period participation × charge asymmetry). -/
noncomputable def ionicOutsideRouteWeight (z_i z_j : ℕ) : ℝ :=
  periodParticipation z_i * periodParticipation z_j *
    (if z_i ≠ z_j then (1 : ℝ) else 0)

/-- Continuous halogen open-channel route weight (homonuclear period-3 halogenicity). -/
noncomputable def halogenOpenChannelRouteWeight (z_i z_j : ℕ) : ℝ :=
  if z_i = z_j ∧ chemicalPeriod z_i = 3 ∧ z_i = 17 then 1 else 0

/-- Ionic outside-contact route: unequal period ≥ 3 partners use the ionic outside layer.
Legacy Prop form of ``ionicOutsideRouteWeight > 0``. -/
def period3IonicOutsideRoute (z_i z_j : ℕ) : Prop :=
  period3OrHeavier z_i ∧ period3OrHeavier z_j ∧ z_i ≠ z_j

/-- Homonuclear period-3 halogen route: equal period-3 chlorine partners.
Legacy Prop form of ``halogenOpenChannelRouteWeight > 0``. -/
def period3HalogenOpenChannelRoute (z_i z_j : ℕ) : Prop :=
  z_i = z_j ∧ chemicalPeriod z_i = 3 ∧ z_i = 17

/-- NaCl is classified by the period-3 ionic outside-contact route. -/
theorem nacl_period3_ionic_outside_route :
    period3IonicOutsideRoute 11 17 := by
  unfold period3IonicOutsideRoute period3OrHeavier chemicalPeriod
  norm_num

/-- Cl₂ is classified by the period-3 halogen open-channel route. -/
theorem cl2_period3_halogen_open_channel_route :
    period3HalogenOpenChannelRoute 17 17 := by
  unfold period3HalogenOpenChannelRoute chemicalPeriod
  norm_num

/-- Outside-contact elongation from charge asymmetry and ``G_eff`` participation. -/
noncomputable def ionicOutsideContactDress (z_i z_j : ℕ) : ℝ :=
  1 + ionicChargeAsymmetry z_i z_j * strongChannelFraction * gamma_HQIV

theorem ionicOutsideContactDress_ge_one {z_i z_j : ℕ}
    (_h : 0 < z_i + z_j) :
    1 ≤ ionicOutsideContactDress z_i z_j := by
  unfold ionicOutsideContactDress
  have hγ : 0 ≤ gamma_HQIV := by rw [gamma_eq_2_5]; norm_num
  have hs : 0 ≤ strongChannelFraction := by unfold strongChannelFraction; norm_num
  have hasy : 0 ≤ ionicChargeAsymmetry z_i z_j := ionicChargeAsymmetry_nonneg z_i z_j
  nlinarith [mul_nonneg hasy hs, mul_nonneg (mul_nonneg hasy hs) hγ]

/-- Period ≥ 3 inert-core lattice contact weight (structural; no tabulated Å). -/
noncomputable def period3InertCoreLatticeDress : ℝ :=
  Real.sqrt (1 + strongChannelFraction)

theorem period3InertCoreLatticeDress_ge_one :
    1 ≤ period3InertCoreLatticeDress := by
  unfold period3InertCoreLatticeDress
  rw [one_le_sqrt]
  unfold strongChannelFraction
  norm_num

/-- Period ≥ 3 inert-core valence/participation elongation (no tabulated Å).

Uses outer-shell ``valenceElectronCount`` (noble-gas core stripped), not the
period-2 steric proxy ``period2ValenceElectronCount``.  For NaCl this is
``(11+17)/(1+7) = 28/8 = 7/2``. -/
noncomputable def ionicInertCoreLengthElongation (z_i z_j : ℕ) : ℝ :=
  let nVal := max (valenceElectronCount z_i + valenceElectronCount z_j) 1
  let nTot := z_i + z_j
  if nTot = 0 then 1
  else if max (chemicalPeriod z_i) (chemicalPeriod z_j) ≤ 2 then 1
  else (nTot : ℝ) / (nVal : ℝ)

/-- Period-3 NaCl inert-core elongation is \(28/8 = 7/2\). -/
theorem ionicInertCoreLengthElongation_nacl :
    ionicInertCoreLengthElongation 11 17 = 7 / 2 := by
  unfold ionicInertCoreLengthElongation chemicalPeriod valenceElectronCount
  norm_num

/-- Therefore the NaCl period-3 outside-contact route strictly elongates the core layer. -/
theorem ionicInertCoreLengthElongation_nacl_gt_one :
    1 < ionicInertCoreLengthElongation 11 17 := by
  rw [ionicInertCoreLengthElongation_nacl]
  norm_num

/-- Ionic outside-contact length target: sum of nested-WF radii × monogamy × outside dress.

This is the **shared** gas/crystal contact core.  Crystal nn multiplies by
``ionicRocksaltLatticeDress``; gas-phase diatomic spectroscopy multiplies by
``ionicGasPhaseEmDress`` (``1+α``). -/
noncomputable def ionicOutsideContactLengthTarget
    (m_i z_i m_j z_j : ℕ) (c : ℝ := 1) : ℝ :=
  (nestedWfCovalentRadiusBohr m_i z_i c + nestedWfCovalentRadiusBohr m_j z_j c) *
    informationalMonogamyLengthFactor *
    ionicOutsideContactDress z_i z_j *
    period3InertCoreLatticeDress *
    ionicInertCoreLengthElongation z_i z_j

/-- Gas-phase EM open dress on ionic outside contacts: ``1 + α = 8/5``.

Same monogamy/EM slot used elsewhere for gas-scale elongation; recovers the
crystal core when composed as ``r_gas = r_outside · (1+α)`` and
``r_lattice = r_outside · ionicRocksaltLatticeDress CN``. -/
noncomputable def ionicGasPhaseEmDress : ℝ := 1 + alpha

theorem ionicGasPhaseEmDress_eq_eight_fifths :
    ionicGasPhaseEmDress = 8 / 5 := by
  unfold ionicGasPhaseEmDress
  rw [alpha_eq_3_5]
  norm_num

theorem ionicGasPhaseEmDress_gt_one : 1 < ionicGasPhaseEmDress := by
  rw [ionicGasPhaseEmDress_eq_eight_fifths]
  norm_num

/-- Gas-phase ionic outside-contact length: core outside target × ``(1+α)``. -/
noncomputable def ionicGasOutsideContactLengthTarget
    (m_i z_i m_j z_j : ℕ) (c : ℝ := 1) : ℝ :=
  ionicOutsideContactLengthTarget m_i z_i m_j z_j c * ionicGasPhaseEmDress

/-- Both partners period ≥ 3 (Lean route predicate used by the period-3/n suite). -/
theorem period3IonicOutsideRoute_of_periods
    {z_i z_j : ℕ}
    (hi : 3 ≤ chemicalPeriod z_i) (hj : 3 ≤ chemicalPeriod z_j) (hne : z_i ≠ z_j) :
    period3IonicOutsideRoute z_i z_j :=
  ⟨hi, hj, hne⟩

/-- Period-3 homonuclear halogen open-channel elongation (same carrier law as period-2). -/
noncomputable def period3HalogenOpenChannelFactor (openChannels : ℕ) : ℝ :=
  (1 + strongChannelFraction / 2) ^ openChannels

theorem period3HalogenOpenChannelFactor_one :
    period3HalogenOpenChannelFactor 1 = 1 + strongChannelFraction / 2 := by
  unfold period3HalogenOpenChannelFactor
  rw [pow_one]

/-- One open halogen channel evaluates to \(5/4\) from the strong \(4/8\) channel. -/
theorem period3HalogenOpenChannelFactor_one_eq_five_fourths :
    period3HalogenOpenChannelFactor 1 = 5 / 4 := by
  rw [period3HalogenOpenChannelFactor_one, strongChannelFraction_eq_four_eighths]
  norm_num

theorem period3HalogenOpenChannelFactor_pos (openChannels : ℕ) :
    0 < period3HalogenOpenChannelFactor openChannels := by
  unfold period3HalogenOpenChannelFactor
  have hbase : 0 < 1 + strongChannelFraction / 2 := by
    unfold strongChannelFraction; norm_num
  exact pow_pos hbase openChannels

/-- Homonuclear halogen dimer length from carrier contact × open-channel elongation. -/
noncomputable def period3HalogenBondLengthTarget (m z openChannels : ℕ) (c : ℝ := 1) : ℝ :=
  (2 * nestedWfCovalentRadiusBohr m z c / informationalMonogamyLengthFactor) *
    period3HalogenOpenChannelFactor openChannels

theorem period3HalogenBondLengthTarget_pos
    (m z openChannels : ℕ) (c : ℝ) (hc : 0 ≤ c) (hz : 0 < z) :
    0 < period3HalogenBondLengthTarget m z openChannels c := by
  unfold period3HalogenBondLengthTarget
  have hr : 0 < nestedWfCovalentRadiusBohr m z c := nestedWfCovalentRadiusBohr_pos m z c hc hz
  have hmono : 0 < informationalMonogamyLengthFactor := by
    rw [informationalMonogamyLengthFactor_eq_seven_tenths]
    norm_num
  have hf : 0 < period3HalogenOpenChannelFactor openChannels :=
    period3HalogenOpenChannelFactor_pos openChannels
  have hquot :
      0 < 2 * nestedWfCovalentRadiusBohr m z c / informationalMonogamyLengthFactor :=
    div_pos (by nlinarith) hmono
  exact mul_pos hquot hf

end

end Hqiv.QuantumChemistry
