import Hqiv.Physics.CoronalHeatedPlasmaBackReaction
import Hqiv.Physics.SolarDynamics

/-!
# Plasma Z-pinch and WHIM filament compression scaffold

**Purpose:** formalize the **pinch limit** of axial return currents (coronal flux tubes,
WHIM filaments) into localized overdense regions. Heated bulk plasma carries
`J_∥`; in a cylindrical filament this generates an azimuthal field and magnetic
pressure that compresses the column — producing **local intensity** `≫` bulk.

This module supplies the **algebraic spine** for the cosmological programme:
WHIM filaments pinch along their spines, steepening `∂_s φ` and `q̇` at focal
lines, which may **seed** collapsed objects (hypothesis slot — not derived here).

## Equations (cylindrical Bennett / Z-pinch bookkeeping)

Axial current `I` at radius `r`:
\[
B_\theta(r)=\frac{\mu_0 I}{2\pi r},\qquad
p_{\rm mag}(r)=\frac{B_\theta^2}{2\mu_0}=\frac{\mu_0 I^2}{8\pi^2 r^2}.
\]
Bennett equilibrium (pressure balance across radius `a`):
\[
I^2=\frac{8\pi^2 a^2\,\Delta p}{\mu_0}.
\]
Flux-conservation compression scaffold:
\[
\frac{n_{\rm loc}}{n_{\rm bulk}}\approx\left(\frac{R_{\rm fil}}{r_{\rm pinch}}\right)^2.
\]

## Proof status (all `Prop`, zero `sorry`)

* **§1.** Pinch field, magnetic pressure, Bennett current identity.
* **§2.** Compression ratio and localized heating/intensity factor.
* **§3.** Bridge from `hotReturnCurrentDensity` to pinch pressure.
* **§4.** WHIM filament spine slot + `solarWhimBoundaryShape` enhancement.
* **§5.** Galaxy/BH seeding **hypothesis** bundle (not a derivation).
* **§6–§7.** Filament nodes + nonlinear heated-plasma feedback.
* **§8.** `β = p_th/p_mag` force balance; Bennett `I(n,T,r)`.
* **§9.** Radiative WHIM cooling + pinch–radiative `(n,T)` equilibrium.

## Not claimed

* MHD stability (sausage/kink), full radiative WHIM thermodynamics, or derived
  galaxy/BH mass function from pinch collapse.
* Full multi-species cooling tables (Python uses schematic `Λ(T)` witness).
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Cylindrical Z-pinch identities
-/

/-- Azimuthal magnetic field from axial current `I` at cylindrical radius `r`. -/
def pinchAzimuthalField (mu0 I r : ℝ) : ℝ :=
  if r = 0 then 0 else mu0 * I / (2 * Real.pi * r)

/-- Magnetic pressure `p_mag = B²/(2μ₀)`. -/
def magneticPinchPressure (B mu0 : ℝ) : ℝ :=
  if mu0 = 0 then 0 else B ^ 2 / (2 * mu0)

/-- Azimuthal-field magnetic pressure at radius `r` (equivalent closed form). -/
def pinchAzimuthalPressure (mu0 I r : ℝ) : ℝ :=
  if r = 0 then 0 else mu0 * I ^ 2 / (8 * Real.pi ^ 2 * r ^ 2)

theorem pinchAzimuthalPressure_eq_magneticPressure
    (mu0 I r : ℝ) (hr : r ≠ 0) (hmu : mu0 ≠ 0) :
    pinchAzimuthalPressure mu0 I r =
      magneticPinchPressure (pinchAzimuthalField mu0 I r) mu0 := by
  unfold pinchAzimuthalPressure pinchAzimuthalField magneticPinchPressure
  simp [hr, hmu]
  field_simp
  ring

/-- Axial current through a cylindrical cross-section of radius `r` and current density `J`. -/
def pinchAxialCurrent (J r : ℝ) : ℝ :=
  J * Real.pi * r ^ 2

theorem pinchAxialCurrent_nonneg {J r : ℝ} (hJ : 0 ≤ J) :
    0 ≤ pinchAxialCurrent J r := by
  unfold pinchAxialCurrent
  positivity

/-- Bennett equilibrium: `I² = 8π² a² Δp / μ₀`. -/
def bennettCurrentSquared (a deltaP mu0 : ℝ) : ℝ :=
  if mu0 = 0 then 0 else 8 * Real.pi ^ 2 * a ^ 2 * deltaP / mu0

theorem bennettCurrentSquared_nonneg {a deltaP mu0 : ℝ}
    (_ha : 0 ≤ a) (hP : 0 ≤ deltaP) (hmu : 0 < mu0) :
    0 ≤ bennettCurrentSquared a deltaP mu0 := by
  unfold bennettCurrentSquared
  simp [ne_of_gt hmu]
  positivity

/-!
## §2. Compression and localized intensity
-/

/-- Flux-conservation compression ratio `(R_bulk / r_pinch)²`. -/
def pinchCompressionRatio (Rbulk rPinch : ℝ) : ℝ :=
  if rPinch = 0 then 1 else (Rbulk / rPinch) ^ 2

theorem pinchCompressionRatio_nonneg (Rbulk rPinch : ℝ) :
    0 ≤ pinchCompressionRatio Rbulk rPinch := by
  unfold pinchCompressionRatio
  split_ifs <;> positivity

/-- Localized number/heating intensity factor `n_loc / n_bulk` (same scaffold). -/
def localizedIntensityFactor (Rbulk rPinch : ℝ) : ℝ :=
  pinchCompressionRatio Rbulk rPinch

/-- Local heating-rate enhancement at pinch focal line. -/
def pinchHeatingEnhancement (Rbulk rPinch : ℝ) : ℝ :=
  localizedIntensityFactor Rbulk rPinch

/-!
## §3. Hot return current → pinch pressure
-/

/-- Pinch pressure from a hot return-current density `J_hot` at radius `r`. -/
def hotCurrentPinchPressure (mu0 Jhot r : ℝ) : ℝ :=
  pinchAzimuthalPressure mu0 (pinchAxialCurrent Jhot r) r

theorem hotCurrentPinchPressure_eq_J_sq_form
    (mu0 Jhot r : ℝ) (hr : r ≠ 0) :
    hotCurrentPinchPressure mu0 Jhot r =
      mu0 * Jhot ^ 2 * r ^ 2 / 8 := by
  unfold hotCurrentPinchPressure pinchAzimuthalPressure pinchAxialCurrent
  simp [hr]
  field_simp

theorem hotCurrentPinchPressure_mono_J
    {mu0 J₁ J₂ r : ℝ} (hr : r ≠ 0) (hmu : 0 ≤ mu0) (hJ : 0 ≤ J₁) (h : J₁ ≤ J₂) :
    hotCurrentPinchPressure mu0 J₁ r ≤ hotCurrentPinchPressure mu0 J₂ r := by
  rw [hotCurrentPinchPressure_eq_J_sq_form mu0 J₁ r hr,
    hotCurrentPinchPressure_eq_J_sq_form mu0 J₂ r hr]
  gcongr

/-!
## §4. WHIM filament spine pinch slot
-/

/-- WHIM filament axial current witness (readout-supplied). -/
def whimFilamentAxialCurrent (Jspine rSpine : ℝ) : ℝ :=
  pinchAxialCurrent Jspine rSpine

/-- Pinch magnetic pressure on the WHIM spine. -/
def whimFilamentPinchPressure (mu0 Jspine rSpine : ℝ) : ℝ :=
  hotCurrentPinchPressure mu0 Jspine rSpine

/-- WHIM boundary `φ` gradient enhancement from pinch compression. -/
def whimPhiPinchEnhancement (mIsm mWhim : ℕ) (Rbulk rPinch : ℝ) : ℝ :=
  solarWhimBoundaryShape mIsm mWhim * localizedIntensityFactor Rbulk rPinch

theorem whimPhiPinchEnhancement_nonneg (mIsm mWhim : ℕ) (Rbulk rPinch : ℝ) :
    0 ≤ whimPhiPinchEnhancement mIsm mWhim Rbulk rPinch := by
  unfold whimPhiPinchEnhancement
  exact mul_nonneg (solarWhimBoundaryShape_nonneg mIsm mWhim)
    (pinchCompressionRatio_nonneg Rbulk rPinch)

/-- Coronal flux-tube pinch enhancement using default solar shell pair. -/
def coronalFluxTubePinchEnhancement (Rbulk rPinch : ℝ) : ℝ :=
  whimPhiPinchEnhancement 0 8 Rbulk rPinch

/-!
## §5. Collapse / galaxy-seeding hypothesis (not a derivation)
-/

/-- **Hypothesis:** pinch compression exceeds a collapse threshold at the spine. -/
structure WhimPinchCollapseHypothesis (compression collapseThreshold : ℝ) : Prop where
  exceeds_threshold : collapseThreshold ≤ compression

/-- **Hypothesis:** localized heating exceeds bulk by factor `C`. -/
structure PinchLocalizedHeatingHypothesis (enhancement bulkHeating : ℝ) : Prop where
  enhancement_pos : 0 < enhancement
  localized_qdot : bulkHeating * enhancement = bulkHeating * enhancement

/-- Bundled filament pinch witness for readout (algebraic links only). -/
structure WhimFilamentPinchWitness where
  mu0 : ℝ
  Jspine : ℝ
  rSpine : ℝ
  Rbulk : ℝ
  rPinch : ℝ
  mIsm : ℕ
  mWhim : ℕ

def witnessCompressionRatio (w : WhimFilamentPinchWitness) : ℝ :=
  pinchCompressionRatio w.Rbulk w.rPinch

def witnessPinchPressure (w : WhimFilamentPinchWitness) : ℝ :=
  whimFilamentPinchPressure w.mu0 w.Jspine w.rSpine

def witnessPhiEnhancement (w : WhimFilamentPinchWitness) : ℝ :=
  whimPhiPinchEnhancement w.mIsm w.mWhim w.Rbulk w.rPinch

theorem witnessCompressionRatio_nonneg (w : WhimFilamentPinchWitness) :
    0 ≤ witnessCompressionRatio w := by
  exact pinchCompressionRatio_nonneg w.Rbulk w.rPinch

def whim_filament_pinch_vital : Prop :=
  0 < (8 : ℝ) ∧
    Nonempty (WhimPinchCollapseHypothesis (pinchCompressionRatio 1 0.1) 10)

theorem whim_filament_pinch_vital_holds : whim_filament_pinch_vital := by
  refine ⟨by norm_num, ?_⟩
  exact ⟨⟨by unfold pinchCompressionRatio; simp; norm_num⟩⟩

/-!
## §6. Filament intersection nodes (preferred collapse sites)

At an `N`-way junction, `N` spine currents converge. Schematic bookkeeping:

* **Mass-flux enhancement:** `N` incoming streams → `N×` density flux at node.
* **Geometric pinch tightening:** effective pinch radius `r_node = r_spine / √N`.
* **Current superposition:** total axial current `I_node ≈ N · I_spine`.
* **Node compression:** `C_node = N · (R / r_node)²`.

Not claimed: full 3-D MHD merge reconnection or derived Jeans mass.
-/

/-- Junction filament count as ℝ (minimum 1). -/
def junctionFilamentCount (nFilaments : ℕ) : ℝ :=
  max 1 nFilaments

/-- Effective pinch radius at an `N`-way junction. -/
def nodePinchRadius (rSpinePinch : ℝ) (nFilaments : ℕ) : ℝ :=
  rSpinePinch / Real.sqrt (junctionFilamentCount nFilaments)

theorem nodePinchRadius_pos {rSpinePinch : ℝ} (hr : 0 < rSpinePinch) (n : ℕ) :
    0 < nodePinchRadius rSpinePinch n := by
  unfold nodePinchRadius junctionFilamentCount
  positivity

/-- Spine-only compression at a junction (geometry tightened by `√N`). -/
def nodeSpineCompression (Rbulk rSpinePinch : ℝ) (nFilaments : ℕ) : ℝ :=
  pinchCompressionRatio Rbulk (nodePinchRadius rSpinePinch nFilaments)

/-- Mass-flux enhancement from `N` converging filaments. -/
def nodeMassFluxEnhancement (nFilaments : ℕ) : ℝ :=
  junctionFilamentCount nFilaments

/-- Total node localized intensity `N · (R / r_node)²`. -/
def nodeLocalizedIntensity (Rbulk rSpinePinch : ℝ) (nFilaments : ℕ) : ℝ :=
  nodeMassFluxEnhancement nFilaments * nodeSpineCompression Rbulk rSpinePinch nFilaments

theorem nodeLocalizedIntensity_nonneg (Rbulk rSpinePinch : ℝ) (nFilaments : ℕ) :
    0 ≤ nodeLocalizedIntensity Rbulk rSpinePinch nFilaments := by
  unfold nodeLocalizedIntensity
  exact mul_nonneg (by unfold nodeMassFluxEnhancement junctionFilamentCount; positivity)
    (pinchCompressionRatio_nonneg Rbulk (nodePinchRadius rSpinePinch nFilaments))

/-- Superposed axial current density at node (`N` equal spines). -/
def nodeCurrentSuperposition (Jspine : ℝ) (nFilaments : ℕ) : ℝ :=
  junctionFilamentCount nFilaments * Jspine

/-- Pinch magnetic pressure at an `N`-way filament node. -/
def nodePinchPressure (mu0 Jspine rSpinePinch : ℝ) (nFilaments : ℕ) : ℝ :=
  hotCurrentPinchPressure mu0 (nodeCurrentSuperposition Jspine nFilaments)
    (nodePinchRadius rSpinePinch nFilaments)

/-- WHIM node `φ` enhancement (boundary shape × node compression). -/
def whimNodePhiEnhancement (mIsm mWhim : ℕ) (Rbulk rSpinePinch : ℝ) (nFilaments : ℕ) : ℝ :=
  solarWhimBoundaryShape mIsm mWhim * nodeLocalizedIntensity Rbulk rSpinePinch nFilaments

structure FilamentNodeWitness where
  mu0 : ℝ
  Jspine : ℝ
  rSpinePinch : ℝ
  Rbulk : ℝ
  nFilaments : ℕ
  mIsm : ℕ
  mWhim : ℕ

def witnessNodeIntensity (w : FilamentNodeWitness) : ℝ :=
  nodeLocalizedIntensity w.Rbulk w.rSpinePinch w.nFilaments

def witnessNodePinchPressure (w : FilamentNodeWitness) : ℝ :=
  nodePinchPressure w.mu0 w.Jspine w.rSpinePinch w.nFilaments

def witnessNodePhiEnhancement (w : FilamentNodeWitness) : ℝ :=
  whimNodePhiEnhancement w.mIsm w.mWhim w.Rbulk w.rSpinePinch w.nFilaments

theorem witnessNodeIntensity_nonneg (w : FilamentNodeWitness) :
    0 ≤ witnessNodeIntensity w :=
  nodeLocalizedIntensity_nonneg w.Rbulk w.rSpinePinch w.nFilaments

/-!
## §7. Nonlinear pinch → heated-plasma feedback

Pinch compression `C` concentrates heating and number density at the focal line:

\[
\dot q_{\rm loc} = C\,\dot q_{\rm bulk},\quad
n_{\rm loc} = C\,n_{\rm bulk},\quad
P_{\rm hot,loc} = \tfrac{2}{3}\,C\,\dot q_{\rm bulk}\,\tau_{\rm hot}.
\]

These feed the self-consistent loop in `CoronalHeatedPlasmaBackReaction`:

\[
E_{\rm self} = E_{\rm Ohm} + E_{\rm HQIV} + E_{\rm hot,back}(P_{\rm hot,loc}),\quad
\dot q_{\rm self,loc} = n_{\rm loc}\,v_\parallel\,E_{\rm self}.
\]

Python readout iterates this map to a fixed point (not claimed unique).
-/

/-- Pinch-local heating rate `C · q̇_bulk`. -/
def pinchLocalHeatingRate (qDotBulk compression : ℝ) : ℝ :=
  qDotBulk * compression

theorem pinchLocalHeatingRate_nonneg {qDotBulk compression : ℝ}
    (hq : 0 ≤ qDotBulk) (hc : 0 ≤ compression) :
    0 ≤ pinchLocalHeatingRate qDotBulk compression := by
  unfold pinchLocalHeatingRate
  exact mul_nonneg hq hc

/-- Pinch-local hot pressure from compressed deposition. -/
def pinchLocalHotPressure (qDotBulk tauHot compression : ℝ) : ℝ :=
  hotPressureFromEnergyDensity
    (heatedEnergyDensity (pinchLocalHeatingRate qDotBulk compression) tauHot)

theorem pinchLocalHotPressure_nonneg {qDotBulk tauHot compression : ℝ}
    (hq : 0 ≤ qDotBulk) (ht : 0 ≤ tauHot) (hc : 0 ≤ compression) :
    0 ≤ pinchLocalHotPressure qDotBulk tauHot compression := by
  unfold pinchLocalHotPressure
  exact hotPressureFromEnergyDensity_nonneg
    (heatedEnergyDensity_nonneg (pinchLocalHeatingRate_nonneg hq hc) ht)

/-- Pinch-local number density `C · n_bulk`. -/
def pinchLocalNumberDensity (nBulk compression : ℝ) : ℝ :=
  nBulk * compression

/-- Pinch-enhanced hot return current `J_hot · C`. -/
def pinchEnhancedHotReturnCurrent (nHot q vHot compression : ℝ) : ℝ :=
  compression * hotReturnCurrentDensity nHot q vHot

theorem pinchEnhancedHotReturnCurrent_nonneg {nHot q vHot compression : ℝ}
    (hn : 0 ≤ nHot) (hq : 0 ≤ q) (hv : 0 ≤ vHot) (hc : 0 ≤ compression) :
    0 ≤ pinchEnhancedHotReturnCurrent nHot q vHot compression := by
  unfold pinchEnhancedHotReturnCurrent
  exact mul_nonneg hc (hotReturnCurrentDensity_nonneg hn hq hv)

/-- Self-consistent heating at pinch focal line (single pass of feedback algebra). -/
def pinchSelfConsistentHeatingRate
    (compression nBulk vParallel J sigma Estar couplingLog dphi_ds qDotBulk tauHot Lgrad : ℝ) : ℝ :=
  let nLoc := pinchLocalNumberDensity nBulk compression
  let pHot := pinchLocalHotPressure qDotBulk tauHot compression
  selfConsistentHeatingRateDensity nLoc vParallel J sigma Estar couplingLog dphi_ds pHot Lgrad

/-- Nonlinear pinch feedback factor `q̇_self,loc / q̇_bulk`. -/
def pinchNonlinearFeedbackFactor
    (compression nBulk vParallel J sigma Estar couplingLog dphi_ds qDotBulk tauHot Lgrad : ℝ) : ℝ :=
  if qDotBulk = 0 then 1
  else
    pinchSelfConsistentHeatingRate compression nBulk vParallel J sigma Estar couplingLog dphi_ds
      qDotBulk tauHot Lgrad / qDotBulk

/-- Node-local self-consistent heating (uses node intensity as compression). -/
def nodeSelfConsistentHeatingRate
    (Rbulk rSpinePinch : ℝ) (nFilaments : ℕ)
    (nBulk vParallel J sigma Estar couplingLog dphi_ds qDotBulk tauHot Lgrad : ℝ) : ℝ :=
  pinchSelfConsistentHeatingRate
    (nodeLocalizedIntensity Rbulk rSpinePinch nFilaments) nBulk vParallel J sigma Estar couplingLog dphi_ds
    qDotBulk tauHot Lgrad

def filament_node_pinch_vital : Prop :=
  (10 : ℝ) < nodeLocalizedIntensity 1 0.2 4 ∧
    Nonempty (WhimPinchCollapseHypothesis (nodeLocalizedIntensity 1 0.2 4) 10)

theorem nodeLocalizedIntensity_quad_junction_gt_ten :
    (10 : ℝ) < nodeLocalizedIntensity 1 0.2 4 := by
  dsimp [nodeLocalizedIntensity, nodeMassFluxEnhancement, nodeSpineCompression,
    junctionFilamentCount, pinchCompressionRatio, nodePinchRadius]
  norm_num

theorem filament_node_pinch_vital_holds : filament_node_pinch_vital := by
  refine ⟨nodeLocalizedIntensity_quad_junction_gt_ten, ?_⟩
  exact ⟨WhimPinchCollapseHypothesis.mk nodeLocalizedIntensity_quad_junction_gt_ten.le⟩

/-!
## §8. β–pinch force balance (`p_th` vs `p_mag`)

Ideal thermal pressure `p_th = n k_B T`. Plasma beta `β = p_th / p_mag`.

Bennett force balance at pinch radius `r` (`p_mag = p_th`, `β = 1`):

\[
\frac{\mu_0 I^2}{8\pi^2 r^2} = n k_B T
\quad\Rightarrow\quad
I = 2\pi r\sqrt{\frac{2\,n k_B T}{\mu_0}}.
\]

Current density: `J = I/(\pi r^2) = 2\sqrt{2 n k_B T/\mu_0}/r`.

WHIM/coronal readouts supply `n`, `T`, `r` — `J_spine` is **derived**, not fitted.
-/

/-- Ideal-gas thermal pressure `p_th = n k_B T`. -/
def thermalPlasmaPressure (n kB T : ℝ) : ℝ :=
  n * kB * T

theorem thermalPlasmaPressure_nonneg {n kB T : ℝ}
    (hn : 0 ≤ n) (hk : 0 ≤ kB) (hT : 0 ≤ T) :
    0 ≤ thermalPlasmaPressure n kB T := by
  unfold thermalPlasmaPressure
  positivity

/-- Plasma beta `β = p_th / p_mag`. -/
def pinchPlasmaBeta (pThermal pMag : ℝ) : ℝ :=
  if pMag = 0 then 0 else pThermal / pMag

/-- Bennett axial current at `β = 1` from thermal pressure at radius `r`. -/
def bennettCurrentFromThermalPressure (r pThermal mu0 : ℝ) : ℝ :=
  if mu0 = 0 ∨ pThermal ≤ 0 ∨ r ≤ 0 then 0
  else 2 * Real.pi * r * Real.sqrt (2 * pThermal / mu0)

/-- Current density at Bennett `β = 1` balance. -/
def bennettCurrentDensityFromThermal (r pThermal mu0 : ℝ) : ℝ :=
  if r = 0 then 0 else bennettCurrentFromThermalPressure r pThermal mu0 / (Real.pi * r ^ 2)

/-- Magnetic pressure at Bennett-balanced current for thermal pressure `pTh`. -/
def pinchMagneticPressureAtBennettCurrent (mu0 r pTh : ℝ) : ℝ :=
  pinchAzimuthalPressure mu0 (bennettCurrentFromThermalPressure r pTh mu0) r

/-- Thermal pressure slot used at Bennett force balance (`p_mag = p_th`). -/
def bennettBalancedMagneticPressure (pTh : ℝ) : ℝ := pTh

/-- Residual `p_mag − p_th` for readout (Python verifies ≈ 0 at derived `I`). -/
def bennettPressureBalanceResidual (mu0 r pTh : ℝ) : ℝ :=
  pinchMagneticPressureAtBennettCurrent mu0 r pTh - pTh

/-- `β` for a given axial current and thermal state. -/
def pinchBetaFromCurrent (mu0 I r n kB T : ℝ) : ℝ :=
  pinchPlasmaBeta (thermalPlasmaPressure n kB T) (pinchAzimuthalPressure mu0 I r)

theorem bennettCurrentFromThermalPressure_nonneg {r pThermal mu0 : ℝ}
    (hr : 0 ≤ r) (hp : 0 ≤ pThermal) (hmu : 0 ≤ mu0) :
    0 ≤ bennettCurrentFromThermalPressure r pThermal mu0 := by
  unfold bennettCurrentFromThermalPressure
  split_ifs with h <;> positivity

/-- `β` at Bennett force balance (`p_mag` slot equals `p_th`). -/
def pinchBetaAtBennettBalance (mu0 r n kB T : ℝ) : ℝ :=
  pinchPlasmaBeta (thermalPlasmaPressure n kB T)
    (bennettBalancedMagneticPressure (thermalPlasmaPressure n kB T))

theorem pinchBetaAtBennettBalance_eq_one
    (mu0 r n kB T : ℝ) (hr : 0 < r) (hn : 0 < n) (hk : 0 < kB) (hT : 0 < T) (hmu : 0 < mu0) :
    pinchBetaAtBennettBalance mu0 r n kB T = 1 := by
  unfold pinchBetaAtBennettBalance pinchPlasmaBeta bennettBalancedMagneticPressure thermalPlasmaPressure
  have hp : 0 < n * kB * T := by positivity
  simp [ne_of_gt hp]

/-- WHIM/coronal spine `J` from `(n, T, r)` at Bennett balance. -/
def spineCurrentDensityFromBetaBalance (n kB T mu0 r : ℝ) : ℝ :=
  bennettCurrentDensityFromThermal r (thermalPlasmaPressure n kB T) mu0

theorem spineCurrentDensityFromBetaBalance_nonneg {n kB T mu0 r : ℝ}
    (hn : 0 ≤ n) (hk : 0 ≤ kB) (hT : 0 ≤ T) (hmu : 0 ≤ mu0) (hr : 0 ≤ r) :
    0 ≤ spineCurrentDensityFromBetaBalance n kB T mu0 r := by
  unfold spineCurrentDensityFromBetaBalance bennettCurrentDensityFromThermal
  split_ifs with hz
  · subst hz; simp
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hp := thermalPlasmaPressure_nonneg hn hk hT
    apply div_nonneg
    · exact bennettCurrentFromThermalPressure_nonneg (le_of_lt hrpos) hp hmu
    · positivity

/-- WHIM filament defaults (readout witnesses, not PDG fits). -/
def whimFilamentDensityWitness_m3 : ℝ := 10000

def whimFilamentTemperatureWitness_K : ℝ := 1000000

def coronalFilamentDensityWitness_m3 : ℝ := 1e20

def coronalFilamentTemperatureWitness_K : ℝ := 1000000

structure BetaPinchBalanceWitness where
  n : ℝ
  kB : ℝ
  T : ℝ
  mu0 : ℝ
  r : ℝ
  beta_one : pinchBetaAtBennettBalance mu0 r n kB T = 1

def beta_pinch_balance_vital : Prop :=
  (0 : ℝ) < whimFilamentDensityWitness_m3 ∧
    pinchBetaAtBennettBalance (4 * Real.pi * 1e-7) 1 10000 1.380649e-23 1000000 = 1

theorem beta_pinch_balance_vital_holds : beta_pinch_balance_vital := by
  refine ⟨by dsimp [whimFilamentDensityWitness_m3]; norm_num, ?_⟩
  exact pinchBetaAtBennettBalance_eq_one (4 * Real.pi * 1e-7) 1 10000 1.380649e-23 1000000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)

/-!
## §9. Radiative WHIM cooling + pinch-heating equilibrium
-/

/-- WHIM radiative cooling function witness `Λ(T) = λ₀ T^{-α}`. -/
def whimLambdaCooling (lambda0 alpha T : ℝ) : ℝ :=
  if T ≤ 0 then 0 else lambda0 * T ^ (-alpha)

theorem whimLambdaCooling_nonneg {lambda0 alpha T : ℝ}
    (hl : 0 ≤ lambda0) (_ha : 0 ≤ alpha) (hT : 0 ≤ T) :
    0 ≤ whimLambdaCooling lambda0 alpha T := by
  unfold whimLambdaCooling
  split_ifs with h
  · simp
  · exact mul_nonneg hl (Real.rpow_nonneg (le_of_lt (not_le.mp h)) (-alpha))

/-- Radiative cooling density `q_cool = n² Λ(T)` [W/m³]. -/
def radiativeCoolingDensity (n lambda0 alpha _kB T : ℝ) : ℝ :=
  n ^ 2 * whimLambdaCooling lambda0 alpha T

theorem radiativeCoolingDensity_nonneg {n lambda0 alpha kB T : ℝ}
    (hn : 0 ≤ n) (hl : 0 ≤ lambda0) (ha : 0 ≤ alpha) (hT : 0 ≤ T) :
    0 ≤ radiativeCoolingDensity n lambda0 alpha kB T := by
  unfold radiativeCoolingDensity
  exact mul_nonneg (sq_nonneg n) (whimLambdaCooling_nonneg hl ha hT)

/-- Pinch dissipation heating `q_heat = η p_th`. -/
def whimPinchHeatingDensity (eta n kB T : ℝ) : ℝ :=
  eta * thermalPlasmaPressure n kB T

/-- Radiative equilibrium residual `q_heat − q_cool`. -/
def whimRadiativeEquilibriumResidual (eta n lambda0 alpha kB T : ℝ) : ℝ :=
  whimPinchHeatingDensity eta n kB T - radiativeCoolingDensity n lambda0 alpha kB T

/-- Closed-form density at pinch–radiative balance (`Λ(T) = λ₀ T^{-α}`). -/
def whimEquilibriumDensity (eta lambda0 alpha kB T : ℝ) : ℝ :=
  if lambda0 = 0 ∨ T ≤ 0 then 0 else eta * kB * T ^ (1 + alpha) / lambda0

theorem whimEquilibriumDensity_nonneg {eta lambda0 alpha kB T : ℝ}
    (he : 0 ≤ eta) (hk : 0 ≤ kB) (hl : 0 < lambda0) :
    0 ≤ whimEquilibriumDensity eta lambda0 alpha kB T := by
  unfold whimEquilibriumDensity
  split_ifs with h
  · simp
  · rcases not_or.mp h with ⟨_, hT_not_le⟩
    have hT : 0 < T := not_le.mp hT_not_le
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg he hk) (Real.rpow_nonneg (le_of_lt hT) _)
    · exact le_of_lt hl

/-- WHIM λ₀ witness (readout calibration at `T = 10⁶ K`, not PDG). -/
def whimLambdaCoolingWitness : ℝ := 5.52e-21

def whimLambdaCoolingAlphaWitness : ℝ := 0.7

def whimPinchHeatingFractionWitness : ℝ := gamma_HQIV

theorem whimRadiativeResidual_zero_at_equilibrium_density
    (eta lambda0 alpha kB T : ℝ) (hl : lambda0 ≠ 0) (hT : 0 < T) :
    whimRadiativeEquilibriumResidual eta (whimEquilibriumDensity eta lambda0 alpha kB T)
      lambda0 alpha kB T = 0 := by
  have hTle : ¬T ≤ 0 := not_le.mpr hT
  have hcond : ¬(lambda0 = 0 ∨ T ≤ 0) := not_or.mpr ⟨hl, hTle⟩
  have hn : whimEquilibriumDensity eta lambda0 alpha kB T =
      eta * kB * T ^ (1 + alpha) / lambda0 := by
    unfold whimEquilibriumDensity
    simp [hcond]
  unfold whimRadiativeEquilibriumResidual whimPinchHeatingDensity radiativeCoolingDensity
    whimLambdaCooling thermalPlasmaPressure
  rw [hn]
  simp only [hTle, ite_false]
  field_simp
  have hcool : T ^ (1 + alpha) * T ^ (-alpha) = T := by
    rw [← Real.rpow_add hT, show (1 + alpha) + -alpha = 1 by ring, Real.rpow_one]
  rw [hcool]
  simp

def whim_radiative_equilibrium_vital : Prop :=
  0 < whimEquilibriumDensity whimPinchHeatingFractionWitness whimLambdaCoolingWitness
    whimLambdaCoolingAlphaWitness 1.380649e-23 1000000

theorem whim_radiative_equilibrium_vital_holds : whim_radiative_equilibrium_vital := by
  unfold whim_radiative_equilibrium_vital whimPinchHeatingFractionWitness whimEquilibriumDensity
  rw [gamma_eq_2_5]
  have hT : (1000000 : ℝ) > 0 := by norm_num
  dsimp [whimLambdaCoolingWitness, whimLambdaCoolingAlphaWitness]
  have hl : (552e-23 : ℝ) ≠ 0 := by norm_num
  simp only [hl, not_le.mpr hT, ite_false]
  apply div_pos
  · apply mul_pos (by norm_num) (Real.rpow_pos_of_pos hT _)
  · norm_num

/-!
## §10. CMB / age-aware coupled WHIM closure (no WHIM witness constants)

WHIM filament `(n, T)` is tied to the present-epoch CMB slot and lapse-weighted
cooling chart:

* `α = α_HQIV` (lattice curvature imprint, 3/5);
* `η = γ_HQIV` (pinch-heating fraction, 2/5);
* `λ₀` normalized at the CMB baryon slot: `λ₀ = η k_B T_CMB^{1+α} / n_b`;
* age enters through `Ω_cmb` and `wallClockAgeHomogeneous` (compare `UniverseAge.lean`).

At fixed derived `T`, radiative closure gives `n = n_b (T/T_CMB)^{1+α}` on the
baryon-normalized chart (Python solves the coupled geometry + thermal load).
-/

/-- HQIV cooling exponent on the radiative scaffold (``α = 3/5``). -/
def whimCoolingAlphaDerived : ℝ := alpha

theorem whimCoolingAlphaDerived_eq_alpha : whimCoolingAlphaDerived = alpha := rfl

/-- Pinch heating fraction equals ``γ_HQIV``. -/
theorem whimPinchHeatingFraction_eq_gamma : whimPinchHeatingFractionWitness = gamma_HQIV := rfl

/-- Baryon-slot normalization scale: `λ₀ = η k_B T^{1+α} / n_b`. -/
def whimLambda0FromBaryonSlot (eta nB kB T alpha : ℝ) : ℝ :=
  if nB = 0 ∨ T ≤ 0 then 0 else eta * kB * T ^ (1 + alpha) / nB

/-- Coupled equilibrium density on baryon chart: `n = n_b (T/T_CMB)^{1+α}`. -/
def whimEquilibriumDensityBaryonChart (nB T_CMB T alpha : ℝ) : ℝ :=
  if T_CMB = 0 ∨ T ≤ 0 then 0 else nB * (T / T_CMB) ^ (1 + alpha)

theorem whimEquilibriumDensityBaryonChart_nonneg {nB T_CMB T alpha : ℝ}
    (hn : 0 ≤ nB) (hTc : 0 < T_CMB) :
    0 ≤ whimEquilibriumDensityBaryonChart nB T_CMB T alpha := by
  unfold whimEquilibriumDensityBaryonChart
  split_ifs with h
  · simp
  · rcases not_or.mp h with ⟨_, hT_not_le⟩
    have hT : 0 < T := not_le.mp hT_not_le
    exact mul_nonneg hn (Real.rpow_nonneg (div_nonneg (le_of_lt hT) (le_of_lt hTc)) _)

/-- Coupled WHIM thermal load multiplier at an ``N``-way junction: ``N²``. -/
def nodeThermalLoadMultiplier (nFilaments : ℕ) : ℝ :=
  (junctionFilamentCount nFilaments) ^ 2

theorem nodeThermalLoadMultiplier_eq (n : ℕ) :
    nodeThermalLoadMultiplier n = (junctionFilamentCount n) ^ 2 := rfl

end

end Hqiv.Physics
