import Mathlib.Algebra.Order.Floor.Semiring
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.Action
import Hqiv.Physics.ContinuumOmaxwellClosure
import Hqiv.QuantumMechanics.HorizonLimitedRenormLocality
import Hqiv.QuantumMechanics.MinkowskiFieldOperatorScaffold
import Hqiv.QuantumMechanics.PauliCommutatorExample
import Hqiv.QuantumMechanics.CCRFiniteDimObstruction
import Hqiv.QuantumMechanics.LocalAlgebraNetScaffold
import Hqiv.QuantumMechanics.PatchQFTBridge
import Hqiv.Physics.SpinStatisticsOperatorBridge

/-!
# Light cone → continuum Maxwell → QM/QFT scaffold (functional link)

This module is the **single import hub** for the idea:

* **Down (geometry / same null ladder):** discrete light-cone data (`Hqiv.Geometry.OctonionicLightCone`, mode
  capacity) feeds **continuum** φ–Maxwell slots on `Fin 4 → ℝ` via
  `Hqiv.Physics.ContinuumOmaxwellClosure` and metric-raised gradients in
  `Hqiv.Geometry.ContinuumMetricGradient`.

* **Mass/couplings (same ladder):** `Hqiv.Physics.HarmonicLadderMass` proves the definitional
  chain from `phi_of_shell` / `shell_shape` through `one_over_alpha_eff` and `alphaEffAtShell` to
  hydrogenic binding scales at shell `m`.

* **Up (same ladder → asymptotic modes):** the **proved** shell/harmonic ratio limit
  (`shell_to_harmonic_limit_holds` in `ContinuumManyBodyQFTScaffold`) is exactly the first
  `HorizonContinuumAxiomsMinimal.shell_to_harmonic_limit` obligation used in
  `HorizonLimitedRenormLocality`.

`LightConeFunctionalBridge` pairs a **minimal axiom record** with a **proof** of its shell slot, so you
do not “cross a valley” informally: `toContinuumClosureHQIV` is just
`horizon_continuum_closure_minimal_HQIV` with that bundle, and `toFullPackageMinimalHQIV` is the same
for `horizon_qm_qft_full_package_minimal_HQIV` (finite Born/kernel layer + that continuum conclusion).

Renorm/cluster/scattering in `horizonContinuumAxiomsMinimal_ratioWitness` use **structured**
scaffold witnesses (`renormalization_in_domain_discreteUV_holds` (alias `renormalization_in_domain_trivial_holds`),
  `cluster_decomposition_zero_kernel_holds`,
`scattering_consistency_zero_channel_holds`). For **Minkowski** microcausality, see
`continuum_many_body_closure_minkowskiMicroWitness` (zero commutator kernel) and
`continuum_many_body_closure_minkowskiIntervalWitness` (`commutatorKernelIntervalMax` = `max 0 η`, nontrivial
on timelike pairs — `ContinuumManyBodyQFTScaffold`).  **Operators on `ℂ⁴`:** `MinkowskiFieldOperatorScaffold`
(`fieldOpFromChart`) and `HorizonFreeFieldScaffold.opCommutator`; **noncommutative toy:** `PauliCommutatorExample`;
**no exact CCR on finite matrices:** `CCRFiniteDimObstruction.not_exists_matrix_CCR_one`; **local net scaffold:**
`LocalAlgebraNetScaffold.diagonalSmearedNet` (isotony + commuting regions); **support-restricted patch net**
(`patchAlgebraAt`, `WeightSupportInRegion`, `patchChartPoint`, `patchEventChartFour`,
`spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions`) in `PatchQFTBridge`; **spin/operator
attachment:** `SpinStatisticsOperatorBridge` turns HQIV mode pairs into concrete smeared interval-max
operators whose observable and Pauli commutator vanish on spacelike patch support.  **Finite patch + limit:**
`accessibleModeBudgetUpToShell`, `accessibleModeBudgetUpToShell_eq_sum_new_modes`,
`accessiblePatch_modeBudget_div_harmonic_tends_four`, `accessiblePatch_shellToHarmonicLimit`,
`PhotonHorizonModeLimit` / `PhotonHorizonModeLimitValue` / `photonHorizonModeLimit_tendsto` (**definite** ratio
limit **`4`** — photon-sector / null-ladder vs `S²` harmonics).
**Directional cluster witnesses:** `clusterCorrelationDirectionalMonogamyRedshift` gives a nonzero forward
cluster kernel using `coherenceProxy` plus inverse-`phi` shell damping; `clusterCorrelationDirectionalMonogamyPhotonGeodesic`
upgrades this to the finite photon transport channel `redshiftedEnergyN 1 (birefringenceRedshiftN ((n:ℝ)+1) κ)`;
`clusterCorrelationDirectionalMonogamyPhotonBudget` keeps the same ledger but drives it by the cumulative
photon mode budget `available_modes n` / `accessibleModeBudgetUpToShell n`; `clusterCorrelationDirectionalMonogamyTimeAngleBudget`
uses the doubled observer-time budget `accessibleModeBudgetUpToTimeAngle (4(n+1))`.
**Time ↔ shell (same ladder as `phi_of_shell`, `timeAngle`):** `shellIndexFromTimeAngle`,
`accessibleModeBudgetUpToTimeAngle`, `accessibleModeBudgetUpToPhiTime`, and the unit-time budget match
(`accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`).  Next layers: region-restricted
supports tied to the light-cone patch—without positing a single global infinite-dimensional Hilbert space
as the HQIV setting.
-/

namespace Hqiv.Physics

open scoped BigOperators Topology
open Finset Filter Topology
open Hqiv
open Hqiv.QM

/-- Same chart type as `coordsGradientComponents` / `contravariantGradientComponentsAt` (continuum hook). -/
abbrev MaxwellQFTChart : Type :=
  Fin 4 → ℝ

/-!
## Discrete ladder → continuum axiom (same object as `ContinuumManyBodyQFTScaffold`)

The shell/harmonic ratio limit is proved from `Hqiv.available_modes` and
`sphericalHarmonicCumulativeCount` (via `SphericalHarmonicsBridge`); this is the discrete
light-cone capacity feeding the first `HorizonContinuumAxiomsMinimal` slot in the QM/QFT package.

### Finite patch (“accessible up to shell `M`”)

HQIV does **not** require a global infinite-dimensional carrier: formal statements live on **finite**
cutoffs, with **asymptotic** content packaged as limits as the shell index grows. The ℝ-valued budget
for shells `0 … M` inclusive is exactly `Hqiv.available_modes M` — cumulative new modes on the null
lattice (`Hqiv.sum_new_modes_eq_available_modes`). The named alias `accessibleModeBudgetUpToShell`
makes that “patch size” reading grepable and ties one place to the shell→harmonic ratio limit.

### Time angle `φ·t` ↔ discrete shell (HQVM × auxiliary ladder)

On the HQVM track, `Hqiv.timeAngle φ t = φ * t` (`HQVMetric`).  Tying `φ` to the shell ladder via
`φ = phi_of_shell m` gives `timeAngle (phi_of_shell m) t = 2 (m+1) t` (`phi_of_shell_closed_form`).
Normalizing by `phiTemperatureCoeff = 2` yields `(m+1) t - 1` after subtracting `1`, whose nonnegative
floor is a **discrete shell index** scaffold (`shellIndexFromTimeAngle`).  At **unit coordinate time**
`t = 1`, this floor is exactly `m`, so the mode budget matches `accessibleModeBudgetUpToShell m`
(`accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`).
-/

/-- ℝ-valued **accessible mode budget** on shells `0 … M` inclusive: cumulative capacity on the
discrete null ladder (`Hqiv.sum_new_modes_eq_available_modes`). Same as `Hqiv.available_modes M`. -/
noncomputable def accessibleModeBudgetUpToShell (M : ℕ) : ℝ :=
  Hqiv.available_modes M

@[simp]
theorem accessibleModeBudgetUpToShell_eq_available (M : ℕ) :
    accessibleModeBudgetUpToShell M = Hqiv.available_modes M :=
  rfl

theorem accessibleModeBudgetUpToShell_eq_sum_new_modes (M : ℕ) :
    accessibleModeBudgetUpToShell M = ∑ i ∈ range (M + 1), Hqiv.new_modes i :=
  (Hqiv.sum_new_modes_eq_available_modes M).symm

/-- Per-shell accessible budget is nonnegative (`available_modes m = 4*(m+2)(m+1)`). -/
theorem accessibleModeBudgetUpToShell_nonneg (M : ℕ) :
    0 ≤ accessibleModeBudgetUpToShell M := by
  rw [accessibleModeBudgetUpToShell_eq_available, Hqiv.available_modes_eq]
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  nlinarith [hM]

/-- Ratio built from the per-patch budget tends to the octonion factor `4` as `M → ∞`
(same `Tendsto` as `continuum_shell_harmonic_ratio_limit` / `shell_to_harmonic_limit_holds`). -/
theorem accessiblePatch_modeBudget_div_harmonic_tends_four :
    Tendsto (fun M : ℕ => accessibleModeBudgetUpToShell M / Hqiv.sphericalHarmonicCumulativeCount M)
      atTop (𝓝 (4 : ℝ)) := by
  simpa [accessibleModeBudgetUpToShell] using continuum_shell_harmonic_ratio_limit

/-- `ShellToHarmonicLimit` — same proposition and proof as `lightCone_discreteModes_shellToHarmonicLimit`;
use this name when narrating **finite-patch** limits (`accessibleModeBudgetUpToShell`). -/
theorem accessiblePatch_shellToHarmonicLimit : ShellToHarmonicLimit :=
  shell_to_harmonic_limit_holds

/-!
### Definite photon / horizon refinement limit (EM mode ladder → `4`)

Massless EM modes live on the **same** discrete null-ladder capacity as the rest of HQIV; when
compared to cumulative angular (`S²`) mode counting, the ratio has a **proved** `Tendsto` to a single
real number — the octonionic factor **`4`**.  There is no continuous parameter: this is the
**definite** asymptotic lock (“photon bookkeeping meets horizon angular refinement”).  A separate
curvature–horizon ratio story uses `Hqiv.omega_k_partial` / `Hqiv.omega_k_partial_tends_to_atTop` in
`OctonionicLightCone` (ratio of curvature integrals, not the `4` here).
-/

/-- **Numeric value** of the asymptotic mode-ratio limit (octonion factor). -/
def PhotonHorizonModeLimitValue : ℝ :=
  4

/-- Same `Prop` as `ShellToHarmonicLimit` — packaged under the photon / horizon refinement name. -/
abbrev PhotonHorizonModeLimit : Prop :=
  ShellToHarmonicLimit

theorem photonHorizonModeLimit_holds : PhotonHorizonModeLimit :=
  shell_to_harmonic_limit_holds

theorem PhotonHorizonModeLimit_iff_shellToHarmonicLimit :
    PhotonHorizonModeLimit ↔ ShellToHarmonicLimit :=
  Iff.rfl

/-- The ratio tends to **neighbourhoods of `PhotonHorizonModeLimitValue = 4`**. -/
theorem photonHorizonModeLimit_tendsto :
    Tendsto (fun M : ℕ => accessibleModeBudgetUpToShell M / Hqiv.sphericalHarmonicCumulativeCount M)
      atTop (𝓝 PhotonHorizonModeLimitValue) := by
  simpa [PhotonHorizonModeLimitValue] using accessiblePatch_modeBudget_div_harmonic_tends_four

theorem PhotonHorizonModeLimitValue_eq : PhotonHorizonModeLimitValue = 4 :=
  rfl

/-!
### Cumulative time angle → shell index → mode budget

`θ / phiTemperatureCoeff` is the continuous “(m+1)”-coordinate when `θ = timeAngle (phi_of_shell m) 1`
(`realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit`).  The floor below packages a **ℕ** shell
index for pairing with `accessibleModeBudgetUpToShell`.
-/

/-- Continuous **(m+1)**-coordinate from cumulative phase: `θ / 2` with `phiTemperatureCoeff = 2`. -/
noncomputable def realShellPlusOneFromTimeAngle (θ : ℝ) : ℝ :=
  θ / phiTemperatureCoeff

theorem realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    realShellPlusOneFromTimeAngle (timeAngle (phi_of_shell m) 1) = m + 1 := by
  unfold realShellPlusOneFromTimeAngle timeAngle
  simp only [mul_one, phi_of_shell_closed_form m, phiTemperatureCoeff_eq_two]
  field_simp

/-- Discrete shell index from cumulative time angle `θ` (nonnegative floor of `(θ/2) - 1`). -/
noncomputable def shellIndexFromTimeAngle (θ : ℝ) : ℕ :=
  ⌊max 0 (θ / phiTemperatureCoeff - 1)⌋₊

theorem shellIndexFromTimeAngle_timeAngle_phi_shell (m : ℕ) (t : ℝ) :
    shellIndexFromTimeAngle (timeAngle (phi_of_shell m) t) =
      ⌊max 0 ((m + 1 : ℝ) * t - 1)⌋₊ := by
  unfold shellIndexFromTimeAngle timeAngle
  have h :
      phi_of_shell m * t / phiTemperatureCoeff - 1 = (m + 1 : ℝ) * t - 1 := by
    rw [phi_of_shell_closed_form m, phiTemperatureCoeff_eq_two]
    ring
  simp [h]

theorem shellIndexFromTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    shellIndexFromTimeAngle (timeAngle (phi_of_shell m) 1) = m := by
  rw [shellIndexFromTimeAngle_timeAngle_phi_shell m 1]
  simp only [mul_one]
  have hs : (m + 1 : ℝ) - 1 = (m : ℝ) := by ring
  rw [hs]
  rw [max_eq_right (Nat.cast_nonneg m)]
  exact Nat.floor_natCast (R := ℝ) m

/-- Mode budget reachable when the discrete shell index is inferred from `θ = φ·t` via
`shellIndexFromTimeAngle`. -/
noncomputable def accessibleModeBudgetUpToTimeAngle (θ : ℝ) : ℝ :=
  accessibleModeBudgetUpToShell (shellIndexFromTimeAngle θ)

/-- Same as `accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) t)`. -/
noncomputable def accessibleModeBudgetUpToPhiTime (m : ℕ) (t : ℝ) : ℝ :=
  accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) t)

theorem accessibleModeBudgetUpToTimeAngle_nonneg (θ : ℝ) :
    0 ≤ accessibleModeBudgetUpToTimeAngle θ := by
  unfold accessibleModeBudgetUpToTimeAngle
  exact accessibleModeBudgetUpToShell_nonneg _

theorem accessibleModeBudgetUpToPhiTime_nonneg (m : ℕ) (t : ℝ) :
    0 ≤ accessibleModeBudgetUpToPhiTime m t := by
  unfold accessibleModeBudgetUpToPhiTime
  exact accessibleModeBudgetUpToTimeAngle_nonneg _

theorem accessibleModeBudgetUpToTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) 1) =
      accessibleModeBudgetUpToShell m := by
  unfold accessibleModeBudgetUpToTimeAngle accessibleModeBudgetUpToShell
  simp [shellIndexFromTimeAngle_timeAngle_phi_shell_unit m]

theorem accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit (m : ℕ) :
    accessibleModeBudgetUpToPhiTime m 1 = accessibleModeBudgetUpToShell m :=
  accessibleModeBudgetUpToTimeAngle_timeAngle_phi_shell_unit m

/-- A doubled observer-time angle `4 (n+1)` packages a cumulative time-angle budget scale without naming `φ`. -/
noncomputable def timeAngleBudgetScaleN (n : ℕ) : ℝ :=
  accessibleModeBudgetUpToTimeAngle (4 * ((n : ℝ) + 1))

/-- The doubled time-angle budget lands exactly on shell budget `2n+1`. -/
theorem timeAngleBudgetScaleN_eq_accessibleModeBudgetUpToShell (n : ℕ) :
    timeAngleBudgetScaleN n = accessibleModeBudgetUpToShell (2 * n + 1) := by
  unfold timeAngleBudgetScaleN accessibleModeBudgetUpToTimeAngle
  rw [show shellIndexFromTimeAngle (4 * ((n : ℝ) + 1)) = 2 * n + 1 by
    unfold shellIndexFromTimeAngle
    rw [phiTemperatureCoeff_eq_two]
    have hcalc : 4 * ((n : ℝ) + 1) / (2 : ℝ) - 1 = (2 * n + 1 : ℝ) := by ring
    rw [hcalc]
    rw [max_eq_right (by positivity : (0 : ℝ) ≤ (2 * n + 1 : ℝ))]
    simpa [Nat.cast_add, Nat.cast_mul] using (Nat.floor_natCast (R := ℝ) (2 * n + 1))]

/-- Closed form for the doubled time-angle budget scale. -/
theorem timeAngleBudgetScaleN_eq (n : ℕ) :
    timeAngleBudgetScaleN n = (4 : ℝ) * ((2 * n + 3 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) := by
  rw [timeAngleBudgetScaleN_eq_accessibleModeBudgetUpToShell, accessibleModeBudgetUpToShell_eq_available,
    Hqiv.available_modes_eq]
  norm_num
  ring

/-- The doubled time-angle budget scale tends to `atTop`. -/
theorem timeAngleBudgetScaleN_tendsto_atTop :
    Tendsto timeAngleBudgetScaleN atTop atTop := by
  rw [show timeAngleBudgetScaleN =
      fun n : ℕ => (4 : ℝ) * ((((2 * n + 3 : ℕ) : ℝ)) * (((2 * n + 2 : ℕ) : ℝ))) by
        funext n
        simpa [mul_assoc] using timeAngleBudgetScaleN_eq n]
  have h2n : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hleft : Tendsto (fun n : ℕ => (((2 * n + 3 : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_mul] using h2n.atTop_add (tendsto_const_nhds (x := (3 : ℝ)))
  have hright : Tendsto (fun n : ℕ => (((2 * n + 2 : ℕ) : ℝ))) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_mul] using h2n.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  have hmul : Tendsto (fun n : ℕ => ((((2 * n + 3 : ℕ) : ℝ)) * (((2 * n + 2 : ℕ) : ℝ)))) atTop atTop :=
    hleft.atTop_mul_atTop₀ hright
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hmul

/-- Photon transport driven by the doubled observer-time budget. -/
noncomputable def timeAngleBudgetTransportN (kappaBeta : ℝ) (n : ℕ) : ℝ :=
  Hqiv.QM.photonGeodesicTransportFromScale timeAngleBudgetScaleN kappaBeta n

theorem timeAngleBudgetTransportN_eq_exp_neg_div (kappaBeta : ℝ) (n : ℕ) :
    timeAngleBudgetTransportN kappaBeta n = Real.exp (-(timeAngleBudgetScaleN n / kappaBeta)) :=
  Hqiv.QM.photonGeodesicTransportFromScale_eq_exp_neg_div timeAngleBudgetScaleN kappaBeta n

theorem timeAngleBudgetTransportN_tendsto_zero (kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    Tendsto (timeAngleBudgetTransportN kappaBeta) atTop (𝓝 0) :=
  Hqiv.QM.photonGeodesicTransportFromScale_tendsto_zero timeAngleBudgetScaleN kappaBeta
    timeAngleBudgetScaleN_tendsto_atTop hκ

/-- Forward cluster kernel using the doubled observer-time budget as the photon transport scale. -/
noncomputable def clusterCorrelationDirectionalMonogamyTimeAngleBudget
    (τPair kappaBeta : ℝ) : Hqiv.QM.CorrelationKernel :=
  fun x y =>
    if y = x + 1 then Hqiv.QM.coherenceProxy x τPair * timeAngleBudgetTransportN kappaBeta x else 0

theorem clusterCorrelationDirectionalMonogamyTimeAngleBudget_succ
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyTimeAngleBudget τPair kappaBeta n (n + 1) =
      Hqiv.QM.coherenceProxy n τPair * timeAngleBudgetTransportN kappaBeta n := by
  simp [clusterCorrelationDirectionalMonogamyTimeAngleBudget]

theorem clusterCorrelationDirectionalMonogamyTimeAngleBudget_succ_eq
    (τPair kappaBeta : ℝ) (n : ℕ) :
    clusterCorrelationDirectionalMonogamyTimeAngleBudget τPair kappaBeta n (n + 1) =
      (1 / (((Hqiv.referenceM + 2 : ℕ) : ℝ) * (Hqiv.referenceM + 1 : ℝ)) * τPair) *
        Real.exp (-(timeAngleBudgetScaleN n / kappaBeta)) := by
  rw [clusterCorrelationDirectionalMonogamyTimeAngleBudget_succ, Hqiv.QM.coherenceProxy,
    Hqiv.QM.etaModePhi_constant, timeAngleBudgetTransportN_eq_exp_neg_div]

theorem cluster_decomposition_directional_monogamy_timeAngleBudget_holds
    (τPair kappaBeta : ℝ) (hκ : 0 < kappaBeta) :
    Hqiv.QM.ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyTimeAngleBudget τPair kappaBeta) := by
  dsimp [Hqiv.QM.ClusterDecompositionStatement]
  have hC :
      (fun n : ℕ =>
        clusterCorrelationDirectionalMonogamyTimeAngleBudget τPair kappaBeta n (n + 1)) =
      fun n : ℕ =>
        (1 / (((Hqiv.referenceM + 2 : ℕ) : ℝ) * (Hqiv.referenceM + 1 : ℝ)) * τPair) *
          timeAngleBudgetTransportN kappaBeta n := by
    funext n
    rw [clusterCorrelationDirectionalMonogamyTimeAngleBudget_succ_eq]
    rw [timeAngleBudgetTransportN_eq_exp_neg_div]
  rw [hC]
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (1 / (((Hqiv.referenceM + 2 : ℕ) : ℝ) * (Hqiv.referenceM + 1 : ℝ)) * τPair) *
            timeAngleBudgetTransportN kappaBeta n)
        atTop
        (𝓝
          ((1 / (((Hqiv.referenceM + 2 : ℕ) : ℝ) * (Hqiv.referenceM + 1 : ℝ)) * τPair) * 0)) :=
    (tendsto_const_nhds (x := (1 / (((Hqiv.referenceM + 2 : ℕ) : ℝ) * (Hqiv.referenceM + 1 : ℝ)) * τPair))).mul
      (timeAngleBudgetTransportN_tendsto_zero kappaBeta hκ)
  simpa using hlim

/--
GR-shaped package at the doubled observer-time budget scale.

The same cumulative time-angle budget that drives the photon transport witness can be
used as the homogeneous HQVM field input: it fixes the lapse channel, determines
`G_eff`, and turns the HQVM gravitational action into the Friedmann equation at that
scale.
-/
theorem timeAngleBudgetScale_feeds_HQVM_GR
    (n : ℕ) (Φ t rho_m rho_r : ℝ) :
    HQVM_lapse Φ (timeAngleBudgetScaleN n) t = 1 + Φ + timeAngle (timeAngleBudgetScaleN n) t ∧
      H_of_phi (timeAngleBudgetScaleN n) = timeAngleBudgetScaleN n ∧
      G_eff (timeAngleBudgetScaleN n) = (timeAngleBudgetScaleN n) ^ alpha ∧
      (S_HQVM_grav (timeAngleBudgetScaleN n) rho_m rho_r = 0 ↔
        HQVM_Friedmann_eq (timeAngleBudgetScaleN n) rho_m rho_r) ∧
      (HQVM_Friedmann_eq (timeAngleBudgetScaleN n) rho_m rho_r ↔
        (13/5 : ℝ) * (timeAngleBudgetScaleN n) ^ 2 =
          8 * Real.pi * ((timeAngleBudgetScaleN n) ^ alpha) * (rho_m + rho_r)) := by
  have hnonneg : 0 ≤ timeAngleBudgetScaleN n := by
    rw [timeAngleBudgetScaleN_eq_accessibleModeBudgetUpToShell]
    exact accessibleModeBudgetUpToShell_nonneg (2 * n + 1)
  refine ⟨HQVM_lapse_eq_timeAngle Φ (timeAngleBudgetScaleN n) t, H_of_phi_eq (timeAngleBudgetScaleN n),
    G_eff_eq (timeAngleBudgetScaleN n) hnonneg, S_HQVM_grav_zero_iff_Friedmann (timeAngleBudgetScaleN n) rho_m rho_r,
    ?_⟩
  exact HQVM_Friedmann_eq_power (timeAngleBudgetScaleN n) rho_m rho_r hnonneg

/--
Time-angle transport plus GR package at the same scale.

This is the bridge-level statement that the observer-time budget simultaneously
drives exponential photon attenuation and the homogeneous HQVM gravity slot.
-/
theorem timeAngleBudgetTransport_and_HQVM_GR
    (n : ℕ) (kappaBeta : ℝ) (Φ t rho_m rho_r : ℝ) :
    timeAngleBudgetTransportN kappaBeta n =
        Real.exp (-(timeAngleBudgetScaleN n / kappaBeta)) ∧
      HQVM_lapse Φ (timeAngleBudgetScaleN n) t = 1 + Φ + timeAngle (timeAngleBudgetScaleN n) t ∧
      H_of_phi (timeAngleBudgetScaleN n) = timeAngleBudgetScaleN n ∧
      G_eff (timeAngleBudgetScaleN n) = (timeAngleBudgetScaleN n) ^ alpha ∧
      (S_HQVM_grav (timeAngleBudgetScaleN n) rho_m rho_r = 0 ↔
        HQVM_Friedmann_eq (timeAngleBudgetScaleN n) rho_m rho_r) := by
  rcases timeAngleBudgetScale_feeds_HQVM_GR n Φ t rho_m rho_r with ⟨hlapse, hH, hG, hgrav, _⟩
  exact ⟨timeAngleBudgetTransportN_eq_exp_neg_div kappaBeta n, hlapse, hH, hG, hgrav⟩

/-- `available_modes / sphericalHarmonicCumulativeCount → 4` along `atTop` (discrete ↔ harmonic bridge). -/
theorem lightCone_discreteModes_shellToHarmonicLimit : ShellToHarmonicLimit :=
  shell_to_harmonic_limit_holds

/-- Constant scalar on `MaxwellQFTChart` ⇒ zero `coordsGradientComponents`; emergent O–Maxwell RHS matches `general`. -/
theorem lightCone_emergent_coordsField_constPhi_eq_general (J_src : Fin 8 → Fin 4 → ℝ) (r : ℝ)
    (c : MaxwellQFTChart) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_coordsField J_src (fun _ => r) c a ν =
      emergentMaxwellInhomogeneous_O_general J_src a ν :=
  emergent_coordsField_const_eq_general J_src r c a ν

/-- Minimal continuum axioms together with a proof witness for the shell/harmonic field. -/
structure LightConeFunctionalBridge where
  minimal : HorizonContinuumAxiomsMinimal
  /-- Discharges `minimal.shell_to_harmonic_limit` (typically from `shell_to_harmonic_limit_holds`). -/
  shellProof : minimal.shell_to_harmonic_limit

/-- The ratio scaffold + lattice microcausality witness from `HorizonLimitedRenormLocality`. -/
def LightConeFunctionalBridge.ratioWitnessBridge : LightConeFunctionalBridge where
  minimal := horizonContinuumAxiomsMinimal_ratioWitness
  shellProof := shell_to_harmonic_limit_holds

/-- Light-cone bridge witness using Minkowski interval microcausality and doubled time-angle budget transport. -/
def LightConeFunctionalBridge.timeAngleBudgetWitnessBridge : LightConeFunctionalBridge where
  minimal :=
    { shell_to_harmonic_limit := ShellToHarmonicLimit
      renormalization_in_domain := RenormalizationInDomainStatement
      microcausality_in_domain := microcausality_in_domain_minkowski_interval_scaffold
      cluster_decomposition_in_domain :=
        Hqiv.QM.ClusterDecompositionStatement (clusterCorrelationDirectionalMonogamyTimeAngleBudget 1 1)
      scattering_consistency_in_domain := ScatteringConsistencyStatement scatteringChannelZero }
  shellProof := shell_to_harmonic_limit_holds

/-- `ratioWitnessBridge.shellProof` is definitionally the discrete-mode limit (`lightCone_discreteModes_shellToHarmonicLimit`). -/
theorem lightCone_ratioWitnessBridge_shellProof_eq_discreteLimit :
    LightConeFunctionalBridge.ratioWitnessBridge.shellProof = lightCone_discreteModes_shellToHarmonicLimit :=
  rfl

theorem lightCone_timeAngleBudgetWitnessBridge_cluster :
    LightConeFunctionalBridge.timeAngleBudgetWitnessBridge.minimal.cluster_decomposition_in_domain :=
  cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one

/-- Feed a bridge + proofs of the other minimal slots into `horizon_continuum_closure_minimal_HQIV`. -/
theorem LightConeFunctionalBridge.toContinuumClosureHQIV (b : LightConeFunctionalBridge)
    (hRenorm : b.minimal.renormalization_in_domain)
    (hMicro : b.minimal.microcausality_in_domain)
    (hCluster : b.minimal.cluster_decomposition_in_domain)
    (hScatter : b.minimal.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV b.minimal b.shellProof hRenorm hMicro hCluster hScatter

/-- Finite Born/kernel layer + continuum closure: same as `horizon_qm_qft_full_package_minimal_HQIV`
    with `A` and `hShell` taken from the bridge. -/
theorem LightConeFunctionalBridge.toFullPackageMinimalHQIV (b : LightConeFunctionalBridge)
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (hRenorm : b.minimal.renormalization_in_domain)
    (hMicro : b.minimal.microcausality_in_domain)
    (hCluster : b.minimal.cluster_decomposition_in_domain)
    (hScatter : b.minimal.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
      (normSq ψ
          = redshiftedEnergyN (normSq (collapseTo i ψ))
              (birefringenceRedshiftN betaRad kappaBeta)
              * Real.exp (betaRad / kappaBeta)
            + auxTransferForOutcome i ψ) ∧
      HorizonContinuumClosureStatementCoreHQIV :=
  horizon_qm_qft_full_package_minimal_HQIV ψ hψ κ i betaRad kappaBeta b.minimal b.shellProof hRenorm hMicro
    hCluster hScatter

/-- Full package with `ratioWitnessBridge` (structured renorm/cluster/scattering; lattice microcausality). -/
theorem lightConeMaxwellQFT_fullPackage_ratioWitness
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
      (normSq ψ
          = redshiftedEnergyN (normSq (collapseTo i ψ))
              (birefringenceRedshiftN betaRad kappaBeta)
              * Real.exp (betaRad / kappaBeta)
            + auxTransferForOutcome i ψ) ∧
      HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toFullPackageMinimalHQIV LightConeFunctionalBridge.ratioWitnessBridge ψ hψ κ i
    betaRad kappaBeta renormalization_in_domain_discreteUV_holds microcausality_in_domain_free_lattice_holds
    cluster_decomposition_zero_kernel_holds scattering_consistency_zero_channel_holds

/-- Same proof as applying `horizon_qm_qft_full_package_minimal_HQIV` to `horizonContinuumAxiomsMinimal_ratioWitness`. -/
theorem lightConeMaxwellQFT_fullPackage_ratioWitness_eq {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    lightConeMaxwellQFT_fullPackage_ratioWitness ψ hψ κ i betaRad kappaBeta =
      horizon_qm_qft_full_package_minimal_HQIV ψ hψ κ i betaRad kappaBeta horizonContinuumAxiomsMinimal_ratioWitness
        shell_to_harmonic_limit_holds renormalization_in_domain_discreteUV_holds
        microcausality_in_domain_free_lattice_holds cluster_decomposition_zero_kernel_holds
        scattering_consistency_zero_channel_holds :=
  rfl

/-- Same conclusion as `continuum_many_body_closure_ratioWitness_trivialRest`, reachable from Physics
    via `LightConeFunctionalBridge` (structured renorm/cluster/scattering; lattice microcausality). -/
theorem lightConeMaxwellQFT_continuumClosure_ratioWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toContinuumClosureHQIV LightConeFunctionalBridge.ratioWitnessBridge
    renormalization_in_domain_discreteUV_holds microcausality_in_domain_free_lattice_holds
    cluster_decomposition_zero_kernel_holds scattering_consistency_zero_channel_holds

/-- Continuum closure with interval-max microcausality and doubled time-angle budget transport. -/
theorem lightConeMaxwellQFT_continuumClosure_timeAngleBudgetWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toContinuumClosureHQIV LightConeFunctionalBridge.timeAngleBudgetWitnessBridge
    renormalization_in_domain_discreteUV_holds microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one)
    scattering_consistency_zero_channel_holds

/-- Full package with interval-max microcausality and doubled time-angle budget transport. -/
theorem lightConeMaxwellQFT_fullPackage_timeAngleBudgetWitness
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
      (normSq ψ
          = redshiftedEnergyN (normSq (collapseTo i ψ))
              (birefringenceRedshiftN betaRad kappaBeta)
              * Real.exp (betaRad / kappaBeta)
            + auxTransferForOutcome i ψ) ∧
      HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toFullPackageMinimalHQIV LightConeFunctionalBridge.timeAngleBudgetWitnessBridge
    ψ hψ κ i betaRad kappaBeta renormalization_in_domain_discreteUV_holds
    microcausality_in_domain_minkowski_interval_scaffold_holds
    (cluster_decomposition_directional_monogamy_timeAngleBudget_holds 1 1 zero_lt_one)
    scattering_consistency_zero_channel_holds

/-- The bridge theorem is definitionally the same proof as `continuum_many_body_closure_ratioWitness_trivialRest`. -/
theorem lightConeMaxwellQFT_continuumClosure_ratioWitness_eq :
    lightConeMaxwellQFT_continuumClosure_ratioWitness =
      continuum_many_body_closure_ratioWitness_trivialRest :=
  rfl

end Hqiv.Physics
