import Hqiv.Physics.DynamicBBNBaryogenesis
import Hqiv.Physics.NuclearCausticBinding
import Hqiv.Physics.NuclearCurvatureBinding
import Hqiv.Physics.NeutronBindingStabilityScaffold
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ComptonIRWindow
import Hqiv.Geometry.AlphaGammaForcedByLattice
import Hqiv.Physics.HQIVNuclei

/-!
# Outside-curvature temperature dynamics (nuclear binding + β± slots)

Before a full `nucleon(p,n)` function, this module locks the **temperature-dependent
outside curvature** that weakens or deepens nucleon own-binding and outside caustics.

* **Release** — `bbnBindingReleaseFactor` at `T = T_Pl/ξ` (BBN / cooling).
* **Bonded deepen** — favorable inside/outside temperature balance deepens outside wells.
* **Free weaken** — sub-lock-in Ω readout weakens own binding (β− branch).

Inside trapped curvature (`nuclearInsideBindingAtShell`) stays the structural lock-in
spine; outside caustics and trace binding carry ξ.

Python: `scripts/hqiv_nuclear_outside_temperature_dynamics.py`.
-/

namespace Hqiv.Physics

open Hqiv
open ContinuousXiPath

noncomputable section

/-- Temperature at horizon coordinate ξ on the BBN ladder. -/
noncomputable def T_MeV_from_xi (ξ : ℝ) : ℝ := T_Pl_MeV / ξ

/-- Outside-curvature release factor at ξ (same as BBN binding release at T(ξ)). -/
noncomputable def outsideCurvatureReleaseFactor (ξ : ℝ) : ℝ :=
  bbnBindingReleaseFactor (T_MeV_from_xi ξ)

theorem outsideCurvatureReleaseFactor_pos (ξ : ℝ) :
    0 < outsideCurvatureReleaseFactor ξ := by
  unfold outsideCurvatureReleaseFactor
  exact bbnBindingReleaseFactor_pos (T_MeV_from_xi ξ)

/-- At lock-in calibration the outside release factor is unity (zero curvature slope). -/
def outsideCurvatureLockinCalibrated : Prop :=
  outsideCurvatureReleaseFactor xiLockin = 1

theorem outsideCurvatureLockinCalibrated_holds : outsideCurvatureLockinCalibrated := by
  unfold outsideCurvatureLockinCalibrated outsideCurvatureReleaseFactor T_MeV_from_xi
  exact bbnBindingReleaseFactor_at_xiLockin

/-- Ωₖ readout at ξ (continuous chart). -/
noncomputable def omegaReadoutAtXi (ξ : ℝ) : ℝ := omegaK_xi ξ

/-- Nucleon own-binding at ξ: composite trace × outside release (bonded lock-in spine). -/
noncomputable def nucleonOwnBindingAtXi (m : ℕ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  bbnNucleonTraceBinding m c * outsideCurvatureReleaseFactor ξ

/-- Outside caustic stack modulated by outside temperature at ξ. -/
noncomputable def nuclearOutsideCausticBindingAtXi
    (m : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearOutsideCausticBinding m A θ c * outsideCurvatureReleaseFactor ξ

/-- Cluster binding at ξ: inside structural + outside caustics × release. -/
noncomputable def nuclearClusterBindingAtXi
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  nuclearInsideBindingAtShell m m_cluster A c +
    nuclearOutsideCausticBindingAtXi m A θ ξ c

theorem nuclearClusterBindingAtXi_add
    (m m_cluster : ℕ) (A : ℕ) (θ : ℝ) (ξ : ℝ) (c : ℝ) :
    nuclearClusterBindingAtXi m m_cluster A θ ξ c =
      nuclearInsideBindingAtShell m m_cluster A c +
        nuclearOutsideCausticBindingAtXi m A θ ξ c := by
  unfold nuclearClusterBindingAtXi
  ring

/-- β− overlap slot: isospin gap + free curvature deficit (scaffold). -/
noncomputable def betaMinusOverlapAtXi (ξ : ℝ) : ℝ :=
  freeNeutronOverlapEnergy (omegaReadoutAtXi ξ)

theorem betaMinusOverlap_eq_scaffold (ξ : ℝ) :
    betaMinusOverlapAtXi ξ = freeNeutronOverlapEnergy (omegaK_xi ξ) := rfl

/-- Bonded stability predicate (well + shared binding; skew slot open). -/
def bondedNuclearStableAtXi (wellDepth : ℝ) (ξ : ℝ) : Prop :=
  0 < wellDepth + nucleonOwnBindingAtXi referenceM ξ

/-- Dimensionless gravitational potential slot `ε = GM/(Rc²)` for outside support. -/
structure OutsideGravityWitness where
  phiEpsilon : ℝ

/-- One additive layer of the weak-field binding stack (Earth, Sun, Galaxy, …). -/
structure OutsideGravityLayerWitness where
  label : String
  phiEpsilon : ℝ

/-- Sum of weak-field binding layers booked into the outside channel. -/
noncomputable def outsideGravityPhiSum (layers : List OutsideGravityLayerWitness) : ℝ :=
  (layers.map fun g => g.phiEpsilon).sum

/-- Molecular host binding inherited by one nucleus (bond-state network contact share). -/
structure OutsideMolecularWitness where
  hostLabel : String
  phiEpsilon : ℝ

/-- Outside support from local gravity via `G_eff(1+ε)` (`HQVMetric.G_eff`, α = 3/5). -/
noncomputable def outsideGravityGeffModulator (g : OutsideGravityWitness) : ℝ :=
  if g.phiEpsilon ≤ 0 then 1
  else 1 + gamma_HQIV * ((1 + g.phiEpsilon) ^ alpha - 1)

/-- β± channel tag (structural; weak widths separate). -/
inductive BetaDecayChannel
  | betaMinus
  | betaPlus
  deriving DecidableEq, Repr

/-! ## Local curvature neutrino opacity (weak-width catalysis slot)

Same ``B_curv`` / outside ``G_eff`` stack as bound-state readouts.  Effective opacity
dresses the relic neutrino bath at OOM ``(1/s)⁴ ≈ 3.8×10⁸`` barn (``s = 1/140``).
Weak width receives a fractional catalysis booked through monogamy participation only.
-/

/-- Effective relic-neutrino opacity (barn OOM witness). -/
noncomputable def localCurvatureNeutrinoOpacityBarn (ξ φ : ℝ) : ℝ :=
  (1 / outerHorizonNeutrinoSuppression) ^ 4 *
    tuftCurvatureBudgetAtXi ξ *
    outsideGravityGeffModulator ⟨φ⟩

theorem localCurvatureNeutrinoOpacityBarn_lockin_zeroGravity :
    localCurvatureNeutrinoOpacityBarn xiLockin 0 = (140 : ℝ) ^ 4 := by
  unfold localCurvatureNeutrinoOpacityBarn outsideGravityGeffModulator
  rw [outerHorizonNeutrinoSuppression_eq_inv_140, tuftCurvatureBudgetAtXi_at_lockin]
  norm_num

/-- Additive catalysis fraction on weak β width (central slot). -/
noncomputable def localCurvatureWeakWidthCatalysis (ξ φ : ℝ) : ℝ :=
  let s := outerHorizonNeutrinoSuppression
  let lockin := gamma_HQIV ^ 2 * (1 - s) * (1 - gamma_HQIV / 5) * strongChannelFraction
  let imprint := max 0 (tuftCurvatureBudgetAtXi ξ * outsideGravityGeffModulator ⟨φ⟩ - 1)
  lockin * (1 + imprint / max lockin 1e-30)

noncomputable def localCurvatureWeakWidthFactor (ξ φ : ℝ) : ℝ :=
  1 + localCurvatureWeakWidthCatalysis ξ φ

/-- Monogamy envelope ``±γ/5`` on catalysis (low / high width factors). -/
noncomputable def localCurvatureWeakWidthFactorLow (ξ φ : ℝ) : ℝ :=
  let c := localCurvatureWeakWidthCatalysis ξ φ
  1 + c / (1 + gamma_HQIV / 5)

noncomputable def localCurvatureWeakWidthFactorHigh (ξ φ : ℝ) : ℝ :=
  let c := localCurvatureWeakWidthCatalysis ξ φ
  1 + c * (1 + gamma_HQIV / 5)

/-!
## Outside-curvature binding modulator (Python `outside_curvature_binding_modulator`)

Bonded branch deepens wells when inside/outside temperature balance favors closure;
free branch weakens when Ω readout drops below lock-in. Unity at `ξ_lock`.
-/

/-- Chart background temperature `T_bg = 1/ξ` on the dimensionless ladder. -/
noncomputable def chartBackgroundTemperatureAtXi (ξ : ℝ) : ℝ :=
  if 0 < ξ then 1 / ξ else 0

/-- Inner trapped contact temperature at ξ. -/
noncomputable def effectiveInsideTemperatureAtXi (ξ : ℝ) : ℝ :=
  chartBackgroundTemperatureAtXi ξ / max (tuftInnerTrappingAtXi ξ) 1e-30

/-- Outer T13-suppressed temperature at ξ. -/
noncomputable def effectiveOutsideTemperatureAtXi (ξ : ℝ) : ℝ :=
  chartBackgroundTemperatureAtXi ξ * t13_outer_suppression_at_xi ξ

/-- Log inside/outside balance driving bonded deepening. -/
noncomputable def outsideTemperatureBalanceAtXi (ξ : ℝ) : ℝ :=
  Real.log (effectiveInsideTemperatureAtXi ξ / max (effectiveOutsideTemperatureAtXi ξ) 1e-30)

/-- Bonded outside-curvature modulator (deepen branch). -/
noncomputable def outsideCurvatureBindingModulatorBonded (ξ : ℝ) : ℝ :=
  let release := outsideCurvatureReleaseFactor ξ
  let omega_norm := omegaReadoutAtXi ξ / max (omegaReadoutAtXi xiLockin) 1e-30
  let balance := outsideTemperatureBalanceAtXi ξ
  release * (1 + gamma_HQIV * max 0 balance * omega_norm)

/-- Free outside-curvature modulator (β− weakening branch). -/
noncomputable def outsideCurvatureBindingModulatorFree (ξ : ℝ) : ℝ :=
  let release := outsideCurvatureReleaseFactor ξ
  let omega_norm := omegaReadoutAtXi ξ / max (omegaReadoutAtXi xiLockin) 1e-30
  let deficit := max 0 (1 - omega_norm)
  let hot_release_penalty := gamma_HQIV * (1 - release)
  let sub_lock_penalty := gamma_HQIV * deficit
  let weaken := 1 - hot_release_penalty - sub_lock_penalty
  release * max weaken 0

/-- Unified bonded/free outside modulator (off-lock-in chart extension).

At `ξ = ξ_lock` Python applies an explicit unity readout before this formula;
see `outsideCurvatureBindingModulatorLockinReadout`.
-/
noncomputable def outsideCurvatureBindingModulatorChart (ξ : ℝ) (bonded : Bool) : ℝ :=
  if bonded then outsideCurvatureBindingModulatorBonded ξ
  else outsideCurvatureBindingModulatorFree ξ

/-- Lock-in calibration row (Python short-circuit at `XI_LOCKIN`). -/
def outsideCurvatureBindingModulatorLockinReadout : ℝ := 1

theorem outsideCurvatureBindingModulatorLockinReadout_eq_one :
    outsideCurvatureBindingModulatorLockinReadout = 1 := rfl

/-- Combined temperature + gravity outside modulator (Python ``outside_environment_modulator``). -/
noncomputable def outsideEnvironmentModulator
    (ξ : ℝ) (bonded : Bool) (g : OutsideGravityWitness) : ℝ :=
  outsideCurvatureBindingModulatorChart ξ bonded * outsideGravityGeffModulator g

theorem outsideEnvironmentModulator_gravity_identity
    (ξ : ℝ) (bonded : Bool) :
    outsideEnvironmentModulator ξ bonded ⟨0⟩ =
      outsideCurvatureBindingModulatorChart ξ bonded := by
  unfold outsideEnvironmentModulator outsideGravityGeffModulator
  simp

theorem outsideEnvironmentModulator_gravity_nonneg
    (ξ : ℝ) (bonded : Bool) (g : OutsideGravityWitness)
    (htemp : 0 ≤ outsideCurvatureBindingModulatorChart ξ bonded)
    (hgrav : 0 ≤ outsideGravityGeffModulator g) :
    0 ≤ outsideEnvironmentModulator ξ bonded g := by
  unfold outsideEnvironmentModulator
  exact mul_nonneg htemp hgrav

/-!
## Bond-corridor relic-ν dress (covalent monogamy axis)

Interior nuclear wells shield bulk relic-bath catalysis; the shared bond axis leaks
with aperture ``2η s`` where ``η = θ/phaseTheta`` and ``s = outerHorizonNeutrinoSuppression``.
-/

/-- Linear Compton IR participation clamped to the unit window. -/
noncomputable def bondCorridorEtaLinear (η : ℝ) : ℝ := max 0 (min η 1)

/-- Axial corridor aperture ``2η s`` on a covalent bond contact. -/
noncomputable def bondCorridorAperture (η : ℝ) : ℝ :=
  2 * bondCorridorEtaLinear η * outerHorizonNeutrinoSuppression

theorem bondCorridorAperture_eq_two_eta_over_140
    (η : ℝ) (hη : 0 ≤ η ∧ η ≤ 1) :
    bondCorridorAperture η = 2 * η / 140 := by
  unfold bondCorridorAperture bondCorridorEtaLinear
  rw [outerHorizonNeutrinoSuppression_eq_inv_140]
  simp [hη.1, hη.2]
  ring

theorem bondCorridorAperture_nonneg (η : ℝ) : 0 ≤ bondCorridorAperture η := by
  unfold bondCorridorAperture bondCorridorEtaLinear
  have hs : 0 ≤ outerHorizonNeutrinoSuppression := le_of_lt outerHorizonNeutrinoSuppression_pos
  have hclamp : 0 ≤ max 0 (min η 1) := le_max_left 0 (min η 1)
  nlinarith [hs, hclamp]

theorem bondCorridorAperture_le_two_suppression (η : ℝ) :
    bondCorridorAperture η ≤ 2 * outerHorizonNeutrinoSuppression := by
  unfold bondCorridorAperture bondCorridorEtaLinear
  have hs : 0 ≤ outerHorizonNeutrinoSuppression := le_of_lt outerHorizonNeutrinoSuppression_pos
  have hclamp : 0 ≤ max 0 (min η 1) := le_max_left 0 (min η 1)
  have hη : max 0 (min η 1) ≤ 1 := by
    rw [max_le_iff]
    constructor
    · norm_num
    · exact min_le_right η 1
  nlinarith [hs, hclamp, hη]

/-- Partial relic-bath dress on bonded covalent observables. -/
noncomputable def bondCorridorNeutrinoDress (ξ φ η : ℝ) : ℝ :=
  1 + localCurvatureWeakWidthCatalysis ξ φ * bondCorridorAperture η

theorem bondCorridorNeutrinoDress_eq_one_when_eta_zero (ξ φ : ℝ) :
    bondCorridorNeutrinoDress ξ φ 0 = 1 := by
  unfold bondCorridorNeutrinoDress bondCorridorAperture bondCorridorEtaLinear
  simp

theorem localCurvatureWeakWidthCatalysis_nonneg (ξ φ : ℝ) :
    0 ≤ localCurvatureWeakWidthCatalysis ξ φ := by
  unfold localCurvatureWeakWidthCatalysis
  have hlock :
      0 <
        gamma_HQIV ^ 2 * (1 - outerHorizonNeutrinoSuppression) * (1 - gamma_HQIV / 5) *
          strongChannelFraction := by
    rw [gamma_forced_two_fifths, outerHorizonNeutrinoSuppression_eq_inv_140]
    unfold strongChannelFraction
    norm_num
  have hlock' :
      0 ≤
        gamma_HQIV ^ 2 * (1 - outerHorizonNeutrinoSuppression) * (1 - gamma_HQIV / 5) *
          strongChannelFraction := le_of_lt hlock
  have hbracket :
      0 ≤
        1 +
          max 0 (tuftCurvatureBudgetAtXi ξ * outsideGravityGeffModulator { phiEpsilon := φ } - 1) /
            max
              (gamma_HQIV ^ 2 * (1 - outerHorizonNeutrinoSuppression) * (1 - gamma_HQIV / 5) *
                strongChannelFraction)
              1e-30 := by
    have hden :
        0 <
          max
            (gamma_HQIV ^ 2 * (1 - outerHorizonNeutrinoSuppression) * (1 - gamma_HQIV / 5) *
              strongChannelFraction)
            1e-30 := (lt_max_iff).mpr (Or.inl hlock)
    have hone : (0 : ℝ) ≤ 1 := by norm_num
    apply add_nonneg hone
    apply div_nonneg (le_max_left _ _) (le_of_lt hden)
  exact mul_nonneg hlock' hbracket

theorem bondCorridorNeutrinoDress_ge_one (ξ φ η : ℝ) :
    1 ≤ bondCorridorNeutrinoDress ξ φ η := by
  unfold bondCorridorNeutrinoDress
  linarith [mul_nonneg (localCurvatureWeakWidthCatalysis_nonneg ξ φ) (bondCorridorAperture_nonneg η)]

/-- Compton θ maps to corridor aperture through ``phaseParticipationEta``. -/
theorem bondCorridorAperture_from_theta
    (θ : ℝ) (hθ : 0 ≤ θ) (hθb : θ ≤ phaseTheta) :
    bondCorridorAperture (phaseParticipationEta θ) =
      2 * (phaseParticipationEta θ) * outerHorizonNeutrinoSuppression := by
  unfold bondCorridorAperture bondCorridorEtaLinear phaseParticipationEta
  have hη : 0 ≤ θ / phaseTheta := div_nonneg hθ (le_of_lt phaseTheta_pos)
  have hηb : θ / phaseTheta ≤ 1 := by
    rw [div_le_one phaseTheta_pos]
    exact hθb
  simp [hη, hηb]

end

end Hqiv.Physics
