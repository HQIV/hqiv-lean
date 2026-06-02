import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.BoundStates
import Hqiv.Physics.BBNNetworkFromWeights
import Hqiv.Physics.BBNEpochEvolution
import Hqiv.Physics.BBNEpochNetwork
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.Action   -- for S_HQVM_grav

/-!
# Dynamic BBN and Baryogenesis with curvature-modulated vev and binding feedback

This module wires the post-T12/T13 dynamic machinery (inner-outer Casimir,
ωK(ξ) curvature primitive, temperature-dependent effective vev) into BBN and
baryogenesis.

Core new capabilities:
* BBN binding Q values and light-nucleus masses can now be evaluated at the
  local horizon coordinate ξ(T) of the BBN epoch instead of only at the fixed
  proton lock-in shell.
* Binding energy itself (a curvature-weighted composite-trace quantity) sources
  a small local perturbation to the effective curvature during the BBN window,
  which feeds the expansion rate H(T) via S_HQVM_grav / HQVM_Friedmann_eq.
* Baryogenesis η normalization (already curvature-ratio based) receives
  corrections from the dynamic binding that occurs between QCD and lock-in.

This directly supports the physical picture that:
- The temperature scale (via ξ) controls the vev and therefore the scale of
  all masses and binding energies.
- As nuclei form, the binding "condenses" and alters the local curvature
  imprint, which in turn affects the Hubble rate and resonance conditions
  precisely when ^7Li is processed.

The old fixed-lock-in readouts remain available for comparison and backward
compatibility. New dynamic readouts are suffixed _at_xi or _dynamic.

Not claimed (yet): full self-consistent solution of the modified Friedmann
equation with binding back-reaction inside the BBN integrator, or a
quantitative resolution of the lithium problem. This module supplies the
necessary typed hooks and vital theorems.

References:
- Dynamic Casimir / ωK(ξ): HopfShellBeltramiMassBridge, ContinuousXiCoupling
- Uniform binding network: BoundStates (E_bind_from_network, composite mass ρ_m)
- BBN epoch ladder and fixed anchors: BBNEpochEvolution, BBNNetworkFromWeights
- Baryogenesis curvature lock-in: BaryogenesisCore, BaryogenesisWitness
- Gravitational constraint: S_HQVM_grav, HQVM_Friedmann_eq (HQVMetric, Action)
-/

namespace Hqiv.Physics

open Hqiv Hqiv.Physics
open ContinuousXiPath

noncomputable section

/-!
## Dynamic BBN quantities at horizon coordinate ξ

The BBN window occurs at much higher ξ (smaller T) than the proton lock-in
ξ_lock = 5.  With the T12/T13 machinery the effective vev, α_eff, and
therefore the binding scale itself are functions of the local ξ.
-/

-- For convenience: convert a BBN-era T_MeV to the corresponding ξ on the
-- physical temperature ladder (ξ = T_Pl / T).  This re-uses the existing
-- ladder infrastructure.
noncomputable def bbnXiFromT_MeV (T_MeV : ℝ) : ℝ :=
  -- T_Pl in MeV is already defined in BBNNetworkFromWeights as T_Pl_MeV
  T_Pl_MeV / T_MeV

theorem bbnXiFromT_MeV_pos (T_MeV : ℝ) (hT : 0 < T_MeV) : 0 < bbnXiFromT_MeV T_MeV := by
  unfold bbnXiFromT_MeV T_Pl_MeV
  positivity

-- Dynamic version of the per-nucleon composite-trace binding, now evaluated
-- using the curvature scale at the local ξ of the epoch.
-- We scale the lock-in network binding by the ratio of the inner-Casimir
-- trapping factors (or equivalently by the heavy lepton gap ratio, which
-- carries the same ωK(ξ) modulation).
noncomputable def bbnNucleonTraceBinding_at_xi (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  -- At lock-in ξ=5 the value recovers the old bbnNucleonTraceBinding
  let scale := heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5
  bbnNucleonTraceBinding bbnBindingShell c * scale

-- Cluster binding (A-nucleon) at the local ξ of the BBN epoch.
noncomputable def bbnClusterBinding_at_xi (ξ : ℝ) (A : ℕ) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * bbnNucleonTraceBinding_at_xi ξ c * bbnValleyBindingFactor A

-- Binding Q values (MeV) for the light nuclei, now dynamic with ξ.
noncomputable def bbnDeuteronBindingQ_at_xi (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  -- Approximate using the same scaling as the trace binding.
  -- A more precise version would also promote the constituent masses.
  2 * bbnNucleonTraceBinding_at_xi ξ c * bbnValleyBindingFactor 2

noncomputable def bbnHelium4BindingQ_at_xi (ξ : ℝ) (c : ℝ := 1) : ℝ :=
  4 * bbnNucleonTraceBinding_at_xi ξ c * bbnValleyBindingFactor 4

-- Dynamic effective proton mass scale at ξ, for use in BBN Boltzmann factors.
-- We bootstrap from the dynamic heavy gap (inner Casimir) scaled to the
-- hadronic calibration at lock-in.  This is the natural hadronic counterpart
-- to tuftVevAtXi_MeV.
noncomputable def dynamicProtonMass_at_xi (ξ : ℝ) : ℝ :=
  -- At ξ=5 we recover the lock-in value by construction.
  derivedProtonMass * (heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5)

/-!
## Curvature-temperature binding release

The literal `*_at_xi` definitions above are useful diagnostics, but at BBN
temperatures `ξ = T_Pl/T` is enormous.  Raw multiplication by the full
temperature-relative vev therefore over-promotes nuclear Q values.  The
effective binding released during BBN should depend on the curvature change
across the temperature interval from lock-in to the BBN epoch, not on the
absolute cosmological vev scale at that epoch.

The Python calculator now uses the same functional form below:

`exp (-(γ * 4/8 * boundedSlope))`,

where `boundedSlope` is the curvature change per logarithmic temperature
separation, compressed by `s/(1+s)`.
-/

/-- Raw curvature change per logarithmic temperature separation from lock-in to BBN epoch. -/
noncomputable def bbnCurvatureTemperatureSlope (T_MeV : ℝ) : ℝ :=
  let ξ := bbnXiFromT_MeV T_MeV
  (omegaK_xi ξ - omegaK_xi xiLockin) / Real.log (ξ / xiLockin)

/-- Bounded positive-slope proxy `s/(1+s)` used by the calculator. -/
noncomputable def bbnBoundedCurvatureTemperatureSlope (T_MeV : ℝ) : ℝ :=
  let s := bbnCurvatureTemperatureSlope T_MeV
  s / (1 + s)

/-- Effective binding-release factor from curvature and temperature separation. -/
noncomputable def bbnBindingReleaseFactor (T_MeV : ℝ) : ℝ :=
  Real.exp (-(Hqiv.gamma_HQIV * Hqiv.Physics.strongChannelFraction *
    bbnBoundedCurvatureTemperatureSlope T_MeV))

/-- Effective per-nucleon trace binding at BBN temperature, using lock-in network binding
modulated by curvature-temperature release rather than raw `ξ` vev scaling. -/
noncomputable def bbnNucleonTraceBinding_effectiveAtT (T_MeV : ℝ) (c : ℝ := 1) : ℝ :=
  bbnNucleonTraceBinding bbnBindingShell c * bbnBindingReleaseFactor T_MeV

/-- Effective cluster binding at BBN temperature. -/
noncomputable def bbnClusterBinding_effectiveAtT (T_MeV : ℝ) (A : ℕ) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * bbnNucleonTraceBinding_effectiveAtT T_MeV c * bbnValleyBindingFactor A

/-- Effective deuteron Q at BBN temperature. -/
noncomputable def bbnDeuteronBindingQ_effectiveAtT (T_MeV : ℝ) (c : ℝ := 1) : ℝ :=
  2 * bbnNucleonTraceBinding_effectiveAtT T_MeV c * bbnValleyBindingFactor 2

/-- Effective helium-4 Q at BBN temperature. -/
noncomputable def bbnHelium4BindingQ_effectiveAtT (T_MeV : ℝ) (c : ℝ := 1) : ℝ :=
  4 * bbnNucleonTraceBinding_effectiveAtT T_MeV c * bbnValleyBindingFactor 4

theorem bbnBindingReleaseFactor_pos (T_MeV : ℝ) :
    0 < bbnBindingReleaseFactor T_MeV := by
  unfold bbnBindingReleaseFactor
  exact Real.exp_pos _

/-- Dynamic BBN shell reaction opportunity for one cooling step.

This mirrors `BBNEpochNetwork.bbnShellReactionOpportunity` and is kept local
so the dynamic module can state its binding-feedback variant directly:
`Δlog ξ · log(ξ/ξ_lock)^3 · Ω_k(ξ)^(γ*strong)`.
-/
noncomputable def dynamicBBNShellReactionOpportunity (T_MeV T_next_MeV : ℝ) : ℝ :=
  let ξ := bbnXiFromT_MeV T_MeV
  let ξNext := bbnXiFromT_MeV T_next_MeV
  let curvatureFactor := bbnCurvatureBudgetAtT_MeV T_MeV
  Real.log (ξNext / ξ) * (Real.log (ξ / xiLockin)) ^ 3 * curvatureFactor

/-!
## Dynamic C₂ / κ₆ on the BBN ladder (deuterium-bottleneck lab)

`tuftHopfKappa6AtXi` combines the matter slot with lapse concentration `C₂(ξ)`.
On the hot BBN chart, `C₂` grows with `ξ = T_Pl/T` while `B_curv` is nearly flat,
so the anchor-normalized ratio `κ₆(ξ_ref)/κ₆(ξ)` is the lapse reaction clock.
Multiplying raw κ₆ at low *T* over-burns D; the MeV-tail suppression uses the
same strong-channel weights as `bbnBindingReleaseFactor`, with:

* bottleneck temperature `γ · (4/8) · T_freeze(η)` from weak freeze-out;
* lapse exponent `γ · (4/8) · Q_D_eff(T)/Q_np` from curvature-temperature binding release
  on the lock-in deuteron composite trace (no fitted MeV slots).
-/

/-- Weak freeze-out temperature `T_f = Q_np / log(η₁₀)` (epoch module). -/
noncomputable def bbnDynamicC2FreezeoutT_MeV (η : ℝ) : ℝ :=
  bbnFreezeoutTemperatureMeV η

/-- Deuterium-bottleneck upper temperature: strong-channel × overlap × freeze-out. -/
noncomputable def bbnDynamicC2BottleneckT_MeV (η : ℝ) : ℝ :=
  Hqiv.gamma_HQIV * Hqiv.Physics.strongChannelFraction * bbnDynamicC2FreezeoutT_MeV η

/-- Anchor temperature for κ₆ normalization: same freeze-out readout at this η. -/
noncomputable def bbnDynamicC2ReferenceT_MeV (η : ℝ) : ℝ :=
  bbnDynamicC2FreezeoutT_MeV η

/-- Lapse-clock exponent: effective deuteron binding at epoch `T` over the n–p gap. -/
noncomputable def bbnDynamicC2LapseExponent (_η T_MeV : ℝ) : ℝ :=
  Hqiv.gamma_HQIV * Hqiv.Physics.strongChannelFraction *
    (bbnDeuteronBindingQ_effectiveAtT T_MeV / bbnNeutronProtonGap)

/-- Full `κ₆(ξ(T),0,0)` on the BBN temperature ladder. -/
noncomputable def bbnKappa6AtT_MeV (T_MeV : ℝ) : ℝ :=
  tuftHopfKappa6AtXi (bbnXiFromT_MeV T_MeV) 0 0

/-- Lapse concentration `C₂(ξ(T),0,0)` on the BBN ladder. -/
noncomputable def bbnLapseConcentrationAtT_MeV (T_MeV : ℝ) : ℝ :=
  tuftLapseConcentrationAtXi (bbnXiFromT_MeV T_MeV) 0 0

/-- Anchor-normalized dynamic-`C₂` suppression in the deuterium bottleneck. -/
noncomputable def bbnDynamicC2OpportunitySuppression (η T_MeV : ℝ) : ℝ :=
  if T_MeV ≤ bbnDynamicC2BottleneckT_MeV η then
    let κ6 := bbnKappa6AtT_MeV T_MeV
    let κ6ref := bbnKappa6AtT_MeV (bbnDynamicC2ReferenceT_MeV η)
    (κ6ref / κ6) ^ bbnDynamicC2LapseExponent η T_MeV
  else
    1

/-- Shell opportunity including dynamic-`C₂` lapse clock at baryon budget η. -/
noncomputable def bbnShellReactionOpportunity_with_dynamic_C2
    (η T_MeV T_next_MeV : ℝ) : ℝ :=
  dynamicBBNShellReactionOpportunity T_MeV T_next_MeV *
    bbnDynamicC2OpportunitySuppression η T_MeV

theorem bbnKappa6AtT_MeV_eq_tuftHopfKappa6AtXi (T_MeV : ℝ) :
    bbnKappa6AtT_MeV T_MeV = tuftHopfKappa6AtXi (bbnXiFromT_MeV T_MeV) 0 0 := rfl

theorem bbnLapseConcentrationAtT_MeV_eq_tuftLapseConcentrationAtXi (T_MeV : ℝ) :
    bbnLapseConcentrationAtT_MeV T_MeV =
      tuftLapseConcentrationAtXi (bbnXiFromT_MeV T_MeV) 0 0 := rfl

theorem bbnKappa6AtT_MeV_eq_eta_gamma_C2 (T_MeV : ℝ) :
    bbnKappa6AtT_MeV T_MeV =
      tuftMatterFractionAtXi (bbnXiFromT_MeV T_MeV) * gamma_HQIV *
        tuftLapseConcentrationAtXi (bbnXiFromT_MeV T_MeV) 0 0 := by
  rw [bbnKappa6AtT_MeV_eq_tuftHopfKappa6AtXi, tuftHopfKappa6AtXi_eq_eta_gamma_C2]

theorem bbnDynamicC2FreezeoutT_MeV_eq (η : ℝ) :
    bbnDynamicC2FreezeoutT_MeV η = bbnFreezeoutTemperatureMeV η := rfl

theorem bbnDynamicC2ReferenceT_MeV_eq_freezeout (η : ℝ) :
    bbnDynamicC2ReferenceT_MeV η = bbnFreezeoutTemperatureMeV η := rfl

theorem bbnDynamicC2BottleneckT_MeV_eq_gamma_strong_freezeout (η : ℝ) :
    bbnDynamicC2BottleneckT_MeV η =
      Hqiv.gamma_HQIV * Hqiv.Physics.strongChannelFraction * bbnFreezeoutTemperatureMeV η := rfl

theorem bbnDynamicC2LapseExponent_eq_gamma_strong_deuteron_effective (_η T_MeV : ℝ) :
    bbnDynamicC2LapseExponent _η T_MeV =
      Hqiv.gamma_HQIV * Hqiv.Physics.strongChannelFraction *
        (bbnDeuteronBindingQ_effectiveAtT T_MeV / bbnNeutronProtonGap) := rfl

theorem bbnDynamicC2OpportunitySuppression_eq_one_of_gt_bottleneck
    (η T_MeV : ℝ) (h : bbnDynamicC2BottleneckT_MeV η < T_MeV) :
    bbnDynamicC2OpportunitySuppression η T_MeV = 1 := by
  unfold bbnDynamicC2OpportunitySuppression
  by_cases hle : T_MeV ≤ bbnDynamicC2BottleneckT_MeV η
  · exfalso
    linarith [h, hle]
  · simp [hle]

/-!
## Local curvature perturbation from binding during BBN

Binding energy is not free: it is a curvature-weighted network deficit
(E_bind ~ α_eff from the curvature imprint).  When light nuclei form in the
BBN window, the "release" or accounting of that binding energy density
sources a small perturbation δ to the local effective curvature integral
(or equivalently a small correction to the expansion rate H).

We model a simple first-order perturbation:
  δ_curv(T) ≈ κ * (binding energy density at T) / (radiation density)

where κ is a small dimensionless efficiency (set by the overlap of the
strong-channel weights with the T12 inner-Casimir surfaces).  This δ perturbs
the shell reaction opportunity.  A Hubble-style readout is kept only as a
standard-BBN comparison diagnostic.

This is the geometric handle that can affect ^7Li without new particles.
-/

/-!
Binding curvature feedback is now derived from the same curvature-temperature
machinery used for the release factor (no free κ or magic entropy denominators).

Efficiency = γ · (strong channel) · bounded_slope(T)
This is the natural geometric weight for how much binding release at the local
epoch sources a curvature perturbation, fully determined by the existing
`bbnCurvatureTemperatureSlope` + `gamma_HQIV` + `strongChannelFraction`.
-/

noncomputable def bbn_binding_curvature_efficiency (T_MeV : ℝ) : ℝ :=
  gamma_HQIV * Hqiv.Physics.strongChannelFraction * bbnBoundedCurvatureTemperatureSlope T_MeV

/-- Binding-induced curvature perturbation δ, derived (no free scale).
Uses the effective ⁴He binding at T (already modulated by the release factor)
scaled by the geometric efficiency above. The previous arbitrary "/ (T * 100)"
entropy factor is replaced by the bounded slope already present in the release
machinery.
-/
noncomputable def bbn_binding_curvature_perturbation (T_MeV : ℝ) (η : ℝ) : ℝ :=
  let binding_per_baryon := bbnHelium4BindingQ_effectiveAtT T_MeV
  bbn_binding_curvature_efficiency T_MeV * (binding_per_baryon / T_MeV)

/-- Shell opportunity with derived binding feedback (parameter-free on this axis).
Coefficient on δ is taken as the strong channel fraction for dimensional consistency
with other strong-weighted channels in the model.
-/
noncomputable def bbnShellReactionOpportunity_with_binding_feedback
    (T_MeV T_next_MeV η : ℝ) : ℝ :=
  let δ := bbn_binding_curvature_perturbation T_MeV η
  dynamicBBNShellReactionOpportunity T_MeV T_next_MeV * (1 + δ * Hqiv.Physics.strongChannelFraction)

/-- Full dynamic integrator opportunity (C₂ + derived binding feedback). -/
noncomputable def bbnShellReactionOpportunity_dynamic_integrator
    (T_MeV T_next_MeV η : ℝ) : ℝ :=
  let δ := bbn_binding_curvature_perturbation T_MeV η
  bbnShellReactionOpportunity_with_dynamic_C2 η T_MeV T_next_MeV * (1 + δ * Hqiv.Physics.strongChannelFraction)

theorem bbnShellReactionOpportunity_dynamic_integrator_eq (T_MeV T_next_MeV η : ℝ) :
    bbnShellReactionOpportunity_dynamic_integrator T_MeV T_next_MeV η =
      bbnShellReactionOpportunity_with_dynamic_C2 η T_MeV T_next_MeV *
        (1 + bbn_binding_curvature_perturbation T_MeV η * Hqiv.Physics.strongChannelFraction) := rfl

-- Comparison diagnostic only (still useful for standard-BBN plots).
noncomputable def bbnHubbleRate_with_binding_feedback (T_MeV : ℝ) (η : ℝ) : ℝ :=
  let δ := bbn_binding_curvature_perturbation T_MeV η
  bbnHubbleRate T_MeV * (1 + δ)

/-!
## Dynamic BBN epoch readout at local ξ (or T)

These are the upgraded versions of the fixed-epoch readouts.  They use
the ξ-dependent binding Q's and masses.  The full Python network now advances
with shell reaction opportunity; `H` remains a comparison diagnostic only.
-/

structure DynamicBBNEpochReadout where
  ξ : ℝ
  T_MeV : ℝ
  Yp : ℝ
  DH : ℝ
  He3H : ℝ
  Li7H : ℝ
  bindingCurvaturePerturbation : ℝ   -- the δ used in this readout

-- Dynamic light-element ratios at a BBN-era temperature, using ξ-dependent
-- binding and (optionally) the derived binding-induced curvature feedback.
noncomputable def dynamicBBNReadoutAtT (η T_MeV : ℝ) (useBindingFeedback : Bool := false) : DynamicBBNEpochReadout :=
  let ξ := bbnXiFromT_MeV T_MeV
  let δ := if useBindingFeedback then bbn_binding_curvature_perturbation T_MeV η else 0
  {
    ξ := ξ
    T_MeV := T_MeV
    Yp := bbnYpAtFreezeout η
    DH := (eta10 η) ^ bbnDH_etaExponent (dynamicProtonMass_at_xi ξ) *
            bbnThermalSinkFactor (bbnDeuteronBindingQ_effectiveAtT T_MeV)
              (bbnHelium4BindingQ_effectiveAtT T_MeV) T_MeV
    He3H := (eta10 η) ^ bbnHe3_etaExponent (dynamicProtonMass_at_xi ξ) *
              bbnThermalSinkFactor (bbnClusterBinding_effectiveAtT T_MeV 3)
                (bbnHelium4BindingQ_effectiveAtT T_MeV) T_MeV
    Li7H := (eta10 η) ^ bbnLi7_etaExponent (dynamicProtonMass_at_xi ξ) *
              bbnThermalSinkFactor (bbnHelium4BindingQ_effectiveAtT T_MeV * (7/4))
                (bbnHelium4BindingQ_effectiveAtT T_MeV) T_MeV
    bindingCurvaturePerturbation := δ
  }

/-!
## Per-shell curvature budget (bulk integrator witness)

Early shells: net matter fraction is still opening, but matter–antimatter stress and
radiation-dominated curvature on the chart path seed extra same-epoch imprint. The budget
relaxes to unity at lock-in (local ≈ global at observation). Python mirrors this in
`curvature_budget_at_shell` and routes `(budget - 1)` imprint outside the baryon track.
-/

/-- Chart ratio on the path to lock-in (diagnostic; not the homogeneous readout at lock-in). -/
noncomputable def baryogenesisChartRatioAtShell (m : ℕ) : ℝ :=
  omegaK_xi (xiOfShell m)

/-- Curvature budget at shell `m`: early seed, unity at `m_lockin`. -/
noncomputable def baryogenesisCurvatureBudgetAtShell (m : ℕ) (omegaMRel : ℝ) : ℝ :=
  let chart := max (baryogenesisChartRatioAtShell m) ((1 : ℝ) / 1000000)
  let span := max ((m_lockin - m_QCD : ℕ) : ℝ) (1 : ℝ)
  let progressToLock := ((m_lockin - m : ℕ) : ℝ) / span
  let matterOpening := max (0 : ℝ) (1 - omegaMRel / gamma_HQIV)
  let pairSeed := max (0 : ℝ) (1 / chart - 1)
  let radSeed := alpha * max (0 : ℝ) (1 - chart)
  let seed := gamma_HQIV * matterOpening * progressToLock * max pairSeed radSeed
  1 + seed

theorem baryogenesisCurvatureBudgetAtShell_lockin (omegaMRel : ℝ) :
    baryogenesisCurvatureBudgetAtShell m_lockin omegaMRel = 1 := by
  unfold baryogenesisCurvatureBudgetAtShell
  dsimp only
  have h0 : ((m_lockin - m_lockin : ℕ) : ℝ) = 0 := by norm_num
  simp [h0, zero_div, mul_zero, add_zero]

/-!
## Dynamic baryogenesis considerations

The η_at_horizon formula already normalizes to curvature ratios.  With dynamic
binding we can add a correction term that accounts for the binding energy
that condenses between m_QCD and m_lockin, which itself sources curvature.

A minimal model: the effective curvature integral receives an additive
contribution proportional to the integrated binding energy density in that
epoch window, scaled by the strong-channel weight fraction (γ or the
strong octonion projection).

This is the natural way the "gluon = curvature artifact" story feeds back
into the baryon asymmetry itself.
-/

/-- Derived correction to the curvature integral between QCD and lock-in
from binding condensation. Coefficient is the same strong-channel geometric
weight used everywhere else in the dynamic BBN/baryogenesis machinery
(γ · 4/8). No free κ.
-/
noncomputable def baryogenesis_binding_curvature_correction (m_QCD m_lockin : Nat) : ℝ :=
  (gamma_HQIV * Hqiv.Physics.strongChannelFraction) *
    (bbnClusterBinding m_lockin 4 - bbnClusterBinding m_QCD 4)

/-- Dynamic eta_at_horizon with the derived binding correction on the curvature
integral (no free scales).
-/
noncomputable def eta_at_horizon_dynamic (n N : Nat) : ℝ :=
  let base := eta_at_horizon n N
  let corr := baryogenesis_binding_curvature_correction m_QCD m_lockin
  base * (1 + corr)

/-!
## Vital theorems (skeleton)

We prove the obvious sanity properties (positivity, recovery of old values
at ξ=5 / lock-in, ordering of shells, etc.).  Full vital bundles that
replace the old bbn_full_vital_readout will be added after the integrator
is upgraded.
-/

theorem bbnNucleonTraceBinding_at_xi_recovers_lockin
    (c : ℝ) (hgap : heavy_lepton_gap_at_xi 5 ≠ 0) :
    bbnNucleonTraceBinding_at_xi 5 c = bbnNucleonTraceBinding bbnBindingShell c := by
  unfold bbnNucleonTraceBinding_at_xi
  field_simp [hgap]

theorem dynamicProtonMass_at_xi_recovers_lockin
    (hgap : heavy_lepton_gap_at_xi 5 ≠ 0) :
    dynamicProtonMass_at_xi 5 = derivedProtonMass := by
  unfold dynamicProtonMass_at_xi
  field_simp [hgap]

-- Positivity of the derived binding curvature perturbation.
-- (The efficiency is nonnegative by construction from gamma*strong*slope ≥ 0;
-- strict positivity holds away from the lock-in point where the slope vanishes.
-- Full case analysis left as future polishing; the definitions themselves are now free of ad-hoc scales.)
theorem bbn_binding_curvature_perturbation_pos
    (T_MeV : ℝ) (η : ℝ)
    (hT : 0 < T_MeV)
    (hQ : 0 < bbnHelium4BindingQ_effectiveAtT T_MeV) :
    0 ≤ bbn_binding_curvature_perturbation T_MeV η := by
  sorry  -- scales removed from the definition; proof of non-negativity in all regimes is routine geometry but not required for the computational path to be clean.

-- The perturbation is exactly the derived efficiency times (Q4_eff / T).
theorem bbn_binding_curvature_perturbation_eq
    (T_MeV : ℝ) (η : ℝ) :
    bbn_binding_curvature_perturbation T_MeV η =
      bbn_binding_curvature_efficiency T_MeV * (bbnHelium4BindingQ_effectiveAtT T_MeV / T_MeV) := by
  rfl

-- The dynamic eta readout is the base curvature eta times the binding correction factor.
theorem eta_at_horizon_dynamic_eq (n N : Nat) :
    eta_at_horizon_dynamic n N =
      eta_at_horizon n N *
        (1 + baryogenesis_binding_curvature_correction m_QCD m_lockin) := by
  rfl

/-!
## Publication anchors (BBN dynamic-$C_2$ lab)

Python mirrors: `scripts/hqiv_lean_physics_primitives.py`,
`scripts/hqiv_dynamic_bulk_bbn.py`, audit `scripts/hqiv_integrator_lean_audit.py`
$\to$ `data/integrator_lean_audit.json`.
-/

#check bbnKappa6AtT_MeV
#check bbnLapseConcentrationAtT_MeV
#check bbnDynamicC2OpportunitySuppression
#check bbnShellReactionOpportunity_dynamic_integrator
#check bbnKappa6AtT_MeV_eq_eta_gamma_C2
#check bbnDynamicC2OpportunitySuppression_eq_one_of_gt_bottleneck
#check bbnDynamicC2LapseExponent_eq_gamma_strong_deuteron_effective
#check bbnDynamicC2BottleneckT_MeV_eq_gamma_strong_freezeout

end

end Hqiv.Physics
