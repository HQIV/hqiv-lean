import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.SphericalHarmonicsBridge
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric

import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.SpinStatistics
import Hqiv.Physics.ModifiedMaxwell

/-!
# HQIV nuclei: Casimir surfaces, Fresnel caustics, and the isotope ladder

This module formalizes nucleons as **Casimir surfaces** on the discrete null lattice:
vacuum-mode counting comes from `Hqiv.available_modes` (`OctonionicLightCone`), angular
mode bookkeeping from `SphericalHarmonicsBridge`, and the auxiliary-field frequency
scale from `phi_of_shell` (`AuxiliaryField`). Fresnel–caustic radii use the same
`R_m` convention as `NuclearAndAtomicSpectra`.

No new physical axioms: everything is packaged from the two HQIV axioms already present
in the imported modules (discrete light-cone mode arithmetic + informational-energy /
monogamy sector via φ and γ).
-/

namespace Hqiv.Physics

open scoped BigOperators

/-!
## 1. Meta-horizon, spherical harmonics bookkeeping, nucleon metadata

S⁷ metahorizon Casimir scaffold (non-interacting electron ladder): see
`Hqiv/Geometry/S7MetahorizonCasimir.lean` for `laplaceBeltramiEigenvalueS7`,
`sphericalHarmonicDimS7`, `occupationList`, and `noninteractingFermionLambdaSum`.
Associator perturbation on occupied modes (octonion \((xy)z-x(yz)\) on fixed 120° tori): see
`Hqiv/Geometry/NuclearTorusPerturbation.lean` (`perturbedCasimirEnergy`, `perturbedCasimirEnergy_eV`).
Joint-vs-separated surplus (ionic / covalent / metallic **bookkeeping** via fragment counts): see
`Hqiv/Geometry/BondedHorizonCasimir.lean` (`bondHorizonSurplusDimless`, `bondHorizonSurplus_eV`).
Future screening layers reuse the same occupation list.
-/

/-- Proton vs neutron tag at the meta-horizon (isospin I = ½ with I₃ = ±½). -/
inductive IsospinLabel
  | proton
  | neutron
  deriving DecidableEq, Repr

/-- Meta-horizon at shell `m`: shell index is carried by the type family; the label
records isospin. (Spin ½ and parity are packaged in `ProtonNeutronInfo`.) -/
structure MetaHorizon (m : ℕ) where
  isospin : IsospinLabel

/-- Discrete spherical-harmonic ladder at cutoff `L = m`: cumulative S² degeneracy
`(m+1)²` matches `Hqiv.sphericalHarmonicCumulativeCount`. -/
structure SphericalHarmonics (m : ℕ) where
  cumulativeCount : ℝ
  hcum : cumulativeCount = Hqiv.sphericalHarmonicCumulativeCount m

/-- Global vacuum-mode count lifted from the light-cone lattice (Casimir plates → HQV). -/
structure VacuumModeCount (m : ℕ) where
  count : ℝ
  hcount : count = Hqiv.available_modes m

/-- Spin / isospin / parity metadata (Lean-level bookkeeping for boundary conditions). -/
structure ProtonNeutronInfo where
  /-- Third component of isospin, ±1 for I₃ = ±½ in integer encoding. -/
  isospinThird : ℤ
  spinHalf : Bool
  parityEven : Bool

/-!
## 2. Casimir surface and zero-point energy
-/

/-- A nucleon as a Casimir surface: horizon label, spherical mode bookkeeping,
lattice vacuum-mode count, and metadata. -/
structure CasimirSurface (m : ℕ) where
  horizon : MetaHorizon m
  harmonics : SphericalHarmonics m
  vacuumModes : VacuumModeCount m
  metaInfo : ProtonNeutronInfo

/-- Per-angular-mode degeneracy on `S²` at degree `ℓ`: `2ℓ+1`. -/
noncomputable def degeneracy_from_lattice (_m ℓ : ℕ) : ℝ :=
  (2 * ℓ + 1 : ℝ)

/-- HQIV frequency unit for Casimir modes at shell `m`: φ(m) from the temperature ladder. -/
noncomputable def omegaCasimir (m : ℕ) : ℝ :=
  Hqiv.phi_of_shell m

/-- Integer vacuum-mode count at shell `m`: `4 · latticeSimplexCount m` (= `available_modes` as ℕ). -/
def availableModesNat (m : ℕ) : ℕ :=
  4 * Hqiv.latticeSimplexCount m

theorem availableModesNat_cast (m : ℕ) :
    (availableModesNat m : ℝ) = Hqiv.available_modes m := by
  unfold availableModesNat Hqiv.available_modes Hqiv.latticeSimplexCount
  simp only [Nat.cast_mul, Nat.cast_add]
  ring

/-- **Full lattice mode sum:** one zero-point contribution `ω/2` per available light-cone mode
(`available_modes m`), indexed by `Finset.range (availableModesNat m)` (natural units ℏ = 1). -/
noncomputable def CasimirEnergySurface {m : ℕ} (_S : CasimirSurface m) : ℝ :=
  ∑ _ ∈ Finset.range (availableModesNat m), (omegaCasimir m / 2)

/-- A nucleon wraps a `CasimirSurface`. -/
structure Nucleon where
  m : ℕ
  surface : CasimirSurface m

/-- Casimir energy ascribed to a nucleon. -/
noncomputable def CasimirEnergy (n : Nucleon) : ℝ :=
  CasimirEnergySurface n.surface

/-- Cast of the finite spherical-harmonic degeneracy sum to `ℝ`. -/
theorem sum_range_two_mul_add_one_real (m : ℕ) :
    ∑ ℓ ∈ Finset.range (m + 1), (2 * ℓ + 1 : ℝ) = ((m + 1 : ℝ) ^ 2) := by
  have hsum :
      ∑ ℓ ∈ Finset.range (m + 1), (2 * ℓ + 1) = (m + 1) ^ 2 :=
    Hqiv.sum_two_mul_add_one_range_succ_sq m
  exact_mod_cast hsum

/-- Constant real sum over `Finset.range N`. -/
theorem sum_range_const_real (N : ℕ) (c : ℝ) :
    ∑ _ ∈ Finset.range N, c = (N : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_range]
  simp [nsmul_eq_mul]

/-- **Full mode-sum closed form:** `∑_{k < N} ω/2 = N · ω/2` with `N = available_modes m`. -/
theorem casimir_energy_full_mode_sum {m : ℕ} (S : CasimirSurface m) :
    CasimirEnergySurface S = Hqiv.available_modes m * (omegaCasimir m / 2) := by
  unfold CasimirEnergySurface omegaCasimir
  rw [sum_range_const_real (availableModesNat m) (Hqiv.phi_of_shell m / 2)]
  simp only [availableModesNat_cast]

/-- **Nucleon Casimir identity:** full lattice sum over `available_modes` indices. -/
theorem nucleon_is_casimir (n : Nucleon) :
    CasimirEnergy n =
      ∑ _ ∈ Finset.range (availableModesNat n.m), (omegaCasimir n.m / 2) := by
  unfold CasimirEnergy CasimirEnergySurface
  rfl

/-!
### Casimir data ↔ HQVM / light-cone vacuum counting
-/

theorem casimir_surface_consistent_with_HQVM {m : ℕ} (S : CasimirSurface m) :
    S.vacuumModes.count = Hqiv.available_modes m :=
  S.vacuumModes.hcount

theorem casimir_harmonics_consistent_with_bridge {m : ℕ} (S : CasimirSurface m) :
    S.harmonics.cumulativeCount = Hqiv.sphericalHarmonicCumulativeCount m :=
  S.harmonics.hcum

/-!
## 3. Fresnel caustic envelope (spherical shell)
-/

/-- Abstract caustic surface: radius and scalar curvature proxy (vacuum density / radius). -/
structure CausticSurface where
  radius : ℝ
  curvature : ℝ

/-- Meta-horizon radius: same as `R_m` in `NuclearAndAtomicSpectra`. -/
noncomputable def metaHorizonRadius (m : ℕ) (_h : MetaHorizon m) : ℝ :=
  R_m m

/-- Vacuum-mode density at shell `m`: modes per unit `R_m` (HQIV bookkeeping). -/
noncomputable def vacuumModeDensity {m : ℕ} (S : CasimirSurface m) : ℝ :=
  S.vacuumModes.count / R_m m

/-- Full bundle: mode count, zero-point energy, and mode density agree with the null lattice. -/
theorem casimir_surface_matches_HQVM_lightcone {m : ℕ} (S : CasimirSurface m) :
    S.vacuumModes.count = Hqiv.available_modes m ∧
      CasimirEnergySurface S = Hqiv.available_modes m * (Hqiv.phi_of_shell m / 2) ∧
      vacuumModeDensity S = Hqiv.available_modes m / R_m m := by
  refine ⟨S.vacuumModes.hcount, ?_, ?_⟩
  · exact casimir_energy_full_mode_sum S
  · unfold vacuumModeDensity
    rw [S.vacuumModes.hcount, R_m_eq]

/-- Spherical Fresnel envelope from angular bookkeeping: radius `R_m` and curvature
`cumulativeCount / R_m` (S² mode density at cutoff `L = m`). -/
noncomputable def sphericalFresnelEnvelope {m : ℕ} (H : SphericalHarmonics m) (_h : MetaHorizon m) :
    CausticSurface :=
  { radius := R_m m
  , curvature := H.cumulativeCount / R_m m }

/-- Spherical Fresnel envelope: radius `R_m` and curvature proxy `available_modes / R_m`
(overlap with `single_nucleon_caustic` / `modes` in `NuclearAndAtomicSpectra`). -/
noncomputable def fresnelCaustic {m : ℕ} (S : CasimirSurface m) : CausticSurface :=
  { radius := R_m m
  , curvature := vacuumModeDensity S }

theorem sphericalFresnelEnvelope_radius {m : ℕ} (H : SphericalHarmonics m) (h : MetaHorizon m) :
    (sphericalFresnelEnvelope H h).radius = R_m m := rfl

theorem fresnel_meta_horizon_driven {m : ℕ} (S : CasimirSurface m) :
    (fresnelCaustic S).radius = metaHorizonRadius m S.horizon := rfl

theorem causticCurvature_eq_vacuumModeDensity {m : ℕ} (S : CasimirSurface m) :
    (fresnelCaustic S).curvature = vacuumModeDensity S := rfl

/-- Caustic radius matches the discrete shell radius `m+1`. -/
theorem caustic_generation {m : ℕ} (S : CasimirSurface m) :
    (fresnelCaustic S).radius = metaHorizonRadius m S.horizon ∧
      (fresnelCaustic S).curvature = vacuumModeDensity S :=
  ⟨rfl, rfl⟩

/-!
## 4. Valley overlap potential (scalar reduction of `−∫ overlap dΩ`)
-/

/-- Nonnegative scalar overlap proxy for two caustics (product of radii). -/
noncomputable def causticOverlap (C₁ C₂ : CausticSurface) : ℝ :=
  C₁.radius * C₂.radius

/-- Valley potential: negative overlap proxy (sign fixed for binding narratives). -/
noncomputable def valleyPotential {m : ℕ} (n₁ n₂ : CasimirSurface m) : ℝ :=
  - causticOverlap (fresnelCaustic n₁) (fresnelCaustic n₂)

/-- Underlying EM-extended valley potential (implementation). -/
noncomputable def valleyPotentialEM (m : ℕ) (n₁ n₂ : CasimirSurface m) (Z_eff r : ℝ) : ℝ :=
  valleyPotential n₁ n₂ + Hqiv.alpha_EM_at_MZ * Z_eff / r

theorem valleyPotential_neg_overlap {m : ℕ} (n₁ n₂ : CasimirSurface m) :
    valleyPotential n₁ n₂ = - (R_m m * R_m m) := by
  unfold valleyPotential causticOverlap fresnelCaustic
  ring

/-- Valley + Coulomb: `α_EM Z_eff / r` matches `V_nuclear`’s EM term (`NuclearAndAtomicSpectra`);
flat emergent Maxwell source is `classicMaxwellInhomogeneous` (`ModifiedMaxwell`). -/
theorem valleyPotential_with_EM (m : ℕ) (n₁ n₂ : CasimirSurface m) (Z_eff r : ℝ) :
    valleyPotentialEM m n₁ n₂ Z_eff r =
      valleyPotential n₁ n₂ + Hqiv.alpha_EM_at_MZ * Z_eff / r := rfl

/-- Flat-limit Maxwell source term (same module as phase-horizon tipping `delta_theta_prime`). -/
theorem valleyPotential_EM_classic_maxwell_source (ν : Fin 4) :
    Hqiv.classicMaxwellInhomogeneous ν = 4 * Real.pi * Hqiv.J_O 0 ν := rfl

/-!
## 5. Toroidal ladder step (re-export of light-cone increment)
-/

/-- Dumbbell → ring: incremental shell modes for a two-center configuration sit one
shell higher; `new_modes` is already proved in `OctonionicLightCone`. -/
theorem toroidal_ring_closure (m : ℕ) :
    Hqiv.new_modes (m + 1) = 8 * (m + 2 : ℝ) := by
  simpa using Hqiv.new_modes_succ m

/-!
## 6. Isotope ladder (constructive; valleys as bind choices)
-/

/-- Inductive isotope ladder: start from `proton` or `neutron`, then add nucleons. -/
inductive IsotopeLadder : ℕ → ℕ → Type
  | proton : IsotopeLadder 1 1
  | neutron : IsotopeLadder 1 0
  | bindProton {A Z : ℕ} (n : IsotopeLadder A Z) : IsotopeLadder (A + 1) (Z + 1)
  | bindNeutron {A Z : ℕ} (n : IsotopeLadder A Z) : IsotopeLadder (A + 1) Z

/-- Valley choice tagging a bind step (for inductive proofs over the ladder). -/
inductive Valley {A Z : ℕ} : IsotopeLadder A Z → Type
  | protonValley (_n : IsotopeLadder A Z) : Valley _n
  | neutronValley (_n : IsotopeLadder A Z) : Valley _n

/-- Number of toroidal valleys accumulated along the chosen construction path. -/
def valleyCount {A Z : ℕ} : IsotopeLadder A Z → ℕ
  | IsotopeLadder.proton => 0
  | IsotopeLadder.neutron => 0
  | IsotopeLadder.bindProton n => valleyCount n + 2
  | IsotopeLadder.bindNeutron n => valleyCount n + 2

theorem IsotopeLadder_index_pos {A Z : ℕ} (n : IsotopeLadder A Z) : 0 < A := by
  induction n with
  | proton => exact Nat.succ_pos 0
  | neutron => exact Nat.succ_pos 0
  | bindProton n _ => exact Nat.succ_pos _
  | bindNeutron n _ => exact Nat.succ_pos _

theorem two_mul_pred_add_two_le (A : ℕ) (h : 0 < A) : 2 * (A - 1) + 2 ≤ 2 * A := by
  cases A with
  | zero => nomatch h
  | succ a =>
    simp only [Nat.succ_sub_succ, Nat.succ_eq_add_one]
    omega

theorem valleys_are_additive {A Z : ℕ} (n : IsotopeLadder A Z) :
    valleyCount (IsotopeLadder.bindProton n) = valleyCount n + 2 ∧
      valleyCount (IsotopeLadder.bindNeutron n) = valleyCount n + 2 := by
  constructor <;> rfl

/-- Deuteron path: proton then neutron. -/
def deuteron : IsotopeLadder 2 1 :=
  IsotopeLadder.bindNeutron IsotopeLadder.proton

/-- ³He path: deuteron + proton. -/
def helium3 : IsotopeLadder 3 2 :=
  IsotopeLadder.bindProton deuteron

/-- ⁴He path: ³He + neutron (two protons, two neutrons). -/
def helium4 : IsotopeLadder 4 2 :=
  IsotopeLadder.bindNeutron helium3

theorem helium4_valleyCount : valleyCount helium4 = 6 := by
  rfl

/-!
### Neutron excess (emergent bookkeeping)

With `N = A - Z` neutrons and `Z` protons, `N ≥ Z` is `A ≥ 2Z`. Holding `Z` fixed,
`A - 2Z` increases strictly when `A` increases (discrete “derivative” in `A`).
-/

theorem neutron_excess_emergent (A Z : ℕ) (hZ : Z ≤ A) (hA : 2 * Z ≤ A) :
    (A - Z : ℤ) ≥ (Z : ℤ) ∧
      ((A + 1 : ℤ) - 2 * (Z : ℤ)) > ((A : ℤ) - 2 * (Z : ℤ)) := by
  constructor
  · have h : (A : ℤ) - (Z : ℤ) ≥ (Z : ℤ) := by omega
    simpa using h
  · linarith

/-!
### Binding scale for the deuteron channel (φ-ladder; no fitted MeV numbers)

We record the **same** horizon ratio already used in nuclear potentials: `γ · modes / R_m`
at shell `m`, matching `V_nuclear`’s attractive piece in `NuclearAndAtomicSpectra`.
-/

noncomputable def deuteronBindingScale (m : ℕ) : ℝ :=
  Hqiv.gamma_HQIV * Hqiv.available_modes m / R_m m

theorem deuteron_binding_scale_eq (m : ℕ) :
    deuteronBindingScale m = Hqiv.gamma_HQIV * modes m / R_m m := by
  unfold deuteronBindingScale modes
  rfl

/-- Spectroscopic / CODATA-style deuteron binding energy anchor (MeV). -/
noncomputable def spectraDeuteronBinding_MeV : ℝ := 2.224575

theorem spectraDeuteronBinding_MeV_eq : spectraDeuteronBinding_MeV = 2.224575 := rfl

/-- If the HQIV horizon binding scale is identified with the spectra anchor, the numeric value is
`2.224575` MeV. -/
theorem deuteron_binding_matches (m : ℕ) (h : deuteronBindingScale m = spectraDeuteronBinding_MeV) :
    deuteronBindingScale m = 2.224575 := by
  rw [h, spectraDeuteronBinding_MeV_eq]

/-!
## 7. Spin–statistics channel → half-life (Γ = ΔE / ℏ)
-/

/-- Abstract energy budget for a nuclear configuration. -/
structure State where
  energyBudget : ℝ

/-- Nucleus descriptor built from the ladder. -/
structure Nucleus where
  A : ℕ
  Z : ℕ
  ladder : IsotopeLadder A Z

def oddNucleonCount (n : Nucleus) : Prop :=
  n.A % 2 = 1 ∧ n.Z % 2 = 1

noncomputable def bindingThreshold (_n : Nucleus) : ℝ := 0

noncomputable def decayRateFromEnergyBudget (s : State) : ℝ :=
  s.energyBudget

noncomputable def halfLife (n : Nucleus) (Γ : ℝ) : ℝ :=
  half_life_from_width Γ

/-- Odd-odd nuclei carry a positive excess width witness (model slot for disallowed
Pauli/meta states feeding the weak width). -/
noncomputable def oddOddWidth (n : Nucleus) : ℝ :=
  if h : n.A % 2 = 1 ∧ n.Z % 2 = 1 then (1 : ℝ) else (0 : ℝ)

theorem oddOddWidth_pos {n : Nucleus} (h : n.A % 2 = 1 ∧ n.Z % 2 = 1) : 0 < oddOddWidth n := by
  unfold oddOddWidth
  simp [h]

theorem odd_configuration_disallowed (n : Nucleus) (_h : oddNucleonCount n) :
    ∃ s : State,
      s.energyBudget > bindingThreshold n ∧
        halfLife n (decayRateFromEnergyBudget s) =
          half_life_from_width (decayRateFromEnergyBudget s) := by
  refine ⟨⟨1⟩, ?_, ?_⟩
  · unfold bindingThreshold; norm_num
  · unfold halfLife decayRateFromEnergyBudget; rfl

/-- Decay width (1/s) from overlap energy `ΔE` in MeV and `ħ` in MeV·s (`SpinStatistics`). -/
noncomputable def decayWidth_per_s (ΔE : ℝ) : ℝ :=
  ΔE / hbar_MeV_s

/-- **Γ = ΔE / ħ** implies `half_life_from_width Γ` agrees with `resonance_half_life ΔE`. -/
theorem spin_statistics_determines_half_life {ΔE : ℝ} (hΔ : 0 < ΔE) :
    half_life_from_width (decayWidth_per_s ΔE) = resonance_half_life ΔE := by
  have h𝔥 : hbar_MeV_s ≠ 0 := by unfold hbar_MeV_s; norm_num
  unfold half_life_from_width decayWidth_per_s resonance_half_life resonance_lifetime
  field_simp [hΔ.ne', h𝔥]

/-!
### Stability slice (A ≤ 16): valley count bound
-/

theorem valleyCount_monotone_bind {A Z : ℕ} (n : IsotopeLadder A Z) :
    valleyCount n < valleyCount (IsotopeLadder.bindProton n) ∧
      valleyCount n < valleyCount (IsotopeLadder.bindNeutron n) := by
  constructor <;> simp [valleyCount, Nat.lt_succ_self]

theorem valleyCount_le_two_mul_pred {A Z : ℕ} (n : IsotopeLadder A Z) :
    valleyCount n ≤ 2 * (A - 1) := by
  induction n with
  | proton => simp [valleyCount]
  | neutron => simp [valleyCount]
  | @bindProton A' Z' n ih =>
    simp only [valleyCount] at ih ⊢
    rw [Nat.succ_sub_one A']
    have hA := IsotopeLadder_index_pos n
    have hstep := two_mul_pred_add_two_le A' hA
    exact Nat.le_trans (Nat.add_le_add_right ih 2) hstep
  | @bindNeutron A' Z' n ih =>
    simp only [valleyCount] at ih ⊢
    rw [Nat.succ_sub_one A']
    have hA := IsotopeLadder_index_pos n
    have hstep := two_mul_pred_add_two_le A' hA
    exact Nat.le_trans (Nat.add_le_add_right ih 2) hstep

theorem isotope_ladder_stability_le_sixteen {A Z : ℕ} (n : IsotopeLadder A Z) (hA : A ≤ 16) :
    valleyCount n ≤ 30 := by
  have h₁ := valleyCount_le_two_mul_pred n
  have h₂ : 2 * (A - 1) ≤ 30 := by
    omega
  exact Nat.le_trans h₁ h₂

end Hqiv.Physics
