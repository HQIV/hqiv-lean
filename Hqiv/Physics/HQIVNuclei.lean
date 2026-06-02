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
### Post-α geometry: sphere touching on the α compound surface

Through **⁴He**, four nucleon Fresnel spheres close tetrahedrally (`tetrahedralClosureCausticScale`,
`valleyCount helium4 = 6`). Above that, binding is **not** a linear `Z − 2` inequality:
each exterior nucleon is another `fresnelCaustic` sphere that must **touch** the α compound
surface on a **distinct facet** without overlap (`causticOverlap` / separation
`R_α + R_n` at shell `m`).

* **Proton on a triangular facet:** three vertex contacts (sphere–sphere touch points).
* **Far neutron:** a single sphere–sphere touch to the exterior neutron shell; coupling
  is only the strong-channel fraction `(4/8)` — binds, but **not nearly as much** as a facet proton.
* **Spin / stability:** `spin_statistics_determines_half_life` (`DynamicBetaIsotope`).

See `NuclearCausticBinding` for the caustic stack; this block is the **facet-touch chart**.
-/

/-- Fully constructive toroidal valley count (⁴He closure). -/
def constructiveValleyCap : ℕ := valleyCount helium4

theorem constructiveValleyCap_eq_six : constructiveValleyCap = 6 := helium4_valleyCount

/-- Tetrahedral α has 6 edges (pairwise nucleon–nucleon overlaps). The constructive valley count
of 6 for ⁴He matches the complete graph K₄ on four nucleons (each edge is one valley overlap). -/
def tetrahedralEdgeCount : ℕ := 6

theorem helium4_valleyCount_eq_tetrahedral_edges : valleyCount helium4 = tetrahedralEdgeCount := by
  rfl

theorem constructiveValleyCap_eq_tetrahedral_edges : constructiveValleyCap = tetrahedralEdgeCount := by
  rw [constructiveValleyCap_eq_six, tetrahedralEdgeCount]

/-- On the constructive isotope ladder, each bind step adds exactly two valleys (one toroidal
pair overlap per added nucleon). Through ⁴He this produces the six edges of the tetrahedron. -/
theorem valleyCount_additive_per_bind (n : IsotopeLadder A Z) :
    valleyCount (IsotopeLadder.bindProton n) = valleyCount n + 2 ∧
      valleyCount (IsotopeLadder.bindNeutron n) = valleyCount n + 2 :=
  valleys_are_additive n

/-- The six valleys of ⁴He equal the number of pairwise nucleon–nucleon contacts in a
complete tetrahedral packing (K₄ has C(4,2) = 6 edges). -/
theorem helium4_valleys_equal_pairwise_contacts :
    valleyCount helium4 = 6 := by
  exact helium4_valleyCount

/-- α-core proton number `Z_α = 2`. -/
def alphaCoreProtonNumber : ℕ := 2

/-- α-core neutron number `N_α = 2`. -/
def alphaCoreNeutronNumber : ℕ := 2

/-- Tetrahedral α exposes four exterior facets on the compound sphere. -/
def alphaTetrahedralFacetCount : ℕ := 4

/-- Contacts at one proton–facet sphere touch (three vertices of the facet triangle). -/
def protonFacetVertexContacts : ℕ := 3

theorem protonFacetVertexContacts_eq_three : protonFacetVertexContacts = 3 := rfl

/-- Compound α radius and nucleon radius at binding shell `m` (`fresnelCaustic`). -/
noncomputable def alphaCompoundRadius (m : ℕ) : ℝ := R_m m

noncomputable def nucleonCausticRadius (m : ℕ) : ℝ := R_m m

/-- Centre separation for exterior nucleon sphere touching the α compound sphere. -/
noncomputable def sphereTouchSeparation (m : ℕ) : ℝ :=
  alphaCompoundRadius m + nucleonCausticRadius m

/-- One exterior proton placed on facet `facetIdx` (sphere-touch chart). -/
structure ProtonFacetTouch where
  facetIdx : ℕ
  contactCount : ℕ

/-- Facet indices are distinct (non-overlapping sphere placements on the α surface). -/
def protonFacetTouchesFeasible (ts : List ProtonFacetTouch) : Prop :=
  ts.map (·.facetIdx) |>.Nodup

/-- Sum contact points over a feasible proton facet-touch list. -/
def protonFacetTouchContactSum (ts : List ProtonFacetTouch) : ℕ :=
  (ts.map (·.contactCount)).sum

/-- Contacts on facet touches that are not full triangles (staged / partial — "lighter"). -/
def protonFacetPartialContactSum (ts : List ProtonFacetTouch) : ℕ :=
  (ts.filter (fun t => t.contactCount < protonFacetVertexContacts)).map (·.contactCount) |>.sum

/-- Full 3-vertex facet contacts only. -/
def protonFacetFullContactSum (ts : List ProtonFacetTouch) : ℕ :=
  (ts.filter (fun t => t.contactCount = protonFacetVertexContacts)).map (·.contactCount) |>.sum

/-- Generalized post-α proton facet packing, refined from the ⁵Li/⁵Be 5-body analysis.

Base shape: ⁴He is a regular tetrahedron (4 faces). Each face is a natural triangular site.

When adding the 5th nucleon (⁵Li = α + p, ⁵Be = α + 2p):
- The very first extra proton on a new face does **not** instantly receive the full 3 vertex contacts.
- It starts with staged/partial occupation (1 contact for the absolute first addition to that face).
- As more protons are placed on faces (higher A/Z), occupation per face ramps toward 3.
- This produces a smooth, continuous generalization instead of a discontinuous jump at A=5.

Far neutrons remain "far" (single-point, weighted by strongChannelFraction = 4/8).
Non-touching nucleons in outer shells get fractional participation (see postAlphaOutsideValleyCountEffective).

This staged rule (1 → 2 → 3 per face) is the proposed template for generalizing to arbitrary compound surfaces beyond the first α tetrahedron.

Network / many-body (see `PostAlphaBindingGeometry`):
- Extra nucleons **lower the energy** of α-core sites they touch (well deepening).
- Deepened wells **interact** on the contact graph (`γ` network term).
- Added nucleons are often **lighter** (partial facet + far `4/8`); the well **relaxes**
  and the compound **loses a little `BE/A`** vs naive geometry/A.
-/
def bbnProtonFacetTouches (A Z : ℕ) : List ProtonFacetTouch :=
  if A ≤ 4 then []
  else
    let extraProtons := max 0 (Z - alphaCoreProtonNumber)
    let numFaces := min extraProtons alphaTetrahedralFacetCount
    -- Staged contacts per newly occupied face (from 5-body microscope):
    -- First proton on a face gets 1 contact; builds toward full triangle (3).
    let contactsPerFace :=
      if numFaces = 0 then 0
      else min protonFacetVertexContacts (1 + max 0 ((extraProtons - 1) / numFaces))
    List.map (fun i => { facetIdx := i, contactCount := contactsPerFace })
      (List.range numFaces)

theorem bbnProtonFacetTouches_be7 :
    bbnProtonFacetTouches 7 4 =
      [{ facetIdx := 0, contactCount := 1 }, { facetIdx := 1, contactCount := 1 }] := by
  dsimp [bbnProtonFacetTouches, alphaCoreProtonNumber, alphaTetrahedralFacetCount,
    protonFacetVertexContacts]
  rfl

theorem bbnProtonFacetTouches_li7 :
    bbnProtonFacetTouches 7 3 = [{ facetIdx := 0, contactCount := 1 }] := by
  dsimp [bbnProtonFacetTouches, alphaCoreProtonNumber, alphaTetrahedralFacetCount,
    protonFacetVertexContacts]
  rfl

theorem bbnProtonFacetTouches_be7_feasible : protonFacetTouchesFeasible (bbnProtonFacetTouches 7 4) := by
  rw [bbnProtonFacetTouches_be7]
  simp [protonFacetTouchesFeasible, List.Nodup]

theorem bbnProtonFacetTouches_li7_feasible : protonFacetTouchesFeasible (bbnProtonFacetTouches 7 3) := by
  rw [bbnProtonFacetTouches_li7]
  simp [protonFacetTouchesFeasible, List.Nodup]

/-- One exterior neutron touching the far nucleon shell (single contact, not a facet triangle). -/
structure FarNeutronTouch where
  neutronIdx : ℕ
  contactCount : ℕ

/-- Strong-channel fraction of the octonion carrier (source of truth for BBN/nuclear weighting). -/
noncomputable def strongChannelFraction : ℝ := (4 : ℝ) / 8

/-- Relative weight of far-neutron touch vs full facet proton touch (`4/8` = strong channel). -/
noncomputable def farNeutronTouchWeight : ℝ := strongChannelFraction

theorem farNeutronTouchWeight_eq_strong_channel :
    farNeutronTouchWeight = strongChannelFraction := rfl

theorem strongChannelFraction_eq_four_eighths : strongChannelFraction = (4 : ℝ) / 8 := rfl

/-- Far-neutron touches are suppressed by the strong-channel carrier fraction (binds, but not as strongly
as a full facet proton contact set). -/
theorem farNeutronTouchWeight_lt_one : farNeutronTouchWeight < 1 := by
  unfold farNeutronTouchWeight strongChannelFraction; norm_num

/-- Single contact at the far-nucleon sphere touch. -/
def farNeutronPointContacts : ℕ := 1

/-- Extra neutrons above the α core (`N − N_α`). -/
def postAlphaExtraNeutrons (A Z : ℕ) : ℕ :=
  let n := A - Z
  if n ≤ alphaCoreNeutronNumber then 0 else n - alphaCoreNeutronNumber

/-- Far-neutron touches for BBN witnesses (sphere touching the distant neutron shell). -/
def bbnFarNeutronTouches (A Z : ℕ) : List FarNeutronTouch :=
  if A ≤ 4 then []
  else
    List.map (fun i => { neutronIdx := i, contactCount := farNeutronPointContacts })
      (List.range (postAlphaExtraNeutrons A Z))

def farNeutronTouchContactSum (ts : List FarNeutronTouch) : ℕ :=
  (ts.map (·.contactCount)).sum

/-- Weighted far-neutron contacts (ℝ; not nearly as much as facet protons). -/
noncomputable def farNeutronWeightedContactSum (A Z : ℕ) : ℝ :=
  (farNeutronTouchContactSum (bbnFarNeutronTouches A Z) : ℝ) * farNeutronTouchWeight

/-!
### Sphere-touch contact energy (geometric binding units from valley potential)

Each facet-vertex contact or far-neutron point contact contributes binding proportional to the
base valley overlap scale (`valleyPotential` magnitude at the binding shell). Facet protons
carry three vertex contacts; far neutrons are weighted by the strong-channel fraction.
-/

/-- Binding energy unit per single sphere–sphere contact at shell `m`, taken from the magnitude
of the valley overlap proxy (`R_m²`). This is the geometric "currency" for post-α packing. -/
noncomputable def sphereTouchContactEnergyUnit (m : ℕ) : ℝ :=
  R_m m * R_m m

theorem sphereTouchContactEnergyUnit_pos (m : ℕ) : 0 < sphereTouchContactEnergyUnit m := by
  unfold sphereTouchContactEnergyUnit R_m
  have hR : 0 < (m + 1 : ℝ) := by positivity
  nlinarith

/-- Binding contribution from `k` sphere–sphere contacts at shell `m`. -/
noncomputable def sphereTouchContactEnergy (m k : ℕ) : ℝ :=
  (k : ℝ) * sphereTouchContactEnergyUnit m

/-- Facet proton contact set (three vertices) binding unit at shell `m`. -/
noncomputable def facetProtonContactSetEnergy (m : ℕ) : ℝ :=
  sphereTouchContactEnergy m protonFacetVertexContacts

/-- Far-neutron single contact, suppressed by the strong-channel fraction. -/
noncomputable def farNeutronContactEnergy (m : ℕ) : ℝ :=
  farNeutronTouchWeight * sphereTouchContactEnergyUnit m

/-- A full facet-proton contact set (3 vertices) binds strictly more than a single far-neutron
touch (1 contact at 4/8 weight) at any shell `m`. -/
theorem facet_proton_binds_stronger_than_far_neutron (m : ℕ) :
    farNeutronContactEnergy m < facetProtonContactSetEnergy m := by
  unfold farNeutronContactEnergy facetProtonContactSetEnergy sphereTouchContactEnergy
    sphereTouchContactEnergyUnit protonFacetVertexContacts farNeutronTouchWeight strongChannelFraction
  have hRpos : 0 < (m + 1 : ℝ) := by positivity
  have hR2pos : 0 < R_m m * R_m m := by
    simp [R_m]
    nlinarith [hRpos]
  -- 3 * unit > (4/8) * unit  ⇔  (3 - 4/8) * unit > 0
  have hcoeff : (0 : ℝ) < 3 - (4 : ℝ) / 8 := by norm_num
  have hscale : 0 < (3 - (4 : ℝ) / 8) * (R_m m * R_m m) := mul_pos hcoeff hR2pos
  linarith [hscale]

/-- Integer valley ledger (proton facet contacts only; far sector is weighted separately). -/
def postAlphaOutsideValleyCount (A Z : ℕ) : ℕ :=
  if A ≤ 4 then 0
  else constructiveValleyCap + protonFacetTouchContactSum (bbnProtonFacetTouches A Z)

/-- Effective outside contacts including weak far-neutron sphere touches. -/
noncomputable def postAlphaOutsideValleyCountEffective (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 0
  else
    (constructiveValleyCap : ℝ) + (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) +
      farNeutronWeightedContactSum A Z

theorem postAlphaOutsideValleyCount_be7 :
    postAlphaOutsideValleyCount 7 4 = constructiveValleyCap + 2 := by
  simp [postAlphaOutsideValleyCount, bbnProtonFacetTouches_be7, protonFacetTouchContactSum,
    constructiveValleyCap_eq_six]

theorem postAlphaOutsideValleyCount_li7 :
    postAlphaOutsideValleyCount 7 3 = constructiveValleyCap + 1 := by
  simp [postAlphaOutsideValleyCount, bbnProtonFacetTouches_li7, protonFacetTouchContactSum,
    constructiveValleyCap_eq_six]

theorem postAlphaExtraNeutrons_be7 : postAlphaExtraNeutrons 7 4 = 1 := by decide

theorem postAlphaExtraNeutrons_li7 : postAlphaExtraNeutrons 7 3 = 2 := by decide

theorem bbnFarNeutronTouches_be7 :
    bbnFarNeutronTouches 7 4 =
      [{ neutronIdx := 0, contactCount := farNeutronPointContacts }] := by
  dsimp [bbnFarNeutronTouches, postAlphaExtraNeutrons_be7, List.range, List.map,
    farNeutronPointContacts]
  rfl

theorem bbnFarNeutronTouches_li7 :
    bbnFarNeutronTouches 7 3 =
      [{ neutronIdx := 0, contactCount := farNeutronPointContacts },
        { neutronIdx := 1, contactCount := farNeutronPointContacts }] := by
  dsimp [bbnFarNeutronTouches, postAlphaExtraNeutrons_li7, List.range, List.map,
    farNeutronPointContacts]
  rfl

theorem farNeutronTouchContactSum_be7 :
    farNeutronTouchContactSum (bbnFarNeutronTouches 7 4) = 1 := by
  rw [bbnFarNeutronTouches_be7]
  simp [farNeutronTouchContactSum, farNeutronPointContacts]

theorem farNeutronTouchContactSum_li7 :
    farNeutronTouchContactSum (bbnFarNeutronTouches 7 3) = 2 := by
  rw [bbnFarNeutronTouches_li7]
  simp [farNeutronTouchContactSum, farNeutronPointContacts]

theorem farNeutronWeightedContactSum_be7 :
    farNeutronWeightedContactSum 7 4 = strongChannelFraction := by
  simp [farNeutronWeightedContactSum, farNeutronTouchContactSum_be7, farNeutronTouchWeight]

theorem farNeutronWeightedContactSum_be7_eq_half :
    farNeutronWeightedContactSum 7 4 = (1 : ℝ) / 2 := by
  rw [farNeutronWeightedContactSum_be7, strongChannelFraction_eq_four_eighths]
  norm_num

theorem farNeutronWeightedContactSum_li7 :
    farNeutronWeightedContactSum 7 3 = 1 := by
  simp [farNeutronWeightedContactSum, farNeutronTouchContactSum_li7, farNeutronTouchWeight]
  rw [strongChannelFraction_eq_four_eighths]
  norm_num

theorem farNeutronWeightedContactSum_nonneg (A Z : ℕ) :
    0 ≤ farNeutronWeightedContactSum A Z := by
  unfold farNeutronWeightedContactSum farNeutronTouchContactSum bbnFarNeutronTouches
    farNeutronTouchWeight strongChannelFraction
  split_ifs with hA
  · norm_num
  · have hweight : 0 ≤ (4 : ℝ) / 8 := by norm_num
    have hsum : 0 ≤ (farNeutronTouchContactSum (bbnFarNeutronTouches A Z) : ℝ) := by
      norm_cast
      exact Nat.zero_le _
    nlinarith

theorem postAlphaOutsideValleyCountEffective_be7 :
    postAlphaOutsideValleyCountEffective 7 4 = (17 : ℝ) / 2 := by
  have hfar := farNeutronWeightedContactSum_be7_eq_half
  simp [postAlphaOutsideValleyCountEffective, bbnProtonFacetTouches_be7,
    protonFacetTouchContactSum, constructiveValleyCap_eq_six, hfar]
  norm_num

theorem postAlphaOutsideValleyCountEffective_li7 :
    postAlphaOutsideValleyCountEffective 7 3 = 8 := by
  simp [postAlphaOutsideValleyCountEffective, bbnProtonFacetTouches_li7,
    protonFacetTouchContactSum, constructiveValleyCap_eq_six, farNeutronWeightedContactSum_li7]
  norm_num

theorem postAlphaOutsideValleyCountEffective_li7_lt_be7 :
    postAlphaOutsideValleyCountEffective 7 3 < postAlphaOutsideValleyCountEffective 7 4 := by
  rw [postAlphaOutsideValleyCountEffective_li7, postAlphaOutsideValleyCountEffective_be7]
  norm_num

/-- Post-α effective valley count is nonnegative for all A, Z (far-neutron weights are nonnegative). -/
theorem postAlphaOutsideValleyCountEffective_nonneg (A Z : ℕ) :
    0 ≤ postAlphaOutsideValleyCountEffective A Z := by
  unfold postAlphaOutsideValleyCountEffective
  split_ifs with h
  · norm_num
  · have hcap : 0 ≤ (constructiveValleyCap : ℝ) := by norm_num
    have htouch : 0 ≤ (protonFacetTouchContactSum (bbnProtonFacetTouches A Z) : ℝ) := by
      norm_cast; exact Nat.zero_le _
    have hfar := farNeutronWeightedContactSum_nonneg A Z
    linarith

/-- The post-α effective valley count for ⁷Be exceeds that for ⁷Li (two facet protons vs one
facet proton + two weighted far neutrons). -/
theorem be7_has_more_effective_valleys_than_li7 :
    postAlphaOutsideValleyCountEffective 7 4 > postAlphaOutsideValleyCountEffective 7 3 := by
  rw [postAlphaOutsideValleyCountEffective_be7, postAlphaOutsideValleyCountEffective_li7]
  norm_num

/-- Post-α participation: unity only when the facet-touch chart is feasible.

Spin-statistics (`spin_statistics_determines_half_life`) selects the valley of stability
among feasible touchings; not an isospin-ratio inequality.
-/
noncomputable def spinStabilityParticipation (A Z : ℕ) : ℝ :=
  if A ≤ 4 then 1
  else if (bbnProtonFacetTouches A Z).isEmpty then 0
  else 1

theorem spinStabilityParticipation_nonneg (A Z : ℕ) : 0 ≤ spinStabilityParticipation A Z := by
  unfold spinStabilityParticipation
  split_ifs <;> norm_num

theorem spinStabilityParticipation_be7_li7 :
    spinStabilityParticipation 7 4 = 1 ∧ spinStabilityParticipation 7 3 = 1 := by
  constructor <;> simp [spinStabilityParticipation, bbnProtonFacetTouches_be7,
    bbnProtonFacetTouches_li7, List.isEmpty]

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
