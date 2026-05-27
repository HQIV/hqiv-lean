import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Hqiv.Algebra.SMEmbedding
import Hqiv.Algebra.ShellResidueCRT
import Hqiv.Physics.BaryogenesisCore
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.OctonionicZeta
import Hqiv.Physics.SphereProjectedMassTransfer
import Hqiv.Geometry.SphericalHarmonicsBridge

namespace Hqiv.Physics

open Hqiv
open Complex

/-!
## Conserved quantum-number content → harmonic complexity → mass hierarchy

**Classification (SM quantum numbers that must project onto Fano triples to close the surface wave):**
- **Neutrino:** lepton number only → **1** independent triple.
- **Charged lepton:** lepton number + electric charge → **2** triples.
- **Quark:** baryon number + electric charge + colour → **3** triples.

This module proves:
1. Strict ordering of `conservedTripleCount` and of a squared **intrinsic wave complexity** proxy.
2. **`intrinsicWaveComplexity c` equals the cumulative `S²` spherical-harmonic degeneracy** `(L+1)²`
   at `L = l - 1` for `l = conservedTripleCount c` (`intrinsicWaveComplexity_eq_sphericalHarmonicCumulativeCount_pred`,
   via `Hqiv.sphericalHarmonicCumulativeCount` in `SphericalHarmonicsBridge`).
3. A visible-state heavy color-composed witness `allowedColorResonanceMass _ .heavy` now normalized
   from the top lock-in channel, with the down-like heavy branch exported through the heavy-shell
   detuning and visible-state bookkeeping budget rather than a naive half-weight rule.

Shared lock-in temperature enters neutrino masses through `T_lockin` and outer surfaces (see
`m_nu_e_derived_eq_suppression_times_M_Z`); τ and top use the existing GeV witnesses in the
resonance modules. The **ordering** is therefore a proved consequence of those witnesses, not a new
mass-table input.

For the new post-Step-B roadmap, this file should be read as the first clean
bridge from a raw mass hierarchy to a **closure-decoration hierarchy**:

- neutrino = minimal **spin-only / neutral** fermionic closure,
- charged lepton = **spin + charge** closure,
- quark = **spin + charge + colour** closure.

**Taxonomy vs inevitability:** the closure layers are a **proved classification + ordering** package
(strict inequalities from the witnesses). They organize the narrative across sectors and reuse the
same harmonic-complexity proxy; they **do not** yet replace the GeV / shell-table anchors in
`ChargedLeptonResonance` and `QuarkMetaResonance`, nor do they force a unique realization of those
witnesses without additional theorems.

**Note:** Numeric agreement with PDG for every flavour is still handled by the tolerance lemmas in
`QuarkMetaResonance` / `ChargedLeptonResonance` where present; this file establishes the **global**
ν ≪ charged lepton ≪ top hierarchy from the derived ν scale and the τ/top anchors.

### Scaling ansatz (bridge to `effCorrected` + `SurfaceWaveSelfClock`)

A **minimal combined scaling** compatible with the self-clock / Mexican-hat story uses the same
`effCorrected δ m` as `GlobalDetuning` and `SurfaceWaveSelfClock.mexicanHatVeff` (inverse in `V_eff`):

`massScalingAnsatz k δ l m := k * l² * effCorrected δ m`,

with `l` the conserved-triple count (1 / 2 / 3) and **`k > 0` a single normalization** (paper /
curvature-imprint slot — **not** fixed to `δ_E` or `6⁷√3` in Lean here).

**Proved below:** strict monotonicity of this ansatz in `l` (fixed shell) and in `m` (fixed `l`, `0 ≤ δ`),
whenever denominators stay positive. This matches “larger harmonic content (`l²`) or larger shell
index ⇒ larger effective surface factor ⇒ larger mass scale” at the ansatz level.

Triality / Spin(8) automorphisms are **not** re-proved here; the narrative link “three `l` values ↔ three
representation images” belongs in `Triality` / SO(8) closure modules. This file stays physics-bridge
lightweight.
-/

/-- Sector distinguished by how many independent SM quantum numbers must close on the storing wave. -/
inductive FermionContentClass
  | neutrino
  | chargedLepton
  | quark
  deriving DecidableEq, Repr

/-- Decoration layer for the fermionic closure story:
minimal spin closure, then charge decoration, then colour composition. -/
inductive FermionClosureLayer
  | spinOnly
  | chargeDecorated
  | colorComposed
  deriving DecidableEq, Repr

/-- Shell-visible charge states. The visible ladder only exports neutral or integer-sign states;
fractional quark labels remain internal residual bookkeeping in the algebra layer. -/
inductive VisibleChargeState
  | neutral
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Integer visible charge carried by a shell-visible state. -/
def VisibleChargeState.toInt : VisibleChargeState → Int
  | .neutral => 0
  | .positive => 1
  | .negative => -1

/-- Rational form of the visible shell charge for comparison with the algebraic charge table. -/
def VisibleChargeState.toRat (q : VisibleChargeState) : ℚ :=
  q.toInt

/-- Convert the closure layer to a natural rank for ordering lemmas. -/
def FermionClosureLayer.rank : FermionClosureLayer → ℕ
  | .spinOnly => 1
  | .chargeDecorated => 2
  | .colorComposed => 3

/-- The current ν / charged-lepton / quark classes viewed as closure-decoration layers. -/
def closureLayerOfContent (c : FermionContentClass) : FermionClosureLayer :=
  match c with
  | .neutrino => .spinOnly
  | .chargedLepton => .chargeDecorated
  | .quark => .colorComposed

/-- Independent Fano-plane triples required (ν:1, charged ℓ:2, quark:3). -/
def conservedTripleCount (c : FermionContentClass) : ℕ :=
  match c with
  | .neutrino => 1
  | .chargedLepton => 2
  | .quark => 3

/-- Visible shell-charge states allowed by each closure layer. -/
def visibleChargeStateAllowed : FermionClosureLayer → VisibleChargeState → Prop
  | .spinOnly, .neutral => True
  | .spinOnly, _ => False
  | .chargeDecorated, .positive => True
  | .chargeDecorated, .negative => True
  | .chargeDecorated, .neutral => False
  | .colorComposed, _ => True

theorem conservedTripleCount_ν_lt_ℓ :
    conservedTripleCount .neutrino < conservedTripleCount .chargedLepton := by
  decide

theorem conservedTripleCount_ℓ_lt_q :
    conservedTripleCount .chargedLepton < conservedTripleCount .quark := by
  decide

theorem closureLayerOfContent_neutrino :
    closureLayerOfContent .neutrino = FermionClosureLayer.spinOnly := rfl

theorem closureLayerOfContent_chargedLepton :
    closureLayerOfContent .chargedLepton = FermionClosureLayer.chargeDecorated := rfl

theorem closureLayerOfContent_quark :
    closureLayerOfContent .quark = FermionClosureLayer.colorComposed := rfl

theorem closureLayer_rank_neutrino_lt_chargedLepton :
    (closureLayerOfContent .neutrino).rank < (closureLayerOfContent .chargedLepton).rank := by
  decide

theorem closureLayer_rank_chargedLepton_lt_quark :
    (closureLayerOfContent .chargedLepton).rank < (closureLayerOfContent .quark).rank := by
  decide

theorem closureLayer_rank_matches_triple_count (c : FermionContentClass) :
    (closureLayerOfContent c).rank = conservedTripleCount c := by
  cases c <;> rfl

theorem visibleChargeStateAllowed_spinOnly_iff (q : VisibleChargeState) :
    visibleChargeStateAllowed .spinOnly q ↔ q = .neutral := by
  cases q <;> simp [visibleChargeStateAllowed]

theorem visibleChargeStateAllowed_chargeDecorated_iff (q : VisibleChargeState) :
    visibleChargeStateAllowed .chargeDecorated q ↔ q = .positive ∨ q = .negative := by
  cases q <;> simp [visibleChargeStateAllowed]

theorem visibleChargeStateAllowed_colorComposed (q : VisibleChargeState) :
    visibleChargeStateAllowed .colorComposed q := by
  cases q <;> simp [visibleChargeStateAllowed]

theorem neutrino_visible_charge_is_neutral :
    visibleChargeStateAllowed (closureLayerOfContent .neutrino) .neutral := by
  simp [closureLayerOfContent, visibleChargeStateAllowed]

theorem chargedLepton_visible_charge_is_signed :
    visibleChargeStateAllowed (closureLayerOfContent .chargedLepton) .positive ∧
      visibleChargeStateAllowed (closureLayerOfContent .chargedLepton) .negative := by
  exact ⟨by simp [closureLayerOfContent, visibleChargeStateAllowed],
    by simp [closureLayerOfContent, visibleChargeStateAllowed]⟩

theorem quark_visible_charge_channels_are_integer_states :
    visibleChargeStateAllowed (closureLayerOfContent .quark) .neutral ∧
      visibleChargeStateAllowed (closureLayerOfContent .quark) .positive ∧
      visibleChargeStateAllowed (closureLayerOfContent .quark) .negative := by
  exact ⟨by simp [closureLayerOfContent, visibleChargeStateAllowed],
    by simp [closureLayerOfContent, visibleChargeStateAllowed],
    by simp [closureLayerOfContent, visibleChargeStateAllowed]⟩

theorem visibleChargeState_toRat_values (q : VisibleChargeState) :
    q.toRat = 0 ∨ q.toRat = 1 ∨ q.toRat = -1 := by
  cases q <;> simp [VisibleChargeState.toRat, VisibleChargeState.toInt]

theorem visibleChargeState_toRat_ne_two_thirds (q : VisibleChargeState) :
    q.toRat ≠ (2 / 3 : ℚ) := by
  cases q <;> norm_num [VisibleChargeState.toRat, VisibleChargeState.toInt]

theorem visibleChargeState_toRat_ne_neg_one_third (q : VisibleChargeState) :
    q.toRat ≠ (-1 / 3 : ℚ) := by
  cases q <;> norm_num [VisibleChargeState.toRat, VisibleChargeState.toInt]

/-- Within the current three-class fermion taxonomy, the neutral/spin-only class
is the first closure rung. This is an enumerated-class theorem, not a uniqueness
claim over all possible future fermionic closure records. -/
theorem neutral_spinOnly_is_first_current_fermionic_closure_rung :
    closureLayerOfContent .neutrino = FermionClosureLayer.spinOnly ∧
      (∀ c : FermionContentClass,
        (closureLayerOfContent .neutrino).rank ≤ (closureLayerOfContent c).rank) ∧
      (∀ c : FermionContentClass,
        (closureLayerOfContent c).rank = (closureLayerOfContent .neutrino).rank ↔
          c = .neutrino) := by
  constructor
  · rfl
  constructor
  · intro c
    cases c <;> decide
  · intro c
    cases c <;> simp [closureLayerOfContent, FermionClosureLayer.rank]

theorem visible_shell_states_match_integer_lepton_charges :
    VisibleChargeState.toRat .neutral = Hqiv.Algebra.chargeFromY 4 (1 / 2) ∧
      VisibleChargeState.toRat .negative = Hqiv.Algebra.chargeFromY 5 (-1 / 2) ∧
      VisibleChargeState.toRat .positive = Hqiv.Algebra.chargeFromY 6 0 := by
  rw [Hqiv.Algebra.lepton_doublet_neutral_component_charge_zero,
    Hqiv.Algebra.lepton_doublet_charged_component_charge_neg_one,
    Hqiv.Algebra.charged_lepton_singlet_charge_pos_one]
  norm_num [VisibleChargeState.toRat, VisibleChargeState.toInt]

theorem quark_fractional_embedding_charges_are_residual_not_visible (q : VisibleChargeState) :
    q.toRat ≠ Hqiv.Algebra.chargeFromY 0 (1 / 2) ∧
      q.toRat ≠ Hqiv.Algebra.chargeFromY 1 (-1 / 2) := by
  rw [Hqiv.Algebra.up_component_charge_two_thirds,
    Hqiv.Algebra.down_component_charge_neg_one_third]
  exact ⟨visibleChargeState_toRat_ne_two_thirds q,
    visibleChargeState_toRat_ne_neg_one_third q⟩

theorem shellClass28_and_closureRank_are_parallel_bookkeeping (m : ℕ) (c : FermionContentClass) :
    Hqiv.Algebra.shellClass28 m = (m : ZMod 28) ∧
      (closureLayerOfContent c).rank = conservedTripleCount c := by
  exact ⟨rfl, closureLayer_rank_matches_triple_count c⟩

theorem quark_loop_residual_denominator_matches_colorComposed_rank :
    colorComposedResidualDenominator = (closureLayerOfContent .quark).rank := by
  norm_num [colorComposedResidualDenominator, closureLayerOfContent, FermionClosureLayer.rank]

theorem quark_residuals_are_loop_multiplicity_over_color_rank :
    ResidualChargeChannel.toRat .upLike =
      ResidualChargeChannel.loopMultiplicity .upLike / (closureLayerOfContent .quark).rank ∧
      ResidualChargeChannel.toRat .downLike =
        ResidualChargeChannel.loopMultiplicity .downLike / (closureLayerOfContent .quark).rank := by
  constructor <;> norm_num [ResidualChargeChannel.toRat, ResidualChargeChannel.loopMultiplicity,
    colorComposedResidualDenominator, closureLayerOfContent, FermionClosureLayer.rank]

theorem upLike_quark_residual_is_double_downLike_magnitude_over_color_rank :
    ResidualChargeChannel.toRat .upLike =
      2 * |ResidualChargeChannel.toRat .downLike| := by
  exact upLike_residual_is_double_downLike_magnitude

/-- Squared triple count: proxy for independent phase windings / harmonic complexity. -/
noncomputable def intrinsicWaveComplexity (c : FermionContentClass) : ℝ :=
  (conservedTripleCount c : ℝ) ^ 2

theorem intrinsicWaveComplexity_eq_sq (c : FermionContentClass) :
    intrinsicWaveComplexity c = (conservedTripleCount c : ℝ) ^ 2 :=
  rfl

theorem intrinsic_complexity_ν_lt_ℓ :
    intrinsicWaveComplexity .neutrino < intrinsicWaveComplexity .chargedLepton := by
  simp [intrinsicWaveComplexity, conservedTripleCount]

theorem intrinsic_complexity_ℓ_lt_q :
    intrinsicWaveComplexity .chargedLepton < intrinsicWaveComplexity .quark := by
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

theorem chargedLeptonContentCount_eq_conservedTripleCount :
    chargedLeptonContentCount = conservedTripleCount .chargedLepton := by
  simp [chargedLeptonContentCount, conservedTripleCount]

theorem chargedLepton_intrinsicWaveComplexity_eq_content_square :
    intrinsicWaveComplexity .chargedLepton = (chargedLeptonContentCount : ℝ) ^ 2 := by
  simp [intrinsicWaveComplexity, chargedLeptonContentCount, conservedTripleCount]

theorem chargedLepton_chargeDecorationFactor_over_neutral :
    intrinsicWaveComplexity .chargedLepton = 4 * intrinsicWaveComplexity .neutrino := by
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

theorem quark_intrinsicWaveComplexity_eq_content_square :
    intrinsicWaveComplexity .quark = (conservedTripleCount .quark : ℝ) ^ 2 := by
  simp [intrinsicWaveComplexity, conservedTripleCount]

theorem colorComposed_factor_over_chargeDecorated :
    intrinsicWaveComplexity .quark = (9 : ℝ) / 4 * intrinsicWaveComplexity .chargedLepton := by
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

theorem colorComposed_factor_over_neutral :
    intrinsicWaveComplexity .quark = 9 * intrinsicWaveComplexity .neutrino := by
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

theorem m_tau_from_lockin_surface_candidate_eq_chargeDecorated_closure :
    m_tau_from_lockin_surface_candidate =
      tauLockinSurfaceNormalization * intrinsicWaveComplexity .chargedLepton *
        effectiveSurface m_tau m_tau := by
  rw [chargedLepton_intrinsicWaveComplexity_eq_content_square]
  unfold m_tau_from_lockin_surface_candidate
  ring

theorem m_mu_from_lockin_surface_candidate_eq_chargeDecorated_relaxation :
    m_mu_from_lockin_surface_candidate =
      (tauLockinSurfaceNormalization * intrinsicWaveComplexity .chargedLepton *
        effectiveSurface m_tau m_tau) / resonance_k_tau_mu := by
  rw [m_mu_from_lockin_surface_candidate_eq_tau_over_resonance,
    m_tau_from_lockin_surface_candidate_eq_chargeDecorated_closure]

theorem m_e_from_lockin_surface_candidate_eq_chargeDecorated_two_step_relaxation :
    m_e_from_lockin_surface_candidate =
      (tauLockinSurfaceNormalization * intrinsicWaveComplexity .chargedLepton *
        effectiveSurface m_tau m_tau) / (resonance_k_tau_mu * resonance_k_mu_e) := by
  rw [m_e_from_lockin_surface_candidate_eq_tau_over_resonanceProduct,
    m_tau_from_lockin_surface_candidate_eq_chargeDecorated_closure]

theorem nucleonTraceChannelCount_eq_colorComposedTripleCount :
    nucleonTraceChannelCount = conservedTripleCount .quark := by
  simp [nucleonTraceChannelCount, conservedTripleCount]

theorem nucleonTraceChannelCount_eq_colorComposed_rank :
    nucleonTraceChannelCount = (closureLayerOfContent .quark).rank := by
  rw [closureLayer_rank_matches_triple_count]
  exact nucleonTraceChannelCount_eq_colorComposedTripleCount

theorem colorComposed_baryon_binding_uses_three_channel_network :
    nucleonSharedBinding_MeV =
      E_bind_QCD_from_network referenceM
        (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) := by
  rw [nucleonSharedBinding_from_composite_trace]
  rfl

theorem protonMassFromMetaHarmonics_eq_colorComposed_network_mass :
    protonMassFromMetaHarmonics_MeV =
      M_nucleon_from_network referenceM protonConstituentMass_MeV
        (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) := by
  rfl

theorem neutronMassFromMetaHarmonics_eq_colorComposed_network_mass :
    neutronMassFromMetaHarmonics_MeV =
      M_nucleon_from_network referenceM neutronConstituentMass_MeV
        (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) := by
  rfl

theorem colorComposed_quark_rung_has_three_harmonics_and_network_binding :
    nucleonTraceChannelCount = (closureLayerOfContent .quark).rank ∧
      protonMassFromMetaHarmonics_MeV =
        M_nucleon_from_network referenceM protonConstituentMass_MeV
          (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) ∧
      neutronMassFromMetaHarmonics_MeV =
        M_nucleon_from_network referenceM neutronConstituentMass_MeV
          (networkWeightFromCompositeTrace nucleonTraceDiagonal nucleonTraceState) := by
  exact ⟨nucleonTraceChannelCount_eq_colorComposed_rank,
    protonMassFromMetaHarmonics_eq_colorComposed_network_mass,
    neutronMassFromMetaHarmonics_eq_colorComposed_network_mass⟩

/-!
### S² phase harmonics ↔ `l²` (same quadratic as cumulative Laplace–Beltrami degeneracy)

On `S²`, the number of independent spherical-harmonic modes through degree `L` is `(L+1)²`
(`Hqiv.sum_two_mul_add_one_range_succ_sq` / `Hqiv.sphericalHarmonicCumulativeCount`).

For each sector, `conservedTripleCount c` is `l ∈ {1,2,3}`. Taking `L = l - 1` gives
`(L+1)² = l²`, which is exactly `intrinsicWaveComplexity c`. So the **same** integer `l²` that
weights `massScalingAnsatz` equals the **continuum** angular-mode capacity at cutoff `L = l-1`.

This does **not** identify the seven Fano lines with the three sectors: the seven-way split is
shell residue mod `7` (`OctonionicZeta` / `fano_prime`), while `l` is the conserved-triple count.
-/

theorem intrinsicWaveComplexity_eq_sphericalHarmonicCumulativeCount_pred (c : FermionContentClass) :
    intrinsicWaveComplexity c =
      sphericalHarmonicCumulativeCount (conservedTripleCount c - 1) := by
  cases c <;> simp [intrinsicWaveComplexity, conservedTripleCount, sphericalHarmonicCumulativeCount]
  <;> norm_num

/-!
### Combined `l² × effCorrected` scaling (normalization `k` > 0)
-/

/-- Candidate neutrino shells **4…6** (flattened-valley / small-`m` narrative; not unique). -/
def neutrinoShellCandidate : Finset ℕ :=
  Finset.Icc 4 6

theorem neutrinoShellCandidate_eq : neutrinoShellCandidate = Finset.Icc 4 6 :=
  rfl

/-- `m = 5` lies in the candidate band (matches the illustrative `m_ν ≈ 5` shell in the paper note). -/
theorem referenceNeutrinoShell_mem : (5 : ℕ) ∈ neutrinoShellCandidate := by
  simp [neutrinoShellCandidate]

/-- Mass-scale ansatz: single normalization `k` times `l²` times δ-corrected surface (`GlobalDetuning`). -/
noncomputable def massScalingAnsatz (k δ : ℝ) (l m : ℕ) : ℝ :=
  k * (l : ℝ) ^ 2 * effCorrected δ m

/--
Top-anchored normalization removes the free scale `k` by fixing the color-composed
heavy channel at the lock-in shell.
-/
noncomputable def topAnchoredNormalization (δ : ℝ) : ℝ :=
  allowedColorResonanceMass .upLike .heavy /
    (intrinsicWaveComplexity .quark * effCorrected δ m_top_at_lockin)

/--
Top-anchored derived map for each content class at shell `m`: same `l² × effCorrected`
form, but with `k` fixed by the top anchor at `m_top_at_lockin`.
-/
noncomputable def massScalingTopAnchored (δ : ℝ) (c : FermionContentClass) (m : ℕ) : ℝ :=
  massScalingAnsatz (topAnchoredNormalization δ) δ (closureLayerOfContent c).rank m

/--
With top-anchored normalization, every class/shell value is exactly the top anchor
times a content-factor ratio and a shell-surface ratio.
-/
theorem massScalingTopAnchored_eq_anchor_times_content_and_surface_ratio
    (δ : ℝ) (c : FermionContentClass) (m : ℕ)
    (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    massScalingTopAnchored δ c m =
      allowedColorResonanceMass .upLike .heavy *
        (intrinsicWaveComplexity c / intrinsicWaveComplexity .quark) *
        (effCorrected δ m / effCorrected δ m_top_at_lockin) := by
  unfold massScalingTopAnchored massScalingAnsatz topAnchoredNormalization
  have heff_pos : 0 < effCorrected δ m_top_at_lockin := effCorrected_pos δ m_top_at_lockin hden
  have heff_ne : effCorrected δ m_top_at_lockin ≠ 0 := ne_of_gt heff_pos
  have hq_ne : intrinsicWaveComplexity .quark ≠ 0 := by
    simp [intrinsicWaveComplexity, conservedTripleCount]
  rw [closureLayer_rank_matches_triple_count]
  field_simp [heff_ne, hq_ne]
  rw [intrinsicWaveComplexity_eq_sq c]
  ring_nf

/-- Grounded closure condition: top-anchored map recovers the heavy up-like top anchor exactly. -/
theorem massScalingTopAnchored_quark_top_shell_eq_anchor
    (δ : ℝ) (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    massScalingTopAnchored δ .quark m_top_at_lockin =
      allowedColorResonanceMass .upLike .heavy := by
  rw [massScalingTopAnchored_eq_anchor_times_content_and_surface_ratio δ .quark m_top_at_lockin hden]
  have heff_pos : 0 < effCorrected δ m_top_at_lockin := effCorrected_pos δ m_top_at_lockin hden
  have heff_ne : effCorrected δ m_top_at_lockin ≠ 0 := ne_of_gt heff_pos
  have hq_ne : intrinsicWaveComplexity .quark ≠ 0 := by
    simp [intrinsicWaveComplexity, conservedTripleCount]
  field_simp [hq_ne, heff_ne]

/-- Same grounded closure, stated directly on the exported top GeV witness. -/
theorem massScalingTopAnchored_quark_top_shell_eq_top_GeV
    (δ : ℝ) (hden : RindlerDenDeltaPos δ m_top_at_lockin) :
    massScalingTopAnchored δ .quark m_top_at_lockin = m_top_GeV := by
  rw [massScalingTopAnchored_quark_top_shell_eq_anchor δ hden,
    allowedColorResonanceMass_upLike_heavy_eq_top_GeV]

/-- Closure-layer form of the ansatz for each sector. -/
theorem massScalingAnsatz_closureLayer_forms (k δ : ℝ) (m : ℕ) :
    massScalingAnsatz k δ (closureLayerOfContent .neutrino).rank m =
      k * intrinsicWaveComplexity .neutrino * effCorrected δ m ∧
      massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m =
        k * intrinsicWaveComplexity .chargedLepton * effCorrected δ m ∧
      massScalingAnsatz k δ (closureLayerOfContent .quark).rank m =
        k * intrinsicWaveComplexity .quark * effCorrected δ m := by
  constructor
  · simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank, intrinsicWaveComplexity,
      conservedTripleCount]
  constructor
  · simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank, intrinsicWaveComplexity,
      conservedTripleCount]
  · simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank, intrinsicWaveComplexity,
      conservedTripleCount]

/-- At fixed shell and detuning, charge-decorated ansatz is exactly `4×` spin-only. -/
theorem massScalingAnsatz_chargeDecorated_eq_four_mul_spinOnly
    (k δ : ℝ) (m : ℕ) :
    massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m =
      4 * massScalingAnsatz k δ (closureLayerOfContent .neutrino).rank m := by
  simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank]
  ring

/-- At fixed shell and detuning, color-composed ansatz is exactly `9×` spin-only. -/
theorem massScalingAnsatz_colorComposed_eq_nine_mul_spinOnly
    (k δ : ℝ) (m : ℕ) :
    massScalingAnsatz k δ (closureLayerOfContent .quark).rank m =
      9 * massScalingAnsatz k δ (closureLayerOfContent .neutrino).rank m := by
  simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank]
  ring

/-- At fixed shell and detuning, color-composed ansatz is exactly `9/4×` charge-decorated. -/
theorem massScalingAnsatz_colorComposed_eq_nine_quarters_mul_chargeDecorated
    (k δ : ℝ) (m : ℕ) :
    massScalingAnsatz k δ (closureLayerOfContent .quark).rank m =
      (9 / 4 : ℝ) * massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m := by
  simp [massScalingAnsatz, closureLayerOfContent, FermionClosureLayer.rank]
  ring

private theorem sq_lt_sq_of_lt_of_pos {l1 l2 : ℕ} (h0 : 0 < l1) (hlt : l1 < l2) :
    (l1 : ℝ) ^ 2 < (l2 : ℝ) ^ 2 := by
  have h1 : (l1 : ℝ) < (l2 : ℝ) := Nat.cast_lt.mpr hlt
  have pos1 : 0 < (l1 : ℝ) := Nat.cast_pos.mpr h0
  have pos2 : 0 < (l2 : ℝ) := lt_trans pos1 h1
  nlinarith [h1, pos1, pos2]

/-- Larger conserved-triple count ⇒ larger ansatz at fixed `k`, `δ`, `m` (`k > 0`, `l` increasing). -/
theorem massScalingAnsatz_lt_of_lt_l {k δ : ℝ} {l1 l2 m : ℕ} (hk : 0 < k)
    (hl1 : 0 < l1) (hll : l1 < l2) (hδ : RindlerDenDeltaPos δ m) :
    massScalingAnsatz k δ l1 m < massScalingAnsatz k δ l2 m := by
  unfold massScalingAnsatz
  have heff : 0 < effCorrected δ m := effCorrected_pos δ m hδ
  have hsq := sq_lt_sq_of_lt_of_pos hl1 hll
  calc
    k * (l1 : ℝ) ^ 2 * effCorrected δ m
        = (l1 : ℝ) ^ 2 * (k * effCorrected δ m) := by ring
    _ < (l2 : ℝ) ^ 2 * (k * effCorrected δ m) := mul_lt_mul_of_pos_right hsq (mul_pos hk heff)
    _ = k * (l2 : ℝ) ^ 2 * effCorrected δ m := by ring

/-- At fixed positive `k` and `RindlerDenDeltaPos δ m`, the three fermion content rungs are strictly
ordered by closure rank (hence by `conservedTripleCount`): spin-only < charge-decorated < color-composed. -/
theorem massScalingAnsatz_fermion_three_rungs_strict_order (k δ : ℝ) (m : ℕ) (hk : 0 < k)
    (hδ : RindlerDenDeltaPos δ m) :
    massScalingAnsatz k δ (closureLayerOfContent .neutrino).rank m <
        massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m ∧
      massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m <
        massScalingAnsatz k δ (closureLayerOfContent .quark).rank m := by
  refine ⟨?_, ?_⟩
  · have hν := closureLayer_rank_neutrino_lt_chargedLepton
    have h0 : 0 < (closureLayerOfContent .neutrino).rank := by
      rw [closureLayer_rank_matches_triple_count .neutrino]
      decide
    exact massScalingAnsatz_lt_of_lt_l hk h0 hν hδ
  · have hχ := closureLayer_rank_chargedLepton_lt_quark
    have h0 : 0 < (closureLayerOfContent .chargedLepton).rank := by
      rw [closureLayer_rank_matches_triple_count .chargedLepton]
      decide
    exact massScalingAnsatz_lt_of_lt_l hk h0 hχ hδ

/-- Larger shell index ⇒ larger ansatz at fixed `k`, `l` (`k > 0`, `l > 0`, `0 ≤ δ`). -/
theorem massScalingAnsatz_lt_of_lt_m {k δ : ℝ} {l m n : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hδ : 0 ≤ δ) (hmn : m < n) (_hδm : RindlerDenDeltaPos δ m) (_hδn : RindlerDenDeltaPos δ n) :
    massScalingAnsatz k δ l m < massScalingAnsatz k δ l n := by
  unfold massScalingAnsatz
  have he := effCorrected_strictMono_nat hδ hmn
  have hl2 : 0 < (l : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hl) 2
  have hkl : 0 < k * (l : ℝ) ^ 2 := mul_pos hk hl2
  calc
    k * (l : ℝ) ^ 2 * effCorrected δ m
        = (k * (l : ℝ) ^ 2) * effCorrected δ m := by ring
    _ < (k * (l : ℝ) ^ 2) * effCorrected δ n := mul_lt_mul_of_pos_left he hkl
    _ = k * (l : ℝ) ^ 2 * effCorrected δ n := by ring

/-- At `s = -1` with trivial rapidity phase, the mass ansatz is `k·l²` times the shell zeta term. -/
theorem massScalingAnsatz_eq_k_l2_mul_zetaHQIVTerm_at_minus_one (k δ : ℝ) (l m : ℕ) (φ t : ℝ)
    (hphase : φ * t * delta_theta_prime (m : ℝ) = 0) :
    (massScalingAnsatz k δ l m : ℂ) = k * (l : ℝ) ^ 2 * zetaHQIVTerm δ φ t (-1) m := by
  unfold massScalingAnsatz zetaHQIVTerm
  have h0 : (φ * t * delta_theta_prime (m : ℝ) : ℂ) = 0 := by
    simpa using congrArg (fun (x : ℝ) => (x : ℂ)) hphase
  have harg : I * φ * t * delta_theta_prime (m : ℝ) = 0 := by
    have hI : I * φ * t * delta_theta_prime (m : ℝ) = I * ((φ * t * delta_theta_prime (m : ℝ)) : ℂ) := by ring_nf
    rw [hI, h0]
    simp
  have hcexp : cexp (I * φ * t * delta_theta_prime (m : ℝ)) = 1 := by rw [harg, Complex.exp_zero]
  simp [hcexp, neg_neg, Complex.cpow_one]

/-!
### Observed hierarchy from existing HQIV witnesses (same units: GeV-scale ℝ)
-/

/-- The derived electron-neutrino witness is the neutral outer-closure witness multiplied by the
outer-horizon neutrino suppression factor. This is the current cleanest “spin-first / neutral”
mass hook in the repo. -/
theorem m_nu_e_derived_from_neutralClosureWitness :
    m_nu_e_derived = outerHorizonNeutrinoSuppression * neutralClosureWitness := by
  rfl

/-- The whole ν ladder descends from the neutral outer-closure witness rather than the charged or
scalar closure channels. -/
theorem neutrino_ladder_from_neutralClosureWitness :
    m_nu_e_derived = outerHorizonNeutrinoSuppression * neutralClosureWitness ∧
    m_nu_mu_derived = outerHorizonNeutrinoSuppression ^ 2 * neutralClosureWitness ∧
    m_nu_tau_derived = outerHorizonNeutrinoSuppression ^ 3 * neutralClosureWitness := by
  constructor
  · exact m_nu_e_derived_from_neutralClosureWitness
  constructor
  · unfold m_nu_mu_derived
    rw [m_nu_e_derived_from_neutralClosureWitness]
    ring
  · unfold m_nu_tau_derived m_nu_mu_derived
    rw [m_nu_e_derived_from_neutralClosureWitness]
    ring

/-- Consolidated M3 package: in the current content bridge, the neutrino ladder
is the neutral/spin-only first fermionic rung and it descends from
`neutralClosureWitness`. The theorem deliberately quantifies only over
`FermionContentClass`, so it does not claim uniqueness in any larger future
fermion-closure search space. -/
theorem neutrino_ladder_is_current_neutral_spin_first_rung :
    closureLayerOfContent .neutrino = FermionClosureLayer.spinOnly ∧
      (∀ c : FermionContentClass,
        (closureLayerOfContent .neutrino).rank ≤ (closureLayerOfContent c).rank) ∧
      m_nu_e_derived = outerHorizonNeutrinoSuppression * neutralClosureWitness ∧
      m_nu_mu_derived = outerHorizonNeutrinoSuppression ^ 2 * neutralClosureWitness ∧
      m_nu_tau_derived = outerHorizonNeutrinoSuppression ^ 3 * neutralClosureWitness := by
  rcases neutral_spinOnly_is_first_current_fermionic_closure_rung with
    ⟨hspin, hmin, _huniqCurrent⟩
  rcases neutrino_ladder_from_neutralClosureWitness with ⟨he, hmu, htau⟩
  exact ⟨hspin, hmin, he, hmu, htau⟩

theorem m_nu_e_derived_lt_m_tau_from_resonance_anchor :
    m_nu_e_derived < m_tau_from_resonance := by
  rw [outer_horizon_neutrino_witness_from_adjacent_surfaces]
  have hsup :
      gammaDerived / outerHorizonSurface (referenceM + 2) = (1 : ℝ) / 140 := by
    simp [gammaDerived, referenceM, qcdShell, stepsFromQCDToLockin, latticeStepCount, outerHorizonSurface,
      alpha]
    norm_num
  rw [hsup, m_tau_from_resonance]
  have hmul : (1 : ℝ) / 140 * M_Z_derived < (1 : ℝ) / 140 * 120 :=
    mul_lt_mul_of_pos_left M_Z_derived_lt_one_twenty (by norm_num)
  have h120 : (1 : ℝ) / 140 * 120 < 1776.86e-3 := by norm_num
  linarith [hmul, h120]

theorem resonance_k_tau_mu_gt_one : 1 < resonance_k_tau_mu := by
  have hthr : chargedLeptonTauMuThreshold ≤ resonance_k_tau_mu := by
    rw [resonance_k_tau_mu_eq_geometricResonanceStep]
    exact derivedLeptonMuonShell_meets_threshold
  exact lt_of_lt_of_le chargedLeptonTauMuThreshold_gt_one hthr

theorem resonance_k_mu_e_gt_one : 1 < resonance_k_mu_e := by
  have hthr : chargedLeptonMuEThreshold ≤ resonance_k_mu_e := by
    rw [resonance_k_mu_e_eq_geometricResonanceStep]
    exact derivedLeptonElectronShell_meets_threshold
  exact lt_of_lt_of_le chargedLeptonMuEThreshold_gt_one hthr

theorem m_mu_from_lockin_surface_candidate_lt_m_tau_from_lockin_surface_candidate :
    m_mu_from_lockin_surface_candidate < m_tau_from_lockin_surface_candidate := by
  rw [m_mu_from_lockin_surface_candidate_eq_tau_over_resonance]
  have hτpos : 0 < m_tau_from_lockin_surface_candidate := by
    exact m_tau_from_lockin_surface_candidate_pos
  have hrpos : 0 < resonance_k_tau_mu := lt_trans zero_lt_one resonance_k_tau_mu_gt_one
  refine (div_lt_iff₀ hrpos).2 ?_
  nlinarith [hτpos, resonance_k_tau_mu_gt_one]

theorem m_e_from_lockin_surface_candidate_lt_m_mu_from_lockin_surface_candidate :
    m_e_from_lockin_surface_candidate < m_mu_from_lockin_surface_candidate := by
  rw [m_e_from_lockin_surface_candidate_eq_mu_over_resonance]
  have hμpos : 0 < m_mu_from_lockin_surface_candidate := by
    have hτpos : 0 < m_tau_from_lockin_surface_candidate := by
      exact m_tau_from_lockin_surface_candidate_pos
    have hrpos : 0 < resonance_k_tau_mu := lt_trans zero_lt_one resonance_k_tau_mu_gt_one
    rw [m_mu_from_lockin_surface_candidate_eq_tau_over_resonance]
    exact div_pos hτpos hrpos
  have hrpos : 0 < resonance_k_mu_e := lt_trans zero_lt_one resonance_k_mu_e_gt_one
  refine (div_lt_iff₀ hrpos).2 ?_
  nlinarith [hμpos, resonance_k_mu_e_gt_one]

theorem chargeDecorated_candidate_ladder_descends :
    m_nu_e_derived < m_tau_from_resonance ∧
      m_e_from_lockin_surface_candidate < m_mu_from_lockin_surface_candidate ∧
      m_mu_from_lockin_surface_candidate < m_tau_from_lockin_surface_candidate := by
  exact ⟨m_nu_e_derived_lt_m_tau_from_resonance_anchor,
    m_e_from_lockin_surface_candidate_lt_m_mu_from_lockin_surface_candidate,
    m_mu_from_lockin_surface_candidate_lt_m_tau_from_lockin_surface_candidate⟩

/-- Consolidated M4 package: the charged-lepton candidate ladder is the current
charge-decorated rung above the neutral/spin-only base, with signed visible
charges and the existing τ→μ→e relaxation order. This packages the rung; it does
not remove the active τ GeV witness. -/
theorem chargedLepton_ladder_is_chargeDecorated_rung_on_neutral_base :
    closureLayerOfContent .chargedLepton = FermionClosureLayer.chargeDecorated ∧
      (closureLayerOfContent .neutrino).rank <
        (closureLayerOfContent .chargedLepton).rank ∧
      visibleChargeStateAllowed (closureLayerOfContent .chargedLepton) .positive ∧
      visibleChargeStateAllowed (closureLayerOfContent .chargedLepton) .negative ∧
      m_nu_e_derived < m_tau_from_resonance ∧
      m_e_from_lockin_surface_candidate < m_mu_from_lockin_surface_candidate ∧
      m_mu_from_lockin_surface_candidate < m_tau_from_lockin_surface_candidate := by
  rcases chargedLepton_visible_charge_is_signed with ⟨hpos, hneg⟩
  rcases chargeDecorated_candidate_ladder_descends with ⟨hντ, heμ, hμτ⟩
  exact ⟨closureLayerOfContent_chargedLepton,
    closureLayer_rank_neutrino_lt_chargedLepton, hpos, hneg, hντ, heμ, hμτ⟩

theorem chargeDecorated_tau_candidate_lt_colorComposed_heavy_visible_band :
    m_tau_from_lockin_surface_candidate < allowedColorResonanceMass .upLike .heavy := by
  have hτ : m_tau_from_lockin_surface_candidate < m_tau_from_resonance :=
    m_tau_from_lockin_surface_candidate_lt_resonance
  have hres : m_tau_from_resonance < allowedColorResonanceMass .upLike .heavy := by
    rw [allowedColorResonanceMass_upLike_heavy_eq_top_GeV, m_tau_from_resonance]
    norm_num [m_top_GeV]
  exact lt_trans hτ hres

theorem visible_state_hierarchy_ν_e_tau_colorHeavy :
    m_nu_e_derived < m_tau_from_resonance ∧
      m_tau_from_lockin_surface_candidate < allowedColorResonanceMass .upLike .heavy := by
  exact ⟨m_nu_e_derived_lt_m_tau_from_resonance_anchor,
    chargeDecorated_tau_candidate_lt_colorComposed_heavy_visible_band⟩

/-- Heavy charged-lepton selector sits above the top lock-in shell. -/
theorem top_and_tau_lockin_rung_offset :
    m_top_at_lockin < leptonHeavyVertexShell := by
  simpa [m_top_at_lockin, m_lockin_eq_referenceM] using leptonHeavyVertexShell_gt_m_lockin

theorem top_and_tau_lockin_is_index_level_alignment :
    referenceM < leptonHeavyVertexShell ∧ m_top_at_lockin = referenceM := by
  exact ⟨leptonHeavyVertexShell_gt_referenceM, rfl⟩

/-- **ν_e derived scale is strictly below the τ resonance anchor.** -/
theorem m_nu_e_derived_lt_m_tau_from_resonance : m_nu_e_derived < m_tau_from_resonance := by
  exact m_nu_e_derived_lt_m_tau_from_resonance_anchor

/-- Content-class order aligns with the strict chain of triple counts. -/
theorem content_class_order_matches_triple_counts :
    conservedTripleCount .neutrino < conservedTripleCount .chargedLepton ∧
      conservedTripleCount .chargedLepton < conservedTripleCount .quark :=
  ⟨conservedTripleCount_ν_lt_ℓ, conservedTripleCount_ℓ_lt_q⟩

theorem colorComposed_visible_resonance_above_chargeDecorated_same_shell
    {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : RindlerDenDeltaPos δ m) :
    massScalingAnsatz k δ (closureLayerOfContent .chargedLepton).rank m <
      massScalingAnsatz k δ (closureLayerOfContent .quark).rank m := by
  have hl1 : 0 < (closureLayerOfContent .chargedLepton).rank := by
    simp [closureLayerOfContent, FermionClosureLayer.rank]
  have hlt : (closureLayerOfContent .chargedLepton).rank < (closureLayerOfContent .quark).rank := by
    exact closureLayer_rank_chargedLepton_lt_quark
  exact massScalingAnsatz_lt_of_lt_l hk hl1 hlt hδ

/-- Default sphere-transfer control used by the content bridge:
captures explicit angular momentum/excitation slots and "now"-scale transfer. -/
noncomputable def defaultSphereTransferSpec : SphereTransferSpec where
  angularMomentum := 2
  excitation := 0
  lambdaNow := 1 + gamma_HQIV
  anglePower := 1

/-- Sphere-projected transfer factor by content class:
neutrino/charged-lepton channels use `S³` only; quarks include `S⁷` hypercharge (two-pole default). -/
noncomputable def sphereProjectedTransferByContent (c : FermionContentClass) : ℝ :=
  match c with
  | .neutrino => leptonTransferThreshold defaultSphereTransferSpec
  | .chargedLepton => leptonTransferThreshold defaultSphereTransferSpec
  | .quark => quarkTransferThreshold defaultSphereTransferSpec 2

theorem sphereProjectedTransferByContent_leptons_use_only_s3 :
    sphereProjectedTransferByContent .neutrino =
      leptonTransferThreshold defaultSphereTransferSpec ∧
    sphereProjectedTransferByContent .chargedLepton =
      leptonTransferThreshold defaultSphereTransferSpec := by
  constructor <;> rfl

theorem sphereProjectedTransferByContent_quark_uses_s3_and_s7 :
    sphereProjectedTransferByContent .quark =
      quarkTransferThreshold defaultSphereTransferSpec 2 := rfl

end Hqiv.Physics
