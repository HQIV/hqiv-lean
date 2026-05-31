import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.ReadoutGaugeSeed
import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.ContinuousXiPath

namespace Hqiv.Physics

open Hqiv.Physics.ContinuousXiPath

/-!
# Neutron binding stability scaffold (bonded vs free)

Paper: `papers/paper/nucleon_binding_beta_decay.tex`, Conjecture β (curvature ledger +
skew alignment in nuclear wells vs sub-lock-in free branch).

**Proved here:** packaging of existing binding (`nucleonSharedBinding_MeV`), spin–statistics
width identity (`Γ = ΔE/ħ`), continuous-ξ lock-in calibration (`omegaK_xi xiLockin = 1`),
and conditional discrete–continuous Ωₖ readout at `referenceM` (via `readoutOmegaKIntegerBridge`).

**Open slots (explicit `Prop`):** skew alignment, full β Q-value / 880 s lifetime, and
identification of weak tipping matrix elements with `freeNeutronOverlapEnergy`.
-/

/-! ## Embedding and stability predicates -/

/--
Nuclear environment for a neutron: well depth from `nuclear_effective_potential` /
integrated Maxwell well / deuteron-scale bookkeeping, Ωₖ readout, continuous-ξ coordinate,
and skew alignment (Conjecture β).
-/
structure NuclearNeutronEmbedding where
  /-- Environmental well depth (MeV-scale bookkeeping; not the shared baryon trace alone). -/
  wellDepth : ℝ
  /-- Normalized Ωₖ-type readout at the embedding shell (≥ 1 when the ledger is closed). -/
  omegaReadout : ℝ
  /-- Horizon coordinate ξ on the continuous chart (`xiOfShell m = m + 1`). -/
  xiReadout : ℝ
  /-- Triality-compatible skew realignment (Conjecture β; not discharged here). -/
  skewAligned : Prop

/-- Shared composite-trace binding plus a nonnegative nuclear well closes the depth slot. -/
def wellDepthSufficient (e : NuclearNeutronEmbedding) : Prop :=
  0 < e.wellDepth + nucleonSharedBinding_MeV

/-- Curvature ledger closed at or above lock-in calibration (Ω ≥ 1). -/
def curvatureLedgerClosed (e : NuclearNeutronEmbedding) : Prop :=
  1 ≤ e.omegaReadout

/-- Bonded neutron stability: depth + closed Ω ledger + skew alignment (Conjecture β). -/
def bondedNeutronStable (e : NuclearNeutronEmbedding) : Prop :=
  wellDepthSufficient e ∧ curvatureLedgerClosed e ∧ e.skewAligned

/-! ## Free branch: overlap energy and decay channels -/

/-- Sub-lock-in curvature deficit (zero when `omegaReadout ≥ 1`). -/
noncomputable def freeNeutronCurvatureDeficit (omegaReadout : ℝ) : ℝ :=
  max 0 (1 - omegaReadout)

/--
Strong-resonance overlap witness: hypercharge bookkeeping gap plus optional curvature deficit.

Not identified with the full β Q-value (~0.78 MeV); see Conjecture β remark in the nucleon paper.
-/
noncomputable def freeNeutronOverlapEnergy (omegaReadout : ℝ) : ℝ :=
  nucleonIsospinGap_MeV + freeNeutronCurvatureDeficit omegaReadout

theorem freeNeutronCurvatureDeficit_nonneg (omegaReadout : ℝ) :
    0 ≤ freeNeutronCurvatureDeficit omegaReadout := by
  unfold freeNeutronCurvatureDeficit
  positivity

theorem freeNeutronOverlapEnergy_nonneg (omegaReadout : ℝ) :
    0 ≤ freeNeutronOverlapEnergy omegaReadout := by
  unfold freeNeutronOverlapEnergy freeNeutronCurvatureDeficit
  rw [nucleonIsospinGap_eq_one]
  positivity

theorem freeNeutronOverlapEnergy_eq_isospinGap_when_ledger_closed
    {ω : ℝ} (hω : 1 ≤ ω) :
    freeNeutronOverlapEnergy ω = nucleonIsospinGap_MeV := by
  unfold freeNeutronOverlapEnergy freeNeutronCurvatureDeficit
  have hmax : max 0 (1 - ω) = 0 := by
    rw [max_eq_left (by linarith)]
  rw [hmax, nucleonIsospinGap_eq_one, add_zero]

theorem freeNeutronOverlapEnergy_pos (omegaReadout : ℝ) :
    0 < freeNeutronOverlapEnergy omegaReadout := by
  unfold freeNeutronOverlapEnergy freeNeutronCurvatureDeficit
  rw [nucleonIsospinGap_eq_one]
  have hnonneg : 0 ≤ max 0 (1 - omegaReadout) := by positivity
  linarith

def freeNeutronCurvatureSubLockin (omegaReadout : ℝ) : Prop :=
  omegaReadout < 1

theorem freeNeutronCurvatureDeficit_pos_of_subLockin
    {ω : ℝ} (hω : freeNeutronCurvatureSubLockin ω) :
    0 < freeNeutronCurvatureDeficit ω := by
  unfold freeNeutronCurvatureDeficit freeNeutronCurvatureSubLockin at *
  have h1w : 1 - ω > 0 := by linarith
  simpa [max_eq_left h1w.le] using h1w

theorem freeNeutronOverlapEnergy_gt_isospinGap_of_subLockin
    {ω : ℝ} (hω : freeNeutronCurvatureSubLockin ω) :
    nucleonIsospinGap_MeV < freeNeutronOverlapEnergy ω := by
  unfold freeNeutronOverlapEnergy freeNeutronCurvatureDeficit
  rw [nucleonIsospinGap_eq_one]
  exact lt_add_of_pos_right _ (freeNeutronCurvatureDeficit_pos_of_subLockin hω)

/-! ## Strong width vs weak β channel (kept separate) -/

/-- Strong-resonance width `Γ = ΔE/ħ` from `SpinStatistics` / `HQIVNuclei`. -/
noncomputable def freeNeutronStrongDecayWidth (omegaReadout : ℝ) : ℝ :=
  decayWidth_per_s (freeNeutronOverlapEnergy omegaReadout)

/--
Weak β width slot: electric tipping / `G_F_from_beta` (not the strong `ΔE/ħ` line).

Lifetime ~ 880 s is **not** derived from `freeNeutronOverlapEnergy`.
-/
noncomputable def freeNeutronWeakDecayWidth (m_e ℳ : ℝ) : ℝ :=
  beta_decay_rate Fermion.neutron m_e ℳ

theorem freeNeutronStrongDecayWidth_pos (omegaReadout : ℝ) :
    0 < freeNeutronStrongDecayWidth omegaReadout := by
  unfold freeNeutronStrongDecayWidth decayWidth_per_s
  exact div_pos (freeNeutronOverlapEnergy_pos omegaReadout) (by unfold hbar_MeV_s; norm_num)

theorem free_neutron_strong_half_life_from_spin_statistics (omegaReadout : ℝ) :
    half_life_from_width (freeNeutronStrongDecayWidth omegaReadout) =
      resonance_half_life (freeNeutronOverlapEnergy omegaReadout) :=
  spin_statistics_determines_half_life (freeNeutronOverlapEnergy_pos omegaReadout)

/-! ## Continuous ξ participation (lock-in calibration) -/

/--
Readout at lock-in on the continuous chart: `omegaK_xi xiLockin = 1`.

Uses only the proved continuous lock-in theorem (no global Ω bridge required).
-/
theorem bondedNeutronReadoutCalibrated
    (e : NuclearNeutronEmbedding) (hXi : e.xiReadout = xiLockin) :
    omegaK_xi e.xiReadout = 1 := by
  rw [hXi]
  simpa [omegaK_partial_xi] using omegaK_partial_xi_lockin

theorem bondedNeutronReadoutCalibrated_discrete
    (hpos : 0 < curvature_integral referenceM) :
    omega_k_partial referenceM = 1 :=
  omega_k_partial_at_reference hpos

/--
When the global `Ωₖ` integer bridge holds and the embedding sits at lock-in ξ,
continuous and discrete readouts agree and equal `1`.
-/
theorem bondedNeutronOmegaReadout_matches_continuous_at_lockin
    (hBridge : readoutOmegaKIntegerBridge)
    (hpos : 0 < curvature_integral referenceM)
    (e : NuclearNeutronEmbedding) (hXi : e.xiReadout = xiLockin) :
    omegaK_xi e.xiReadout = omega_k_partial referenceM ∧
      omegaK_xi xiLockin = 1 ∧ omega_k_partial referenceM = 1 := by
  have hΩxi : omegaK_xi e.xiReadout = 1 := bondedNeutronReadoutCalibrated e hXi
  have hΩdisc : omega_k_partial referenceM = 1 := omega_k_partial_at_reference hpos
  refine ⟨?_, ?_, ?_⟩
  · rw [hXi, xiLockin_eq_xiOfShell_referenceM, hBridge referenceM, hΩdisc]
  · exact omegaK_partial_xi_lockin
  · exact hΩdisc

theorem bondedNeutron_curvatureLedger_from_lockin_xi
    (e : NuclearNeutronEmbedding) (hXi : e.xiReadout = xiLockin)
    (hΩ : e.omegaReadout = omegaK_xi e.xiReadout) :
    curvatureLedgerClosed e := by
  unfold curvatureLedgerClosed
  rw [hΩ, bondedNeutronReadoutCalibrated e hXi]

/-- No unfavorable imprint increment at a fixed calibrated ξ (degenerate step). -/
theorem bondedNeutron_unfavorableImprint_zero_at_lockin
    (e : NuclearNeutronEmbedding) (hXi : e.xiReadout = xiLockin) :
    imprintWeightedReadoutPhase_xi e.xiReadout e.xiReadout = 0 := by
  rw [hXi]
  exact imprintWeightedReadoutPhase_xi_of_omega_eq xiLockin xiLockin rfl

theorem bondedNeutron_imprint_matches_discrete_at_reference
    (hBridge : readoutOmegaKIntegerBridge) :
    imprintWeightedReadoutPhase_xi_alias
        (xiOfShell referenceM) (xiOfShell (referenceM + 1)) =
      imprintWeightedReadoutPhase referenceM :=
  imprintWeightedReadoutPhase_xi_matches_integer_step hBridge referenceM

end Hqiv.Physics
