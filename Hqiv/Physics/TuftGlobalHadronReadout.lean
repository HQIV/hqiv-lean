import Mathlib.Tactic
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.HadronMassReadout
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.TuftShellChart
import Hqiv.Physics.HadronMassReadout
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.MetaHorizonTrappedPlanckMass
import Hqiv.Physics.TuftShellChart

namespace Hqiv.Physics

open ContinuousXiPath

/-!
# Global TUFT hadron excitation readout (single formula, all sectors)

Python anchor: `scripts/hqiv_tuft_global_hadron_readout.py`.

## First-principles chain

1. **Ground** — vev-pinned baryon anchor scaled to TUFT chart row (`g_chart = g_heavy · m_chart/m_heavy`).
2. **Content weight** — `tuftContentExcitationWeight` from `HadronMassReadout` closure geometry.
3. **Beltrami drum** — chart surface / geometric-resonance steps (not per-hadron operators).
4. **Trapped inside ratio** — curvature volume × Planck budget (`tuftHadronTrappedInsideRatioAtShell`).
5. **Split inversion (partial closure)** — first-order on the trapped curve:
   `Δξ = w·ΔM_Beltrami / (g · ∂R/∂m)|_{m_ref}` with
   `∂R/∂m|_{m_ref} = R(m_ref+1,m_ref) − 1`.
6. **Channel twist** — 1-jet Fano detuning × `Ω_k` ratio, normalized to unity at `ξ_lock` per `(n,ℓ)`.

## Global mass

```text
m(ξ, channel) = g_chart(ξ) · [ 1 + (R_in(global) − 1) · G_twist(ξ) ]
```

* `R_in` branch (full closure, w = 1):
  - ground → 1
  - n=0, ℓ=1 → Compton phase (`tuftHadronEffectiveShellPhase`)
  - n=0, ℓ≥2 → split orbital Beltrami
  - ℓ=0, n≥1 → Compton phase radial
  - mixed n,ℓ → split radial + orbital Beltrami
* Partial meson closure (w<1): split with content weight always
-/

/-! ## Excitation channel tag -/

/-- Canonical excitation tag: TUFT chart row + internal quanta + valence content. -/
structure TuftExcitationChannel where
  chartShell : ℕ
  n : ℕ
  ℓ : ℕ
  valenceQuarks : ℕ
  nStrange : ℕ := 0
  isoscalar : Bool := false
  negativeParity : Bool := false
  deriving Repr

def tuftExcitationModeShell (ch : TuftExcitationChannel) : ℕ :=
  ch.chartShell + ch.n + ch.ℓ

def tuftExcitationRadialShell (ch : TuftExcitationChannel) : ℕ :=
  ch.chartShell + ch.n

def tuftExcitationOrbitalShell (ch : TuftExcitationChannel) : ℕ :=
  ch.chartShell + ch.ℓ

theorem tuftExcitationModeShell_baryon_ground :
    tuftExcitationModeShell ⟨tuftHeavyChartShell, 0, 0, 3, 0, false, false⟩ =
      tuftHeavyChartShell := by
  simp [tuftExcitationModeShell, tuftHeavyChartShell_eq_four]

/-! ## Content weight (re-export spine) -/

noncomputable def tuftGlobalContentWeight (ch : TuftExcitationChannel) : ℝ :=
  tuftContentExcitationWeight ch.valenceQuarks ch.nStrange ch.isoscalar

/-- Valence closure × excitation Beltrami coupling (unity for meson partial closure). -/
noncomputable def tuftGlobalBeltramiWeight (ch : TuftExcitationChannel) : ℝ :=
  tuftGlobalContentWeight ch *
    tuftExcitationCouplingWeight ch.n ch.ℓ ch.negativeParity

/-! ## Chart ground and Beltrami drum -/

noncomputable def tuftGlobalGroundAtXi_MeV (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  if ch.chartShell = tuftHeavyChartShell then
    tuftHadronGroundAtXi_MeV ξ
  else
    tuftMesonVectorGroundAtXi_MeV ξ

noncomputable def tuftGlobalBeltramiRadialDeltaAtXi (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  if ch.chartShell = tuftHeavyChartShell then
    tuftHadronBeltramiRadialDeltaAtXi ξ ch.n
  else
    tuftMesonBeltramiRadialDeltaAtXi ξ ch.n

noncomputable def tuftGlobalBeltramiOrbitalDeltaAtXi (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  if ch.chartShell = tuftHeavyChartShell then
    tuftHadronBeltramiOrbitalDeltaAtXi ξ ch.ℓ
  else
    tuftMesonBeltramiOrbitalDeltaAtXi ξ ch.ℓ

/-! ## Channel twist (unity at ξ_lock per mode) -/

noncomputable def tuftGlobalChannelTwistRatio (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  if ch.chartShell = tuftHeavyChartShell then
    tuftHadronGlobalChannelTwistRatio ξ ch.n ch.ℓ
  else
    tuftMesonGlobalChannelTwistRatio ξ ch.n ch.ℓ

theorem tuftGlobalChannelTwistRatio_at_lockin (ch : TuftExcitationChannel) :
    tuftGlobalChannelTwistRatio xiLockin ch = 1 := by
  unfold tuftGlobalChannelTwistRatio
  split_ifs <;> simp [tuftHadronGlobalChannelTwistRatio_at_lockin, tuftMesonGlobalChannelTwistRatio_at_lockin]

/-! ## Trapped inside ratio: discrete vs split (first-order curve inversion) -/

private theorem tuftHadronTrappedInsideRatioAtShell_eq_meta (m mRef : ℕ) :
    tuftHadronTrappedInsideRatioAtShell m mRef = metaHorizonTrappedInsideRatio m mRef := by
  unfold tuftHadronTrappedInsideRatioAtShell metaHorizonTrappedInsideRatio
    tuftHadronCurvatureVolumeThrough metaHorizonCurvatureVolumeThrough
    tuftHadronTrappedPlanckBudgetThrough trappedPlanckCumulativeBudget
  rfl

private theorem tuftHadronTrappedPlanckBudgetThrough_pos (m : ℕ) :
    0 < tuftHadronTrappedPlanckBudgetThrough m := by
  unfold tuftHadronTrappedPlanckBudgetThrough vacuumZeroPointEnergy
  have hne : (Finset.Icc planckUVCutoff m).Nonempty := ⟨planckUVCutoff, by
    simp [planckUVCutoff, Finset.mem_Icc]⟩
  refine Finset.sum_pos (fun k _ => ?_) hne
  have h1 : 0 < shellModeMultiplicity k := shellModeMultiplicity_pos k
  have h2 : 0 < shellOmega k := shellOmega_pos k
  exact div_pos (mul_pos h1 h2) (by norm_num : (0 : ℝ) < 2)

private theorem tuftHadronTrappedInsideRatioAtShell_self (m : ℕ) :
    tuftHadronTrappedInsideRatioAtShell m m = 1 := by
  rw [tuftHadronTrappedInsideRatioAtShell_eq_meta, metaHorizonTrappedInsideRatio_self]
  · exact metaHorizonCurvatureVolumeThrough_pos m
  · exact tuftHadronTrappedPlanckBudgetThrough_pos m

noncomputable def tuftTrappedInsideRatioSlopeAtChart (mRef : ℕ) : ℝ :=
  metaHorizonTrappedInsideRatio (mRef + 1) mRef - 1

theorem tuftTrappedInsideRatioSlopeAtChart_pos (mRef : ℕ) :
    0 < tuftTrappedInsideRatioSlopeAtChart mRef := by
  unfold tuftTrappedInsideRatioSlopeAtChart
  have hlt : mRef < mRef + 1 := Nat.lt_succ_self mRef
  exact (sub_pos).2 (metaHorizonTrappedInsideRatio_gt_one_of_shell_gt hlt)

/-- First-order Beltrami → ξ offset on the chart trapped curve. -/
noncomputable def tuftBeltramiDeltaToXiOffset (mRef : ℕ) (ground wDeltaM : ℝ) : ℝ :=
  if wDeltaM ≤ 0 then 0 else wDeltaM / (ground * tuftTrappedInsideRatioSlopeAtChart mRef)

theorem tuftBeltramiDeltaToXiOffset_zero (mRef : ℕ) (ground : ℝ) :
    tuftBeltramiDeltaToXiOffset mRef ground 0 = 0 := by
  simp [tuftBeltramiDeltaToXiOffset]

noncomputable def tuftGlobalEffectiveXiSplitAtXi (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  let mRef := ch.chartShell
  let ground := tuftGlobalGroundAtXi_MeV ξ ch
  let w := tuftGlobalBeltramiWeight ch
  let xi0 := xiOfShell mRef
  if ch.n = 0 ∧ ch.ℓ = 0 then
    xi0
  else
    xi0 +
      (if ch.n = 0 then 0 else
        tuftBeltramiDeltaToXiOffset mRef ground (w * tuftGlobalBeltramiRadialDeltaAtXi ξ ch)) +
      (if ch.ℓ = 0 then 0 else
        tuftBeltramiDeltaToXiOffset mRef ground (w * tuftGlobalBeltramiOrbitalDeltaAtXi ξ ch))

noncomputable def tuftGlobalTrappedInsideRatioAtXi (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  if ch.n = 0 ∧ ch.ℓ = 0 then
    1
  else
    let w := tuftGlobalContentWeight ch
    let mRef := ch.chartShell
    if w ≠ 1 then
      tuftHadronTrappedInsideRatioInterp (tuftGlobalEffectiveXiSplitAtXi ξ ch - 1) mRef
    else if ch.valenceQuarks ≠ 3 then
      tuftHadronTrappedInsideRatioAtShell (tuftExcitationModeShell ch) mRef
    else if ch.n = 0 ∧ ch.ℓ = 1 then
      tuftHadronTrappedInsideRatioInterp (tuftHadronEffectiveShellPhase 0 1) mRef
    else if ch.n = 0 ∧ 2 ≤ ch.ℓ then
      tuftHadronTrappedInsideRatioInterp (tuftGlobalEffectiveXiSplitAtXi ξ ch - 1) mRef
    else if ch.ℓ = 0 ∧ 1 ≤ ch.n then
      tuftHadronTrappedInsideRatioInterp (tuftHadronEffectiveShellPhase ch.n 0) mRef
    else
      tuftHadronTrappedInsideRatioInterp (tuftGlobalEffectiveXiSplitAtXi ξ ch - 1) mRef

theorem tuftGlobalTrappedInsideRatioAtXi_ground (ξ : ℝ) (ch : TuftExcitationChannel)
    (h : ch.n = 0 ∧ ch.ℓ = 0) :
    tuftGlobalTrappedInsideRatioAtXi ξ ch = 1 := by
  unfold tuftGlobalTrappedInsideRatioAtXi
  simp [h.1, h.2]

/-! ## Global excited mass (single readout) -/

noncomputable def tuftExcitedMassGlobalAtXi_MeV (ξ : ℝ) (ch : TuftExcitationChannel) : ℝ :=
  let g := tuftGlobalGroundAtXi_MeV ξ ch
  let r := tuftGlobalTrappedInsideRatioAtXi ξ ch
  let twist := tuftGlobalChannelTwistRatio ξ ch
  g * (1 + (r - 1) * twist)

theorem tuftExcitedMassGlobalAtXi_MeV_ground (ξ : ℝ) (ch : TuftExcitationChannel)
    (h : ch.n = 0 ∧ ch.ℓ = 0) :
    tuftExcitedMassGlobalAtXi_MeV ξ ch = tuftGlobalGroundAtXi_MeV ξ ch := by
  unfold tuftExcitedMassGlobalAtXi_MeV
  rw [tuftGlobalTrappedInsideRatioAtXi_ground ξ ch h]
  ring

/-- Baryon specialization on the heavy TUFT chart. -/
noncomputable def tuftExcitedMassGlobalBaryonChannelAtXi_MeV (ξ : ℝ) (n ℓ : ℕ) : ℝ :=
  tuftExcitedMassGlobalAtXi_MeV ξ ⟨tuftHeavyChartShell, n, ℓ, 3, 0, false, false⟩

/-- Meson specialization on the strong TUFT chart. -/
noncomputable def tuftExcitedMassGlobalMesonChannelAtXi_MeV (ξ : ℝ) (n ℓ nStrange : ℕ) (isoscalar : Bool) : ℝ :=
  tuftExcitedMassGlobalAtXi_MeV ξ ⟨tuftStrongChartShell, n, ℓ, 2, nStrange, isoscalar, false⟩

#check tuftExcitedMassGlobalAtXi_MeV
#check tuftExcitedMassGlobalBaryonChannelAtXi_MeV
#check tuftExcitedMassGlobalMesonChannelAtXi_MeV

end Hqiv.Physics
