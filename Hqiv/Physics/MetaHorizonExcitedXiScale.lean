import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.FanoDetuningFirstOrder
import Hqiv.Physics.FanoSectorSpectralMassEmergence
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.MetaHorizonBeltramiExcitedStates

namespace Hqiv.Physics

open ContinuousXiPath

/-!
# Meta-horizon excited masses on the continuous ξ ladder

Excited radial/orbital channels sit on **`totalModeShell n ℓ = referenceM + n + ℓ`**, one rung
above the lock-in ground on the integer chart.  That rung carries **extra curvature**
(`Ω_k(ξ)`) and **affine Fano/O-Maxwell detuning twist** (`1 + γ/2 · m`).

This module proves that the **ξ-scaled excited readout** factors as:

* hadronic ground at epoch `ξ` (dynamic Casimir / heavy-gap normalization);
* lock-in Beltrami excitation increments (`MetaHorizonBeltramiExcitedStates`);
* explicit **curvature × detuning twist** from the excited channel shell.

At `ξ = ξ_lock` and `(n,ℓ) = (0,0)` all twist factors reduce to `1` and the readout
recovers `metaHorizonExcitedMassReadout`.
-/

/-! ## Excited-channel geometry on the ξ ladder -/

/-- Shell index probed by a combined radial/orbital excitation. -/
def metaHorizonExcitedChannelShell (n ℓ : ℕ) : ℕ :=
  totalModeShell n ℓ

theorem metaHorizonExcitedChannelShell_eq_totalModeShell (n ℓ : ℕ) :
    metaHorizonExcitedChannelShell n ℓ = totalModeShell n ℓ := rfl

theorem metaHorizonExcitedChannelShell_ground_eq_referenceM :
    metaHorizonExcitedChannelShell 0 0 = referenceM := by
  simp [metaHorizonExcitedChannelShell, totalModeShell]

/-- Ground excited channel equals the TUFT heavy chart row (numeric coincidence with `referenceM` today). -/
theorem metaHorizonExcitedChannelShell_ground_eq_tuftHeavyChartShell :
    metaHorizonExcitedChannelShell 0 0 = tuftHeavyChartShell := by
  rw [metaHorizonExcitedChannelShell_ground_eq_referenceM, referenceM_eq_tuftHeavyChartShell_numeric]

theorem metaHorizonExcitedChannelShell_ground :
    metaHorizonExcitedChannelShell 0 0 = referenceM :=
  metaHorizonExcitedChannelShell_ground_eq_referenceM

/-- Horizon coordinate of the excited channel on the integer ξ chart. -/
noncomputable def metaHorizonExcitedChannelXi (n ℓ : ℕ) : ℝ :=
  xiOfShell (metaHorizonExcitedChannelShell n ℓ)

theorem metaHorizonExcitedChannelXi_ground :
    metaHorizonExcitedChannelXi 0 0 = xiLockin := by
  rw [metaHorizonExcitedChannelXi, metaHorizonExcitedChannelShell_ground, xiLockin_eq_xiOfShell_referenceM]

theorem metaHorizonExcitedChannelXi_succ (n ℓ : ℕ) :
    metaHorizonExcitedChannelXi (n + 1) ℓ =
      metaHorizonExcitedChannelXi n ℓ + 1 := by
  simp [metaHorizonExcitedChannelXi, metaHorizonExcitedChannelShell, totalModeShell, xiOfShell]
  ring_nf

theorem metaHorizonExcitedChannelXi_gt_one (n ℓ : ℕ) :
    (1 : ℝ) < metaHorizonExcitedChannelXi n ℓ := by
  rw [metaHorizonExcitedChannelXi, xiOfShell, metaHorizonExcitedChannelShell, totalModeShell,
    referenceM_eq_four]
  norm_cast
  omega

/-! ## Curvature and detuning twist weights -/

/-- `Ω_k` ratio: excited channel vs lock-in reference on the temperature ladder. -/
noncomputable def metaHorizonExcitedOmegaKRatio (n ℓ : ℕ) : ℝ :=
  omegaK_xi (metaHorizonExcitedChannelXi n ℓ) / omegaK_xi xiLockin

/-- Affine Fano/O-Maxwell detuning twist at the excited shell index. -/
noncomputable def metaHorizonExcitedDetuningTwist (n ℓ : ℕ) : ℝ :=
  omaxwellFanoDetuning1Jet (metaHorizonExcitedChannelShell n ℓ) /
    omaxwellFanoDetuning1Jet referenceM

/--
Combined **curvature × twist** weight for excitation increments observed at epoch `ξ`.

The numerator uses the **excited channel's** integer-chart ξ sample; the denominator
anchors the epoch reference `ξ` on the continuous ladder.  The detuning factor records
the Rindler/Fano jet growth (`B = ⋆d` sector) along the excited shell index.
-/
noncomputable def metaHorizonExcitedChannelTwistAtEpoch (ξ : ℝ) (n ℓ : ℕ) : ℝ :=
  (omegaK_xi (metaHorizonExcitedChannelXi n ℓ) / omegaK_xi ξ) *
    metaHorizonExcitedDetuningTwist n ℓ

theorem metaHorizonExcitedOmegaKRatio_ground :
    metaHorizonExcitedOmegaKRatio 0 0 = 1 := by
  rw [metaHorizonExcitedOmegaKRatio, metaHorizonExcitedChannelXi_ground, omegaK_xi_lockin_eq_one]
  field_simp [omegaK_xi_lockin_eq_one]

theorem metaHorizonExcitedDetuningTwist_ground :
    metaHorizonExcitedDetuningTwist 0 0 = 1 := by
  rw [metaHorizonExcitedDetuningTwist, metaHorizonExcitedChannelShell_ground]
  field_simp [ne_of_gt (omaxwellFanoDetuning1Jet_pos referenceM)]

theorem metaHorizonExcitedChannelTwistAtEpoch_at_lockin_ground :
    metaHorizonExcitedChannelTwistAtEpoch xiLockin 0 0 = 1 := by
  unfold metaHorizonExcitedChannelTwistAtEpoch
  rw [metaHorizonExcitedChannelXi_ground, metaHorizonExcitedDetuningTwist_ground, omegaK_xi_lockin_eq_one]
  field_simp [omegaK_xi_lockin_eq_one, one_mul]

private theorem xiOfShell_lt_of_shell_lt {m₁ m₂ : ℕ} (h : m₁ < m₂) :
    xiOfShell m₁ < xiOfShell m₂ := by
  simp [xiOfShell]
  exact_mod_cast h

private theorem omaxwellFanoDetuning1Jet_lt_of_lt {m₁ m₂ : ℕ} (h : m₁ < m₂) :
    omaxwellFanoDetuning1Jet m₁ < omaxwellFanoDetuning1Jet m₂ := by
  rw [omaxwellFanoDetuning1Jet_eq_one_plus_half_gamma, omaxwellFanoDetuning1Jet_eq_one_plus_half_gamma,
    gamma_eq_2_5]
  have hm : (m₁ : ℝ) < m₂ := Nat.cast_lt.mpr h
  nlinarith

theorem metaHorizonExcitedDetuningTwist_gt_one_of_channel_above_lockin
    {n ℓ : ℕ} (h : referenceM < metaHorizonExcitedChannelShell n ℓ) :
    1 < metaHorizonExcitedDetuningTwist n ℓ := by
  unfold metaHorizonExcitedDetuningTwist
  have hjet :
      omaxwellFanoDetuning1Jet referenceM < omaxwellFanoDetuning1Jet (metaHorizonExcitedChannelShell n ℓ) :=
    omaxwellFanoDetuning1Jet_lt_of_lt h
  have hden : 0 < omaxwellFanoDetuning1Jet referenceM := omaxwellFanoDetuning1Jet_pos referenceM
  rw [one_lt_div hden]
  exact hjet

theorem metaHorizonExcitedOmegaKRatio_gt_one_of_channel_xi_above_lockin
    {n ℓ : ℕ} (h : xiLockin < metaHorizonExcitedChannelXi n ℓ) :
    1 < metaHorizonExcitedOmegaKRatio n ℓ := by
  unfold metaHorizonExcitedOmegaKRatio
  have hpos : 0 < omegaK_xi xiLockin := by rw [omegaK_xi_lockin_eq_one]; norm_num
  rw [one_lt_div hpos]
  exact omegaK_xi_strictMono xiLockin (metaHorizonExcitedChannelXi n ℓ)
    (le_of_eq xiLockin_eq_five.symm) h

theorem metaHorizonExcitedChannelTwist_gt_one_at_lockin_of_radial
    (n : ℕ) (hn : 0 < n) :
    1 < metaHorizonExcitedChannelTwistAtEpoch xiLockin n 0 := by
  have hshell : referenceM < metaHorizonExcitedChannelShell n 0 := by
    simp only [metaHorizonExcitedChannelShell, totalModeShell]
    omega
  have hshell_lt : referenceM < referenceM + n := by omega
  have hξ : xiLockin < metaHorizonExcitedChannelXi n 0 := by
    rw [metaHorizonExcitedChannelXi, metaHorizonExcitedChannelShell, totalModeShell]
    exact xiOfShell_lt_of_shell_lt hshell_lt
  have hω := metaHorizonExcitedOmegaKRatio_gt_one_of_channel_xi_above_lockin hξ
  have hjet := metaHorizonExcitedDetuningTwist_gt_one_of_channel_above_lockin hshell
  have hω' : 1 < omegaK_xi (metaHorizonExcitedChannelXi n 0) := by
    unfold metaHorizonExcitedOmegaKRatio at hω
    rw [omegaK_xi_lockin_eq_one, div_one] at hω
    exact hω
  have hξpos : 1 < metaHorizonExcitedChannelXi n 0 := by
    have h5 : (1 : ℝ) < xiLockin := by rw [xiLockin_eq_five]; norm_num
    linarith
  have hωpos : 0 < omegaK_xi (metaHorizonExcitedChannelXi n 0) :=
    omegaK_xi_pos (metaHorizonExcitedChannelXi n 0) hξpos
  unfold metaHorizonExcitedDetuningTwist at hjet
  unfold metaHorizonExcitedChannelTwistAtEpoch metaHorizonExcitedDetuningTwist
  rw [omegaK_xi_lockin_eq_one, div_one]
  exact lt_trans hω' (lt_mul_of_one_lt_right hωpos hjet)

theorem metaHorizonExcitedChannelTwistAtEpoch_pos (ξ : ℝ) (n ℓ : ℕ) (hξ : (1 : ℝ) < ξ) :
    0 < metaHorizonExcitedChannelTwistAtEpoch ξ n ℓ := by
  unfold metaHorizonExcitedChannelTwistAtEpoch metaHorizonExcitedDetuningTwist
  have hch : (1 : ℝ) < metaHorizonExcitedChannelXi n ℓ :=
    metaHorizonExcitedChannelXi_gt_one n ℓ
  have hω : 0 < omegaK_xi (metaHorizonExcitedChannelXi n ℓ) / omegaK_xi ξ :=
    div_pos (omegaK_xi_pos (metaHorizonExcitedChannelXi n ℓ) hch) (omegaK_xi_pos ξ hξ)
  have hjet : 0 < omaxwellFanoDetuning1Jet (metaHorizonExcitedChannelShell n ℓ) /
      omaxwellFanoDetuning1Jet referenceM :=
    div_pos (omaxwellFanoDetuning1Jet_pos _) (omaxwellFanoDetuning1Jet_pos referenceM)
  exact mul_pos hω hjet

/-! ## ξ-scaled hadronic ground and excited readout -/

/-- Dynamic hadronic ground at epoch `ξ` (Casimir/heavy-gap normalization at lock-in). -/
noncomputable def metaHorizonHadronicGroundAtXi (ξ : ℝ) : ℝ :=
  derivedProtonMass * (heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5)

theorem metaHorizonHadronicGroundAtXi_at_lockin :
    metaHorizonHadronicGroundAtXi xiLockin = derivedProtonMass := by
  unfold metaHorizonHadronicGroundAtXi
  have hξ : xiLockin = (5 : ℝ) := xiLockin_eq_five
  rw [hξ, heavy_lepton_gap_at_lockin_eq_four_fifths]
  ring

theorem metaHorizonHadronicGroundAtXi_at_five :
    metaHorizonHadronicGroundAtXi 5 = derivedProtonMass := by
  rw [← xiLockin_eq_five]
  exact metaHorizonHadronicGroundAtXi_at_lockin

/-- Beltrami excitation increment at epoch `ξ`, including curvature/twist on the channel. -/
noncomputable def metaHorizonBeltramiExcitationIncrementAtXi (ξ : ℝ) (n ℓ : ℕ) : ℝ :=
  (metaHorizonHadronicGroundAtXi ξ / derivedProtonMass) *
    (radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ) *
    metaHorizonExcitedChannelTwistAtEpoch ξ n ℓ

/--
**Main ξ-scaled excited mass:** dynamic ground plus twisted Beltrami increment.

At `ξ = ξ_lock` and `(n,ℓ) = (0,0)` all twist factors reduce to `1` and the readout
matches the lock-in catalog.  For genuine excitations the readout equals the catalog
plus an explicit **curvature/twist correction** term.
-/
noncomputable def metaHorizonExcitedBaryonMassAtXi (ξ : ℝ) (n ℓ : ℕ) : ℝ :=
  metaHorizonHadronicGroundAtXi ξ + metaHorizonBeltramiExcitationIncrementAtXi ξ n ℓ

theorem metaHorizonExcitedBaryonMassAtXi_ground (ξ : ℝ) :
    metaHorizonExcitedBaryonMassAtXi ξ 0 0 = metaHorizonHadronicGroundAtXi ξ := by
  simp [metaHorizonExcitedBaryonMassAtXi, metaHorizonBeltramiExcitationIncrementAtXi,
    radialExcitationDeltaOperational_zero, orbitalExcitationDeltaOperational_zero, mul_zero, add_zero]

theorem metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_catalog_plus_curvature_correction (n ℓ : ℕ) :
    metaHorizonExcitedBaryonMassAtXi xiLockin n ℓ =
      metaHorizonExcitedMassReadout n ℓ +
        (radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ) *
          (metaHorizonExcitedChannelTwistAtEpoch xiLockin n ℓ - 1) := by
  unfold metaHorizonExcitedBaryonMassAtXi metaHorizonBeltramiExcitationIncrementAtXi
    metaHorizonExcitedMassReadout
  rw [metaHorizonHadronicGroundAtXi_at_lockin]
  have hdp : derivedProtonMass ≠ 0 := ne_of_gt derivedProtonMass_pos
  field_simp [hdp]
  ring

theorem metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_catalog_when_ground :
    metaHorizonExcitedBaryonMassAtXi xiLockin 0 0 = metaHorizonExcitedMassReadout 0 0 := by
  rw [metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_catalog_plus_curvature_correction,
    metaHorizonExcitedChannelTwistAtEpoch_at_lockin_ground, sub_self, mul_zero, add_zero]

theorem metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_beltrami (n ℓ : ℕ) :
    metaHorizonExcitedBaryonMassAtXi xiLockin n ℓ =
      metaHorizonExcitedMassFromBeltramiSpectrum n ℓ +
        (metaHorizonBeltramiRadialDelta n + metaHorizonBeltramiOrbitalDelta ℓ) *
          (metaHorizonExcitedChannelTwistAtEpoch xiLockin n ℓ - 1) := by
  rw [metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_catalog_plus_curvature_correction,
    metaHorizonExcitedMassReadout_eq_beltramiSpectralReadout,
    metaHorizonBeltramiRadialDelta_eq_radialOperational,
    metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational]

theorem metaHorizonExcitedBaryonMassAtXi_eq_ground_plus_twisted_beltrami (ξ : ℝ) (n ℓ : ℕ) :
    metaHorizonExcitedBaryonMassAtXi ξ n ℓ =
      metaHorizonHadronicGroundAtXi ξ +
        (metaHorizonHadronicGroundAtXi ξ / derivedProtonMass) *
          (metaHorizonBeltramiRadialDelta n + metaHorizonBeltramiOrbitalDelta ℓ) *
          metaHorizonExcitedChannelTwistAtEpoch ξ n ℓ := by
  unfold metaHorizonExcitedBaryonMassAtXi metaHorizonBeltramiExcitationIncrementAtXi
  rw [metaHorizonBeltramiRadialDelta_eq_radialOperational,
    metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational]

theorem metaHorizonExcitedBaryonMassAtXi_reflects_channel_curvature (ξ : ℝ) (n ℓ : ℕ) :
    metaHorizonExcitedBaryonMassAtXi ξ n ℓ =
      metaHorizonHadronicGroundAtXi ξ +
        (metaHorizonHadronicGroundAtXi ξ / derivedProtonMass) *
          (radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ) *
          (omegaK_xi (metaHorizonExcitedChannelXi n ℓ) / omegaK_xi ξ) *
          (omaxwellFanoDetuning1Jet (metaHorizonExcitedChannelShell n ℓ) /
            omaxwellFanoDetuning1Jet referenceM) := by
  rw [metaHorizonExcitedBaryonMassAtXi_eq_ground_plus_twisted_beltrami]
  simp only [metaHorizonExcitedChannelTwistAtEpoch, metaHorizonExcitedDetuningTwist,
    metaHorizonBeltramiRadialDelta_eq_radialOperational,
    metaHorizonBeltramiOrbitalDelta_eq_orbitalOperational]
  ring_nf

/-! ## Witness -/

structure MetaHorizonExcitedXiScaleWitness where
  channel_xi_ground : metaHorizonExcitedChannelXi 0 0 = xiLockin
  twist_ground_at_lockin : metaHorizonExcitedChannelTwistAtEpoch xiLockin 0 0 = 1
  lockin_catalog_plus_correction :
    ∀ n ℓ, metaHorizonExcitedBaryonMassAtXi xiLockin n ℓ =
      metaHorizonExcitedMassReadout n ℓ +
        (radialExcitationDeltaOperational n + orbitalExcitationDeltaOperational ℓ) *
          (metaHorizonExcitedChannelTwistAtEpoch xiLockin n ℓ - 1)
  radial_twist_gt_one : ∀ n, 0 < n →
    1 < metaHorizonExcitedChannelTwistAtEpoch xiLockin n 0
  curvature_factorization :
    ∀ ξ n ℓ, metaHorizonExcitedBaryonMassAtXi ξ n ℓ =
      metaHorizonHadronicGroundAtXi ξ +
        metaHorizonBeltramiExcitationIncrementAtXi ξ n ℓ

theorem metaHorizonExcitedXiScaleWitness_default : MetaHorizonExcitedXiScaleWitness where
  channel_xi_ground := metaHorizonExcitedChannelXi_ground
  twist_ground_at_lockin := metaHorizonExcitedChannelTwistAtEpoch_at_lockin_ground
  lockin_catalog_plus_correction := metaHorizonExcitedBaryonMassAtXi_at_lockin_eq_catalog_plus_curvature_correction
  radial_twist_gt_one := metaHorizonExcitedChannelTwist_gt_one_at_lockin_of_radial
  curvature_factorization := fun ξ n ℓ => by
    unfold metaHorizonExcitedBaryonMassAtXi
    rfl

end Hqiv.Physics
