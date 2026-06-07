import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.ContinuousXiCoupling
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Physics.HopfShellBeltramiMassBridge
import Hqiv.Physics.HorizonBlackbodySpectrum
import Hqiv.Physics.MetaHorizonExcitedStates

namespace Hqiv.Physics

open scoped BigOperators
open Hqiv
open ContinuousXiPath

/-!
# Meta-horizon masses from trapped Planck volume under the curvature curve

No independent gluon sector: binding and excitation masses are read from **Planck
zero-point modes trapped inside** the closed carrier curve, relative to the
lock-in ground.

Two certified factors multiply at shell `m`:

* **Curvature volume** — cumulative `curvature_integral (m+1)` (area under the
  imprint density `(1/x)(1+α log x)` sampled on integer shells);
* **Trapped Planck budget** — cumulative `vacuumZeroPointEnergy` from the Planck
  pole through shell `m` (finite shell sum `Σ N_k ω_k/2`).

The excited readout at channel shell `m_exc = totalModeShell n ℓ` is
`derivedProtonMass` times the inside ratio of these two factors relative
to `referenceM`.  Epoch `ξ` modulates inner trapping through `Ω_k(ξ)` on the
continuous ladder (same slot as inner Casimir dynamics).
-/

/-! ## Trapped Planck budget and curvature volume -/

/-- Cumulative Planck zero-point energy trapped from the Planck pole through shell `m`. -/
noncomputable def trappedPlanckCumulativeBudget (m : ℕ) : ℝ :=
  vacuumZeroPointEnergy planckUVCutoff m

private theorem trappedPlanckShellSlice_pos (m : ℕ) :
    0 < shellModeMultiplicity m * shellOmega m / 2 := by
  exact div_pos (mul_pos (shellModeMultiplicity_pos m) (shellOmega_pos m))
    (by norm_num : (0 : ℝ) < 2)

theorem trappedPlanckCumulativeBudget_nonneg (m : ℕ) :
    0 ≤ trappedPlanckCumulativeBudget m := by
  unfold trappedPlanckCumulativeBudget vacuumZeroPointEnergy
  refine Finset.sum_nonneg ?_
  intro k _
  have h1 : 0 ≤ shellModeMultiplicity k := shellModeMultiplicity_nonneg k
  have h2 : 0 ≤ shellOmega k := le_of_lt (shellOmega_pos k)
  exact div_nonneg (mul_nonneg h1 h2) (by norm_num : (0 : ℝ) ≤ 2)

private theorem trappedPlanckCumulativeBudget_pos (m : ℕ) :
    0 < trappedPlanckCumulativeBudget m := by
  unfold trappedPlanckCumulativeBudget vacuumZeroPointEnergy
  have hne : (Finset.Icc planckUVCutoff m).Nonempty := ⟨planckUVCutoff, by
    simp [planckUVCutoff, Finset.mem_Icc]⟩
  refine Finset.sum_pos (fun k _ => ?_) hne
  exact trappedPlanckShellSlice_pos k

private theorem icc_zero_eq_range (m : ℕ) : Finset.Icc (0 : ℕ) m = Finset.range (m + 1) := by
  ext x
  constructor
  · intro hx; simp [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
  · intro hx; simp [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega

private theorem trappedPlanckCumulativeBudget_lt_succ (m : ℕ) :
    trappedPlanckCumulativeBudget m < trappedPlanckCumulativeBudget (m + 1) := by
  unfold trappedPlanckCumulativeBudget vacuumZeroPointEnergy
  rw [show planckUVCutoff = 0 from rfl, icc_zero_eq_range m, icc_zero_eq_range (m + 1)]
  have hsum :
      (∑ x ∈ Finset.range (m + 2), shellModeMultiplicity x * shellOmega x / 2) =
        (∑ x ∈ Finset.range (m + 1), shellModeMultiplicity x * shellOmega x / 2) +
          shellModeMultiplicity (m + 1) * shellOmega (m + 1) / 2 := by
    rw [show m + 1 + 1 = m + 2 from by omega, Finset.sum_range_succ]
  rw [hsum]
  apply lt_add_of_pos_right
  exact trappedPlanckShellSlice_pos (m + 1)

private theorem trappedPlanckCumulativeBudget_lt_add (m₁ k : ℕ) :
    trappedPlanckCumulativeBudget m₁ < trappedPlanckCumulativeBudget (m₁ + k + 1) := by
  induction k with
  | zero => exact trappedPlanckCumulativeBudget_lt_succ m₁
  | succ k ih =>
    exact lt_trans ih (trappedPlanckCumulativeBudget_lt_succ (m₁ + k + 1))

private theorem trappedPlanckCumulativeBudget_strictMono {m₁ m₂ : ℕ} (h : m₁ < m₂) :
    trappedPlanckCumulativeBudget m₁ < trappedPlanckCumulativeBudget m₂ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  exact trappedPlanckCumulativeBudget_lt_add m₁ k

/-- Cumulative curvature-imprint volume through shell `m` (inclusive). -/
noncomputable def metaHorizonCurvatureVolumeThrough (m : ℕ) : ℝ :=
  curvature_integral (m + 1)

theorem metaHorizonCurvatureVolumeThrough_pos (m : ℕ) :
    0 < metaHorizonCurvatureVolumeThrough m :=
  curvature_integral_pos (by omega)

private theorem metaHorizonCurvatureVolumeThrough_referenceM_pos :
    0 < metaHorizonCurvatureVolumeThrough referenceM := by
  rw [referenceM_eq_four]
  exact curvature_integral_pos (by decide)

private theorem trappedPlanckCumulativeBudget_referenceM_pos :
    0 < trappedPlanckCumulativeBudget referenceM := by
  rw [referenceM_eq_four]
  exact trappedPlanckCumulativeBudget_pos 4

/-! ## Inside ratio: curve volume × trapped Planck budget -/

/--
**Trapped inside ratio** at excited shell `m_exc` relative to lock-in shell `m_ref`.

This is the discrete HQIV analogue of “volume under the curve” (curvature
integral) times “Planck spectrum inside the closure” (cumulative zero-point sum).
-/
noncomputable def metaHorizonTrappedInsideRatio (m_exc m_ref : ℕ) : ℝ :=
  (metaHorizonCurvatureVolumeThrough m_exc / metaHorizonCurvatureVolumeThrough m_ref) *
    (trappedPlanckCumulativeBudget m_exc / trappedPlanckCumulativeBudget m_ref)

theorem metaHorizonTrappedInsideRatio_self (m : ℕ)
    (hcur : 0 < metaHorizonCurvatureVolumeThrough m)
    (hplanck : 0 < trappedPlanckCumulativeBudget m) :
    metaHorizonTrappedInsideRatio m m = 1 := by
  unfold metaHorizonTrappedInsideRatio
  field_simp [hcur.ne', hplanck.ne']

theorem metaHorizonTrappedInsideRatio_referenceM_ground :
    metaHorizonTrappedInsideRatio referenceM referenceM = 1 := by
  refine metaHorizonTrappedInsideRatio_self referenceM ?_ ?_
  · exact metaHorizonCurvatureVolumeThrough_referenceM_pos
  · exact trappedPlanckCumulativeBudget_referenceM_pos

theorem metaHorizonTrappedInsideRatio_gt_one_of_shell_gt
    {m_exc m_ref : ℕ} (h : m_ref < m_exc) :
    1 < metaHorizonTrappedInsideRatio m_exc m_ref := by
  unfold metaHorizonTrappedInsideRatio
  have hcur_ref : 0 < metaHorizonCurvatureVolumeThrough m_ref :=
    curvature_integral_pos (Nat.succ_pos _)
  have hcur_exc :
      metaHorizonCurvatureVolumeThrough m_ref < metaHorizonCurvatureVolumeThrough m_exc := by
    unfold metaHorizonCurvatureVolumeThrough
    exact curvature_integral_strict_mono (Nat.add_lt_add_right h 1)
  have hplanck_ref : 0 < trappedPlanckCumulativeBudget m_ref :=
    trappedPlanckCumulativeBudget_pos m_ref
  have hplanck_exc : trappedPlanckCumulativeBudget m_ref < trappedPlanckCumulativeBudget m_exc :=
    trappedPlanckCumulativeBudget_strictMono h
  have hcur_ratio : 1 < metaHorizonCurvatureVolumeThrough m_exc / metaHorizonCurvatureVolumeThrough m_ref := by
    rw [one_lt_div hcur_ref]
    exact hcur_exc
  have hplanck_ratio : 1 < trappedPlanckCumulativeBudget m_exc / trappedPlanckCumulativeBudget m_ref := by
    rw [one_lt_div hplanck_ref]
    exact hplanck_exc
  have hcurpos : 0 < metaHorizonCurvatureVolumeThrough m_exc / metaHorizonCurvatureVolumeThrough m_ref :=
    div_pos (metaHorizonCurvatureVolumeThrough_pos m_exc) hcur_ref
  have hplanckpos : 0 < trappedPlanckCumulativeBudget m_exc / trappedPlanckCumulativeBudget m_ref :=
    div_pos (trappedPlanckCumulativeBudget_pos m_exc) hplanck_ref
  exact lt_trans hcur_ratio (lt_mul_of_one_lt_right hcurpos hplanck_ratio)

/-! ## Lock-in mass readout -/

/--
**Primary trapped-Planck mass readout** at lock-in: proton scale times the
inside ratio on the excited channel shell.
-/
noncomputable def metaHorizonTrappedPlanckMassReadout (n ℓ : ℕ) : ℝ :=
  derivedProtonMass *
    metaHorizonTrappedInsideRatio (totalModeShell n ℓ) referenceM

theorem metaHorizonTrappedPlanckMassReadout_ground :
    metaHorizonTrappedPlanckMassReadout 0 0 = derivedProtonMass := by
  unfold metaHorizonTrappedPlanckMassReadout
  simp [totalModeShell, Nat.add_zero, metaHorizonTrappedInsideRatio_referenceM_ground, one_mul]

theorem metaHorizonTrappedPlanckMassReadout_gt_ground_of_channel_above_lockin
    {n ℓ : ℕ} (h : referenceM < totalModeShell n ℓ) :
    derivedProtonMass < metaHorizonTrappedPlanckMassReadout n ℓ := by
  unfold metaHorizonTrappedPlanckMassReadout
  have hratio := metaHorizonTrappedInsideRatio_gt_one_of_shell_gt h
  exact lt_mul_of_one_lt_right derivedProtonMass_pos hratio

/-! ## ξ-scaled readout (dynamic ground via inner/outer Casimir gap) -/

noncomputable def metaHorizonTrappedPlanckMassAtXi (ξ : ℝ) (n ℓ : ℕ) : ℝ :=
  derivedProtonMass * (heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5) *
    metaHorizonTrappedInsideRatio (totalModeShell n ℓ) referenceM

theorem metaHorizonTrappedPlanckMassAtXi_at_lockin (n ℓ : ℕ) :
    metaHorizonTrappedPlanckMassAtXi xiLockin n ℓ =
      metaHorizonTrappedPlanckMassReadout n ℓ := by
  unfold metaHorizonTrappedPlanckMassAtXi metaHorizonTrappedPlanckMassReadout
  have hξ : xiLockin = (5 : ℝ) := xiLockin_eq_five
  rw [hξ, heavy_lepton_gap_at_lockin_eq_four_fifths]
  ring

theorem metaHorizonTrappedPlanckMassAtXi_ground (ξ : ℝ) :
    metaHorizonTrappedPlanckMassAtXi ξ 0 0 =
      derivedProtonMass * (heavy_lepton_gap_at_xi ξ / heavy_lepton_gap_at_xi 5) := by
  unfold metaHorizonTrappedPlanckMassAtXi
  simp [totalModeShell, Nat.add_zero, metaHorizonTrappedInsideRatio_referenceM_ground, one_mul]

/-! ## Witness -/

structure MetaHorizonTrappedPlanckWitness where
  ground_readout : metaHorizonTrappedPlanckMassReadout 0 0 = derivedProtonMass
  inside_ratio_reflexive :
    metaHorizonTrappedInsideRatio referenceM referenceM = 1
  lockin_xi_recovery :
    ∀ n ℓ, metaHorizonTrappedPlanckMassAtXi xiLockin n ℓ =
      metaHorizonTrappedPlanckMassReadout n ℓ
  excited_gt_ground :
    ∀ n ℓ, referenceM < totalModeShell n ℓ →
      derivedProtonMass < metaHorizonTrappedPlanckMassReadout n ℓ

theorem metaHorizonTrappedPlanckWitness_default : MetaHorizonTrappedPlanckWitness where
  ground_readout := metaHorizonTrappedPlanckMassReadout_ground
  inside_ratio_reflexive := metaHorizonTrappedInsideRatio_referenceM_ground
  lockin_xi_recovery := metaHorizonTrappedPlanckMassAtXi_at_lockin
  excited_gt_ground := fun n ℓ h => metaHorizonTrappedPlanckMassReadout_gt_ground_of_channel_above_lockin h

end Hqiv.Physics
