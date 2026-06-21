import Hqiv.Story.S3FortyFiveProjection
import Hqiv.Story.S3RotationRigidity
import Hqiv.Story.S3HarmonicHolonomyAssociatorAdjointAttack
import Hqiv.Story.S3LogPhaseZetaCouplingFrontier
import Hqiv.Story.S3RotationAdjointHeightPhaseBSDBridge
import Hqiv.Story.S3OnLineSpectralProductHeightPhaseLadder

/-!
# σ–t rotation vector — 45° (RH) + 90° (BSD) + height phase

Engineers a concrete **σ–t vector** from the shared functional-equation pair
`(σ, 1−σ)` and the 45°/90° rotation ladder:

| Component | Definition | Zero locus |
|-----------|------------|------------|
| **σ₄₅** | `rot45Free (functionalPair σ)` | `σ = 1/2` (RH / FE adjoint) |
| **σ₉₀** | `rot90Free (functionalPair σ)` | `σ = 1` (BSD / convergence wall) |
| **height phase** | `2 t log 30 − π` | discrete ladder when `OnLineHeightPhaseLockAt t` |

The 45° and 90° coordinates are the **same affine σ-axis** with different anchors;
proving the affine relation makes the dual capstone a single vector toward
`SigmaTPhaseCouplingAt` without discharging the RH-equivalent coupling gate.
-/

namespace Hqiv.Story

open Complex Real Hqiv.Geometry

noncomputable section

/-! ## Height-phase offset -/

/--
**Height-phase offset** at critical-line height `t = Im ρ`.

On the proved ladder target, `OnLineHeightPhaseLockAt t` is equivalent to
`sigmaTHeightPhaseOffset t ∈ 2π ℤ` (`sigma_t_height_phase_lock_iff_offset`).
-/
noncomputable def sigmaTHeightPhaseOffset (t : ℝ) : ℝ :=
  2 * t * Real.log 30 - Real.pi

theorem sigma_t_height_phase_offset_eq_two_pi_mul (t : ℝ) (k : ℤ) :
    sigmaTHeightPhaseOffset t = (2 : ℝ) * (k : ℝ) * Real.pi ↔
      (2 : ℝ) * t * Real.log 30 = Real.pi + (2 : ℝ) * (k : ℝ) * Real.pi := by
  unfold sigmaTHeightPhaseOffset
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! ## σ–t vector packaging -/

/--
Engineered **σ–t rotation vector** at a complex point `ρ`.

* `sigma45` — 45° equator coordinate (RH channel).
* `sigma90` — 90° convergence-wall coordinate (BSD channel).
* `heightPhase` — log-30 height offset toward `OnLineHeightPhaseLockAt`.
-/
structure SigmaTRotationVector where
  sigma45 : ℝ
  sigma90 : ℝ
  heightPhase : ℝ

/-- Package the three rotation/height components at `ρ`. -/
noncomputable def sigmaTRotationVectorAt (ρ : ℂ) : SigmaTRotationVector where
  sigma45 := rot45Free (functionalPair ρ.re)
  sigma90 := rot90Free (functionalPair ρ.re)
  heightPhase := sigmaTHeightPhaseOffset ρ.im

theorem sigma_t_rotation_vector_sigma45 (ρ : ℂ) :
    (sigmaTRotationVectorAt ρ).sigma45 = rot45Free (functionalPair ρ.re) :=
  rfl

theorem sigma_t_rotation_vector_sigma90 (ρ : ℂ) :
    (sigmaTRotationVectorAt ρ).sigma90 = rot90Free (functionalPair ρ.re) :=
  rfl

theorem sigma_t_rotation_vector_height (ρ : ℂ) :
    (sigmaTRotationVectorAt ρ).heightPhase = sigmaTHeightPhaseOffset ρ.im :=
  rfl

/-! ## Affine 45° ↔ 90° bridge (proved) -/

/--
The 90° coordinate is an affine image of the 45° coordinate on the FE pair:
`σ₉₀ = (√2/2) · σ₄₅ − 1/2`.
-/
theorem rot90Free_eq_rot45_affine (σ : ℝ) :
    rot90Free (functionalPair σ) =
      rot45Free (functionalPair σ) * (Real.sqrt 2 / 2) - (1 / 2 : ℝ) := by
  rw [rot90Free_functionalPair, rot45Free_functionalPair]
  field_simp
  ring

/--
Critical line (`σ₄₅ = 0`) is exactly the 90° offset `σ₉₀ = −1/2` —
the two rotation landmarks on the same affine σ-axis.
-/
theorem rot45_zero_iff_rot90_neg_half (σ : ℝ) :
    rot45Free (functionalPair σ) = 0 ↔ rot90Free (functionalPair σ) = -(1 / 2 : ℝ) := by
  rw [rot90Free_eq_rot45_affine]
  constructor
  · intro h
    simp [h]
  · intro h
    have hnum :
        rot45Free (functionalPair σ) * (Real.sqrt 2 / 2) = 0 := by linarith
    have hsqrt : Real.sqrt 2 / 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp hnum).resolve_right hsqrt

theorem rot90_positive_iff_sigma_gt_one (σ : ℝ) :
    0 < rot90Free (functionalPair σ) ↔ (1 : ℝ) < σ := by
  simp [rot90Free_functionalPair]

theorem sigma_t_vector_critical_line_iff (ρ : ℂ) :
    (sigmaTRotationVectorAt ρ).sigma45 = 0 ↔ ρ.re = (1 / 2 : ℝ) :=
  rot45Free_functionalPair_eq_zero_iff ρ.re

theorem sigma_t_vector_bsd_wall_iff (ρ : ℂ) :
    (sigmaTRotationVectorAt ρ).sigma90 = 0 ↔ ρ.re = (1 : ℝ) :=
  rot90Free_functionalPair_eq_zero_iff ρ.re

theorem sigma_t_vector_on_critical_line (ρ : ℂ) (hs : ρ.re = (1 / 2 : ℝ)) :
    (sigmaTRotationVectorAt ρ).sigma45 = 0 ∧
      (sigmaTRotationVectorAt ρ).sigma90 = -(1 / 2 : ℝ) := by
  constructor
  · exact (sigma_t_vector_critical_line_iff ρ).mpr hs
  · rw [sigma_t_rotation_vector_sigma90]
    exact (rot45_zero_iff_rot90_neg_half ρ.re).mp
      ((sigma_t_vector_critical_line_iff ρ).mpr hs)

theorem sigma_t_vector_at_critical_height (t : ℝ) :
    let ρ := criticalLinePointAtHeight t
    (sigmaTRotationVectorAt ρ).sigma45 = 0 ∧
      (sigmaTRotationVectorAt ρ).sigma90 = -(1 / 2 : ℝ) ∧
        (sigmaTRotationVectorAt ρ).heightPhase = sigmaTHeightPhaseOffset t := by
  dsimp
  have hs : (criticalLinePointAtHeight t).re = (1 / 2 : ℝ) := criticalLinePointAtHeight_re t
  constructor
  · exact (sigma_t_vector_critical_line_iff _).mpr hs
  constructor
  · rw [sigma_t_rotation_vector_sigma90]
    exact (rot45_zero_iff_rot90_neg_half _).mp
      ((sigma_t_vector_critical_line_iff _).mpr hs)
  · simp [sigmaTRotationVectorAt, criticalLinePointAtHeight]

/-! ## Height-phase ladder in vector language (proved via ladder module) -/

theorem sigma_t_height_phase_lock_iff_offset
    (hLadder : OnLineSpectralProductOpposedIffHeightPhase) (t : ℝ) :
    OnLineHeightPhaseLockAt t ↔
      ∃ k : ℤ, sigmaTHeightPhaseOffset t = (2 : ℝ) * (k : ℝ) * Real.pi := by
  rw [on_line_height_phase_lock_iff hLadder]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (sigma_t_height_phase_offset_eq_two_pi_mul t k).mpr hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (sigma_t_height_phase_offset_eq_two_pi_mul t k).mp hk⟩

theorem sigma_t_height_phase_lock_at_point_iff_offset
    (hLadder : OnLineSpectralProductOpposedIffHeightPhase) {ρ : ℂ}
    (_hs : ρ.re = (1 / 2 : ℝ)) :
    OnLineHeightPhaseLockAt ρ.im ↔
      ∃ k : ℤ, (sigmaTRotationVectorAt ρ).heightPhase = (2 : ℝ) * (k : ℝ) * Real.pi := by
  rw [sigma_t_rotation_vector_height]
  exact sigma_t_height_phase_lock_iff_offset hLadder ρ.im

/-! ## Coupling frontier packaging (honest; RH-equivalent gate not discharged) -/

/--
**Proved σ–t vector bundle** (no open height ladder): affine 45°/90° bridge,
BSD half-plane readout, and unconditional σ–t coupling at nontrivial zeros.
-/
structure SigmaTRotationVectorBridgeProved where
  rotation_bsd_bridge : RotationAdjointHeightPhaseBSDBridge
  rot45_rot90_affine : ∀ σ : ℝ,
    rot90Free (functionalPair σ) =
      rot45Free (functionalPair σ) * (Real.sqrt 2 / 2) - (1 / 2 : ℝ)
  rot45_zero_iff_rot90_neg_half :
    ∀ σ : ℝ,
      rot45Free (functionalPair σ) = 0 ↔
        rot90Free (functionalPair σ) = -(1 / 2 : ℝ)
  sigma_t_coupling_at_zeros :
    ∀ {ρ : ℂ}, IsNontrivialZetaZero ρ → SigmaTPhaseCouplingAt ρ

noncomputable def sigma_t_rotation_vector_bridge_proved : SigmaTRotationVectorBridgeProved where
  rotation_bsd_bridge := rotation_adjoint_height_phase_bsd_bridge
  rot45_rot90_affine := rot90Free_eq_rot45_affine
  rot45_zero_iff_rot90_neg_half := rot45_zero_iff_rot90_neg_half
  sigma_t_coupling_at_zeros := fun {_ρ} h => sigma_t_coupling_at_every_nontrivial_zero h

def SigmaTRotationVectorBridgeProvedInhabited : Prop :=
  Nonempty SigmaTRotationVectorBridgeProved

theorem sigma_t_rotation_vector_bridge_proved_inhabited :
    SigmaTRotationVectorBridgeProvedInhabited :=
  ⟨sigma_t_rotation_vector_bridge_proved⟩

/--
**Full σ–t vector bundle** (includes the proved height-phase ladder).
Discharging `height_phase_open` is supplied by
`on_line_spectral_product_opposed_iff_height_phase`.
-/
structure SigmaTRotationVectorBridge extends SigmaTRotationVectorBridgeProved where
  height_phase_open : OnLineSpectralProductOpposedIffHeightPhase

def SigmaTRotationVectorBridgeInhabited : Prop :=
  Nonempty SigmaTRotationVectorBridge

theorem sigma_t_rotation_vector_bridge_inhabited_of_height_ladder
    (hLadder : OnLineSpectralProductOpposedIffHeightPhase) :
    SigmaTRotationVectorBridgeInhabited :=
  ⟨{
    toSigmaTRotationVectorBridgeProved := sigma_t_rotation_vector_bridge_proved
    height_phase_open := hLadder
  }⟩

theorem sigma_t_rotation_vector_bridge_inhabited :
    SigmaTRotationVectorBridgeInhabited :=
  sigma_t_rotation_vector_bridge_inhabited_of_height_ladder
    on_line_spectral_product_opposed_iff_height_phase

/--
**Open σ–t pin (named).**  Discharging this is the same content as
`OnLineSpectralProductOpposedIffHeightPhase` / slot-budget height lock.
-/
def SigmaTHeightPhaseLadderOpen : Prop :=
  OnLineSpectralProductOpposedIffHeightPhase

theorem sigma_t_height_phase_ladder_open_iff :
    SigmaTHeightPhaseLadderOpen ↔ OnLineSpectralProductOpposedIffHeightPhase :=
  Iff.rfl

end

end Hqiv.Story
