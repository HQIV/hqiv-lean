import Hqiv.Geometry.HarmonicMulModCubeTriangulation
import Hqiv.Story.S3HarmonicCascadeZetaRegularization
import Hqiv.Story.S3ZetaGoldbachTailBandCrossChannelBridge

/-!
# Mul-mod cube triangulation ↔ ζ(2)−ζ(3) tail band — cross-channel bridge

Parallel to `S3ZetaGoldbachTailBandCrossChannelBridge`:

| ζ / Goldbach channel | Mul-mod / holonomy channel |
|----------------------|----------------------------|
| square tail `ζ(2)−1` | raw finite cascade `6→5→11→7` |
| cube tail `ζ(3)−1` | mod‑7 single-cube fibre `{0,±1}` |
| band width `ζ(2)−ζ(3)` | three-cube triangulation of `ℤ/7ℤ` |
| global associator cap | coprime mul-mod sweep / Lie promotion |
| off-line exclusion | raw obstruction ideal `385·(2∪3)ℕ` |
| regularized closure | infinite prime cascade + `harmonicOrbitMulModMultiplierReg` |

**Geometric reading.**  A mul-mod group `(ℤ/nℤ, ×m)` is **1-dimensional** transport (one multiplier).
Mod‑7 splits the shell into seven Fano fibres; a **single** cube only sees `{0,±1}`, but **three**
cube slots **triangulate** every residue — the same dimensional jump as square tail → cube tail.
The `ζ(2)−ζ(3)` band width is the regularization slack; the prime cascade is the adelic completion
replacing the blind terminal `7`.
-/

namespace Hqiv.Story

open Hqiv.Geometry Real Complex

noncomputable section

structure MulModCubeTriangulationGeometry where
  triangulate : ∀ r : ZMod 7, ∃ a b c : ZMod 7, a ^ 3 + b ^ 3 + c ^ 3 = r

noncomputable def mulModCubeTriangulationGeometry_default : MulModCubeTriangulationGeometry where
  triangulate := triangulate_mod7

structure MulModZetaTailTriangulationCarrier where
  tail_band_literal :
    ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3
  tail_band_pos : 0 < goldbachAnnulusZetaTailBandWidth
  global_budget : GoldbachAnnulusAssociatorGlobalBudget
  cascade_reg : HarmonicCascadeRegularization

noncomputable def mulMod_zeta_tail_triangulation_carrier_default :
    MulModZetaTailTriangulationCarrier :=
  { tail_band_literal := zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three
    tail_band_pos := goldbach_annulus_zeta_tail_band_width_pos
    global_budget := goldbach_annulus_associator_global_budget
    cascade_reg := harmonicCascadeRegularization_default }

structure MulModCubeTriangulationCrossChannelBridge where
  cube_geometry : MulModCubeTriangulationGeometry
  tail_triangulation : MulModZetaTailTriangulationCarrier
  obstruction_classification :
    ∀ n, harmonicRawObstructionShell n ↔ ¬ HarmonicMulModMultiplierCoprimeObstruction n
  discharge_770 :
    harmonicRawObstructionShell 770 ∧
      harmonicStructuredCascadeMultiplier 770 (by decide) = 13 ∧
        harmonicFirstCoprimeCascadeIndex 770 (by decide) = 3

noncomputable def mulMod_cube_triangulation_cross_channel_default :
    MulModCubeTriangulationCrossChannelBridge where
  cube_geometry := mulModCubeTriangulationGeometry_default
  tail_triangulation := mulMod_zeta_tail_triangulation_carrier_default
  obstruction_classification := harmonic_raw_obstruction_iff_not_coprime
  discharge_770 :=
    ⟨harmonic_raw_obstruction_shell_770,
      harmonicStructuredCascadeMultiplier_fixes_770,
      harmonicFirstCoprimeCascadeIndex_discharges_770⟩

def MulModCubeTriangulationMethodCarrier : Prop :=
  (∀ r : ZMod 7, ∃ a b c : ZMod 7, a ^ 3 + b ^ 3 + c ^ 3 = r) ∧
    ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3 ∧
      0 < goldbachAnnulusZetaTailBandWidth ∧
        GoldbachAnnulusAssociatorGlobalBudget ∧
          GlobalHarmonicLiePromotionReg ∧
            (∀ n, harmonicRawObstructionShell n ↔ ¬ HarmonicMulModMultiplierCoprimeObstruction n) ∧
              (∀ n (hn : 0 < n), ∃ i, harmonicCascadeTrialAtCoprime n hn i) ∧
                harmonicStructuredCascadeMultiplier 770 (by decide) = 13

theorem mulMod_cube_triangulation_method_carrier :
    MulModCubeTriangulationMethodCarrier :=
  ⟨triangulate_mod7,
    zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three,
    goldbach_annulus_zeta_tail_band_width_pos,
    goldbach_annulus_associator_global_budget,
    global_harmonic_lie_promotion_reg,
    harmonic_raw_obstruction_iff_not_coprime,
    fun n hn => exists_harmonic_cascade_trial_at_coprime n hn,
    harmonicStructuredCascadeMultiplier_fixes_770⟩

theorem raw_obstruction_iff_not_coprime (n : ℕ) :
    harmonicRawObstructionShell n ↔ ¬ HarmonicMulModMultiplierCoprimeObstruction n :=
  harmonic_raw_obstruction_iff_not_coprime n

theorem obstruction_shell_zero_mod_seven {n : ℕ} (h : harmonicRawObstructionShell n) :
    (n : ZMod 7) = 0 :=
  harmonic_raw_obstruction_shell_zero_residue h

end

end Hqiv.Story
