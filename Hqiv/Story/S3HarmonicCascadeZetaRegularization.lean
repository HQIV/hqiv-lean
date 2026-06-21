import Hqiv.Geometry.HarmonicCascadeRegularization
import Hqiv.Story.S3ClosureDeltaLiftBridge
import Hqiv.Story.S3MulModSO4LiePromotion
import Hqiv.Story.DimensionalGrowthAnalyticScaffold
import Hqiv.Story.S3SO4ZetaProjectionClosedForm
import Hqiv.Story.S3ZetaGoldbachTailBandCrossChannelBridge
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Harmonic cascade regularization ↔ ζ closure of `H_n`

HQIV already packages the harmonic–ζ analogy on the **growth** side:

* **Raw / divergent:** `harmonicPartialSum n = H_n` (partial sum, `→ ∞`);
* **Regularized cumulative:** `curvature_integral n = K(n) ≥ H_n` with
  `K(n) = H_n + α·logWeightedSum n` (log correction before phase closure);
* **Closed tail:** `ζ(2) − 1`, `ζ(3) − 1`, band width `ζ(2) − ζ(3)` (Mathlib).

This module adds the **mul-mod / Lie promotion** parallel:

* **Raw finite cascade:** `harmonicOrbitMulModMultiplier` (dies at `770`);
* **Regularized cascade:** `harmonicOrbitMulModMultiplierReg` (always coprime);
* **Lie promotion:** `so4LiePromotion_of_coprime` on the regularized multiplier.

The p-adic reading: raw cascade = finite prefix of local unit tests;
regularization = extend the prime tower to a coprime adelic unit (first prime
≥ `13` above the shell when the prefix saturates).
-/

namespace Hqiv.Story

open Hqiv.Geometry Hqiv.Algebra Real Complex

noncomputable section

/-! ## ζ regularization of `H_n` (re-export spine) -/

/--
**Harmonic–ζ regularization carrier.**  Packages the proved HQIV split between
divergent harmonic partial sums and closed ζ / curvature readouts.
-/
structure HarmonicZetaRegularization where
  harmonic : ℕ → ℝ
  harmonic_le_curvature : ∀ n, harmonic n ≤ curvature_integral n
  curvature_split :
    ∀ n,
      curvature_integral n =
        harmonic n + Hqiv.alpha * Hqiv.logWeightedSum n
  zeta_two : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6
  tail_band :
    ((goldbachAnnulusZetaTailBandWidth : ℝ) : ℂ) = riemannZeta 2 - riemannZeta 3

noncomputable def harmonicZetaRegularization_default : HarmonicZetaRegularization where
  harmonic := harmonicPartialSum
  harmonic_le_curvature := harmonicPartialSum_le_curvatureChannel
  curvature_split := curvature_integral_harmonic_log_split
  zeta_two := riemannZeta_two_so4_pi_sector
  tail_band := zeta_goldbach_tail_band_is_literal_zeta_two_minus_zeta_three

/-! ## Cascade regularization (mul-mod parallel) -/

/--
**Cascade regularization carrier.**  Raw finite prefix vs regularized multiplier
+ global Lie promotion.
-/
structure HarmonicCascadeRegularization where
  raw_multiplier : ℕ → ℕ
  raw_obstructed_at_770 : ¬ HarmonicMulModMultiplierCoprimeObstruction 770
  reg_multiplier : ∀ n, 0 < n → ℕ
  reg_coprime : ∀ n (hn : 0 < n), Nat.Coprime (reg_multiplier n hn) n
  reg_extends_raw :
    ∀ n (hn : 0 < n), HarmonicMulModMultiplierCoprimeObstruction n →
      reg_multiplier n hn = raw_multiplier n
  global_lie_promotion_reg : GlobalHarmonicLiePromotionReg

noncomputable def harmonicCascadeRegularization_default : HarmonicCascadeRegularization where
  raw_multiplier := harmonicOrbitMulModMultiplier
  raw_obstructed_at_770 := harmonic_raw_not_coprime_770
  reg_multiplier := harmonicOrbitMulModMultiplierReg
  reg_coprime := fun n hn =>
    (harmonic_reg_multiplier_coprime n hn : Nat.Coprime (harmonicOrbitMulModMultiplierReg n hn) n)
  reg_extends_raw := harmonic_reg_extends_raw
  global_lie_promotion_reg := global_harmonic_lie_promotion_reg

/-! ## Regularized Lie promotion -/

/--
Regularized Lie promotion: multiplier is the **regularized cascade**, not only the
raw `harmonicOrbitMulModMultiplier`.
-/
structure SO4RegCascadeLiePromotion (n : ℕ) (hn : 0 < n) where
  holonomy : SO4PhaseDeltaHolonomyPack
  plaquette_commutator_eq_delta :
    ⁅planeGen (0 : Fin 4) (1 : Fin 4) (by decide), planeGen (1 : Fin 4) (3 : Fin 4) (by decide)⁆ =
      so4DeltaGenerator
  multiplier : ℕ
  multiplier_eq : multiplier = harmonicOrbitMulModMultiplierReg n hn
  sweep : MulModScaleOrbitSweep n multiplier
  hits :
    ∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ so4LieTransportIndex n multiplier x = k

structure G2RegCascadeLiePromotion (n : ℕ) (hn : 0 < n) extends SO4RegCascadeLiePromotion n hn where
  phase_lift_in_g2 : Hqiv.phaseLiftDelta ∈ G2UnionDelta
  harmonic_real : harmonicEvenOrbitMultiplier = 6 / 5

noncomputable def so4LiePromotion_reg (n : ℕ) (hn : 0 < n) : SO4RegCascadeLiePromotion n hn where
  holonomy := so4_phase_delta_holonomy_pack_default
  plaquette_commutator_eq_delta := so4_seed_commutator_eq_so4_delta_generator
  multiplier := harmonicOrbitMulModMultiplierReg n hn
  multiplier_eq := rfl
  sweep := harmonic_mul_mod_sweep_reg n hn
  hits := fun k hk₀ hk => by
    obtain ⟨x, hxlt, heq⟩ := mulModScaleOrbitSweep_hits (harmonic_mul_mod_sweep_reg n hn) hk₀ hk
    exact ⟨x, hxlt, by simpa [so4_lie_transport_index_eq_mul_mod] using heq⟩

noncomputable def g2LiePromotion_reg (n : ℕ) (hn : 0 < n) : G2RegCascadeLiePromotion n hn where
  toSO4RegCascadeLiePromotion := so4LiePromotion_reg n hn
  phase_lift_in_g2 := phase_lift_delta_mem_g2_union
  harmonic_real := harmonicEvenOrbitMultiplier_eq_six_fifths

theorem delta_carrier_lie_promotion_reg (n : ℕ) (hn : 0 < n) :
    Nonempty (G2RegCascadeLiePromotion n hn) :=
  ⟨g2LiePromotion_reg n hn⟩

theorem harmonic_midpoint_bundle_lie_promotion_reg {N p q : ℕ}
    (B : MidpointHarmonicMulModBundle N p q) :
    SO4DeltaMulModLiePromotion B.shell B.multiplier :=
  harmonic_midpoint_bundle_gives_lie_promotion B

/-!
## Analogy table (proved objects)

| Divergent / raw | Regularized / closed |
|-----------------|----------------------|
| `harmonicPartialSum n` | `curvature_integral n` |
| `harmonicOrbitMulModMultiplier n` | `harmonicOrbitMulModMultiplierReg n hn` |
| fails at `770` | `GlobalHarmonicLiePromotionReg` |
| tail partial sums | `ζ(2)−ζ(3)` band (`goldbachAnnulusZetaTailBandWidth`) |

The **infinite-dimensional** Lie lift and **profinite/p-adic** packaging of the
extended prime tower remain the next analytic layer — this module discharges the
**regularized unit selection** that makes Lie promotion global on every shell.
-/

end

end Hqiv.Story
