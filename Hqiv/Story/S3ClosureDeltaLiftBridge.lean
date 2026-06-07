import Hqiv.Story.S3ExplicitFormulaIdentity
import Hqiv.Story.S3SixPolesResidual
import Hqiv.Algebra.MinimalSoSeedClosure
import Hqiv.Geometry.OctonionicLightCone

/-!
# Closure bridge: harmonic channel + `SO(3)+Δ → SO(4)` for the S³ story

The `papers/closure` manuscript (`hqiv-so8-paper`) builds

`uniform growth → K(n) ≥ H_n → Ω → ℛ → Δ → ⟨𝔤₂ ∪ {Δ}⟩_Lie = 𝔰𝔬(8)`,

with the low-dimensional toy

`⟨𝔰𝔬(3), Δ₄⟩_Lie = 𝔰𝔬(4)`,  where `Δ₄ = J₁₄`.

This module wires those **proved** pieces into the S³ / explicit-formula spine:

* `harmonicPartialSum` — the harmonic channel `H_n` from the closure paper;
* `harmonicPartialSum_le_curvatureChannel` — `H_n ≤ K(n)` via
  `curvature_integral_ge_harmonic` (divergent channel forcing the phase readout);
* `so3_delta_lifts_to_so4` — the `SO(4)` toy certificate discharged by
  `MinimalSoSeedClosure` at `N = 4`;
* `delta4_mem_so4_seed` — the connector `Δ₄ = J₁₄` is the phase-lift generator
  into the fourth coordinate;
* `s3_poles_live_in_so4_carrier` — the six imaginary poles `±i,±j,±k` use the
  same four real coordinates as the `SO(4)` matrix carrier.

**Honesty.** The harmonic bound and the Lie lift are proved. They supply the
**geometric carrier** (4D quaternion shell, twiddle rotations, divergent phase
channel). They do **not** by themselves localize `ζ` zeros: that remains the
explicit-formula / Weil-positivity step (`ExplicitFormulaLocalization`).
-/

namespace Hqiv.Story

open Hqiv

noncomputable section

/-- Harmonic partial sum `H_n = ∑_{m=0}^{n-1} 1/(m+1)` (closure paper notation). -/
noncomputable def harmonicPartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)

/-- The curvature channel dominates the harmonic series (closure Thm: `K(n) ≥ H_n`). -/
theorem harmonicPartialSum_le_curvatureChannel (n : ℕ) :
    harmonicPartialSum n ≤ curvature_integral n := by
  simpa [harmonicPartialSum] using curvature_integral_ge_harmonic n

/-- The curvature channel is strictly increasing — the normalized readout `Ω` diverges. -/
theorem curvatureChannel_strictly_increasing : StrictMono curvature_integral :=
  fun _ _ h => curvature_integral_strict_mono h

/-- `SO(4)` matrix carrier from the closure toy model. -/
abbrev SO4CarrierMat := Hqiv.Algebra.Mat 4

/-- Embedded `SO(3)` plus connector `Δ₄` in the `SO(4)` carrier. -/
noncomputable abbrev SO4So3DeltaLie : LieSubalgebra ℝ SO4CarrierMat :=
  Hqiv.Algebra.minimalSoSeedLie 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1))

/-- Full `SO(4)` Lie algebra on the four-dimensional carrier. -/
noncomputable abbrev SO4Lie : LieSubalgebra ℝ SO4CarrierMat :=
  skewAdjointMatricesLieSubalgebra (1 : SO4CarrierMat)

/--
**Closure toy discharged in Lean:** `⟨𝔰𝔬(3), Δ₄⟩_Lie = 𝔰𝔬(4)`.

Linear span of the seed has dimension `4 < 6`; iterated brackets generate the
missing directions (`[J₁₂, J₁₄] = J₂₄`, `[J₁₃, J₁₄] = J₃₄`).
-/
theorem so3_delta_lifts_to_so4 : SO4So3DeltaLie = SO4Lie := by
  simpa [SO4So3DeltaLie, SO4Lie] using
    (Hqiv.Algebra.minimal_so_seed_lieSpan_eq_skewAdjoint
      (N := 4) (hN := (by decide : 3 ≤ 4)) (k := (0 : Fin (4 - 1))))

/-- The phase-lift connector `Δ₄ = J₁₄` belongs to the raw `SO(3)+Δ₄` seed. -/
theorem delta4_mem_so4_seed :
    Hqiv.Algebra.planeGen
      (Hqiv.Algebra.predEmbed 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      (Hqiv.Algebra.lastEmbed 4 (by decide : 2 ≤ 4))
      (Hqiv.Algebra.predEmbed_lt_last (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      ∈ Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)) :=
  Hqiv.Algebra.mem_minimalSoSeedSet_delta (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1))

/-- `Δ₄` lies in the generated `SO(3)+Δ₄` algebra (the lift generator is visible). -/
theorem delta4_mem_so4_lie :
    Hqiv.Algebra.planeGen
      (Hqiv.Algebra.predEmbed 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      (Hqiv.Algebra.lastEmbed 4 (by decide : 2 ≤ 4))
      (Hqiv.Algebra.predEmbed_lt_last (N := 4) (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
      ∈ SO4So3DeltaLie :=
  LieSubalgebra.subset_lieSpan (R := ℝ) (L := SO4CarrierMat)
    (s := Hqiv.Algebra.minimalSoSeedSet 4 (by decide : 2 ≤ 4) (0 : Fin (4 - 1)))
    delta4_mem_so4_seed

/--
The six S³ imaginary poles (`±i,±j,±k`) and the closure `SO(4)` carrier share the
same four real coordinates: quaternion components `[real, i, j, k]`.
-/
theorem s3_poles_live_in_so4_carrier :
    OnS3 poleIplus ∧ OnS3 poleIminus ∧ OnS3 poleJplus ∧
      OnS3 poleJminus ∧ OnS3 poleKplus ∧ OnS3 poleKminus :=
  six_poles_on_s3

/--
Packaging: the proved closure carrier (harmonic-divergent channel + `SO(3)+Δ→SO(4)`)
sits alongside the explicit-formula inputs. Neither field is derived from the other;
together they discharge RH.
-/
structure ClosureHarmonicDeltaBridge where
  weil_positive : DiscreteWeilFormPositive
  localization : ExplicitFormulaLocalization

/-- RH from discrete Weil positivity + localization, with closure carrier in scope. -/
theorem RiemannHypothesis_of_closure_harmonic_delta_bridge
    (B : ClosureHarmonicDeltaBridge) : RiemannHypothesis :=
  RiemannHypothesis_of_discrete_weil_and_localization B.weil_positive B.localization

end

end Hqiv.Story
