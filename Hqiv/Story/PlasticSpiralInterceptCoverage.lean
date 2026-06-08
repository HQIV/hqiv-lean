import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import Hqiv.Geometry.GeneralRiemannianRapidityOracle

/-!
# Plastic spiral ↔ intercept coverage (proved scaffolding)

This file records **unconditional** facts about the discrete plastic spiral used in
the rapidity oracle (`Hqiv.Geometry.GeneralRiemannianRapidityOracle`):

- the numeric scaffold **aliases** `Hqiv.Geometry.plasticNumber` / `plasticAngle`
  (unique `ρ > 0` with `ρ³ − ρ − 1 = 0`, not a free decimal);
- the orbit-step map is the identity on indices — every natural step is a spiral index;
- phase at step `m` is the linear increment `spiralPlasticAngle * m`.

Alignment / “every arithmetic intercept hits a bounded spiral step” remains an explicit
hypothesis bundle until the corresponding number theory is discharged.

See also `Hqiv.Story.ArityInterceptProofSpine` for the arity-split proof target.
-/

namespace Hqiv.Story

noncomputable section

/-- Plastic number: canonical `Hqiv.Geometry.plasticNumber` (unique `ρ > 0` with `ρ³ = ρ + 1`). -/
noncomputable def spiralPlasticNumber : ℝ := Hqiv.Geometry.plasticNumber

/-- Plastic-number angle step: canonical `Hqiv.Geometry.plasticAngle` (`2π/ρ`). -/
noncomputable def spiralPlasticAngle : ℝ := Hqiv.Geometry.plasticAngle

/-- Canonical discrete orbit step at index `k` (same as `plastic_spiral_orbit_step` there: the identity on `ℕ`). -/
def spiralOrbitStep (k : ℕ) : ℕ := k

/-- Plastic spiral phase at discrete step `m` (linear increment in `m`). -/
noncomputable def plasticSpiralPhaseAtStep (m : ℕ) : ℝ :=
  spiralPlasticAngle * (m : ℝ)

@[simp]
theorem spiral_orbit_step_eq_id (m : ℕ) : spiralOrbitStep m = m := by
  rfl

/--
Every natural index `m` occurs as a `spiralOrbitStep` value (at `step = m`).
-/
theorem exists_spiral_orbit_step_eq (m : ℕ) :
    ∃ step : ℕ, spiralOrbitStep step = m :=
  ⟨m, rfl⟩

@[simp]
theorem plasticSpiralPhaseAtStep_eq (m : ℕ) :
    plasticSpiralPhaseAtStep m = spiralPlasticAngle * (m : ℝ) := by
  rfl

/--
Intercept aligned on the plastic spiral at step `m`: phase is within `ε` of a
declared target angle `target n k`.
-/
def InterceptAlignedOnPlasticSpiral (target : ℕ → ℕ → ℝ) (ε : ℝ) (n k m : ℕ) : Prop :=
  |plasticSpiralPhaseAtStep m - target n k| < ε

/--
Eliminator: if a hypothesis already supplies spiral-aligned witnesses for every
intercept, then every intercept has some spiral step satisfying the alignment
predicate.
-/
theorem intercept_on_spiral_from_global_witness
    (intercept : ℕ → ℕ → Prop)
    (target : ℕ → ℕ → ℝ) (ε : ℝ)
    (h :
      ∀ n k, intercept n k → ∃ m : ℕ, |plasticSpiralPhaseAtStep m - target n k| < ε) :
    ∀ n k, intercept n k → ∃ m : ℕ, InterceptAlignedOnPlasticSpiral target ε n k m := by
  intro n k hi
  exact h n k hi

/--
Bounded-step variant (same eliminator pattern, but records `m ≤ bound` in the witness).
-/
def InterceptAlignedOnPlasticSpiralBounded
    (target : ℕ → ℕ → ℝ) (ε : ℝ) (bound : ℕ) (n k m : ℕ) : Prop :=
  m ≤ bound ∧ |plasticSpiralPhaseAtStep m - target n k| < ε

theorem intercept_on_spiral_bounded_from_global_witness
    (intercept : ℕ → ℕ → Prop)
    (target : ℕ → ℕ → ℝ) (ε : ℝ) (bound : ℕ)
    (h : ∀ n k, intercept n k → ∃ m : ℕ, m ≤ bound ∧ |plasticSpiralPhaseAtStep m - target n k| < ε) :
    ∀ n k, intercept n k → ∃ m : ℕ, InterceptAlignedOnPlasticSpiralBounded target ε bound n k m := by
  intro n k hi
  exact h n k hi

/--
Scalar-target bounded witness form (exactly the effective Diophantine shape used in
phase-control discussions):

`∃ m ≤ bound, |plasticSpiralPhaseAtStep m - target| < ε`.
-/
theorem exists_bounded_phase_hit_from_witness
    (bound : ℕ) (target ε : ℝ)
    (h : ∃ m : ℕ, m ≤ bound ∧ |plasticSpiralPhaseAtStep m - target| < ε) :
    ∃ m : ℕ, m ≤ bound ∧ |plasticSpiralPhaseAtStep m - target| < ε := by
  exact h

/--
Complex phase factor used in the plastic-series candidate:
`exp(2π i · plasticSpiralPhaseAtStep m)`.
-/
noncomputable def plasticPhaseFactor (m : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (plasticSpiralPhaseAtStep m : ℂ))

/-- Radial cubic damping slot `ρ^(3m)` cast to `ℂ`. -/
noncomputable def plasticCubicRadialWeight (m : ℕ) : ℂ :=
  (spiralPlasticNumber : ℂ) ^ (3 * m)

theorem spiralPlasticNumber_pos : 0 < spiralPlasticNumber := by
  simpa [spiralPlasticNumber] using Hqiv.Geometry.plasticNumber_pos

theorem spiralPlasticNumber_nonneg : 0 ≤ spiralPlasticNumber :=
  le_of_lt spiralPlasticNumber_pos

theorem spiralPlasticNumber_gt_one : 1 < spiralPlasticNumber := by
  simpa [spiralPlasticNumber] using Hqiv.Geometry.plasticNumber_mem_Ioo_one_two |>.1

theorem spiralPlasticNumber_pow_three_gt_one : 1 < spiralPlasticNumber ^ (3 : ℕ) := by
  dsimp [spiralPlasticNumber]
  have hρ3 :
      Hqiv.Geometry.plasticNumber ^ 3 = Hqiv.Geometry.plasticNumber + 1 := by
    have h := Hqiv.Geometry.plasticNumber_cubic_eq_zero
    nlinarith
  have h1 : 1 < Hqiv.Geometry.plasticNumber :=
    Hqiv.Geometry.plasticNumber_mem_Ioo_one_two |>.1
  rw [hρ3]
  nlinarith [Hqiv.Geometry.plasticNumber_pos]

/-- Canonical plastic contraction-rate candidate `q = 1 / ρ^3`. -/
noncomputable def plasticCubicContractionRate : ℝ :=
  1 / (spiralPlasticNumber ^ (3 : ℕ))

theorem plasticCubicContractionRate_pos : 0 < plasticCubicContractionRate := by
  unfold plasticCubicContractionRate
  exact one_div_pos.mpr (pow_pos spiralPlasticNumber_pos _)

theorem plasticCubicContractionRate_lt_one : plasticCubicContractionRate < 1 := by
  unfold plasticCubicContractionRate
  have hx : 0 < spiralPlasticNumber ^ (3 : ℕ) := pow_pos spiralPlasticNumber_pos _
  rw [div_lt_iff₀ hx, one_mul]
  exact spiralPlasticNumber_pow_three_gt_one

theorem plasticCubicContractionRate_nonneg : 0 ≤ plasticCubicContractionRate :=
  le_of_lt plasticCubicContractionRate_pos

theorem plasticCubicContractionRate_pow_eq_inv_pow (N : ℕ) :
    plasticCubicContractionRate ^ N = (spiralPlasticNumber ^ (3 * N))⁻¹ := by
  unfold plasticCubicContractionRate
  simp only [div_eq_mul_inv, one_mul]
  rw [inv_pow]
  congr 1
  simpa [mul_comm (3 : ℕ) N] using (pow_mul spiralPlasticNumber 3 N).symm

@[simp]
theorem plasticPhaseFactor_norm (m : ℕ) : ‖plasticPhaseFactor m‖ = 1 := by
  unfold plasticPhaseFactor
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, add_zero, zero_mul, sub_self, Real.exp_zero]

theorem spiralPlastic_cast_ne_zero : (spiralPlasticNumber : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr spiralPlasticNumber_pos.ne'

theorem plasticCubicRadialWeight_ne_zero (m : ℕ) : plasticCubicRadialWeight m ≠ 0 :=
  pow_ne_zero _ spiralPlastic_cast_ne_zero

theorem plasticCubicRadialWeight_norm (m : ℕ) :
    ‖plasticCubicRadialWeight m‖ = spiralPlasticNumber ^ (3 * m) := by
  unfold plasticCubicRadialWeight
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg spiralPlasticNumber_nonneg]

/-- Concrete polynomial/plastic majorant: `A * (m+1)^k / ρ^(3m)`. -/
noncomputable def polynomialPlasticMajorant (A : ℝ) (k : ℕ) : ℕ → ℝ :=
  fun m => A * (m + 1 : ℝ) ^ k / (spiralPlasticNumber ^ (3 * m))

theorem polynomialPlasticMajorant_nonneg (A : ℝ) (k : ℕ) (hA : 0 ≤ A) (m : ℕ) :
    0 ≤ polynomialPlasticMajorant A k m := by
  unfold polynomialPlasticMajorant
  refine div_nonneg (mul_nonneg hA ?_) (pow_nonneg spiralPlasticNumber_nonneg _)
  exact pow_nonneg (add_nonneg (Nat.cast_nonneg m) zero_le_one) _

/-- Bulk kernel `j ↦ (j+1)^k / ρ^(3j)` (prefactor target in the standard `poly(N)·q^N` tail bound). -/
noncomputable def plasticBulkKernel (k : ℕ) (j : ℕ) : ℝ :=
  (j + 1 : ℝ) ^ k / spiralPlasticNumber ^ (3 * j)

theorem plasticBulkKernel_nonneg (k j : ℕ) : 0 ≤ plasticBulkKernel k j := by
  unfold plasticBulkKernel
  refine div_nonneg (pow_nonneg (add_nonneg (Nat.cast_nonneg j) zero_le_one) _)
    (pow_nonneg spiralPlasticNumber_nonneg _)

private lemma cast_N_j_succ_le_mul_succ (N j : ℕ) :
    ((N + j + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
  have hex : (N + 1) * (j + 1) = N * j + (N + j + 1) := by ring
  have hNat : N + j + 1 ≤ (N + 1) * (j + 1) := by
    rw [hex]
    exact Nat.le_add_left _ _
  exact_mod_cast hNat

private lemma polynomialPlasticMajorant_shift_term_le_mul_bulk
    (A : ℝ) (k N j : ℕ) (hA : 0 ≤ A) :
    polynomialPlasticMajorant A k (N + j) ≤
      A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N * plasticBulkKernel k j := by
  have hden :
      spiralPlasticNumber ^ (3 * (N + j)) =
        spiralPlasticNumber ^ (3 * N) * spiralPlasticNumber ^ (3 * j) := by
    rw [← pow_add]
    congr 1
    ring
  have hρprod : 0 ≤ spiralPlasticNumber ^ (3 * N) * spiralPlasticNumber ^ (3 * j) :=
    mul_nonneg (pow_nonneg spiralPlasticNumber_nonneg _) (pow_nonneg spiralPlasticNumber_nonneg _)
  have hcast_m : ((N + j : ℕ) : ℝ) + 1 = ((N + j + 1 : ℕ) : ℝ) := by simp
  have hpow :
      ((N + j + 1 : ℕ) : ℝ) ^ k ≤ (((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ k := by
    refine pow_le_pow_left₀ ?_ (cast_N_j_succ_le_mul_succ N j) k
    exact_mod_cast (Nat.zero_le (N + j + 1))
  have hmulpow :
      (((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ k = (N + 1 : ℝ) ^ k * (j + 1 : ℝ) ^ k := by
    simpa using (mul_pow ((N + 1 : ℕ) : ℝ) ((j + 1 : ℕ) : ℝ) k)
  have hstep1 :
      polynomialPlasticMajorant A k (N + j) ≤
        A * (((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ k /
          (spiralPlasticNumber ^ (3 * N) * spiralPlasticNumber ^ (3 * j)) := by
    unfold polynomialPlasticMajorant
    rw [hden, hcast_m]
    refine div_le_div_of_nonneg_right ?_ hρprod
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hpow hA
  have hRHS :
      A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N * plasticBulkKernel k j =
        A * (((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ k /
          (spiralPlasticNumber ^ (3 * N) * spiralPlasticNumber ^ (3 * j)) := by
    unfold plasticBulkKernel
    rw [plasticCubicContractionRate_pow_eq_inv_pow, hmulpow]
    field_simp [pow_ne_zero, spiralPlasticNumber_pos.ne']
  calc
    polynomialPlasticMajorant A k (N + j)
        ≤ A * (((N + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ k /
            (spiralPlasticNumber ^ (3 * N) * spiralPlasticNumber ^ (3 * j)) := hstep1
    _ = A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N * plasticBulkKernel k j := hRHS.symm

theorem summable_polynomialPlasticMajorant_shift_of_summable_bulk
    (A : ℝ) (k N : ℕ) (hA : 0 ≤ A)
    (hBulk : Summable (plasticBulkKernel k)) :
    Summable (fun j : ℕ => polynomialPlasticMajorant A k (N + j)) := by
  let g : ℕ → ℝ := fun j =>
    A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N * plasticBulkKernel k j
  have hg : Summable g :=
    (hBulk.mul_left (A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N))
  refine Summable.of_nonneg_of_le (fun j => polynomialPlasticMajorant_nonneg A k hA (N + j))
    (fun j => ?_) hg
  exact polynomialPlasticMajorant_shift_term_le_mul_bulk A k N j hA

theorem tsum_polynomialPlasticMajorant_shift_le_mul_bulk_tsum
    (A : ℝ) (k N : ℕ) (hA : 0 ≤ A)
    (hBulk : Summable (plasticBulkKernel k)) :
    (∑' j : ℕ, polynomialPlasticMajorant A k (N + j)) ≤
      (A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N) * ∑' j : ℕ, plasticBulkKernel k j := by
  let a : ℝ := A * (N + 1 : ℝ) ^ k * plasticCubicContractionRate ^ N
  let g : ℕ → ℝ := fun j => a * plasticBulkKernel k j
  have hg : Summable g := hBulk.mul_left a
  have hf :
      Summable (fun j : ℕ => polynomialPlasticMajorant A k (N + j)) :=
    summable_polynomialPlasticMajorant_shift_of_summable_bulk A k N hA hBulk
  have hsplit : (∑' j : ℕ, g j) = a * ∑' j : ℕ, plasticBulkKernel k j := by
    simpa [g, a, mul_assoc, mul_left_comm, mul_comm] using (hBulk.tsum_mul_left a)
  exact (Summable.tsum_mono hf hg fun j => polynomialPlasticMajorant_shift_term_le_mul_bulk A k N j hA).trans
    hsplit.le

/--
Schematic "plastic-baked" zeta(3) accelerated-series data.

`coeff` is the Apéry/Beukers-style coefficient channel,
`constantTerm` is the closed-form offset `C(ρ)`,
and `hSummable` records convergence of the complex series term model.
-/
structure PlasticZeta3SeriesCandidate where
  constantTerm : ℂ
  coeff : ℕ → ℂ
  hSummable :
    Summable (fun m : ℕ => (coeff m / plasticCubicRadialWeight m) * plasticPhaseFactor m)

/-- One term of the plastic `ζ(3)` candidate series at shell index `m`. -/
noncomputable def PlasticZeta3SeriesCandidate.tailTerm (S : PlasticZeta3SeriesCandidate) (m : ℕ) : ℂ :=
  (S.coeff m / plasticCubicRadialWeight m) * plasticPhaseFactor m

/-- The associated candidate series value `C(ρ) + Σ coeff_m · ρ^(-3m) · exp(2π i phase_m)`. -/
noncomputable def PlasticZeta3SeriesCandidate.value (S : PlasticZeta3SeriesCandidate) : ℂ :=
  S.constantTerm + ∑' m : ℕ, S.tailTerm m

/-- The tail/truncation channel used for explicit error-control lemmas. -/
noncomputable def PlasticZeta3SeriesCandidate.tailFrom
    (S : PlasticZeta3SeriesCandidate) (N : ℕ) : ℂ :=
  ∑' k : ℕ, S.tailTerm (N + k)

theorem PlasticZeta3SeriesCandidate.norm_tailTerm_le_polynomialPlasticMajorant
    (S : PlasticZeta3SeriesCandidate) (A : ℝ) (k : ℕ)
    (_hA : 0 ≤ A) (hBound : ∀ m : ℕ, ‖S.coeff m‖ ≤ A * (m + 1 : ℝ) ^ k) (m : ℕ) :
    ‖S.tailTerm m‖ ≤ polynomialPlasticMajorant A k m := by
  have hw : 0 < spiralPlasticNumber ^ (3 * m) := pow_pos spiralPlasticNumber_pos _
  have hw' : ‖plasticCubicRadialWeight m‖ = spiralPlasticNumber ^ (3 * m) :=
    plasticCubicRadialWeight_norm m
  calc
    ‖S.tailTerm m‖
        = ‖S.coeff m / plasticCubicRadialWeight m‖ * ‖plasticPhaseFactor m‖ := by
          rw [PlasticZeta3SeriesCandidate.tailTerm, norm_mul]
    _ = ‖S.coeff m / plasticCubicRadialWeight m‖ := by
          rw [plasticPhaseFactor_norm, mul_one]
    _ = ‖S.coeff m‖ / ‖plasticCubicRadialWeight m‖ := by
          rw [Complex.norm_div]
    _ = ‖S.coeff m‖ / spiralPlasticNumber ^ (3 * m) := by rw [hw']
    _ ≤ (A * (m + 1 : ℝ) ^ k) / spiralPlasticNumber ^ (3 * m) := by
          exact div_le_div_of_nonneg_right (hBound m) hw.le
    _ = polynomialPlasticMajorant A k m := rfl

theorem PlasticZeta3SeriesCandidate.tail_norm_le_tsum_polynomial_majorant
    (S : PlasticZeta3SeriesCandidate) (A : ℝ) (k : ℕ) (N : ℕ)
    (hA : 0 ≤ A) (hBound : ∀ m : ℕ, ‖S.coeff m‖ ≤ A * (m + 1 : ℝ) ^ k)
    (hMaj : Summable (fun j : ℕ => polynomialPlasticMajorant A k (N + j))) :
    ‖S.tailFrom N‖ ≤ ∑' j : ℕ, polynomialPlasticMajorant A k (N + j) := by
  simpa [PlasticZeta3SeriesCandidate.tailFrom] using
    (tsum_of_norm_bounded (Summable.hasSum hMaj) fun j =>
      S.norm_tailTerm_le_polynomialPlasticMajorant A k hA hBound (N + j))

/--
External truncation-error profile for the plastic candidate tail:
`B N` is intended to upper bound `‖tailFrom N‖`.
-/
def PlasticZeta3SeriesCandidate.TailBoundProfile
    (S : PlasticZeta3SeriesCandidate) (B : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ‖S.tailFrom N‖ ≤ B N

/--
Eliminator for tail bounds: if `TailBoundProfile S B` is supplied, we can read off
the explicit truncation error estimate at any cutoff `N`.
-/
theorem PlasticZeta3SeriesCandidate.tail_norm_le_of_profile
    (S : PlasticZeta3SeriesCandidate) (B : ℕ → ℝ)
    (hB : S.TailBoundProfile B) (N : ℕ) :
    ‖S.tailFrom N‖ ≤ B N :=
  hB N

/--
Geometric specialization scaffold for effective convergence control.

`q` is the contraction rate (expected to be tied to plastic scaling), `C` is a
global amplitude constant, and `hGeom` is the supplied bound channel.
-/
structure PlasticZeta3SeriesCandidate.GeometricTailControl
    (S : PlasticZeta3SeriesCandidate) where
  C : ℝ
  q : ℝ
  hCnonneg : 0 ≤ C
  hqnonneg : 0 ≤ q
  hqltOne : q < 1
  hGeom : ∀ N : ℕ, ‖S.tailFrom N‖ ≤ C * q ^ N

/--
Readout theorem for geometric truncation error:
if geometric control data are given, then each cutoff `N` satisfies
`‖tailFrom N‖ ≤ C * q^N`.
-/
theorem PlasticZeta3SeriesCandidate.tail_norm_le_geometric
    (S : PlasticZeta3SeriesCandidate)
    (G : S.GeometricTailControl) (N : ℕ) :
    ‖S.tailFrom N‖ ≤ G.C * G.q ^ N :=
  G.hGeom N

/--
Coefficient-growth-to-geometric-tail theorem (plastic-baked `ζ(3)` accelerator),
in compile-safe skeleton form.

If coefficients satisfy polynomial growth
`‖coeff m‖ ≤ A * (m+1)^k`, and one has established the corresponding tail estimate
at the canonical plastic rate `q = 1/ρ^3`, then this packages the result as a
`GeometricTailControl` witness.

This keeps the file `sorry`-free while exposing the exact theorem shape needed for
the next arithmetic-analytic discharge step.
-/
theorem PlasticZeta3SeriesCandidate.geometric_tail_from_polynomial_coeff_growth
    (S : PlasticZeta3SeriesCandidate)
    (A : ℝ) (k : ℕ)
    (_hA : 0 ≤ A)
    (_hBound : ∀ m : ℕ, ‖S.coeff m‖ ≤ A * (m + 1 : ℝ) ^ k)
    (C : ℝ)
    (hCnonneg : 0 ≤ C)
    (hqnonneg : 0 ≤ plasticCubicContractionRate)
    (hqltOne : plasticCubicContractionRate < 1)
    (hGeom :
      ∀ N : ℕ, ‖S.tailFrom N‖ ≤ C * plasticCubicContractionRate ^ N) :
    ∃ (C q : ℝ), 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∃ G : S.GeometricTailControl, G.C = C ∧ G.q = q := by
  refine ⟨C, plasticCubicContractionRate, hCnonneg, hqnonneg, hqltOne, ?_⟩
  refine ⟨{ C := C
            q := plasticCubicContractionRate
            hCnonneg := hCnonneg
            hqnonneg := hqnonneg
            hqltOne := hqltOne
            hGeom := hGeom }, rfl, rfl⟩

/--
Majorant bridge datum for deriving geometric tail control.

`majorant` models an explicit nonnegative termwise envelope for the tail series
terms, and `hTailLe` / `hMajorantGeom` encode the two analytic steps:

1. tail norm is bounded by the majorant series tail,
2. that majorant tail is bounded geometrically by `C * q^N`.
-/
structure PlasticZeta3SeriesCandidate.MajorantTailBridge
    (S : PlasticZeta3SeriesCandidate) where
  majorant : ℕ → ℝ
  C : ℝ
  q : ℝ
  hCnonneg : 0 ≤ C
  hqnonneg : 0 ≤ q
  hqltOne : q < 1
  hTailLe : ∀ N : ℕ, ‖S.tailFrom N‖ ≤ ∑' k : ℕ, majorant (N + k)
  hMajorantGeom : ∀ N : ℕ, (∑' k : ℕ, majorant (N + k)) ≤ C * q ^ N

/--
If a tail majorant is available and its tail decays geometrically, then the
plastic-series candidate inherits geometric truncation control.
-/
def PlasticZeta3SeriesCandidate.geometric_tail_from_majorant_bridge
    (S : PlasticZeta3SeriesCandidate)
    (B : S.MajorantTailBridge) :
    S.GeometricTailControl := by
  refine
    { C := B.C
      q := B.q
      hCnonneg := B.hCnonneg
      hqnonneg := B.hqnonneg
      hqltOne := B.hqltOne
      hGeom := ?_ }
  intro N
  exact le_trans (B.hTailLe N) (B.hMajorantGeom N)

/--
Readout theorem: the majorant bridge immediately yields the explicit estimate
`‖tailFrom N‖ ≤ C * q^N` at each cutoff.
-/
theorem PlasticZeta3SeriesCandidate.tail_norm_le_geometric_of_majorant_bridge
    (S : PlasticZeta3SeriesCandidate)
    (B : S.MajorantTailBridge) (N : ℕ) :
    ‖S.tailFrom N‖ ≤ B.C * B.q ^ N := by
  exact le_trans (B.hTailLe N) (B.hMajorantGeom N)

/--
Majorant construction from polynomial coefficient growth + plastic cubic damping.

Compile-safe constructive form: we define the concrete majorant
`A*(m+1)^k / ρ^(3m)` explicitly, and if the two analytic inequalities are supplied
for that majorant (tail domination + geometric tail for `q = 1/ρ^3`), we obtain
an actual `MajorantTailBridge`.
-/
theorem PlasticZeta3SeriesCandidate.majorant_from_polynomial_coeff_growth
    (S : PlasticZeta3SeriesCandidate)
    (A : ℝ) (k : ℕ)
    (_hA : 0 ≤ A)
    (_hBound : ∀ m : ℕ, ‖S.coeff m‖ ≤ A * (m + 1 : ℝ) ^ k)
    (C : ℝ)
    (hCnonneg : 0 ≤ C)
    (hqnonneg : 0 ≤ plasticCubicContractionRate)
    (hqltOne : plasticCubicContractionRate < 1)
    (hTailLe :
      ∀ N : ℕ,
        ‖S.tailFrom N‖ ≤
          ∑' j : ℕ, polynomialPlasticMajorant A k (N + j))
    (hMajorantGeom :
      ∀ N : ℕ,
        (∑' j : ℕ, polynomialPlasticMajorant A k (N + j))
          ≤ C * plasticCubicContractionRate ^ N) :
    ∃ B : S.MajorantTailBridge,
      B.majorant = polynomialPlasticMajorant A k ∧
      B.q = plasticCubicContractionRate ∧
      B.C = C := by
  refine ⟨{ majorant := polynomialPlasticMajorant A k
            C := C
            q := plasticCubicContractionRate
            hCnonneg := hCnonneg
            hqnonneg := hqnonneg
            hqltOne := hqltOne
            hTailLe := hTailLe
            hMajorantGeom := hMajorantGeom }, rfl, rfl, rfl⟩

/--
`Analytic debt` package for the concrete polynomial/plastic majorant.

This isolates exactly the two remaining inequalities needed to turn polynomial
coefficient growth into an effective geometric truncation bound:

1. `hTailLe` (tail norm ≤ majorant tail),
2. `hMajorantGeom` (majorant tail ≤ `C * q^N` with `q = 1/ρ^3`).
-/
structure PlasticZeta3SeriesCandidate.PolynomialPlasticAnalyticDebt
    (S : PlasticZeta3SeriesCandidate) (A : ℝ) (k : ℕ) where
  C : ℝ
  hCnonneg : 0 ≤ C
  hqnonneg : 0 ≤ plasticCubicContractionRate
  hqltOne : plasticCubicContractionRate < 1
  hTailLe :
    ∀ N : ℕ,
      ‖S.tailFrom N‖ ≤
        ∑' j : ℕ, polynomialPlasticMajorant A k (N + j)
  hMajorantGeom :
    ∀ N : ℕ,
      (∑' j : ℕ, polynomialPlasticMajorant A k (N + j))
        ≤ C * plasticCubicContractionRate ^ N

/--
One-shot effective bound: once the analytic debt package is supplied, the plastic
accelerator tail estimate is immediate.
-/
theorem PlasticZeta3SeriesCandidate.tail_norm_le_of_polynomialPlasticAnalyticDebt
    (S : PlasticZeta3SeriesCandidate)
    (A : ℝ) (k : ℕ)
    (D : S.PolynomialPlasticAnalyticDebt A k) (N : ℕ) :
    ‖S.tailFrom N‖ ≤ D.C * plasticCubicContractionRate ^ N := by
  exact le_trans (D.hTailLe N) (D.hMajorantGeom N)

/--
The same debt package yields a full `GeometricTailControl` witness at the
canonical plastic rate.
-/
def PlasticZeta3SeriesCandidate.geometricTailControl_of_polynomialPlasticAnalyticDebt
    (S : PlasticZeta3SeriesCandidate)
    (A : ℝ) (k : ℕ)
    (D : S.PolynomialPlasticAnalyticDebt A k) :
    S.GeometricTailControl where
  C := D.C
  q := plasticCubicContractionRate
  hCnonneg := D.hCnonneg
  hqnonneg := D.hqnonneg
  hqltOne := D.hqltOne
  hGeom := S.tail_norm_le_of_polynomialPlasticAnalyticDebt A k D

/-- Apéry-style coefficient channel for `ζ(3)`-type discretization: `a_m = 1/(m+1)^3`. -/
noncomputable def aperyStyleZeta3Coeff (m : ℕ) : ℂ :=
  ((((m + 1 : ℝ) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ)

theorem aperyStyleZeta3Coeff_norm_le_one (m : ℕ) :
    ‖aperyStyleZeta3Coeff m‖ ≤ (1 : ℝ) := by
  have hm1 : (1 : ℝ) ≤ (m + 1 : ℝ) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hpow_ge : (1 : ℝ) ≤ (m + 1 : ℝ) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg ((m + 1 : ℝ) - 1)]
  have hpow_pos : 0 < (m + 1 : ℝ) ^ (3 : ℕ) := by positivity
  have hdiv : (1 : ℝ) / ((m + 1 : ℝ) ^ (3 : ℕ)) ≤ 1 / (1 : ℝ) := by
    exact one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hpow_ge
  have hnonneg : 0 ≤ ((m + 1 : ℝ) ^ (3 : ℕ))⁻¹ := inv_nonneg.mpr (le_of_lt hpow_pos)
  calc
    ‖aperyStyleZeta3Coeff m‖
        = |(((m + 1 : ℝ) ^ (3 : ℕ))⁻¹ : ℝ)| := by
          simpa [aperyStyleZeta3Coeff] using
            (Complex.norm_real (((m + 1 : ℝ) ^ (3 : ℕ))⁻¹))
    _ = ((m + 1 : ℝ) ^ (3 : ℕ))⁻¹ := abs_of_nonneg hnonneg
    _ = (1 : ℝ) / ((m + 1 : ℝ) ^ (3 : ℕ)) := by simp [one_div]
    _ ≤ 1 / (1 : ℝ) := hdiv
    _ = (1 : ℝ) := by norm_num

theorem aperyStyleZeta3Coeff_growth_bound (m : ℕ) :
    ‖aperyStyleZeta3Coeff m‖ ≤ (1 : ℝ) * (m + 1 : ℝ) ^ (0 : ℕ) := by
  simpa using aperyStyleZeta3Coeff_norm_le_one m

theorem polynomialPlasticMajorant_one_zero_eq_geometric (m : ℕ) :
    polynomialPlasticMajorant 1 0 m = plasticCubicContractionRate ^ m := by
  rw [plasticCubicContractionRate_pow_eq_inv_pow]
  unfold polynomialPlasticMajorant
  simp [div_eq_mul_inv]

theorem summable_polynomialPlasticMajorant_one_zero_shift (N : ℕ) :
    Summable (fun j : ℕ => polynomialPlasticMajorant 1 0 (N + j)) := by
  have hgeom0 : Summable (fun n : ℕ => plasticCubicContractionRate ^ n) :=
    (hasSum_geometric_of_lt_one plasticCubicContractionRate_nonneg plasticCubicContractionRate_lt_one).summable
  have hgeom : Summable (fun j : ℕ => plasticCubicContractionRate ^ (N + j)) := by
    simpa [pow_add, Nat.add_comm N, mul_comm, mul_left_comm, mul_assoc] using
      (Summable.mul_left (a := plasticCubicContractionRate ^ N) hgeom0)
  simpa [polynomialPlasticMajorant_one_zero_eq_geometric] using hgeom

theorem tsum_polynomialPlasticMajorant_one_zero_shift_eq
    (N : ℕ) :
    (∑' j : ℕ, polynomialPlasticMajorant 1 0 (N + j)) =
      (1 / (1 - plasticCubicContractionRate)) * plasticCubicContractionRate ^ N := by
  have hqabs : |plasticCubicContractionRate| < 1 := by
    simpa [abs_of_nonneg plasticCubicContractionRate_nonneg] using plasticCubicContractionRate_lt_one
  have hsplit :
      (∑' j : ℕ, plasticCubicContractionRate ^ (N + j)) =
        plasticCubicContractionRate ^ N * (∑' j : ℕ, plasticCubicContractionRate ^ j) := by
    simp [pow_add, Nat.add_comm N, tsum_mul_left, mul_comm]
  calc
    (∑' j : ℕ, polynomialPlasticMajorant 1 0 (N + j))
        = ∑' j : ℕ, plasticCubicContractionRate ^ (N + j) := by
            simp [polynomialPlasticMajorant_one_zero_eq_geometric]
    _ = plasticCubicContractionRate ^ N * (∑' j : ℕ, plasticCubicContractionRate ^ j) := hsplit
    _ = plasticCubicContractionRate ^ N * (1 / (1 - plasticCubicContractionRate)) := by
          rw [tsum_geometric_of_lt_one plasticCubicContractionRate_nonneg
            plasticCubicContractionRate_lt_one]
          simp [one_div]
    _ = (1 / (1 - plasticCubicContractionRate)) * plasticCubicContractionRate ^ N := by ring

theorem tsum_polynomialPlasticMajorant_one_zero_shift_le
    (N : ℕ) :
    (∑' j : ℕ, polynomialPlasticMajorant 1 0 (N + j)) ≤
      (1 / (1 - plasticCubicContractionRate)) * plasticCubicContractionRate ^ N := by
  exact le_of_eq (tsum_polynomialPlasticMajorant_one_zero_shift_eq N)

theorem polynomialPlasticMajorant_A_zero_eq (A : ℝ) (m : ℕ) :
    polynomialPlasticMajorant A 0 m = A * plasticCubicContractionRate ^ m := by
  rw [plasticCubicContractionRate_pow_eq_inv_pow]
  unfold polynomialPlasticMajorant
  simp [div_eq_mul_inv]

theorem summable_polynomialPlasticMajorant_A_zero_shift (A : ℝ) (N : ℕ) (_hA : 0 ≤ A) :
    Summable (fun j : ℕ => polynomialPlasticMajorant A 0 (N + j)) := by
  have h1 := summable_polynomialPlasticMajorant_one_zero_shift N
  simpa [polynomialPlasticMajorant_A_zero_eq, mul_assoc, mul_comm, mul_left_comm] using h1.mul_left A

theorem tsum_polynomialPlasticMajorant_A_zero_shift_eq (A : ℝ) (N : ℕ) (_hA : 0 ≤ A) :
    (∑' j : ℕ, polynomialPlasticMajorant A 0 (N + j)) =
      (A / (1 - plasticCubicContractionRate)) * plasticCubicContractionRate ^ N := by
  have hmul :
      (fun j : ℕ => polynomialPlasticMajorant A 0 (N + j)) =
        fun j : ℕ => A * polynomialPlasticMajorant 1 0 (N + j) := by
    funext j
    simp [polynomialPlasticMajorant_A_zero_eq]
  rw [hmul, tsum_mul_left]
  rw [tsum_polynomialPlasticMajorant_one_zero_shift_eq N]
  field_simp

theorem tsum_polynomialPlasticMajorant_A_zero_shift_le (A : ℝ) (N : ℕ) (hA : 0 ≤ A) :
    (∑' j : ℕ, polynomialPlasticMajorant A 0 (N + j)) ≤
      (A / (1 - plasticCubicContractionRate)) * plasticCubicContractionRate ^ N := by
  exact le_of_eq (tsum_polynomialPlasticMajorant_A_zero_shift_eq A N hA)

/-- Polynomial/plastic analytic debt for nonnegative amplitude `A` and `k = 0`. -/
def PlasticZeta3SeriesCandidate.polynomialPlasticAnalyticDebt_of_nonneg_A0
    (S : PlasticZeta3SeriesCandidate) (A : ℝ)
    (hA : 0 ≤ A)
    (hBound : ∀ m : ℕ, ‖S.coeff m‖ ≤ A * (m + 1 : ℝ) ^ (0 : ℕ)) :
    S.PolynomialPlasticAnalyticDebt A 0 where
  C := A / (1 - plasticCubicContractionRate)
  hCnonneg := by
    have hden : 0 < 1 - plasticCubicContractionRate := by linarith [plasticCubicContractionRate_lt_one]
    exact div_nonneg hA (le_of_lt hden)
  hqnonneg := plasticCubicContractionRate_nonneg
  hqltOne := plasticCubicContractionRate_lt_one
  hTailLe := by
    intro N
    refine S.tail_norm_le_tsum_polynomial_majorant A 0 N hA hBound ?_
    exact summable_polynomialPlasticMajorant_A_zero_shift A N hA
  hMajorantGeom := by
    intro N
    exact tsum_polynomialPlasticMajorant_A_zero_shift_le A N hA

/-- Concrete Apéry-style debt closure with explicit constants `A = 1`, `k = 0`. -/
def PlasticZeta3SeriesCandidate.aperyStyle_polynomialPlasticAnalyticDebt
    (S : PlasticZeta3SeriesCandidate)
    (hCoeff : S.coeff = aperyStyleZeta3Coeff) :
    S.PolynomialPlasticAnalyticDebt 1 0 where
  C := 1 / (1 - plasticCubicContractionRate)
  hCnonneg := by
    have hden : 0 < 1 - plasticCubicContractionRate := by linarith [plasticCubicContractionRate_lt_one]
    exact le_of_lt (one_div_pos.mpr hden)
  hqnonneg := plasticCubicContractionRate_nonneg
  hqltOne := plasticCubicContractionRate_lt_one
  hTailLe := by
    intro N
    refine S.tail_norm_le_tsum_polynomial_majorant 1 0 N (by norm_num) ?_ ?_
    · intro m
      simpa [hCoeff] using aperyStyleZeta3Coeff_growth_bound m
    · exact summable_polynomialPlasticMajorant_one_zero_shift N
  hMajorantGeom := by
    intro N
    exact tsum_polynomialPlasticMajorant_one_zero_shift_le N

/-- 3D phase channel wrapper (root-scale binned field with prime-pole crossings). -/
structure PlasticRootScaleBinnedField3D where
  phi_3D : ℕ → ℝ
  primePoleCrossing : ℕ → ℕ → Prop
  hPhaseCompat : ∀ m : ℕ, phi_3D m = plasticSpiralPhaseAtStep m

open Classical in
/-- Mixed-radix decode of shell index `m` into three axis digits (test hook for 3D bookkeeping). -/
def defaultLatticePointOfIndex (m : ℕ) : Fin 3 → ℤ :=
  ![((m % 10 : ℕ) : ℤ), (((m / 10) % 10 : ℕ) : ℤ), ((m / 100 : ℕ) : ℤ)]

open Classical in
/-- Near-diagonal predicate on the default lattice point (two coordinates differ by at most `1`). -/
def defaultLatticeNearDiagonal (m : ℕ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧
    Int.natAbs (defaultLatticePointOfIndex m i - defaultLatticePointOfIndex m j) ≤ 1

open Classical in
/-- Diagonal boost factor for `default3DCoeff`. -/
noncomputable def default3DBoost (m : ℕ) : ℝ :=
  if defaultLatticeNearDiagonal m then (1.5 : ℝ) else (1 : ℝ)

open Classical in
/-- Prime-pole bonus factor for `default3DCoeff` (uses the two low base-10 digits of `m`). -/
noncomputable def default3DPrimeBonus (F : PlasticRootScaleBinnedField3D) (m : ℕ) : ℝ :=
  if F.primePoleCrossing (m % 10) ((m / 10) % 10) then (2 : ℝ) else (1 : ℝ)

/--
Default 3D coefficient: Apéry base `1/(m+1)^3`, multiplied by a diagonal boost and a
prime-pole bonus (all real factors cast to `ℂ`).

`‖default3DCoeff F m‖ ≤ 3` unconditionally, hence polynomial growth with `A = 3`, `k = 0`.
-/
noncomputable def default3DCoeff (F : PlasticRootScaleBinnedField3D) (m : ℕ) : ℂ :=
  aperyStyleZeta3Coeff m * (default3DBoost m : ℂ) * (default3DPrimeBonus F m : ℂ)

theorem default3DBoost_abs_le (m : ℕ) : |default3DBoost m| ≤ (1.5 : ℝ) := by
  classical
  unfold default3DBoost
  split_ifs <;> norm_num

theorem default3DPrimeBonus_abs_le (F : PlasticRootScaleBinnedField3D) (m : ℕ) :
    |default3DPrimeBonus F m| ≤ (2 : ℝ) := by
  classical
  unfold default3DPrimeBonus
  split_ifs <;> norm_num

theorem default3DCoeff_norm_le_three (F : PlasticRootScaleBinnedField3D) (m : ℕ) :
    ‖default3DCoeff F m‖ ≤ (3 : ℝ) := by
  classical
  unfold default3DCoeff
  have hbase := aperyStyleZeta3Coeff_norm_le_one m
  have hb := default3DBoost_abs_le m
  have hpb := default3DPrimeBonus_abs_le F m
  have hnb : ‖(default3DBoost m : ℂ)‖ = |default3DBoost m| := by
    simpa using (Complex.norm_real (default3DBoost m))
  have hnpb : ‖(default3DPrimeBonus F m : ℂ)‖ = |default3DPrimeBonus F m| := by
    simpa using (Complex.norm_real (default3DPrimeBonus F m))
  have hmul1 :
      ‖aperyStyleZeta3Coeff m‖ * |default3DBoost m| ≤ (1 : ℝ) * (1.5 : ℝ) :=
    mul_le_mul hbase hb (abs_nonneg (default3DBoost m)) (zero_le_one' ℝ)
  have hmul2 :
      ‖aperyStyleZeta3Coeff m‖ * |default3DBoost m| * |default3DPrimeBonus F m| ≤
        (1 * 1.5 : ℝ) * (2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hpb
          (mul_nonneg (norm_nonneg _) (abs_nonneg (default3DBoost m)))).trans
      (mul_le_mul_of_nonneg_right hmul1 (show (0 : ℝ) ≤ (2 : ℝ) from by norm_num))
  calc
    ‖aperyStyleZeta3Coeff m * (default3DBoost m : ℂ) * (default3DPrimeBonus F m : ℂ)‖
        ≤ ‖aperyStyleZeta3Coeff m‖ * ‖(default3DBoost m : ℂ)‖ * ‖(default3DPrimeBonus F m : ℂ)‖ := by
          simpa [mul_assoc] using
            (norm_mul_le (aperyStyleZeta3Coeff m * (default3DBoost m : ℂ)) (default3DPrimeBonus F m : ℂ)).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖aperyStyleZeta3Coeff m‖ * |default3DBoost m| * |default3DPrimeBonus F m| := by
          rw [hnb, hnpb]
    _ ≤ (1 * 1.5 : ℝ) * (2 : ℝ) := hmul2
    _ = (3 : ℝ) := by norm_num

theorem default3DCoeff_growth_bound (F : PlasticRootScaleBinnedField3D) (m : ℕ) :
    ‖default3DCoeff F m‖ ≤ (3 : ℝ) * (m + 1 : ℝ) ^ (0 : ℕ) := by
  simpa using default3DCoeff_norm_le_three F m

/-- Analytic debt for the default 3D coefficient rule (`A = 3`, `k = 0`). -/
def PlasticZeta3SeriesCandidate.default3DCoeff_polynomialPlasticAnalyticDebt
    (S : PlasticZeta3SeriesCandidate) (F : PlasticRootScaleBinnedField3D)
    (hCoeff : S.coeff = default3DCoeff F) :
    S.PolynomialPlasticAnalyticDebt 3 0 :=
  S.polynomialPlasticAnalyticDebt_of_nonneg_A0 3 (by norm_num) (by
    intro m
    rw [hCoeff]
    simpa using default3DCoeff_growth_bound F m)

/-- One-shot geometric tail control using `default3DCoeff`. -/
def PlasticZeta3SeriesCandidate.geometricTailControl_of_rootScaleBinnedField3D_default3DCoeff
    (S : PlasticZeta3SeriesCandidate) (F : PlasticRootScaleBinnedField3D)
    (hCoeff : S.coeff = default3DCoeff F) :
    S.GeometricTailControl :=
  S.geometricTailControl_of_polynomialPlasticAnalyticDebt 3 0
    (S.default3DCoeff_polynomialPlasticAnalyticDebt F hCoeff)

/-- Phase factor driven by an external `phi_3D` channel. -/
noncomputable def plasticPhaseFactor3D (phi_3D : ℕ → ℝ) (m : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (phi_3D m : ℂ))

/-- Build the standard candidate from a 3D phase channel once compatibility is provided. -/
def PlasticZeta3SeriesCandidate.ofPhi3D
    (constantTerm : ℂ) (coeff : ℕ → ℂ)
    (phi_3D : ℕ → ℝ)
    (hPhaseCompat : ∀ m : ℕ, phi_3D m = plasticSpiralPhaseAtStep m)
    (hSummable3D :
      Summable (fun m : ℕ => (coeff m / plasticCubicRadialWeight m) * plasticPhaseFactor3D phi_3D m)) :
    PlasticZeta3SeriesCandidate where
  constantTerm := constantTerm
  coeff := coeff
  hSummable := by
    simpa [plasticPhaseFactor3D, plasticPhaseFactor, plasticSpiralPhaseAtStep, hPhaseCompat,
      mul_assoc, mul_left_comm, mul_comm] using hSummable3D

/-- Convenience bridge from the root-scale/prime-pole 3D field package. -/
def PlasticZeta3SeriesCandidate.ofRootScaleBinnedField3D
    (F : PlasticRootScaleBinnedField3D)
    (constantTerm : ℂ) (coeff : ℕ → ℂ)
    (hSummable3D :
      Summable (fun m : ℕ => (coeff m / plasticCubicRadialWeight m) * plasticPhaseFactor3D F.phi_3D m)) :
    PlasticZeta3SeriesCandidate :=
  PlasticZeta3SeriesCandidate.ofPhi3D constantTerm coeff F.phi_3D F.hPhaseCompat hSummable3D

/-- One-shot geometric tail control for the 3D root-scale binned field
using the Apéry-style coefficient channel. -/
def PlasticZeta3SeriesCandidate.geometricTailControl_of_rootScaleBinnedField3D
    (S : PlasticZeta3SeriesCandidate)
    (F : PlasticRootScaleBinnedField3D)
    (hCoeff : S.coeff = aperyStyleZeta3Coeff) :
    S.GeometricTailControl := by
  let _phaseCompat := F.hPhaseCompat
  exact S.geometricTailControl_of_polynomialPlasticAnalyticDebt 1 0
    (S.aperyStyle_polynomialPlasticAnalyticDebt hCoeff)

/-- Candidate package for odd zeta channels `ζ(2n+1)` driven by the plastic accelerator.

`series` is the concrete accelerated series candidate, while `hModel` records the
intended target-value equality (numerical, symbolic, or future formal bridge).
-/
structure OddZetaClosedFormCandidate where
  n : ℕ
  hn : 1 ≤ n
  series : PlasticZeta3SeriesCandidate
  hModel : True

/-- Analytic-debt payload for an odd-zeta candidate through polynomial/plastic majorants. -/
structure OddZetaClosedFormCandidate.AnalyticDebt
    (Z : OddZetaClosedFormCandidate) where
  A : ℝ
  k : ℕ
  debt : Z.series.PolynomialPlasticAnalyticDebt A k

/-- Once analytic debt is supplied, every odd-zeta candidate gets geometric tail control. -/
def OddZetaClosedFormCandidate.geometricTailControl
    (Z : OddZetaClosedFormCandidate)
    (D : Z.AnalyticDebt) :
    Z.series.GeometricTailControl :=
  Z.series.geometricTailControl_of_polynomialPlasticAnalyticDebt D.A D.k D.debt

/-- Explicit tail readout for odd-zeta candidates under analytic debt. -/
theorem OddZetaClosedFormCandidate.tail_norm_le_geometric
    (Z : OddZetaClosedFormCandidate)
    (D : Z.AnalyticDebt) (N : ℕ) :
    ‖Z.series.tailFrom N‖ ≤
      (Z.geometricTailControl D).C * (Z.geometricTailControl D).q ^ N :=
  (Z.geometricTailControl D).hGeom N

/-- `ζ(3)` is the base odd-zeta slot (`n = 1`) in this package. -/
def zeta3ClosedFormCandidate
    (S : PlasticZeta3SeriesCandidate) :
    OddZetaClosedFormCandidate where
  n := 1
  hn := by decide
  series := S
  hModel := trivial

/-- `ζ(3)` specialization of the one-shot Apéry/plastic debt closure. -/
def zeta3AnalyticDebt_of_apery
    (S : PlasticZeta3SeriesCandidate)
    (hCoeff : S.coeff = aperyStyleZeta3Coeff) :
    (zeta3ClosedFormCandidate S).AnalyticDebt where
  A := 1
  k := 0
  debt := S.aperyStyle_polynomialPlasticAnalyticDebt hCoeff

end

end Hqiv.Story
