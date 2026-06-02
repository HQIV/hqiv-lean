import Hqiv.Algebra.WeakInComplexStructure
import Hqiv.Algebra.Triality
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Weak doublet: Pauli generator quadratic form and EW mass bridges

See module comments in the repository version of this file for the scientific narrative; this header
stays short to keep the formalization readable.

Main deliverables:
* `fin2HermitianInner` — explicit Hermitian pairing on `Fin 2 → ℂ`.
* `weakDoubletCovariantTerm` — static schematic `-i g \sum_a W_a T^a φ` with `T^a = σ^a/2`.
* `weakWPlaneGramReal` — real `2 × 2` Gram matrix for `(σ¹, σ²)` on the `higgsDoubletFin2Coeff v` ray
  (axis labels via `weakWPlaneEmbed : Fin 2 → Fin 3`).
* `weakWPlaneGramMatrix` + `weakWPlaneGramMatrix_trace` / `weakWPlaneGramMatrix_det` — spectral
  certificate (both eigenvalues equal `weakWPlaneGramEigenvalue`) packaged with
  `ew_carrier_gram_mass_certificate` chaining `boson_witness_M_W` / `boson_witness_m_H`.
* `M_W_derived_sq_eq_eight_times_weakWPlaneGramEigenvalue` — factor `8` between `M_W²` and the
  common Gram eigenvalue `g² v² / 8` at the outer-horizon gauge vev.
* `higgsCarrierCinner` / `higgsQuarticPotentialCarrier` / `higgsQuarticLambdaGaugeWitness` — carrier
  inner-product quartic with the same geometric `vacuumExpectationValueGauge` anchor as `M_W`, and
  `m_H_sq_eq_two_lambda_times_vgauge_sq` (no new free parameters: `λ` is defined from witnesses).
* Triality generation tags (`So8RepIndex`) + `weakPhiOfShellOnSo8Rep` / `weakOneOverAlphaEMAtRep` hooks.
* Rational `#eval` / `example` PDG-gap numerics at the bottom of the file.
-/

open scoped BigOperators
open Complex Finset Matrix
open Hqiv.Algebra Hqiv.Physics Hqiv

namespace Hqiv.Physics

noncomputable section

/-- Hermitian inner product on `Fin 2 → ℂ` (standard orthonormal coordinates). -/
def fin2HermitianInner (φ ψ : Fin 2 → ℂ) : ℂ :=
  star (φ 0) * ψ 0 + star (φ 1) * ψ 1

/-- Pauli `σ¹ = σ⁺ + σ⁻`. -/
def weakPauliSigma1 : Matrix (Fin 2) (Fin 2) ℂ :=
  weakPauliPlus + weakPauliMinus

/-- Pauli `σ² = [[0, -I], [I, 0]]` (same as `I • (σ⁻ - σ⁺)` on the doublet chart). -/
def weakPauliSigma2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- The three Pauli matrices on the weak doublet (`σ¹, σ², σ³`). -/
def weakPauliSigma : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => weakPauliSigma1
  | 1 => weakPauliSigma2
  | 2 => weakPauliZ3

/-- Half-Pauli `T^a = σ^a / 2` in the `Fin 2` chart. -/
def weakSU2HalfPauli (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 2) • weakPauliSigma a

/-- Schematic static covariant piece `- ∑_a i g W_a T^a φ` (one kinetic slot). -/
def weakDoubletCovariantTerm (g : ℝ) (W : Fin 3 → ℂ) (φ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ∑ a : Fin 3, (-I * (g : ℂ) * W a) • (weakSU2HalfPauli a).mulVec φ

/-- Common eigenvalue of the `σ¹–σ²` Gram matrix along the `u⁺` VEV ray, at coupling `g`. -/
def weakWPlaneGramEigenvalue (g v : ℝ) : ℝ :=
  g ^ 2 * v ^ 2 / 8

/-- Embed `Fin 2` labels into the first two `SU(2)` axis indices in `Fin 3`. -/
def weakWPlaneEmbed (i : Fin 2) : Fin 3 :=
  match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

theorem weakWPlaneEmbed_zero : weakWPlaneEmbed (0 : Fin 2) = (0 : Fin 3) := rfl

theorem weakWPlaneEmbed_one : weakWPlaneEmbed (1 : Fin 2) = (1 : Fin 3) := rfl

/-- Real Gram matrix for `(T^{weakWPlaneEmbed i} φ, T^{weakWPlaneEmbed j} φ)` scaled by `g²`. -/
def weakWPlaneGramReal (g v : ℝ) (i j : Fin 2) : ℝ :=
  g ^ 2 * (fin2HermitianInner
      ((weakSU2HalfPauli (weakWPlaneEmbed i)).mulVec (higgsDoubletFin2Coeff v))
      ((weakSU2HalfPauli (weakWPlaneEmbed j)).mulVec (higgsDoubletFin2Coeff v))).re

theorem weakPauliSigma1_mulVec_higgsCoeff (v : ℝ) :
    weakPauliSigma1.mulVec (higgsDoubletFin2Coeff v) =
      ![0, Complex.ofReal (v / Real.sqrt 2)] := by
  funext i
  fin_cases i <;> simp [weakPauliSigma1, weakPauliPlus, weakPauliMinus, higgsDoubletFin2Coeff,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_zero, zero_mul, add_zero, zero_add]

theorem weakPauliSigma2_mulVec_higgsCoeff (v : ℝ) :
    weakPauliSigma2.mulVec (higgsDoubletFin2Coeff v) =
      ![0, I * Complex.ofReal (v / Real.sqrt 2)] := by
  funext i
  fin_cases i <;> simp [weakPauliSigma2, higgsDoubletFin2Coeff, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, mul_zero, zero_mul, add_zero, zero_add, mul_comm, mul_left_comm]

theorem weakPauliZ3_mulVec_higgsCoeff (v : ℝ) :
    weakPauliZ3.mulVec (higgsDoubletFin2Coeff v) =
      ![Complex.ofReal (v / Real.sqrt 2), 0] := by
  funext i
  fin_cases i <;> simp [weakPauliZ3, higgsDoubletFin2Coeff, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem weakSU2HalfPauli_axis0_mulVec (v : ℝ) :
    (weakSU2HalfPauli (0 : Fin 3)).mulVec (higgsDoubletFin2Coeff v) =
      ![0, Complex.ofReal (v / Real.sqrt 2 / 2)] := by
  change (((1 : ℂ) / 2) • weakPauliSigma1).mulVec (higgsDoubletFin2Coeff v) = _
  rw [smul_mulVec, weakPauliSigma1_mulVec_higgsCoeff v]
  funext i
  fin_cases i <;>
    simp [Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul, mul_comm, Complex.ofReal_div,
      div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem weakSU2HalfPauli_axis1_mulVec (v : ℝ) :
    (weakSU2HalfPauli (1 : Fin 3)).mulVec (higgsDoubletFin2Coeff v) =
      ![0, I * Complex.ofReal (v / Real.sqrt 2 / 2)] := by
  change (((1 : ℂ) / 2) • weakPauliSigma2).mulVec (higgsDoubletFin2Coeff v) = _
  rw [smul_mulVec, weakPauliSigma2_mulVec_higgsCoeff v]
  funext i
  fin_cases i <;>
    simp [Pi.smul_apply, smul_eq_mul, mul_zero, zero_mul, mul_comm, mul_left_comm, mul_assoc,
      Complex.I_mul_I, neg_mul, Complex.ofReal_div, div_eq_mul_inv]

theorem fin2HermitianInner_halfPlane_diag (v : ℝ) :
    fin2HermitianInner ![0, Complex.ofReal (v / Real.sqrt 2 / 2)]
        ![0, Complex.ofReal (v / Real.sqrt 2 / 2)] =
      Complex.ofReal (v ^ 2 / 8) := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Complex.ext_iff]
  simp [fin2HermitianInner, Complex.star_def, map_zero, zero_mul, add_zero, conj_ofReal,
    pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hsqrt, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
  constructor <;> field_simp [hsqrt, pow_two, mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem fin2HermitianInner_half_plane_offdiag (v : ℝ) :
    (fin2HermitianInner ![0, Complex.ofReal (v / Real.sqrt 2 / 2)]
        ![0, I * Complex.ofReal (v / Real.sqrt 2 / 2)]).re = 0 := by
  simp [fin2HermitianInner, Complex.star_def, map_zero, zero_mul, add_zero, conj_ofReal, conj_I,
    map_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
    zero_add, sub_self]

theorem fin2HermitianInner_half_plane_symm_offdiag (v : ℝ) :
    (fin2HermitianInner ![0, I * Complex.ofReal (v / Real.sqrt 2 / 2)]
        ![0, Complex.ofReal (v / Real.sqrt 2 / 2)]).re = 0 := by
  simp [fin2HermitianInner, Complex.star_def, map_zero, zero_mul, add_zero, conj_ofReal, conj_I,
    map_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, add_zero,
    zero_add, sub_self]

theorem fin2HermitianInner_half_plane_diag2 (v : ℝ) :
    fin2HermitianInner ![0, I * Complex.ofReal (v / Real.sqrt 2 / 2)]
        ![0, I * Complex.ofReal (v / Real.sqrt 2 / 2)] =
      Complex.ofReal (v ^ 2 / 8) := by
  have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Complex.ext_iff]
  simp [fin2HermitianInner, Complex.star_def, conj_I, conj_ofReal, map_mul, Complex.I_mul_I,
    neg_mul, one_mul, mul_neg, neg_neg, zero_mul, add_zero, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, pow_two, hsqrt,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  constructor <;> field_simp [hsqrt, pow_two, mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem weakWPlaneGramReal_diagonal (g v : ℝ) (i : Fin 2) :
    weakWPlaneGramReal g v i i = g ^ 2 * v ^ 2 / 8 := by
  fin_cases i
  · dsimp [weakWPlaneGramReal, weakWPlaneEmbed]
    rw [weakSU2HalfPauli_axis0_mulVec v, fin2HermitianInner_halfPlane_diag v, Complex.ofReal_re]
    ring
  · dsimp [weakWPlaneGramReal, weakWPlaneEmbed]
    rw [weakSU2HalfPauli_axis1_mulVec v, fin2HermitianInner_half_plane_diag2 v, Complex.ofReal_re]
    ring

theorem weakWPlaneGramReal_offdiag (g v : ℝ) :
    weakWPlaneGramReal g v 0 1 = 0 ∧ weakWPlaneGramReal g v 1 0 = 0 := by
  refine And.intro ?_ ?_
  · dsimp [weakWPlaneGramReal, weakWPlaneEmbed]
    rw [weakSU2HalfPauli_axis0_mulVec v, weakSU2HalfPauli_axis1_mulVec v,
      fin2HermitianInner_half_plane_offdiag v]
    ring
  · dsimp [weakWPlaneGramReal, weakWPlaneEmbed]
    rw [weakSU2HalfPauli_axis1_mulVec v, weakSU2HalfPauli_axis0_mulVec v,
      fin2HermitianInner_half_plane_symm_offdiag v]
    ring

theorem weakWPlaneGramReal_eq_smul_identity (g v : ℝ) :
    (Matrix.of fun i j : Fin 2 => weakWPlaneGramReal g v i j) =
      (g ^ 2 * v ^ 2 / 8) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.one_apply, weakWPlaneGramReal_diagonal, weakWPlaneGramReal_offdiag]

/-- Packaged `2 × 2` Gram matrix for the `(σ¹, σ²)` plane at `(g, v)`. -/
noncomputable abbrev weakWPlaneGramMatrix (g v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => weakWPlaneGramReal g v i j

theorem weakWPlaneGramMatrix_eq_smul (g v : ℝ) :
    weakWPlaneGramMatrix g v = weakWPlaneGramEigenvalue g v • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa [weakWPlaneGramMatrix, weakWPlaneGramEigenvalue] using weakWPlaneGramReal_eq_smul_identity g v

theorem weakWPlaneGramMatrix_trace (g v : ℝ) :
    (weakWPlaneGramMatrix g v).trace = 2 * weakWPlaneGramEigenvalue g v := by
  rw [weakWPlaneGramMatrix_eq_smul, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  simp [smul_eq_mul, mul_comm]

theorem weakWPlaneGramMatrix_det (g v : ℝ) :
    (weakWPlaneGramMatrix g v).det = weakWPlaneGramEigenvalue g v ^ 2 := by
  rw [weakWPlaneGramMatrix_eq_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
  ring

theorem weakWPlaneGramEigenvalue_eq (g v : ℝ) (i : Fin 2) :
    weakWPlaneGramReal g v i i = weakWPlaneGramEigenvalue g v := by
  simp [weakWPlaneGramReal_diagonal, weakWPlaneGramEigenvalue]

theorem M_W_derived_sq_eq_eight_times_weakWPlaneGramEigenvalue :
    M_W_derived ^ 2 = 8 * weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge := by
  simp [weakWPlaneGramEigenvalue, M_W_derived, gaugeBosonMassFromVevGauge, su2CouplingDerived]
  ring

/-- Single certificate: Gram spectrum + factor-`8` bridge + rational `M_W` / `m_H` witnesses from
`DerivedGaugeAndLeptonSector.lean` (no PDG literals in the witness definitions). -/
theorem ew_carrier_gram_mass_certificate :
    (weakWPlaneGramMatrix su2CouplingDerived vacuumExpectationValueGauge).trace =
      2 * weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge ∧
      (weakWPlaneGramMatrix su2CouplingDerived vacuumExpectationValueGauge).det =
        weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge ^ 2 ∧
      M_W_derived ^ 2 =
        8 * weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge ∧
      weakWPlaneGramMatrix su2CouplingDerived vacuumExpectationValueGauge =
        weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      M_W_derived = (392 : ℝ) / 5 ∧
      m_H_derived = (588 : ℝ) / 5 :=
  ⟨weakWPlaneGramMatrix_trace _ _, weakWPlaneGramMatrix_det _ _,
    M_W_derived_sq_eq_eight_times_weakWPlaneGramEigenvalue, weakWPlaneGramMatrix_eq_smul _ _,
    boson_witness_M_W, boson_witness_m_H⟩

theorem ew_carrier_gram_chains_chargedClosureWitness :
    chargedClosureWitness = su2CouplingDerived * vacuumExpectationValueGauge ∧
      M_W_derived ^ 2 = 8 * weakWPlaneGramEigenvalue su2CouplingDerived vacuumExpectationValueGauge ∧
      chargedClosureWitness = M_W_derived := by
  refine ⟨?_, ?_, ?_⟩
  · simp [chargedClosureWitness, M_W_derived, gaugeBosonMassFromVevGauge]
  · exact M_W_derived_sq_eq_eight_times_weakWPlaneGramEigenvalue
  · simp [chargedClosureWitness, M_W_derived]

/-! ### Higgs quartic on the projected carrier (`weakJComplexDoublet`) -/

noncomputable def higgsCarrierCinner (Φ Ψ : weakJComplexDoublet) : ℂ :=
  weakCarrierCinner (Φ : WeakComplexOctonionCarrier) (Ψ : WeakComplexOctonionCarrier)

noncomputable def higgsCarrierNormSq (Φ : weakJComplexDoublet) : ℝ :=
  ‖(Φ : WeakComplexOctonionCarrier)‖ ^ 2

theorem higgsCarrierNormSq_eq_re_inner (Φ : weakJComplexDoublet) :
    higgsCarrierNormSq Φ =
      (RCLike.re (inner ℂ (Φ : WeakComplexOctonionCarrier) (Φ : WeakComplexOctonionCarrier)) : ℝ) := by
  simp [higgsCarrierNormSq, norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem higgsCarrierNormSq_higgsVevOfReal {v : ℝ} (hv : 0 ≤ v) :
    higgsCarrierNormSq (higgsVevOfReal v) = v ^ 2 / 2 := by
  dsimp [higgsCarrierNormSq]
  rw [higgsVevOfReal_coe]
  calc
    ‖(Complex.ofReal (v / Real.sqrt 2)) • weakDoubletVecPlusI‖ ^ 2
        = (‖(Complex.ofReal (v / Real.sqrt 2))‖ * ‖weakDoubletVecPlusI‖) ^ 2 := by rw [norm_smul]
    _ = ‖(Complex.ofReal (v / Real.sqrt 2))‖ ^ 2 * ‖weakDoubletVecPlusI‖ ^ 2 := by ring
    _ = ‖(Complex.ofReal (v / Real.sqrt 2))‖ ^ 2 := by rw [weakDoubletVecPlusI_norm]; ring
    _ = v ^ 2 / 2 := by
      have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hprod : 0 ≤ v / Real.sqrt 2 * (v / Real.sqrt 2) :=
        mul_nonneg (div_nonneg hv (Real.sqrt_nonneg _)) (div_nonneg hv (Real.sqrt_nonneg _))
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sq_sqrt hprod,
        show v / Real.sqrt 2 * (v / Real.sqrt 2) = (v / Real.sqrt 2) ^ 2 by ring, div_pow, hsq]

/-- SM-style quartic centered on `‖Φ‖² = v₀²/2`, matching `higgsVevOfReal v₀` on the orthonormal `u⁺`
axis (`higgsQuarticPotentialCarrier_min_at_vev`). -/
noncomputable def higgsQuarticPotentialCarrier (lam v0 : ℝ) (Φ : weakJComplexDoublet) : ℝ :=
  lam * (higgsCarrierNormSq Φ - v0 ^ 2 / 2) ^ 2

theorem higgsQuarticPotentialCarrier_min_at_vev {lam v0 : ℝ} (hv0 : 0 ≤ v0) :
    higgsQuarticPotentialCarrier lam v0 (higgsVevOfReal v0) = 0 := by
  simp [higgsQuarticPotentialCarrier, higgsCarrierNormSq_higgsVevOfReal hv0]

/-- Effective quartic coupling reconstructed from `(m_H, v_gauge)` with the **gauge** outer closure
scale (same geometric `vacuumExpectationValueGauge` anchor as `M_W_derived`); definitional, not a fit. -/
noncomputable def higgsQuarticLambdaGaugeWitness : ℝ :=
  m_H_derived ^ 2 / (2 * vacuumExpectationValueGauge ^ 2)

theorem vacuumExpectationValueGauge_ne_zero : vacuumExpectationValueGauge ≠ 0 := by
  intro h0
  have : M_W_derived = 0 := by simp [M_W_derived, gaugeBosonMassFromVevGauge, h0]
  rw [boson_witness_M_W] at this
  norm_num at this

theorem m_H_sq_eq_two_lambda_times_vgauge_sq :
    m_H_derived ^ 2 =
      2 * higgsQuarticLambdaGaugeWitness * vacuumExpectationValueGauge ^ 2 := by
  unfold higgsQuarticLambdaGaugeWitness
  have hv2 : vacuumExpectationValueGauge ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero vacuumExpectationValueGauge_ne_zero vacuumExpectationValueGauge_ne_zero
  have hden : 2 * vacuumExpectationValueGauge ^ 2 ≠ 0 := mul_ne_zero two_ne_zero hv2
  calc
    m_H_derived ^ 2 = m_H_derived ^ 2 * 1 := by rw [mul_one]
    _ = m_H_derived ^ 2 * ((2 * vacuumExpectationValueGauge ^ 2) / (2 * vacuumExpectationValueGauge ^ 2)) := by
      rw [div_self hden]
    _ = 2 * (m_H_derived ^ 2 / (2 * vacuumExpectationValueGauge ^ 2)) * vacuumExpectationValueGauge ^ 2 := by ring

/-! ### Triality generation tags (`So8RepIndex`) and ladder hooks -/

noncomputable def weakPhiOfShellOnSo8Rep (ρ : So8RepIndex) : ℝ :=
  phi_of_shell ρ.val

/-- Matches `Hqiv.one_over_alpha_EM_derived` at shell `ρ.val` (closed form in `SM_GR_Unification.lean`). -/
noncomputable def weakOneOverAlphaEMAtRep (ρ : So8RepIndex) (c : ℝ) : ℝ :=
  (42 : ℝ) * (1 + c * (3 / 5 : ℝ) * Real.log (weakPhiOfShellOnSo8Rep ρ + 1))

/-- Yukawa assignment constant on the triality orbit: a triality **singlet** by construction. -/
def weakYukawaTrialitySinglet (y : ℂ) (_ρ : So8RepIndex) : ℂ := y

theorem weakYukawaTrialitySinglet_eq (y : ℂ) (ρ ρ' : So8RepIndex) :
    weakYukawaTrialitySinglet y ρ = weakYukawaTrialitySinglet y ρ' := rfl

/-- Diagonal packaging of squared **outer-horizon** electroweak witnesses (W and Higgs portals). -/
def weakEWSectorPodiumMassSqMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![M_W_derived ^ 2, 0; 0, m_H_derived ^ 2]

theorem weakEWSectorPodiumMassSqMatrix_spec :
    weakEWSectorPodiumMassSqMatrix 0 0 = M_W_derived ^ 2 ∧
      weakEWSectorPodiumMassSqMatrix 1 1 = m_H_derived ^ 2 ∧
      weakEWSectorPodiumMassSqMatrix 0 1 = 0 ∧
      weakEWSectorPodiumMassSqMatrix 1 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [weakEWSectorPodiumMassSqMatrix]

theorem weakEWSectorPodiumMassSqMatrix_eigs_eq_boson_witnesses_sq :
    weakEWSectorPodiumMassSqMatrix 0 0 = (392 / 5 : ℝ) ^ 2 ∧
      weakEWSectorPodiumMassSqMatrix 1 1 = (588 / 5 : ℝ) ^ 2 := by
  rcases boson_witness_values with ⟨hW, _, hH⟩
  simp [weakEWSectorPodiumMassSqMatrix, hW, hH]

/-! ### PDG comparison (numeric) -/

theorem M_W_gap_to_PDG_lt_two : M_W_gap_to_PDG < 2 := by
  unfold M_W_gap_to_PDG
  rw [boson_witness_M_W]
  unfold M_W_PDG
  simp only [abs_lt]
  constructor <;> norm_num

theorem m_H_gap_to_PDG_lt_nine : m_H_gap_to_PDG < 9 := by
  unfold m_H_gap_to_PDG
  rw [boson_witness_m_H]
  unfold m_H_PDG
  simp only [abs_lt]
  constructor <;> norm_num

end -- noncomputable section

/-! ### Rational numerics (`#eval`) and PDG-gap `example` checks

The electroweak witnesses live in `ℝ` (Cauchy reals), so we mirror the closed rationals from
`boson_witness_M_W` / `boson_witness_m_H` in `ℚ` for fast kernel evaluation. PDG centrals are
stated explicitly here only as comparison literals (they are **not** inputs to the witness ladder).
-/

/-- Rational mirror of `boson_witness_M_W` for `#eval` smoke tests. -/
def ewRationalWitnessMW : ℚ := 392 / 5

/-- Rational mirror of `boson_witness_m_H`. -/
def ewRationalWitnessMH : ℚ := 588 / 5

#eval ewRationalWitnessMW
#eval ewRationalWitnessMH
#eval (80377 : ℚ) / 1000 - ewRationalWitnessMW
#eval (12511 : ℚ) / 100 - ewRationalWitnessMH

/-- PDG $M_W$ gap (central `80.377`) is below `2` GeV in the module's units (`M_W_gap_to_PDG_lt_two`). -/
example : (80377 : ℝ) / 1000 - (392 : ℝ) / 5 < 2 := by norm_num

/-- PDG $m_H$ gap (central `125.11`) is below `9` GeV (`m_H_gap_to_PDG_lt_nine`). -/
example : (12511 : ℝ) / 100 - (588 : ℝ) / 5 < 9 := by norm_num

example : M_W_gap_to_PDG < 2 ∧ m_H_gap_to_PDG < 9 :=
  And.intro M_W_gap_to_PDG_lt_two m_H_gap_to_PDG_lt_nine

end Hqiv.Physics
