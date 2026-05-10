import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.Action
import Hqiv.Physics.GRFromMaxwell
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Hqiv

open BigOperators Finset

/-!
# Covariant solution: O-Maxwell on the HQVM background

We package a **metric-aware divergence surrogate** for the O-Maxwell equation and
prove that a trivial HQVM-background solution exists.

This file does **not** implement a full manifold covariant derivative. Instead it
uses explicit metric data from `Hqiv.Geometry.HQVMetric` (`sqrt_neg_g_HQVM`,
`HQVM_inverseMetric`) to raise indices and form the algebraic shape that a
covariant divergence would have in a chart with pointwise-frozen metric data.

**Metric-aware formulation:**
- **Index raising surrogate:** use an inverse-metric slot `gInv` to build a raised
  field-strength component from `F`.
- **Weighted divergence surrogate:** use `(1/√(-g)) * Σ_μ √(-g) F^{a μν}` with
  pointwise-frozen `√(-g)` and `gInv`.
- **√(-g)** (volume element): determined by the HQVM metric (lapse N, spatial a, Φ).
- **Covariant solution:** (A, φ, metric data) such that the metric-aware residual
  vanishes and the metric is HQVM (N = 1 + Φ + φ t).

We prove: **flat (Minkowski) limit** is a covariant solution; and the **HQVM
background** (same φ, α) is the metric for which the covariant equation is
consistent with the action-derived dynamics.

**Structural lemmas (this file):**
- `covariant_div_F_O_eq_sum_raised` — the prefactor `√(-g)` **cancels**; the surrogate is
  `∑_μ (g^{-1} ⊗ g^{-1} F)_{μν}`.
- `raisedFieldStrength_O_diagonal` — for any **diagonal** inverse metric (off-diagonal zeros),
  `F^{μν} = g^{μμ} g^{νν} F_{μν}` in the frozen chart sense.
- `covariant_div_F_O_HQVM` / `covariant_O_Maxwell_residual_HQVM_explicit` — specialize to
  `HQVM_inverseMetric`, giving the **explicit HQVM O-Maxwell divergence** before sources.
- `covariant_divergence_rank2` / `covariant_div_F_O_HQVM_Christoffel` — the actual
  **Christoffel-form** chart divergence `∇_μ F^{μν}` with a supplied first jet of `F^{μν}`.
- `covariant_div_F_O_HQVM_Christoffel_eq_of_antisymm` — on HQVM, the free-index connection
  term `Γ^ν_{μρ} F^{μρ}` cancels for antisymmetric `F`, leaving only the trace connection
  piece `Γ^μ_{μρ} F^{ρν}`.
- `covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate` — when metric jets vanish and
  the `F^{μν}` jet is frozen in the first index, the Christoffel-form divergence recovers the
  earlier frozen surrogate (unscaled discrete packaging).
- `covariant_div_F_O_HQVM_Christoffel_rapidity_flat_frozen_jet_eq_scaled_surrogate` — **primary bridge:**
  same frozen raw jet, scaled by `Hqiv.Geometry.rapidityNormalizedJet` (`φ·t·δθ'(m)` from
  `polarAngleFromRapidity`), recovers **`rapidityNormalizedJetCoeff` ×** the metric surrogate.
  Observer-side shell φ-normalization (`rapidityNormalizedShellPhiIncrement` in
  `Hqiv.Physics.HQIVPerturbationScaffold`) is the complementary transport story; tensor jets use
  `rapidityNormalizedJet` from `SpatialSliceRapidityScaffold`.
- `covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate_of_rapidity_unit_coeff` — when
  `rapidityNormalizedJetCoeff = 1`, the rapidity-scaled path agrees with the unscaled frozen-jet
  surrogate.
- `L_O_kinetic_covariant` / `L_O_kinetic_HQVM` — discrete `-(1/4) √(-g) F·F^{up}` with the same `/2`
  convention as `Action.L_O_kinetic`; **`L_O_kinetic_covariant_identityMetric_eq`** recovers flat kinetic.
-/

/-- Identity inverse metric on `Fin 4`, used to recover the pre-`-g` operator shape. -/
def identityMetric4 (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0

/-- Metric-raised field-strength component using a pointwise inverse metric slot. -/
noncomputable def raisedFieldStrength_O (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, gInv μ ρ * gInv ν σ * F a ρ σ

/-- Metric-aware divergence surrogate of `F` in the `ν`-direction for component `a`. -/
noncomputable def covariant_div_F_O (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  (1 / sqrt_neg_g) * ∑ μ : Fin 4, sqrt_neg_g * raisedFieldStrength_O F gInv a μ ν

/-- The `√(-g)` normalization **cancels pointwise**: only `∑_μ F^{a μν}` (raised surrogate) remains. -/
theorem covariant_div_F_O_eq_sum_raised (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0) :
    covariant_div_F_O F sqrt_neg_g gInv a ν =
      ∑ μ : Fin 4, raisedFieldStrength_O F gInv a μ ν := by
  unfold covariant_div_F_O
  rw [← mul_sum]
  field_simp [hsqrt]

/-- One leg of a diagonal inverse metric contracts a vector to the diagonal entry times the matching component. -/
theorem sum_inverseMetric_mul_offdiag_zero (gInv : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i j : Fin 4, i ≠ j → gInv i j = 0) (f : Fin 4 → ℝ) (ν : Fin 4) :
    (∑ σ : Fin 4, gInv ν σ * f σ) = gInv ν ν * f ν := by
  fin_cases ν <;> rw [Fin.sum_univ_four] <;> simp [hdiag]

/-- For diagonal `g^{-1}`, the raised surrogate is `g^{μμ} g^{νν} F_{μν}` (no implicit sum on μ,ν). -/
theorem raisedFieldStrength_O_diagonal (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i j : Fin 4, i ≠ j → gInv i j = 0) (a : Fin 8) (μ ν : Fin 4) :
    raisedFieldStrength_O F gInv a μ ν = gInv μ μ * gInv ν ν * F a μ ν := by
  dsimp [raisedFieldStrength_O]
  have inner (ρ : Fin 4) :
      (∑ σ : Fin 4, gInv ν σ * F a ρ σ) = gInv ν ν * F a ρ ν :=
    sum_inverseMetric_mul_offdiag_zero gInv hdiag (fun σ => F a ρ σ) ν
  calc
    (∑ ρ : Fin 4, ∑ σ : Fin 4, gInv μ ρ * gInv ν σ * F a ρ σ)
        = ∑ ρ : Fin 4, gInv μ ρ * (∑ σ : Fin 4, gInv ν σ * F a ρ σ) := by
            refine sum_congr rfl ?_
            intro ρ _
            calc
              (∑ σ : Fin 4, gInv μ ρ * gInv ν σ * F a ρ σ)
                  = ∑ σ : Fin 4, gInv μ ρ * (gInv ν σ * F a ρ σ) := by simp_rw [← mul_assoc]
              _ = gInv μ ρ * ∑ σ : Fin 4, gInv ν σ * F a ρ σ := by rw [← mul_sum]
    _ = ∑ ρ : Fin 4, gInv μ ρ * (gInv ν ν * F a ρ ν) := by
          refine sum_congr rfl fun ρ _ => by rw [inner ρ]
    _ = ∑ ρ : Fin 4, gInv ν ν * (gInv μ ρ * F a ρ ν) := by
          refine sum_congr rfl fun ρ _ => by ring
    _ = gInv ν ν * ∑ ρ : Fin 4, gInv μ ρ * F a ρ ν := by rw [← mul_sum]
    _ = gInv ν ν * (gInv μ μ * F a μ ν) := by
          rw [sum_inverseMetric_mul_offdiag_zero gInv hdiag (fun ρ => F a ρ ν) μ]
    _ = gInv μ μ * gInv ν ν * F a μ ν := by ring

theorem HQVM_inverseMetric_diag (N a Φ : ℝ) :
    ∀ i j : Fin 4, i ≠ j → HQVM_inverseMetric N a Φ i j = 0 :=
  fun _ _ hij => HQVM_inverseMetric_off_diag N a Φ hij

/-- `raisedFieldStrength_O` on the HQVM inverse metric, in closed form. -/
theorem raisedFieldStrength_O_HQVM_inverseMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8) (μ ν : Fin 4) :
    raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b μ ν =
      HQVM_inverseMetric N aScale Φ μ μ * HQVM_inverseMetric N aScale Φ ν ν * F b μ ν :=
  raisedFieldStrength_O_diagonal F (HQVM_inverseMetric N aScale Φ)
    (HQVM_inverseMetric_diag N aScale Φ) b μ ν

/-- Covariant divergence surrogate on HQVM: sum over μ of `g^{μμ} g^{νν} F_{μν}`. -/
theorem covariant_div_F_O_HQVM (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N a Φ : ℝ) (sqrt_neg_g : ℝ)
    (aIdx : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0) :
    covariant_div_F_O F sqrt_neg_g (HQVM_inverseMetric N a Φ) aIdx ν =
      ∑ μ : Fin 4,
        HQVM_inverseMetric N a Φ μ μ * HQVM_inverseMetric N a Φ ν ν * F aIdx μ ν := by
  rw [covariant_div_F_O_eq_sum_raised F sqrt_neg_g (HQVM_inverseMetric N a Φ) aIdx ν hsqrt]
  refine sum_congr rfl ?_
  intro μ _
  exact raisedFieldStrength_O_HQVM_inverseMetric F N a Φ aIdx μ ν

theorem raisedFieldStrength_O_identityMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (a : Fin 8)
    (μ ν : Fin 4) :
    raisedFieldStrength_O F identityMetric4 a μ ν = F a μ ν := by
  unfold raisedFieldStrength_O identityMetric4
  simp

theorem covariant_div_F_O_identityMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) :
    covariant_div_F_O F 1 identityMetric4 a ν = ∑ μ : Fin 4, F a μ ν := by
  unfold covariant_div_F_O
  simp [raisedFieldStrength_O_identityMetric]

/-- Residual built from explicit metric data, before specializing to HQVM coefficients. -/
noncomputable def covariant_O_Maxwell_residual_withMetric
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  covariant_div_F_O F sqrt_neg_g gInv a ν - 4 * Real.pi * J_O a ν
  - (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0)

/-- **Covariant O-Maxwell equation (residual).** Zero when the covariant equation holds:
    `(1/√(-g)) Σ_μ √(-g) F^{a μν}` balances the source and φ-term, using the scalar
    HQVM coefficient package as pointwise metric data. -/
noncomputable def covariant_O_Maxwell_residual (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  covariant_O_Maxwell_residual_withMetric F
    (sqrt_neg_g_HQVM N aScale Φ) (HQVM_inverseMetric N aScale Φ) φ_val a ν

/-- **Explicit covariant O-Maxwell residual** (divergence piece unfolded) on HQVM data. -/
theorem covariant_O_Maxwell_residual_HQVM_explicit (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ φ_val : ℝ) (b : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g_HQVM N aScale Φ ≠ 0) :
    covariant_O_Maxwell_residual F N aScale Φ φ_val b ν =
      (∑ μ : Fin 4,
          HQVM_inverseMetric N aScale Φ μ μ * HQVM_inverseMetric N aScale Φ ν ν * F b μ ν) -
        4 * Real.pi * J_O b ν -
        (if b = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) := by
  unfold covariant_O_Maxwell_residual covariant_O_Maxwell_residual_withMetric
  rw [covariant_div_F_O_HQVM F N aScale Φ (sqrt_neg_g_HQVM N aScale Φ) b ν hsqrt]

/-- **HQVM metric partials are symmetric in the metric slots** `μ, ν` (because the metric is diagonal). -/
theorem HQVM_metric_partials_symm (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ μ ν : Fin 4) :
    HQVM_metric_partials N a Φ dN da dPhi κ μ ν =
      HQVM_metric_partials N a Φ dN da dPhi κ ν μ := by
  by_cases h : μ = ν
  · subst h
    rfl
  · rw [HQVM_metric_partials_off_diag N a Φ dN da dPhi κ μ ν h]
    rw [HQVM_metric_partials_off_diag N a Φ dN da dPhi κ ν μ (Ne.symm h)]

/-- **Levi-Civita Christoffels are symmetric in the lower slots** when the metric partials are symmetric. -/
theorem Christoffel_levi_civita_symm_lower (gInv : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ κ μ ν : Fin 4, dg κ μ ν = dg κ ν μ) (ρ μ ν : Fin 4) :
    Christoffel_levi_civita gInv dg ρ μ ν = Christoffel_levi_civita gInv dg ρ ν μ := by
  unfold Christoffel_levi_civita
  refine congrArg ((1 / 2) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [hsym σ μ ν]
  ring

/-- **HQVM Christoffels are symmetric in the lower slots** `Γ^ρ_{μν} = Γ^ρ_{νμ}`. -/
theorem Christoffel_HQVM_symm_lower (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    Christoffel_HQVM N a Φ dN da dPhi ρ μ ν =
      Christoffel_HQVM N a Φ dN da dPhi ρ ν μ := by
  exact Christoffel_levi_civita_symm_lower
    (HQVM_inverseMetric N a Φ) (HQVM_metric_partials N a Φ dN da dPhi)
    (HQVM_metric_partials_symm N a Φ dN da dPhi) ρ μ ν

/-- **HQVM-raised field strength stays antisymmetric** when the original `F_{μν}` is antisymmetric. -/
theorem raisedFieldStrength_O_HQVM_antisymm (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8)
    (hF : ∀ c μ ν, F c μ ν = -F c ν μ) (μ ν : Fin 4) :
    raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b μ ν =
      -raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b ν μ := by
  rw [raisedFieldStrength_O_HQVM_inverseMetric, raisedFieldStrength_O_HQVM_inverseMetric,
    hF b ν μ]
  ring

/-- **Connection term on the free upper index vanishes** for an antisymmetric rank-2 tensor and a
lower-symmetric Christoffel slot. This is the algebraic cancellation behind
`∇_μ F^{μν} = ∂_μ F^{μν} + Γ^μ_{μρ} F^{ρν}` for antisymmetric `F`. -/
theorem free_index_connection_term_zero_of_antisymm
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (T : Fin 4 → Fin 4 → ℝ) (ν : Fin 4)
    (hΓ : ∀ μ ρ : Fin 4, Γ ν μ ρ = Γ ν ρ μ)
    (hT : ∀ μ ρ : Fin 4, T μ ρ = -T ρ μ) :
    (∑ μ : Fin 4, ∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ) = 0 := by
  have hdiag : ∀ μ : Fin 4, T μ μ = 0 := by
    intro μ
    linarith [hT μ μ]
  have h01 : T 0 1 = -T 1 0 := hT 0 1
  have h02 : T 0 2 = -T 2 0 := hT 0 2
  have h03 : T 0 3 = -T 3 0 := hT 0 3
  have h12 : T 1 2 = -T 2 1 := hT 1 2
  have h13 : T 1 3 = -T 3 1 := hT 1 3
  have h23 : T 2 3 = -T 3 2 := hT 2 3
  fin_cases ν
  · have g01 : Γ 0 0 1 = Γ 0 1 0 := hΓ 0 1
    have g02 : Γ 0 0 2 = Γ 0 2 0 := hΓ 0 2
    have g03 : Γ 0 0 3 = Γ 0 3 0 := hΓ 0 3
    have g12 : Γ 0 1 2 = Γ 0 2 1 := hΓ 1 2
    have g13 : Γ 0 1 3 = Γ 0 3 1 := hΓ 1 3
    have g23 : Γ 0 2 3 = Γ 0 3 2 := hΓ 2 3
    simp [Fin.sum_univ_four, hdiag, h01, h02, h03, h12, h13, h23, g01, g02, g03, g12, g13, g23]
    ring
  · have g01 : Γ 1 0 1 = Γ 1 1 0 := hΓ 0 1
    have g02 : Γ 1 0 2 = Γ 1 2 0 := hΓ 0 2
    have g03 : Γ 1 0 3 = Γ 1 3 0 := hΓ 0 3
    have g12 : Γ 1 1 2 = Γ 1 2 1 := hΓ 1 2
    have g13 : Γ 1 1 3 = Γ 1 3 1 := hΓ 1 3
    have g23 : Γ 1 2 3 = Γ 1 3 2 := hΓ 2 3
    simp [Fin.sum_univ_four, hdiag, h01, h02, h03, h12, h13, h23, g01, g02, g03, g12, g13, g23]
    ring
  · have g01 : Γ 2 0 1 = Γ 2 1 0 := hΓ 0 1
    have g02 : Γ 2 0 2 = Γ 2 2 0 := hΓ 0 2
    have g03 : Γ 2 0 3 = Γ 2 3 0 := hΓ 0 3
    have g12 : Γ 2 1 2 = Γ 2 2 1 := hΓ 1 2
    have g13 : Γ 2 1 3 = Γ 2 3 1 := hΓ 1 3
    have g23 : Γ 2 2 3 = Γ 2 3 2 := hΓ 2 3
    simp [Fin.sum_univ_four, hdiag, h01, h02, h03, h12, h13, h23, g01, g02, g03, g12, g13, g23]
    ring
  · have g01 : Γ 3 0 1 = Γ 3 1 0 := hΓ 0 1
    have g02 : Γ 3 0 2 = Γ 3 2 0 := hΓ 0 2
    have g03 : Γ 3 0 3 = Γ 3 3 0 := hΓ 0 3
    have g12 : Γ 3 1 2 = Γ 3 2 1 := hΓ 1 2
    have g13 : Γ 3 1 3 = Γ 3 3 1 := hΓ 1 3
    have g23 : Γ 3 2 3 = Γ 3 3 2 := hΓ 2 3
    simp [Fin.sum_univ_four, hdiag, h01, h02, h03, h12, h13, h23, g01, g02, g03, g12, g13, g23]
    ring

/-- **Coordinate covariant divergence** of a rank-2 contravariant tensor `T^{μν}` with supplied first
jet `dT κ μ ν = ∂_κ T^{μν}` and Christoffels `Γ^ρ_{μν}`. -/
noncomputable def covariant_divergence_rank2 (T : Fin 4 → Fin 4 → ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : ℝ :=
  ∑ μ : Fin 4, (dT μ μ ν + (∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) + (∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ))

/-- For antisymmetric `T^{μν}`, the free-index connection term in `∇_μ T^{μν}` cancels, leaving the
trace-connection form. -/
theorem covariant_divergence_rank2_eq_of_antisymm (T : Fin 4 → Fin 4 → ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4)
    (hΓ : ∀ μ ρ : Fin 4, Γ ν μ ρ = Γ ν ρ μ)
    (hT : ∀ μ ρ : Fin 4, T μ ρ = -T ρ μ) :
    covariant_divergence_rank2 T dT Γ ν =
      ∑ μ : Fin 4, (dT μ μ ν + ∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) := by
  unfold covariant_divergence_rank2
  have hzero : (∑ μ : Fin 4, ∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ) = 0 :=
    free_index_connection_term_zero_of_antisymm Γ T ν hΓ hT
  calc
    ∑ μ : Fin 4, (dT μ μ ν + (∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) + (∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ))
        = (∑ μ : Fin 4, (dT μ μ ν + ∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν))
          + (∑ μ : Fin 4, ∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ μ : Fin 4, (dT μ μ ν + ∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) := by
          simp [hzero]

/-- **Frozen first-index jet** for a rank-2 tensor: package `T^{μν}` as `∂_κ T^{μν}` supported only on
`κ = μ`. This matches the older chart-cell surrogate when the connection vanishes. -/
noncomputable def frozenFirstIndexJet (T : Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun κ μ ν => if κ = μ then T μ ν else 0

/-- The diagonal trace of `frozenFirstIndexJet` recovers `∑_μ T^{μν}`. -/
theorem frozenFirstIndexJet_trace_eq_sum (T : Fin 4 → Fin 4 → ℝ) (ν : Fin 4) :
    (∑ μ : Fin 4, frozenFirstIndexJet T μ μ ν) = ∑ μ : Fin 4, T μ ν := by
  refine Finset.sum_congr rfl ?_
  intro μ _
  simp [frozenFirstIndexJet]

/-- **Christoffel-form HQVM divergence** of the raised O-field, with a supplied first jet of
`F^{μν}`. -/
noncomputable def covariant_div_F_O_HQVM_Christoffel (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4) : ℝ :=
  covariant_divergence_rank2
    (fun μ ρ => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b μ ρ)
    (fun κ μ ρ => dRaised b κ μ ρ)
    (Christoffel_HQVM N aScale Φ dN da dPhi) ν

/-- On HQVM, antisymmetry of `F` cancels the `Γ^ν_{μρ} F^{μρ}` term in the Christoffel-form
covariant divergence. -/
theorem covariant_div_F_O_HQVM_Christoffel_eq_of_antisymm (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ) :
    covariant_div_F_O_HQVM_Christoffel F dRaised N aScale Φ dN da dPhi b ν =
      ∑ μ : Fin 4, (dRaised b μ μ ν +
        ∑ ρ : Fin 4,
          Christoffel_HQVM N aScale Φ dN da dPhi μ μ ρ *
            raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b ρ ν) := by
  unfold covariant_div_F_O_HQVM_Christoffel
  exact covariant_divergence_rank2_eq_of_antisymm
    (fun μ ρ => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b μ ρ)
    (fun κ μ ρ => dRaised b κ μ ρ)
    (Christoffel_HQVM N aScale Φ dN da dPhi)
    ν
    (fun μ ρ => Christoffel_HQVM_symm_lower N aScale Φ dN da dPhi ν μ ρ)
    (fun μ ρ => raisedFieldStrength_O_HQVM_antisymm F N aScale Φ b hF μ ρ)

/-- If the HQVM metric jets vanish, the Christoffel-form divergence of the raised field reduces to the
plain trace of the supplied `F^{μν}` jet. -/
theorem covariant_div_F_O_HQVM_Christoffel_zero_of_vanishing_metric_jets
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F dRaised N aScale Φ dN da dPhi b ν =
      ∑ μ : Fin 4, dRaised b μ μ ν := by
  rw [covariant_div_F_O_HQVM_Christoffel_eq_of_antisymm F dRaised N aScale Φ dN da dPhi b ν hF]
  have hterm :
      ∀ μ : Fin 4,
        dRaised b μ μ ν +
            ∑ ρ : Fin 4,
              Christoffel_HQVM N aScale Φ dN da dPhi μ μ ρ *
                raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b ρ ν
          = dRaised b μ μ ν := by
    intro μ
    have hconn :
        (∑ ρ : Fin 4,
          Christoffel_HQVM N aScale Φ dN da dPhi μ μ ρ *
            raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b ρ ν) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro ρ _
      rw [Christoffel_HQVM_zero_of_vanishing_jets N aScale Φ dN da dPhi μ μ ρ hN ha hΦ]
      simp
    simp [hconn]
  exact Finset.sum_congr rfl (fun μ _ => hterm μ)

/-- In the flat/frozen-jet limit, the Christoffel-form HQVM divergence recovers the earlier frozen
surrogate `covariant_div_F_O` with `√(-g) = 1`. -/
theorem covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F
      (fun c κ μ ρ =>
        if c = b then
          frozenFirstIndexJet (fun i j => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b i j) κ μ ρ
        else 0)
      N aScale Φ dN da dPhi b ν =
      covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
  rw [covariant_div_F_O_HQVM_Christoffel_zero_of_vanishing_metric_jets
    F
    (fun c κ μ ρ =>
      if c = b then
        frozenFirstIndexJet (fun i j => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b i j) κ μ ρ
      else 0)
    N aScale Φ dN da dPhi b ν hF hN ha hΦ]
  simp
  rw [frozenFirstIndexJet_trace_eq_sum]
  rw [covariant_div_F_O_eq_sum_raised F 1 (HQVM_inverseMetric N aScale Φ) b ν (by norm_num)]

/-- Frozen-index raw jet for octonion channel `b` on the HQVM-raised field (discrete packaging of
`∂_κ F^{μν}` before rapidity normalization). -/
noncomputable def frozenFirstIndexJet_raisedChannel (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8) : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun a κ μ ρ =>
    if a = b then
      frozenFirstIndexJet (fun i j => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b i j) κ μ ρ
    else 0

/-- **Rapidity-normalized** frozen jet: `Hqiv.Geometry.rapidityNormalizedJet` scales the raw discrete
packaging by `polarAngleFromRapidity φ t m` (same shell phase as `SpatialSliceRapidityScaffold`). -/
noncomputable def rapidityNormalized_frozenFirstIndexJet_raisedChannel (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8) (φ t : ℝ) (m : ℕ) : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Hqiv.Geometry.rapidityNormalizedJet φ t m (frozenFirstIndexJet_raisedChannel F N aScale Φ b)

/-- When HQVM metric jets vanish, Christoffel divergence with rapidity-normalized frozen jet equals
**coefficient ×** the `√(-g)`-cancelled surrogate (main continuum-on-discrete bridge for this file). -/
theorem covariant_div_F_O_HQVM_Christoffel_rapidity_flat_frozen_jet_eq_scaled_surrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (φ t : ℝ) (m : ℕ)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariant_div_F_O_HQVM_Christoffel F
      (rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b φ t m)
      N aScale Φ dN da dPhi b ν =
      Hqiv.Geometry.rapidityNormalizedJetCoeff φ t m *
        covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
  let coeff := Hqiv.Geometry.rapidityNormalizedJetCoeff φ t m
  let dFrozen := frozenFirstIndexJet_raisedChannel F N aScale Φ b
  have hmul (μ : Fin 4) :
      Hqiv.Geometry.rapidityNormalizedJet φ t m dFrozen b μ μ ν = coeff * dFrozen b μ μ ν := by
    simp [Hqiv.Geometry.rapidityNormalizedJet, coeff, dFrozen]
  rw [show rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b φ t m =
      Hqiv.Geometry.rapidityNormalizedJet φ t m dFrozen from rfl]
  rw [covariant_div_F_O_HQVM_Christoffel_zero_of_vanishing_metric_jets F
    (Hqiv.Geometry.rapidityNormalizedJet φ t m dFrozen) N aScale Φ dN da dPhi b ν hF hN ha hΦ]
  rw [Finset.sum_congr rfl (fun μ _ => hmul μ)]
  rw [← Finset.mul_sum]
  have hsumfrozen :
      (∑ μ : Fin 4, dFrozen b μ μ ν) = covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
    have hjet := covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate F N aScale Φ dN da dPhi b ν hF hN ha hΦ
    have hzero := covariant_div_F_O_HQVM_Christoffel_zero_of_vanishing_metric_jets F dFrozen N aScale Φ
      dN da dPhi b ν hF hN ha hΦ
    have hdJet :
        dFrozen =
          (fun c κ μ ρ =>
            if c = b then
              frozenFirstIndexJet (fun i j => raisedFieldStrength_O F (HQVM_inverseMetric N aScale Φ) b i j) κ μ ρ
            else 0) := by
      funext c κ μ ρ
      simp [dFrozen, frozenFirstIndexJet_raisedChannel]
    have hchrist :
        covariant_div_F_O_HQVM_Christoffel F dFrozen N aScale Φ dN da dPhi b ν =
          covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν :=
      (congrArg (fun dRaised => covariant_div_F_O_HQVM_Christoffel F dRaised N aScale Φ dN da dPhi b ν) hdJet).trans
        hjet
    rw [hchrist] at hzero
    exact hzero.symm
  rw [hsumfrozen]

/-- When `rapidityNormalizedJetCoeff = 1`, rapidity scaling is invisible and the result matches
`covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate`. -/
theorem covariant_div_F_O_HQVM_Christoffel_flat_jet_eq_surrogate_of_rapidity_unit_coeff
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (φ t : ℝ) (m : ℕ)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0)
    (hc : Hqiv.Geometry.rapidityNormalizedJetCoeff φ t m = 1) :
    covariant_div_F_O_HQVM_Christoffel F
      (rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b φ t m)
      N aScale Φ dN da dPhi b ν =
      covariant_div_F_O F 1 (HQVM_inverseMetric N aScale Φ) b ν := by
  rw [covariant_div_F_O_HQVM_Christoffel_rapidity_flat_frozen_jet_eq_scaled_surrogate F N aScale Φ
    dN da dPhi b ν φ t m hF hN ha hΦ, hc, one_mul]

/-- Bridge packaging: chart-level `dChart` is `Hqiv.Geometry.rapidityNormalizedJet` applied to the
raw frozen raised-channel jet (`SpatialSliceRapidityScaffold.RapidityNormalizedCovariantJetBridge`). -/
noncomputable def rapidityNormalized_frozen_raised_bridge (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8) (φ t : ℝ) (m : ℕ) :
    Hqiv.Geometry.RapidityNormalizedCovariantJetBridge where
  φ := φ
  t := t
  m := m
  dRaw := frozenFirstIndexJet_raisedChannel F N aScale Φ b
  dChart := rapidityNormalized_frozenFirstIndexJet_raisedChannel F N aScale Φ b φ t m
  eq := rfl

/-- **Covariant solution (data):** potential A, φ value, and metric (N, a, Φ). -/
structure CovariantSolutionData where
  A : Fin 8 → Fin 4 → ℝ
  φ_val : ℝ
  N : ℝ
  a : ℝ
  Φ : ℝ

/-- **Field strength from solution data** (F = dA in the discrete sense). -/
def F_of_solution (d : CovariantSolutionData) : Fin 8 → Fin 4 → Fin 4 → ℝ :=
  fun a μ ν => F_from_A d.A a μ ν

/-- **Covariant solution:** the covariant O-Maxwell residual is zero for all a, ν,
    and the metric is HQVM (N = 1 + Φ + φ t for some t). -/
def IsCovariantSolution (d : CovariantSolutionData) (t : ℝ) : Prop :=
  (∀ a ν, covariant_O_Maxwell_residual (F_of_solution d) d.N d.a d.Φ d.φ_val a ν = 0)
  ∧ d.N = HQVM_lapse d.Φ d.φ_val t

/-- **Trivial (vacuum) covariant solution:** A = 0, J = 0, grad phi = 0, flat metric N = 1.
    The covariant equation holds because all terms vanish. -/
def trivial_covariant_solution_data : CovariantSolutionData where
  A := A_O
  φ_val := 1
  N := 1
  a := 1
  Φ := 0

/-- **Trivial data gives F = 0** (since A = 0). -/
theorem F_of_trivial_solution (a : Fin 8) (μ ν : Fin 4) :
    F_of_solution trivial_covariant_solution_data a μ ν = 0 := by
  unfold F_of_solution F_from_A trivial_covariant_solution_data A_O
  simp only [sub_self]

/-- **Trivial covariant solution:** A = 0, J = 0, grad φ = 0, N = 1 (flat). At t = 0, N = HQVM_lapse 0 1 0 = 1. -/
theorem trivial_is_covariant_solution :
    IsCovariantSolution trivial_covariant_solution_data 0 := by
  unfold IsCovariantSolution covariant_O_Maxwell_residual covariant_O_Maxwell_residual_withMetric
    covariant_div_F_O raisedFieldStrength_O F_of_solution
  unfold trivial_covariant_solution_data F_from_A A_O J_O
  simp only [sub_self, HQVM_lapse, grad_phi]
  constructor
  · intro a ν
    simp [HQVM_inverseMetric, sqrt_neg_g_HQVM]
  · norm_num

/-- **Metric-data residual ⟺ flat identity-metric residual.** -/
theorem covariant_withMetric_eq_iff_emergent_flat
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) :
    covariant_O_Maxwell_residual_withMetric F 1 identityMetric4 φ_val a ν = 0 ↔
    (∑ μ : Fin 4, F a μ ν) - 4 * Real.pi * J_O a ν -
      (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) = 0 := by
  unfold covariant_O_Maxwell_residual_withMetric
  rw [covariant_div_F_O_identityMetric]

/-- **HQVM lapse is the covariant background** (same φ as in the covariant O-Maxwell equation). -/
theorem HQVM_lapse_covariant_background (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t :=
  HQVM_lapse_eq_timeAngle Φ φ t

/-- **Existence of a covariant solution.** -/
theorem exists_covariant_solution :
    Exists (fun (d : CovariantSolutionData) => Exists (fun (t : ℝ) => IsCovariantSolution d t)) :=
  Exists.intro trivial_covariant_solution_data (Exists.intro 0 trivial_is_covariant_solution)

/-!
### Covariant Maxwell kinetic (one chart cell)

Discrete analogue of `-(1/4) √(-g) F_{μν} F^{μν}`: same double-sum `/2` convention as
`Hqiv.Physics.Action.L_O_kinetic`.
-/

/-- **Covariant kinetic** for one formal cell: `-(1/4) √(-g) ∑_{a,μ,ν} F_{μν} F^{μν} / 2`. -/
noncomputable def L_O_kinetic_covariant (A : Fin 8 → Fin 4 → ℝ) (sqrt_neg_g : ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) : ℝ :=
  -(1 / 4) * sqrt_neg_g *
    ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4,
      F_from_A A a μ ν *
        raisedFieldStrength_O (fun b ρ σ => F_from_A A b ρ σ) gInv a μ ν / 2

/-- **`√(-g) = 1` and Euclidean inverse `δ^{μν}`:** same kinetic as `L_O_kinetic`. -/
theorem L_O_kinetic_covariant_identityMetric_eq (A : Fin 8 → Fin 4 → ℝ) :
    L_O_kinetic_covariant A 1 identityMetric4 = L_O_kinetic A := by
  unfold L_O_kinetic_covariant L_O_kinetic
  simp_rw [mul_one, raisedFieldStrength_O_identityMetric, ← pow_two]

/-- **HQVM scalar coefficients** for the covariant kinetic. -/
noncomputable def L_O_kinetic_HQVM (A : Fin 8 → Fin 4 → ℝ) (N aScale Φ : ℝ) : ℝ :=
  L_O_kinetic_covariant A (sqrt_neg_g_HQVM N aScale Φ) (HQVM_inverseMetric N aScale Φ)

end Hqiv
