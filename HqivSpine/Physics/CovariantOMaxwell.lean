import HqivSpine.Geometry.HQVMMetric
import HqivSpine.Physics.Action
import HqivSpine.Physics.ChartMaxwell
import HqivSpine.Physics.Shell
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.CovariantOMaxwell` — covariant plasma O-Maxwell on the HQVM chart

Mined from legacy `Hqiv.Physics.CovariantSolution` (metric-aware divergence surrogate, Christoffel-form
rank-2 divergence, antisymmetric connection cancellation, flat-jet bridge). The plasma source is the
schematic EM-channel injection from legacy `SchematicPlasmaCurrent`.

Honest scope: **chart-point jet** with frozen `√(-g)`, `g^{-1}`, and supplied first jet of raised
`F^{μν}` — not a full manifold covariant derivative or rapidity-normalized jet bridge.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.CovariantOMaxwell

open BigOperators Finset
open HqivSpine.Geometry.HQVMMetric
open ChartMaxwell

/-- Identity inverse metric on `Fin 4`, used to recover the pre-`-g` operator shape. -/
def identityMetric4 (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0

/-- Metric-raised field-strength component using a pointwise inverse metric slot. -/
noncomputable def raisedFieldStrengthO (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, gInv μ ρ * gInv ν σ * F a ρ σ

/-- Metric-aware divergence surrogate of `F` in the `ν`-direction for component `a`. -/
noncomputable def covariantDivFO (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  (1 / sqrt_neg_g) * ∑ μ : Fin 4, sqrt_neg_g * raisedFieldStrengthO F gInv a μ ν

/-- The `√(-g)` normalization **cancels pointwise**: only `∑_μ F^{a μν}` (raised surrogate) remains. -/
theorem covariantDivFOEqSumRaised (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ)
    (gInv : Fin 4 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0) :
    covariantDivFO F sqrt_neg_g gInv a ν =
      ∑ μ : Fin 4, raisedFieldStrengthO F gInv a μ ν := by
  unfold covariantDivFO
  rw [← mul_sum]
  field_simp [hsqrt]

/-- One leg of a diagonal inverse metric contracts a vector to the diagonal entry times the matching component. -/
theorem sumInverseMetricMulOffdiagZero (gInv : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i j : Fin 4, i ≠ j → gInv i j = 0) (f : Fin 4 → ℝ) (ν : Fin 4) :
    (∑ σ : Fin 4, gInv ν σ * f σ) = gInv ν ν * f ν := by
  fin_cases ν <;> rw [Fin.sum_univ_four] <;> simp [hdiag]

/-- For diagonal `g^{-1}`, the raised surrogate is `g^{μμ} g^{νν} F_{μν}` (no implicit sum on μ,ν). -/
theorem raisedFieldStrengthODiagonal (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i j : Fin 4, i ≠ j → gInv i j = 0) (a : Fin 8) (μ ν : Fin 4) :
    raisedFieldStrengthO F gInv a μ ν = gInv μ μ * gInv ν ν * F a μ ν := by
  dsimp [raisedFieldStrengthO]
  have inner (ρ : Fin 4) :
      (∑ σ : Fin 4, gInv ν σ * F a ρ σ) = gInv ν ν * F a ρ ν :=
    sumInverseMetricMulOffdiagZero gInv hdiag (fun σ => F a ρ σ) ν
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
          rw [sumInverseMetricMulOffdiagZero gInv hdiag (fun ρ => F a ρ ν) μ]
    _ = gInv μ μ * gInv ν ν * F a μ ν := by ring


/-- `raisedFieldStrengthO` on the HQVM inverse metric, in closed form. -/
theorem raisedFieldStrengthOHQVMInverseMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8) (μ ν : Fin 4) :
    raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b μ ν =
      hqvmInverseMetric N aScale Φ μ μ * hqvmInverseMetric N aScale Φ ν ν * F b μ ν :=
  raisedFieldStrengthODiagonal F (hqvmInverseMetric N aScale Φ)
    (hqvmInverseMetricDiag N aScale Φ) b μ ν

/-- Covariant divergence surrogate on HQVM: sum over μ of `g^{μμ} g^{νν} F_{μν}`. -/
theorem covariantDivFOHQVM (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N a Φ : ℝ) (sqrt_neg_g : ℝ)
    (aIdx : Fin 8) (ν : Fin 4) (hsqrt : sqrt_neg_g ≠ 0) :
    covariantDivFO F sqrt_neg_g (hqvmInverseMetric N a Φ) aIdx ν =
      ∑ μ : Fin 4,
        hqvmInverseMetric N a Φ μ μ * hqvmInverseMetric N a Φ ν ν * F aIdx μ ν := by
  rw [covariantDivFOEqSumRaised F sqrt_neg_g (hqvmInverseMetric N a Φ) aIdx ν hsqrt]
  refine sum_congr rfl ?_
  intro μ _
  exact raisedFieldStrengthOHQVMInverseMetric F N a Φ aIdx μ ν

theorem raisedFieldStrengthOIdentityMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (a : Fin 8)
    (μ ν : Fin 4) :
    raisedFieldStrengthO F identityMetric4 a μ ν = F a μ ν := by
  unfold raisedFieldStrengthO identityMetric4
  simp

theorem covariantDivFOIdentityMetric (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (a : Fin 8)
    (ν : Fin 4) :
    covariantDivFO F 1 identityMetric4 a ν = ∑ μ : Fin 4, F a μ ν := by
  unfold covariantDivFO
  simp [raisedFieldStrengthOIdentityMetric]

/-- Residual built from explicit metric data, before specializing to HQVM coefficients. -/
noncomputable def covariantOMaxwellResidualWithMetric
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (sqrt_neg_g : ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (J : Current) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  covariantDivFO F sqrt_neg_g gInv a ν - 4 * Real.pi * J a ν
  - (if a = 0 then alphaEM * Real.log (φ_val + 1) * ChartMaxwell.gradPhiLockin ν else 0)

/-- **Covariant O-Maxwell equation (residual).** Zero when the covariant equation holds:
    `(1/√(-g)) Σ_μ √(-g) F^{a μν}` balances the source and φ-term, using the scalar
    HQVM coefficient package as pointwise metric data. -/
noncomputable def covariantOMaxwellResidual (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (J : Current) (N aScale Φ φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  covariantOMaxwellResidualWithMetric F
    (sqrtNegG N aScale Φ) (hqvmInverseMetric N aScale Φ) J φ_val a ν

/-- **Explicit covariant O-Maxwell residual** (divergence piece unfolded) on HQVM data. -/
theorem covariantOMaxwellResidualHQVMExplicit (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (J : Current) (N aScale Φ φ_val : ℝ) (b : Fin 8) (ν : Fin 4)
    (hsqrt : sqrtNegG N aScale Φ ≠ 0) :
    covariantOMaxwellResidual F J N aScale Φ φ_val b ν =
      (∑ μ : Fin 4,
          hqvmInverseMetric N aScale Φ μ μ * hqvmInverseMetric N aScale Φ ν ν * F b μ ν) -
        4 * Real.pi * J b ν -
        (if b = 0 then alphaEM * Real.log (φ_val + 1) * ChartMaxwell.gradPhiLockin ν else 0) := by
  unfold covariantOMaxwellResidual covariantOMaxwellResidualWithMetric
  rw [covariantDivFOHQVM F N aScale Φ (sqrtNegG N aScale Φ) b ν hsqrt]


/-- **HQVM-raised field strength stays antisymmetric** when the original `F_{μν}` is antisymmetric. -/
theorem raisedFieldStrengthOHQVMAntisymm (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (b : Fin 8)
    (hF : ∀ c μ ν, F c μ ν = -F c ν μ) (μ ν : Fin 4) :
    raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b μ ν =
      -raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b ν μ := by
  rw [raisedFieldStrengthOHQVMInverseMetric, raisedFieldStrengthOHQVMInverseMetric,
    hF b ν μ]
  ring

/-- **Connection term on the free upper index vanishes** for an antisymmetric rank-2 tensor and a
lower-symmetric Christoffel slot. This is the algebraic cancellation behind
`∇_μ F^{μν} = ∂_μ F^{μν} + Γ^μ_{μρ} F^{ρν}` for antisymmetric `F`. -/
theorem freeIndexConnectionTermZeroOfAntisymm
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
noncomputable def covariantDivergenceRank2 (T : Fin 4 → Fin 4 → ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4) : ℝ :=
  ∑ μ : Fin 4, (dT μ μ ν + (∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) + (∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ))

/-- For antisymmetric `T^{μν}`, the free-index connection term in `∇_μ T^{μν}` cancels, leaving the
trace-connection form. -/
theorem covariantDivergenceRank2EqOfAntisymm (T : Fin 4 → Fin 4 → ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ν : Fin 4)
    (hΓ : ∀ μ ρ : Fin 4, Γ ν μ ρ = Γ ν ρ μ)
    (hT : ∀ μ ρ : Fin 4, T μ ρ = -T ρ μ) :
    covariantDivergenceRank2 T dT Γ ν =
      ∑ μ : Fin 4, (dT μ μ ν + ∑ ρ : Fin 4, Γ μ μ ρ * T ρ ν) := by
  unfold covariantDivergenceRank2
  have hzero : (∑ μ : Fin 4, ∑ ρ : Fin 4, Γ ν μ ρ * T μ ρ) = 0 :=
    freeIndexConnectionTermZeroOfAntisymm Γ T ν hΓ hT
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
noncomputable def covariantDivFOHQVMChristoffel (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4) : ℝ :=
  covariantDivergenceRank2
    (fun μ ρ => raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b μ ρ)
    (fun κ μ ρ => dRaised b κ μ ρ)
    (christoffelHQVM N aScale Φ dN da dPhi) ν

/-- On HQVM, antisymmetry of `F` cancels the `Γ^ν_{μρ} F^{μρ}` term in the Christoffel-form
covariant divergence. -/
theorem covariantDivFOHQVMChristoffelEqOfAntisymm (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ) :
    covariantDivFOHQVMChristoffel F dRaised N aScale Φ dN da dPhi b ν =
      ∑ μ : Fin 4, (dRaised b μ μ ν +
        ∑ ρ : Fin 4,
          christoffelHQVM N aScale Φ dN da dPhi μ μ ρ *
            raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b ρ ν) := by
  unfold covariantDivFOHQVMChristoffel
  exact covariantDivergenceRank2EqOfAntisymm
    (fun μ ρ => raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b μ ρ)
    (fun κ μ ρ => dRaised b κ μ ρ)
    (christoffelHQVM N aScale Φ dN da dPhi)
    ν
    (fun μ ρ => christoffelHQVMSymmLower N aScale Φ dN da dPhi ν μ ρ)
    (fun μ ρ => raisedFieldStrengthOHQVMAntisymm F N aScale Φ b hF μ ρ)

/-- If the HQVM metric jets vanish, the Christoffel-form divergence of the raised field reduces to the
plain trace of the supplied `F^{μν}` jet. -/
theorem covariantDivFOHQVMChristoffelZeroOfVanishingMetricJets
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (dRaised : Fin 8 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariantDivFOHQVMChristoffel F dRaised N aScale Φ dN da dPhi b ν =
      ∑ μ : Fin 4, dRaised b μ μ ν := by
  rw [covariantDivFOHQVMChristoffelEqOfAntisymm F dRaised N aScale Φ dN da dPhi b ν hF]
  have hterm :
      ∀ μ : Fin 4,
        dRaised b μ μ ν +
            ∑ ρ : Fin 4,
              christoffelHQVM N aScale Φ dN da dPhi μ μ ρ *
                raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b ρ ν
          = dRaised b μ μ ν := by
    intro μ
    have hconn :
        (∑ ρ : Fin 4,
          christoffelHQVM N aScale Φ dN da dPhi μ μ ρ *
            raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b ρ ν) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro ρ _
      rw [christoffelHQVM_zero_of_vanishing_jets N aScale Φ dN da dPhi μ μ ρ hN ha hΦ]
      simp
    simp [hconn]
  exact Finset.sum_congr rfl (fun μ _ => hterm μ)

/-- In the flat/frozen-jet limit, the Christoffel-form HQVM divergence recovers the earlier frozen
surrogate `covariantDivFO` with `√(-g) = 1`. -/
theorem covariantDivFOHQVMChristoffelFlatJetEqSurrogate
    (F : Fin 8 → Fin 4 → Fin 4 → ℝ)
    (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8) (ν : Fin 4)
    (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    covariantDivFOHQVMChristoffel F
      (fun c κ μ ρ =>
        if c = b then
          frozenFirstIndexJet (fun i j => raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b i j) κ μ ρ
        else 0)
      N aScale Φ dN da dPhi b ν =
      covariantDivFO F 1 (hqvmInverseMetric N aScale Φ) b ν := by
  rw [covariantDivFOHQVMChristoffelZeroOfVanishingMetricJets
    F
    (fun c κ μ ρ =>
      if c = b then
        frozenFirstIndexJet (fun i j => raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b i j) κ μ ρ
      else 0)
    N aScale Φ dN da dPhi b ν hF hN ha hΦ]
  simp
  rw [frozenFirstIndexJet_trace_eq_sum]
  rw [covariantDivFOEqSumRaised F 1 (hqvmInverseMetric N aScale Φ) b ν (by norm_num)]

/-! ## Field strength packaging and flat-chart bridge to `Action` -/

def F_of (A : Potential) : Fin 8 → Fin 4 → Fin 4 → ℝ :=
  fun c μ ρ => fieldStrength A c μ ρ

theorem F_of_antisymm (A : Potential) (c : Fin 8) (μ ρ : Fin 4) :
    F_of A c μ ρ = -F_of A c ρ μ :=
  fieldStrength_antisymm A c μ ρ

theorem covariantDivFOIdentityMetric_eq_divergence (A : Potential) (a : Fin 8) (ν : Fin 4) :
    covariantDivFO (F_of A) 1 identityMetric4 a ν = divergence A a ν := by
  rw [covariantDivFOIdentityMetric]
  unfold divergence F_of
  rfl

theorem covariantOMaxwellResidualWithMetric_eq_EL_flat
    (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4) :
    covariantOMaxwellResidualWithMetric (F_of A) 1 identityMetric4 J 1 a ν = EL J A a ν := by
  unfold covariantOMaxwellResidualWithMetric EL
  rw [covariantDivFOIdentityMetric_eq_divergence]
  split_ifs <;> simp [gradPhiLockin_zero]

/-! ## Schematic plasma current (EM octonion leg) -/

/-- Positive Debye-style radial factor (denominator safe on all `r : ℝ`). -/
noncomputable def plasmaRadialProfile (r : ℝ) : ℝ :=
  Real.exp (-max r 0) / (1 + max r 0)

theorem plasmaRadialProfile_pos (r : ℝ) : 0 < plasmaRadialProfile r := by
  unfold plasmaRadialProfile
  have hden : 0 < 1 + max r 0 := by
    have : 0 ≤ max r 0 := le_max_right _ _
    linarith
  exact div_pos (Real.exp_pos _) hden

/-- Schematic scalar source at proxy radius `r`, linear in overall amplitude `j₀`. -/
noncomputable def schematicPlasmaScalar (j₀ r : ℝ) : ℝ := j₀ * plasmaRadialProfile r

/-- Inject the plasma scalar on octonion channel `0` (EM leg); `coord ν` is the radial proxy. -/
noncomputable def plasmaCurrent (j₀ : ℝ) (coord : Fin 4 → ℝ) : Current :=
  fun a ν => if a = 0 then schematicPlasmaScalar j₀ (coord ν) else 0

theorem plasmaCurrent_em_eq_scalar (j₀ : ℝ) (coord : Fin 4 → ℝ) (ν : Fin 4) :
    plasmaCurrent j₀ coord 0 ν = schematicPlasmaScalar j₀ (coord ν) := by
  simp [plasmaCurrent]

theorem plasmaCurrent_nonem_zero (j₀ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4)
    (ha : a ≠ 0) :
    plasmaCurrent j₀ coord a ν = 0 := by
  simp [plasmaCurrent, ha]

theorem plasmaCurrent_zero_j₀ (coord : Fin 4 → ℝ) :
    plasmaCurrent 0 coord = fun _ _ => 0 := by
  funext a ν
  simp [plasmaCurrent, schematicPlasmaScalar]

theorem covariantOMaxwellResidual_lockin_vacuum (N aScale Φ : ℝ) (_hsqrt : sqrtNegG N aScale Φ ≠ 0)
    (a : Fin 8) (ν : Fin 4) :
    covariantOMaxwellResidual (fun _ _ _ => 0) (fun _ _ => 0) N aScale Φ (phi referenceM : ℝ) a ν = 0 := by
  rw [covariantOMaxwellResidualHQVMExplicit (fun _ _ _ => 0) (fun _ _ => 0) N aScale Φ (phi referenceM : ℝ)
    a ν _hsqrt]
  simp [gradPhiLockin_zero]

/-! ## Closure bundle -/

structure CovariantOMaxwellClosure : Prop where
  sqrt_neg_g_cancels :
    ∀ (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N a Φ : ℝ) (aIdx : Fin 8) (ν : Fin 4)
      (hsqrt : sqrtNegG N a Φ ≠ 0),
      covariantDivFO F (sqrtNegG N a Φ) (hqvmInverseMetric N a Φ) aIdx ν =
        ∑ μ : Fin 4, raisedFieldStrengthO F (hqvmInverseMetric N a Φ) aIdx μ ν
  christoffel_flat_jet_surrogate :
    ∀ (F : Fin 8 → Fin 4 → Fin 4 → ℝ) (N aScale Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (b : Fin 8)
      (ν : Fin 4) (hF : ∀ c μ ρ, F c μ ρ = -F c ρ μ)
      (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0),
      covariantDivFOHQVMChristoffel F
        (fun c κ μ ρ =>
          if c = b then
            frozenFirstIndexJet
              (fun i j => raisedFieldStrengthO F (hqvmInverseMetric N aScale Φ) b i j) κ μ ρ
          else 0)
        N aScale Φ dN da dPhi b ν =
        covariantDivFO F 1 (hqvmInverseMetric N aScale Φ) b ν
  flat_identity_eq_action_divergence :
    ∀ (A : Potential) (a : Fin 8) (ν : Fin 4),
      covariantDivFO (F_of A) 1 identityMetric4 a ν = divergence A a ν
  flat_residual_eq_EL :
    ∀ (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4),
      covariantOMaxwellResidualWithMetric (F_of A) 1 identityMetric4 J 1 a ν = EL J A a ν
  grad_phi_lockin_zero : ∀ ν : Fin 4, gradPhiLockin ν = 0
  plasma_em_channel :
    ∀ (j₀ : ℝ) (coord : Fin 4 → ℝ) (ν : Fin 4),
      plasmaCurrent j₀ coord 0 ν = schematicPlasmaScalar j₀ (coord ν)
  lockin_vacuum_residual :
    ∀ (N aScale Φ : ℝ) (hsqrt : sqrtNegG N aScale Φ ≠ 0) (a : Fin 8) (ν : Fin 4),
      covariantOMaxwellResidual (fun _ _ _ => 0) (fun _ _ => 0) N aScale Φ (phi referenceM : ℝ) a ν = 0

theorem covariantOMaxwellClosure : CovariantOMaxwellClosure where
  sqrt_neg_g_cancels := fun F N a Φ aIdx ν hsqrt =>
    covariantDivFOEqSumRaised F (sqrtNegG N a Φ) (hqvmInverseMetric N a Φ) aIdx ν hsqrt
  christoffel_flat_jet_surrogate := covariantDivFOHQVMChristoffelFlatJetEqSurrogate
  flat_identity_eq_action_divergence := covariantDivFOIdentityMetric_eq_divergence
  flat_residual_eq_EL := covariantOMaxwellResidualWithMetric_eq_EL_flat
  grad_phi_lockin_zero := gradPhiLockin_zero
  plasma_em_channel := plasmaCurrent_em_eq_scalar
  lockin_vacuum_residual := covariantOMaxwellResidual_lockin_vacuum

theorem referenceM_covariant_plasma_omaxwell_closed : Nonempty CovariantOMaxwellClosure :=
  ⟨covariantOMaxwellClosure⟩

end HqivSpine.Physics.CovariantOMaxwell
