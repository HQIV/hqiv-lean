import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Hqiv.Physics.Action
import Hqiv.Physics.HQIVFluidClosureScaffold
import Hqiv.Physics.SchematicPlasmaCurrent

namespace Hqiv

open BigOperators Finset
open Hqiv.Physics

/-!
# Action ↔ schematic plasma current

`Action.lean` couples an arbitrary octonion–spacetime current `J_src` to the gauge potential via
`L_O_source_general J_src` and puts the **same** `J_src` into `EL_O_general J_src` as the `-4π J`
Euler–Lagrange term—matching the slot in `emergentMaxwellInhomogeneous_O_general J_src`.

This file proves that **`J_O_plasma j₀ coord`** is a legitimate instance: the **J·A** interaction is
explicit on the EM channel `a = 0`, **linear in `j₀`**, and specializes to the vacuous current at
`j₀ = 0`.

For the same `J_src` together with a continuum φ field on `Fin 4 → ℝ`, use
`Hqiv.Physics.ContinuumOmaxwellClosure` (`action_O_Maxwell_general_coordsField`, `EL_O_general_coordsField`).
If the φ slot should use a metric-raised gradient `g^{νμ} ∂_μ φ` at the basepoint, use the `*_coordsField_metric`
names there (`action_O_Maxwell_general_coordsField_metric`, `EL_O_general_coordsField_metric`, etc.).

Covariant current divergence `∇_μ J^μ` with a position-dependent metric on the chart is in
`Hqiv.Geometry.ContinuumMetricGradient` (`coordCovariantDivergence`, and `coordCovariantDivergence_constDet`
when `g` is constant).

**Fluid coherence:** `HQIVFluidClosureScaffold.coherenceFromPlasmaAmp` uses the **same**
`schematicPlasmaScalar j₀ r` (via `|·|`) as appears in each leg of `L_O_source_general_J_O_plasma` when
`coord = plasmaProxyCoordUniform r` — see `L_O_source_general_J_O_plasma_plasmaProxyCoordUniform` and
`plasma_action_coherence_same_schematic_core` (bookkeeping only, not a dynamical derivation).
-/

theorem J_O_plasma_add_linear (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    J_O_plasma (j₁ + j₂) coord a ν = J_O_plasma j₁ coord a ν + J_O_plasma j₂ coord a ν := by
  simp only [J_O_plasma, schematicPlasmaScalar_add]
  split_ifs <;> ring

theorem J_O_plasma_add (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) :
    J_O_plasma (j₁ + j₂) coord = fun a ν => J_O_plasma j₁ coord a ν + J_O_plasma j₂ coord a ν := by
  funext a ν
  exact J_O_plasma_add_linear j₁ j₂ coord a ν

/-- Only `a = (0 : Fin 8)` carries the plasma scalar; all other octonion indices contribute zero. -/
theorem sum_J_O_plasma_over_octonion (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (ν : Fin 4) :
    (∑ a : Fin 8, J_O_plasma j₀ coord a ν * A a ν) = schematicPlasmaScalar j₀ (coord ν) * A 0 ν := by
  refine Fintype.sum_eq_single (0 : Fin 8) ?_
  intro a ha
  have hav : a.val ≠ 0 := by
    intro h0
    apply ha
    exact Fin.ext h0
  simp [J_O_plasma, hav]

private theorem fintype_sum_sum_comm_fin8_fin4 (f : Fin 8 → Fin 4 → ℝ) :
    (∑ a : Fin 8, ∑ ν : Fin 4, f a ν) = ∑ ν : Fin 4, ∑ a : Fin 8, f a ν := by
  calc
    (∑ a : Fin 8, ∑ ν : Fin 4, f a ν) = ∑ p : Fin 8 × Fin 4, f p.1 p.2 :=
      (Fintype.sum_prod_type' (fun a ν => f a ν)).symm
    _ = ∑ ν : Fin 4, ∑ a : Fin 8, f a ν := Fintype.sum_prod_type_right' _

/-- **J·A** with the plasma current collapses to the EM (`a = 0`) leg and the Debye-weighted scalar. -/
theorem L_O_source_general_J_O_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ coord) A =
      ∑ ν : Fin 4, schematicPlasmaScalar j₀ (coord ν) * A 0 ν := by
  unfold L_O_source_general
  rw [fintype_sum_sum_comm_fin8_fin4 _]
  refine Finset.sum_congr rfl ?_
  intro ν _
  exact sum_J_O_plasma_over_octonion j₀ coord A ν

/-- **Uniform proxy** `coord ν = r`: every leg carries the **same** `schematicPlasmaScalar j₀ r`
(compare `plasmaProxyCoordUniform` in `SchematicPlasmaCurrent`). -/
theorem L_O_source_general_J_O_plasma_plasmaProxyCoordUniform (j₀ r : ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ (plasmaProxyCoordUniform r)) A =
      ∑ ν : Fin 4, schematicPlasmaScalar j₀ r * A 0 ν := by
  rw [L_O_source_general_J_O_plasma]
  refine Finset.sum_congr rfl ?_
  intro ν _
  simp [plasmaProxyCoordUniform]

/-- Definitional expansion for cross-reference from the action side. -/
theorem coherenceFromPlasmaAmp_eq_min_mul_abs_schematic (κ j₀ r : ℝ) :
    coherenceFromPlasmaAmp κ j₀ r = min 1 (κ * |schematicPlasmaScalar j₀ r|) := rfl

/-- Single statement: gauge coupling `L_O` and fluid coherence both reference `schematicPlasmaScalar j₀ r`
when the chart is `plasmaProxyCoordUniform r`. -/
theorem plasma_action_coherence_same_schematic_core (j₀ r κ : ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ (plasmaProxyCoordUniform r)) A =
        ∑ ν : Fin 4, schematicPlasmaScalar j₀ r * A 0 ν ∧
      coherenceFromPlasmaAmp κ j₀ r = min 1 (κ * |schematicPlasmaScalar j₀ r|) :=
  ⟨L_O_source_general_J_O_plasma_plasmaProxyCoordUniform j₀ r A, coherenceFromPlasmaAmp_eq_min_mul_abs_schematic κ j₀ r⟩

/-!
### Derived factorization (shared Debye screening)

`schematicPlasmaScalar j₀ r = j₀ * plasmaRadialProfile r` and `abs_schematicPlasmaScalar` imply both the
gauge source `L_O` (uniform proxy) and fluid `coherenceFromPlasmaAmp` factor through the **same**
positive factor `plasmaRadialProfile r` (defined using `lambdaDebye` in `SchematicPlasmaCurrent`).
This is a **pure algebra** derivation from definitions—not a variational principle or kinetic theorem.
-/

/-- `L_O` factors as `j₀ * plasmaRadialProfile r` times the sum of the EM gauge components. -/
theorem L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum (j₀ r : ℝ)
    (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ (plasmaProxyCoordUniform r)) A =
      j₀ * plasmaRadialProfile r * ∑ ν : Fin 4, A 0 ν := by
  rw [L_O_source_general_J_O_plasma_plasmaProxyCoordUniform]
  calc
    (∑ ν : Fin 4, schematicPlasmaScalar j₀ r * A 0 ν) =
        ∑ ν : Fin 4, j₀ * plasmaRadialProfile r * A 0 ν := by
          refine Finset.sum_congr rfl ?_
          intro ν _
          simp [schematicPlasmaScalar, mul_assoc]
    _ = j₀ * plasmaRadialProfile r * ∑ ν : Fin 4, A 0 ν := by
          rw [← Finset.mul_sum]

/-- Coherence rewrites with `|j₀| * plasmaRadialProfile r` via `abs_schematicPlasmaScalar`. -/
theorem coherenceFromPlasmaAmp_eq_min_mul_abs_j₀_profile (κ j₀ r : ℝ) :
    coherenceFromPlasmaAmp κ j₀ r = min 1 (κ * |j₀| * plasmaRadialProfile r) := by
  rw [coherenceFromPlasmaAmp, abs_schematicPlasmaScalar]
  ac_rfl

/-- **Derived** packaging: same `plasmaRadialProfile r` in gauge coupling and in coherence (through `|j₀|`). -/
theorem plasma_action_coherence_derived (j₀ r κ : ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ (plasmaProxyCoordUniform r)) A =
        j₀ * plasmaRadialProfile r * ∑ ν : Fin 4, A 0 ν ∧
      coherenceFromPlasmaAmp κ j₀ r = min 1 (κ * |j₀| * plasmaRadialProfile r) :=
  ⟨L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum j₀ r A,
    coherenceFromPlasmaAmp_eq_min_mul_abs_j₀_profile κ j₀ r⟩

/-- Same common factor as `plasma_action_coherence_derived`, spelled with `schematicPlasmaScalar`. -/
theorem plasma_action_coherence_derived_schematic (j₀ r κ : ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ (plasmaProxyCoordUniform r)) A =
        schematicPlasmaScalar j₀ r * ∑ ν : Fin 4, A 0 ν ∧
      coherenceFromPlasmaAmp κ j₀ r = min 1 (κ * |schematicPlasmaScalar j₀ r|) := by
  constructor
  · rw [L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum, schematicPlasmaScalar]
  · exact coherenceFromPlasmaAmp_eq_min_mul_abs_schematic κ j₀ r

/-- Uniform proxy: `L_O` for `j₁ + j₂` splits as two `j * profile * ∑ A` terms. -/
theorem L_O_source_general_J_O_plasma_uniform_add (j₁ j₂ r : ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma (j₁ + j₂) (plasmaProxyCoordUniform r)) A =
      j₁ * plasmaRadialProfile r * ∑ ν : Fin 4, A 0 ν +
        j₂ * plasmaRadialProfile r * ∑ ν : Fin 4, A 0 ν := by
  rw [L_O_source_general_J_O_plasma_uniform_eq_j₀_mul_profile_mul_sum (j₁ + j₂)]
  ring

/-- Shell+Debye eddy viscosity with plasma-amplitude coherence, with `min` unfolded through `|j₀|·profile`. -/
theorem hqivEddyViscosity_HQIV_shell_debye_plasmaAmp_eq_profile (m : ℕ) (dotTheta κ j₀ r : ℝ) :
    hqivEddyViscosity_HQIV_shell_debye_plasmaAmp m dotTheta κ j₀ r =
      gamma_HQIV * T m * |dotTheta| * lambdaDebye ^ 2 * min 1 (κ * |j₀| * plasmaRadialProfile r) := by
  unfold hqivEddyViscosity_HQIV_shell_debye_plasmaAmp hqivEddyViscosity_HQIV_shell_debye
  rw [hqivEddyViscosity_HQIV_eq, coherenceFromPlasmaAmp_eq_min_mul_abs_j₀_profile]

/-- F3 total viscosity with plasma coherence, explicit screening factor `plasmaRadialProfile r`. -/
theorem nuTotal_eq_nuMol_add_shell_debye_plasmaAmp_profile (m : ℕ)
    (nuMol nuEddy nuTotal dotTheta κ j₀ r : ℝ)
    (h :
      PlasmaFluidClosureAssumptions nuMol nuEddy nuTotal gamma_HQIV (T m) dotTheta lambdaDebye
        (coherenceFromPlasmaAmp κ j₀ r)) :
    nuTotal =
      nuMol +
        gamma_HQIV * T m * |dotTheta| * lambdaDebye ^ 2 * min 1 (κ * |j₀| * plasmaRadialProfile r) := by
  rw [nuTotal_eq_nuMol_add_shell_debye_plasmaAmp m nuMol nuEddy nuTotal dotTheta κ j₀ r h,
    hqivEddyViscosity_HQIV_shell_debye_plasmaAmp_eq_profile]

/-- Total O-Maxwell action density with plasma source (same φ channel as the default action). -/
noncomputable abbrev action_O_Maxwell_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) : ℝ :=
  action_O_Maxwell_general (J_O_plasma j₀ coord) A φ_val

/-- **Superposition in amplitude `j₀`:** the J·A part adds when two plasma strengths are summed. -/
theorem L_O_source_general_J_O_plasma_add (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma (j₁ + j₂) coord) A =
      L_O_source_general (J_O_plasma j₁ coord) A + L_O_source_general (J_O_plasma j₂ coord) A := by
  rw [J_O_plasma_add j₁ j₂ coord]
  exact L_O_source_general_add_J _ _ A

/-- Euler–Lagrange with plasma current: same algebraic `-4π J_plasma` term as in `EL_O_general`. -/
theorem EL_O_plasma_eq_emergent_shape (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : φ_val + 1 > 0) :
    EL_O_general (J_O_plasma j₀ coord) A φ_val a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_O_plasma j₀ coord a ν -
        (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) :=
  action_O_Maxwell_EL_eq_emergent_general (J_O_plasma j₀ coord) a ν φ_val hφ A

/-- At `j₀ = 0`, plasma-sourced action and EL coincide with the default `J_O` (all zero). -/
theorem action_O_Maxwell_plasma_j₀_zero (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) :
    action_O_Maxwell_general (J_O_plasma 0 coord) A φ_val = action_O_Maxwell A φ_val := by
  rw [J_O_plasma_zero coord]
  rfl

theorem EL_O_plasma_j₀_zero (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general (J_O_plasma 0 coord) A φ_val a ν = EL_O A φ_val a ν := by
  rw [J_O_plasma_zero coord]
  rfl

/-- **Same `-4π J` slot** as `emergentMaxwellInhomogeneous_O_general` (both definitions use `J_src a ν`). -/
theorem EL_O_general_neg_four_pi_J_eq (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (a : Fin 8) (ν : Fin 4) :
    EL_O_general J_src A φ_val a ν + 4 * Real.pi * J_src a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) -
        (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) := by
  rw [EL_O_general_eq_F_divergence_sub_sources]
  simp [F_divergence_sum]
  split_ifs <;> ring

theorem emergent_neg_four_pi_J_eq (J_src : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_general J_src a ν + 4 * Real.pi * J_src a ν =
      -alpha * algebraicMaxwellCouplingLog ν * grad_φ ν := by
  unfold emergentMaxwellInhomogeneous_O_general
  simp_rw [show (0.0 : ℝ) = (0 : ℝ) by norm_num]
  ring

noncomputable def action_total_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val rho_m rho_r : ℝ) : ℝ :=
  action_total_general (J_O_plasma j₀ coord) A φ_val rho_m rho_r

end Hqiv
