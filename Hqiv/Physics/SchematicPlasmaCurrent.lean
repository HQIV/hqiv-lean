import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Field.Basic
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.HQVMetricAnalytic
import Hqiv.Physics.ModifiedMaxwell

namespace Hqiv

/-!
# Schematic plasma source for the emergent O-Maxwell slot

We **do not** model a full vector current or a real `∇·J` here: `ModifiedMaxwell.div_μ` is still the
placeholder that returns `0`, so `charge_conservation_O_general` is vacuous for every source.

What this file adds is an **honest** bridge:

* a positive, continuous radial profile `plasmaRadialProfile` (Debye-style, safe for all `r : ℝ`);
* a scalar amplitude `schematicPlasmaScalar j₀ r = j₀ * plasmaRadialProfile r`, linear in `j₀`;
* a finitary current `J_O_plasma j₀ coord` that injects that scalar along one octonion component,
  using `coord : Fin 4 → ℝ` as a *proxy* for “distance along the chosen direction” (not a full
  radial coordinate on a manifold).

**Modified inertia:** there is no unified `inertiaModifiedCurrents` type yet. Joint “plasma × lapse”
bookkeeping is phenomenological: multiply amplitudes with `HQVM_lapse` (see `Schrodinger.lapseFactor`
and `HQVMPerturbations`) when comparing to non-relativistic limits—**not** proved from a single
action term in Lean.

**Linearised scalar bookkeeping:** `linearisedScalarPerturbation` is the same product with
`φ = phi_of_T Θ` (temperature ladder). It is **not** identified with the lapse-weighted O-Maxwell
RHS without extra dynamics, but the **same** plasma current `J_O_plasma` now couples to `A` in
`L_O_source_general` and appears as `-4π J` in `EL_O_general` — see `ActionPlasmaBridge`.

What we *can* prove here is (i) vanishing at `j₀ = 0`, (ii) repackaging as
`HQVM_lapse_phiT * plasma`, and (iii) under `grad_φ = 0`, the skeleton source for uniform proxy
`coord ν = t` is `-4π * schematicPlasmaScalar j₀ t` (`emergentMaxwell_plasma_uniform_t_flat_phi`).
-/

noncomputable section

/-- Positive screening length (dimensionless placeholder; fix to physical units downstream). -/
noncomputable def lambdaDebye : ℝ := 1

theorem lambdaDebye_pos : 0 < lambdaDebye := by
  unfold lambdaDebye
  norm_num

/-- Debye-style radial factor `exp(-r/λD)/(1 + max r 0 / λD)` is **positive** on `ℝ` and avoids a
    pole at negative `r` (denominator ≥ 1). -/
noncomputable def plasmaRadialProfile (r : ℝ) : ℝ :=
  Real.exp (-r / lambdaDebye) / (1 + max r 0 / lambdaDebye)

/-- For nonnegative proxy radius, the Debye profile is at most `1` (`exp ≤ 1` and denominator `≥ 1`). -/
theorem plasmaRadialProfile_le_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : plasmaRadialProfile r ≤ 1 := by
  unfold plasmaRadialProfile
  have hmax : max r 0 = r := max_eq_left hr
  have hden : 0 < 1 + max r 0 / lambdaDebye := by
    rw [hmax]
    have hterm : 0 ≤ r / lambdaDebye := div_nonneg hr (le_of_lt lambdaDebye_pos)
    linarith
  have hexp_le_one : Real.exp (-r / lambdaDebye) ≤ 1 := by
    have h0 : 0 ≤ r / lambdaDebye := div_nonneg hr (le_of_lt lambdaDebye_pos)
    have hneg : -r / lambdaDebye ≤ 0 := by
      rw [neg_div]
      exact neg_nonpos.mpr h0
    exact (Real.exp_le_one_iff).mpr hneg
  have hone_le_den : 1 ≤ 1 + max r 0 / lambdaDebye := by
    have hterm : 0 ≤ max r 0 / lambdaDebye := div_nonneg (le_max_right r 0) (le_of_lt lambdaDebye_pos)
    linarith
  have hexp_le_den : Real.exp (-r / lambdaDebye) ≤ 1 + max r 0 / lambdaDebye :=
    hexp_le_one.trans hone_le_den
  rw [div_le_one hden]
  exact hexp_le_den

theorem plasmaRadialProfile_pos (r : ℝ) : 0 < plasmaRadialProfile r := by
  have hden : 0 < 1 + max r 0 / lambdaDebye := by
    have hLam : 0 < lambdaDebye := lambdaDebye_pos
    have hmax : 0 ≤ max r 0 := le_max_right _ _
    have hterm : 0 ≤ max r 0 / lambdaDebye := div_nonneg hmax hLam.le
    have hone : (1 : ℝ) ≤ 1 + max r 0 / lambdaDebye := by linarith
    exact lt_of_lt_of_le zero_lt_one hone
  have hexp : 0 < Real.exp (-r / lambdaDebye) := Real.exp_pos _
  exact div_pos hexp hden

theorem plasmaDebye_denominator_ne_zero (x : ℝ) : 1 + max x 0 / lambdaDebye ≠ 0 := by
  have hLamPos : 0 < lambdaDebye := lambdaDebye_pos
  have hmax : 0 ≤ max x 0 := le_max_right _ _
  have hterm : 0 ≤ max x 0 / lambdaDebye := div_nonneg hmax hLamPos.le
  have hone : (1 : ℝ) ≤ 1 + max x 0 / lambdaDebye := by linarith
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one hone)

theorem plasmaRadialProfile_continuous : Continuous plasmaRadialProfile := by
  unfold plasmaRadialProfile
  have hnum : Continuous (fun r : ℝ => -r / lambdaDebye) :=
    (continuous_neg.comp continuous_id).div_const lambdaDebye
  have hden : Continuous (fun r : ℝ => 1 + max r 0 / lambdaDebye) :=
    continuous_const.add ((continuous_id.max continuous_const).div_const lambdaDebye)
  exact (Real.continuous_exp.comp hnum).div hden plasmaDebye_denominator_ne_zero

/-- Schematic scalar source strength at proxy radius `r` (only free parameter is overall `j₀`). -/
noncomputable def schematicPlasmaScalar (j₀ r : ℝ) : ℝ :=
  j₀ * plasmaRadialProfile r

theorem schematicPlasmaScalar_eq_zero_of_j₀ (r : ℝ) : schematicPlasmaScalar 0 r = 0 := by
  simp [schematicPlasmaScalar]

theorem schematicPlasmaScalar_add (j₁ j₂ r : ℝ) :
    schematicPlasmaScalar (j₁ + j₂) r = schematicPlasmaScalar j₁ r + schematicPlasmaScalar j₂ r := by
  simp [schematicPlasmaScalar, add_mul]

/-- Absolute value factorizes because `plasmaRadialProfile r > 0` (same screening factor as in `lambdaDebye`). -/
theorem abs_schematicPlasmaScalar (j₀ r : ℝ) :
    |schematicPlasmaScalar j₀ r| = |j₀| * plasmaRadialProfile r := by
  rw [schematicPlasmaScalar, abs_mul]
  congr 1
  exact abs_of_pos (plasmaRadialProfile_pos r)

/-- Inject the scalar source along octonion component `0`; `coord ν` supplies the radial proxy. -/
noncomputable def J_O_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  if _ : a.val = 0 then schematicPlasmaScalar j₀ (coord ν) else 0

/-- On the EM octonion leg `a = 0`, the plasma current equals the schematic scalar (fluid/O-Maxwell hook). -/
theorem J_O_plasma_eq_schematic_on_em (j₀ : ℝ) (coord : Fin 4 → ℝ) (ν : Fin 4) :
    J_O_plasma j₀ coord (0 : Fin 8) ν = schematicPlasmaScalar j₀ (coord ν) := by
  simp [J_O_plasma]

theorem J_O_plasma_nonem_zero (j₀ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) (ha : a.val ≠ 0) :
    J_O_plasma j₀ coord a ν = 0 := by
  simp [J_O_plasma, ha]

theorem abs_J_O_plasma_em (j₀ : ℝ) (coord : Fin 4 → ℝ) (ν : Fin 4) :
    |J_O_plasma j₀ coord (0 : Fin 8) ν| = |j₀| * plasmaRadialProfile (coord ν) := by
  rw [J_O_plasma_eq_schematic_on_em, abs_schematicPlasmaScalar]

theorem J_O_plasma_zero (coord : Fin 4 → ℝ) : J_O_plasma 0 coord = J_O := by
  funext a ν
  simp [J_O_plasma, J_O, schematicPlasmaScalar]

/-- Phenomenological “lapse-weighted” amplitude (no derived coupling from a single action). -/
noncomputable def schematicPlasmaScalar_times_lapse (Φ φ t j₀ r : ℝ) : ℝ :=
  schematicPlasmaScalar j₀ r * HQVM_lapse Φ φ t

/-- Observer-centric linearised scalar amplitude: HQVM lapse with `φ = phi_of_T Θ`, times the
schematic plasma scalar at proxy radius `t` (same real parameter as lapse time slot).

This is the intended “modified inertia” hook (lapse × collective current). It is bookkeeping until
a variational principle identifies it with a perturbation of the metric or the O-Maxwell RHS. -/
noncomputable def linearisedScalarPerturbation (j₀ Φ Θ t : ℝ) : ℝ :=
  HQVM_lapse Φ (phi_of_T Θ) t * schematicPlasmaScalar j₀ t

theorem linearisedScalarPerturbation_at_zero_j₀ (Φ Θ t : ℝ) :
    linearisedScalarPerturbation 0 Φ Θ t = 0 := by
  simp [linearisedScalarPerturbation, schematicPlasmaScalar_eq_zero_of_j₀]

theorem linearisedScalarPerturbation_eq_schematic_times_lapse (j₀ Φ Θ t : ℝ) :
    linearisedScalarPerturbation j₀ Φ Θ t =
      schematicPlasmaScalar_times_lapse Φ (phi_of_T Θ) t j₀ t := by
  simp [linearisedScalarPerturbation, schematicPlasmaScalar_times_lapse, mul_comm]

theorem linearisedScalarPerturbation_eq_HQVM_lapse_phiT_mul (j₀ Φ Θ t : ℝ) :
    linearisedScalarPerturbation j₀ Φ Θ t =
      HQVM_lapse_phiT (Φ, Θ, t) * schematicPlasmaScalar j₀ t := by
  simp [linearisedScalarPerturbation, HQVM_lapse_phiT_eq]

/-- Use the same proxy radius `t` along every spacetime leg (observer-centric uniform shell). -/
noncomputable def plasmaProxyCoordUniform (t : ℝ) : Fin 4 → ℝ :=
  fun _ => t

theorem charge_conservation_O_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) :
    div_μ (fun μ => emergentMaxwellInhomogeneous_O_general (J_O_plasma j₀ coord) a μ) = 0 :=
  charge_conservation_O_general (J_O_plasma j₀ coord) a

theorem emergentMaxwell_plasma_j₀_zero (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_general (J_O_plasma 0 coord) a ν =
      emergentMaxwellInhomogeneous_O a ν := by
  simp [emergentMaxwellInhomogeneous_O, J_O_plasma_zero coord]

/-- With flat φ and zero `grad_φ`, the O-equation is just the `-4π J` source term. -/
theorem emergentMaxwell_plasma_flat_phi (j₀ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4)
    (_h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff)
    (h_grad_zero : ∀ κ, grad_φ κ = 0) :
    emergentMaxwellInhomogeneous_O_general (J_O_plasma j₀ coord) a ν =
      -4 * Real.pi * J_O_plasma j₀ coord a ν := by
  simp only [emergentMaxwellInhomogeneous_O_general, h_grad_zero, mul_zero, sub_zero]
  ring_nf
  norm_num

/-- For uniform proxy `coord ν = t`, component `0` of the flat-`φ` O-equation is `-4π` times the
schematic plasma scalar at `t`. Compare `linearisedScalarPerturbation` (lapse × scalar) in the
module doc: these are not identified without further dynamics. -/
theorem emergentMaxwell_plasma_uniform_t_flat_phi (j₀ t : ℝ) (ν : Fin 4)
    (h_phi_const : ∀ x, phi_of_T x = phiTemperatureCoeff)
    (h_grad_zero : ∀ κ, grad_φ κ = 0) :
    emergentMaxwellInhomogeneous_O_general (J_O_plasma j₀ (plasmaProxyCoordUniform t)) 0 ν =
      -4 * Real.pi * schematicPlasmaScalar j₀ t := by
  simpa [plasmaProxyCoordUniform, J_O_plasma] using
    emergentMaxwell_plasma_flat_phi j₀ (plasmaProxyCoordUniform t) 0 ν h_phi_const h_grad_zero

end

end Hqiv
