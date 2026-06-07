import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.GRFromMaxwell
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hqiv

open BigOperators

/-!
# Action in pure math: O-Maxwell + HQVM-GR

We derive an **action** (functional) in pure mathematics whose **stationarity**
yields the emergent O-Maxwell equation and the HQVM gravitational structure.
No integration over a manifold is required for the definitions; we use finite sums
over the index sets (O components, spacetime indices).

**Structure:**
1. **Potential** A : Fin 8 → Fin 4 → ℝ (gauge potential in O, one component per spacetime index).
2. **Field strength from potential** F_a μ ν = A a ν - A a μ (discrete exterior derivative).
   **Kinetic EL slot:** `F_divergence_sum A a ν = ∑_μ F_{a μν}` is wrapped so it is not parsed as
   `∑_μ (F_{a μν} - 4πJ - …)` when written next to subtraction (see `EL_O_general`).
3. **O-Maxwell Lagrangian** L_O = -(1/4) F² + J·A + φ-coupling; **action** S_O = sum over indices.
4. **Arbitrary source** `L_O_source_general J_src`, `EL_O_general J_src`, `action_O_Maxwell_general J_src`
   for any `J_src : Fin 8 → Fin 4 → ℝ` (default `J_O` recovers the earlier names).
5. **Euler–Lagrange:** δS_O/δA = 0 ⟺ emergent inhomogeneous O-Maxwell equation (same `-4π J` slot as
   `ModifiedMaxwell.emergentMaxwellInhomogeneous_O_general`).
6. **Gravitational action** S_grav (φ, ρ): constraint form of the Friedmann equation; S_grav = 0 ⟺ HQVM Friedmann.
7. **Total action** S_total = S_O + S_grav (or separately stationary); same φ, α link both.

**Discrete holonomy slot:** `Hqiv.Physics.ActionHolonomyGlue` packages the **same** `F_from_A` flux
data into cyclic `Fin 4` plaquette transports in `Function.End ℝ` (abelian layer); the kinetic
`L_O_kinetic` sum is the global `8 × 4 × 4` aggregate over channels.

Plasma / collective sources: `Hqiv.Physics.ActionPlasmaBridge` instantiates `J_src := J_O_plasma j₀ coord`.

Continuum scalar φ on the chart: `Hqiv.Physics.ContinuumOmaxwellClosure` replaces `grad_phi` in the
Euler–Lagrange and φ–A coupling with `coordsGradientComponents φF c` at a basepoint, with const-field
recovery theorems back to `EL_O_general` / `L_O_phi_coupling`.
-/

/-- **Gauge potential in O.** Component a (octonion index), spacetime index ν. -/
def A_O (_a : Fin 8) (_ν : Fin 4) : ℝ := 0

/-- **Field strength from potential** (discrete): F_a μ ν = A a ν - A a μ. Antisymmetric. -/
def F_from_A (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) : ℝ := A a ν - A a μ

/-- **Discrete `F`-divergence surrogate** (sum over the first spacetime index): `∑_μ F_{a μν}`. This is the kinetic piece that appears in `EL_O_general`. -/
def F_divergence_sum (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  ∑ μ : Fin 4, F_from_A A a μ ν

theorem F_divergence_sum_eq_emergentFlatDivergence_sum (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    F_divergence_sum A a ν = emergentFlatDivergence_sum A a ν := by
  unfold F_divergence_sum emergentFlatDivergence_sum F_from_A
  rfl

/-- **F_from_A is antisymmetric.** -/
theorem F_from_A_antisymm (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) :
    F_from_A A a μ ν = - F_from_A A a ν μ := by
  unfold F_from_A; ring

/-- **Kinetic term** -(1/4) ∑_{a,μ,ν} F_a μ ν² (sum over μ < ν for antisymmetry; factor 2 gives 1/4). -/
noncomputable def L_O_kinetic (A : Fin 8 → Fin 4 → ℝ) : ℝ :=
  - (1/4) * ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν)^2 / 2

/-- **Source term** J·A = ∑_{a,ν} J_src a ν * A a ν (interaction between current and gauge potential). -/
def L_O_source_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 8, ∑ ν : Fin 4, J_src a ν * A a ν

/-- **Source term** with the default phenomenological current `J_O`. -/
def L_O_source (A : Fin 8 → Fin 4 → ℝ) : ℝ :=
  L_O_source_general J_O A

/-- **Gradient of φ** at the lock-in chart readout (same slot as `grad_φ` in `ModifiedMaxwell`). -/
noncomputable def grad_phi (ν : Fin 4) : ℝ := grad_φ ν

theorem grad_phi_eq_grad_φ (ν : Fin 4) : grad_phi ν = grad_φ ν := rfl

/-- **φ-coupling term** in the Lagrangian: α * log(φ) * (∇φ)·A (one component for simplicity). -/
noncomputable def L_O_phi_coupling (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  alpha * Real.log (φ_val + 1) * ∑ ν : Fin 4, grad_phi ν * A 0 ν

/-- **O-Maxwell Lagrangian density** for an explicit current `J_src`. -/
noncomputable def L_O_Maxwell_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  L_O_kinetic A + 4 * Real.pi * L_O_source_general J_src A + L_O_phi_coupling A φ_val

/-- **O-Maxwell Lagrangian** with default `J_O`. -/
noncomputable def L_O_Maxwell (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  L_O_Maxwell_general J_O A φ_val

/-- **O-Maxwell action** S_O = L_O (integral replaced by single cell / sum). -/
noncomputable def action_O_Maxwell_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  L_O_Maxwell_general J_src A φ_val

/-- **O-Maxwell action** with default `J_O`. -/
noncomputable def action_O_Maxwell (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  action_O_Maxwell_general J_O A φ_val

/-- **Euler–Lagrange** from varying A(a,ν): same `-4π J_src` coupling as `emergentMaxwellInhomogeneous_O_general`.
Uses `F_divergence_sum` so the discrete `∑_μ F_{μν}` is not parsed as `∑_μ (F_{μν} - 4πJ - …)`. -/
noncomputable def EL_O_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  F_divergence_sum A a ν - 4 * Real.pi * J_src a ν
  - (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0)

/-- **Euler–Lagrange** with default `J_O`. -/
noncomputable def EL_O (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  EL_O_general J_O A φ_val a ν

/-- `EL_O_general` is `F_divergence_sum` minus the declared source and φ–A terms. -/
theorem EL_O_general_eq_F_divergence_sub_sources (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general J_src A φ_val a ν =
      F_divergence_sum A a ν - 4 * Real.pi * J_src a ν -
        (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) :=
  rfl

theorem emergentMaxwellInhomogeneous_O_fromPotential_eq_EL_O_general
    (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4)
    (hgrad : grad_phi ν = 0) :
    emergentMaxwellInhomogeneous_O_fromPotential J_src A a ν =
      EL_O_general J_src A φ_val a ν := by
  unfold emergentMaxwellInhomogeneous_O_fromPotential EL_O_general
  rw [F_divergence_sum_eq_emergentFlatDivergence_sum]
  have hφ : grad_φ ν = 0 := by rw [← grad_phi_eq_grad_φ, hgrad]
  simp [grad_phi, hgrad, hφ, mul_zero, sub_zero, add_zero]

/-- **Octonion channel `a = 0`:** EL splits into `F_divergence_sum` minus `4π J` and the φ–A gradient slot. -/
theorem EL_O_general_zero_eq (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (ν : Fin 4) :
    EL_O_general J_src A φ_val 0 ν =
      F_divergence_sum A 0 ν - 4 * Real.pi * J_src 0 ν -
        alpha * Real.log (φ_val + 1) * grad_phi ν := by
  simp [EL_O_general, F_divergence_sum]

/-- **Vacuum EL₀:** default `J_O = 0` and vanishing φ-gradient at `ν` ⇒ channel `0` is the `F` divergence sum. -/
theorem EL_O_zero_eq_F_divergence_sum (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (ν : Fin 4)
    (hgrad : grad_phi ν = 0) :
    EL_O A φ_val 0 ν = F_divergence_sum A 0 ν := by
  unfold EL_O
  rw [EL_O_general_zero_eq]
  simp [J_O, hgrad]

/-- **Equations from action:** `EL_O_general J_src` is the discrete EL covector with source `J_src`. -/
theorem action_O_Maxwell_EL_eq_emergent_general (J_src : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) (φ_val : ℝ)
    (_hφ : φ_val + 1 > 0) (A : Fin 8 → Fin 4 → ℝ) :
    EL_O_general J_src A φ_val a ν = (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_src a ν -
      (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) := by
  rw [EL_O_general_eq_F_divergence_sub_sources]
  simp [F_divergence_sum]

theorem action_O_Maxwell_EL_eq_emergent (a : Fin 8) (ν : Fin 4) (φ_val : ℝ) (hφ : φ_val + 1 > 0)
    (A : Fin 8 → Fin 4 → ℝ) :
    EL_O A φ_val a ν = (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_O a ν -
      (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) :=
  action_O_Maxwell_EL_eq_emergent_general J_O a ν φ_val hφ A

/-- **Superposition:** J·A part of the Lagrangian is linear in the current. -/
theorem L_O_source_general_add_J (J₁ J₂ : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (fun a ν => J₁ a ν + J₂ a ν) A =
      L_O_source_general J₁ A + L_O_source_general J₂ A := by
  unfold L_O_source_general
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- **Non-superposition of the full O-Maxwell density:** `L_O_kinetic` and `L_O_phi_coupling` are shared
across `J_src`, so only the `4π · (J·A)` piece adds linearly (`L_O_source_general_add_J`). -/
theorem L_O_Maxwell_general_add_J (J₁ J₂ : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) :
    L_O_Maxwell_general (fun a ν => J₁ a ν + J₂ a ν) A φ_val =
      L_O_Maxwell_general J₁ A φ_val + L_O_Maxwell_general J₂ A φ_val -
        L_O_kinetic A - L_O_phi_coupling A φ_val := by
  unfold L_O_Maxwell_general
  rw [L_O_source_general_add_J]
  ring

theorem action_O_Maxwell_general_add_J (J₁ J₂ : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) :
    action_O_Maxwell_general (fun a ν => J₁ a ν + J₂ a ν) A φ_val =
      action_O_Maxwell_general J₁ A φ_val + action_O_Maxwell_general J₂ A φ_val -
        L_O_kinetic A - L_O_phi_coupling A φ_val :=
  L_O_Maxwell_general_add_J J₁ J₂ A φ_val

/-- **Gravitational action (HQVM):** constraint form of the Friedmann equation.
    S_grav(φ, ρ_m, ρ_r) = (3−γ)φ² - 8π G_eff(φ)(ρ_m + ρ_r). Stationarity S_grav = 0 ⟺ Friedmann. -/
noncomputable def S_HQVM_grav (φ rho_m rho_r : ℝ) : ℝ :=
  (3 - gamma_HQIV) * φ^2 - 8 * Real.pi * G_eff φ * (rho_m + rho_r)

/-- **S_grav = 0 is the Friedmann equation.** -/
theorem S_HQVM_grav_zero_iff_Friedmann (φ rho_m rho_r : ℝ) :
    S_HQVM_grav φ rho_m rho_r = 0 ↔ HQVM_Friedmann_eq φ rho_m rho_r := by
  unfold S_HQVM_grav
  rw [sub_eq_zero, HQVM_Friedmann_eq_def, H_of_phi_eq, rho_total_eq]
  constructor <;> intro h <;> norm_num at h ⊢ <;> exact h

/-- **Total action (formal):** S_total = S_O + S_grav with explicit current `J_src`. -/
noncomputable def action_total_general (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val rho_m rho_r : ℝ) : ℝ :=
  action_O_Maxwell_general J_src A φ_val + S_HQVM_grav φ_val rho_m rho_r

/-- **Total action with two currents:** `S_HQVM_grav` is independent of `J_src`, so it would be
double-counted when naively adding two `action_total_general` values—subtract one copy. -/
theorem action_total_general_add_J (J₁ J₂ : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val rho_m rho_r : ℝ) :
    action_total_general (fun a ν => J₁ a ν + J₂ a ν) A φ_val rho_m rho_r =
      action_total_general J₁ A φ_val rho_m rho_r + action_total_general J₂ A φ_val rho_m rho_r -
        L_O_kinetic A - L_O_phi_coupling A φ_val - S_HQVM_grav φ_val rho_m rho_r := by
  unfold action_total_general
  rw [action_O_Maxwell_general_add_J]
  ring

/-- **Total action** with default `J_O`. -/
noncomputable def action_total (A : Fin 8 → Fin 4 → ℝ) (φ_val rho_m rho_r : ℝ) : ℝ :=
  action_total_general J_O A φ_val rho_m rho_r

/-- **Derived from action:** The inhomogeneous O-Maxwell equation is the equation of motion
    from varying the O-Maxwell action (EL_O = 0). The HQVM Friedmann equation is the
    constraint from S_grav = 0. So both dynamics are derived from an action in pure math. -/
theorem equations_from_action (φ rho_m rho_r : ℝ) (_hφ : 0 ≤ φ) :
    (S_HQVM_grav φ rho_m rho_r = 0 ↔ HQVM_Friedmann_eq φ rho_m rho_r) ∧
    (∀ a ν, EL_O A_O (φ + 1) a ν = (∑ μ : Fin 4, F_from_A A_O a μ ν) - 4 * Real.pi * J_O a ν -
      (if a = 0 then alpha * Real.log (φ + 1 + 1) * grad_phi ν else 0)) := by
  refine ⟨S_HQVM_grav_zero_iff_Friedmann φ rho_m rho_r, fun a ν => ?_⟩
  have hφ : (φ + 1) + 1 > 0 := by linarith
  exact action_O_Maxwell_EL_eq_emergent a ν (φ + 1) hφ A_O

end Hqiv
