import HqivSpine.Physics.Action
import HqivSpine.Physics.NowSlice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.Gravity` — the Friedmann sector and the total action

`Action` gave the O-Maxwell (gauge) half of the Lagrangian; this module supplies the
**gravitational** half and assembles the **total action**, so the spine carries the
whole variational story.

Everything is fixed by the lattice exponent `α = 3/5` and the now-slice curvature `φ`
(the expansion-rate curvature carried by `NowSlice`), with no new input:

* **Monogamy split** `γ = 1 − α = 2/5`, hence the prefactor `3 − γ = 13/5`;
* **Homogeneous Hubble rate** `H(φ) = φ` — the now-slice expansion curvature *is* the
  Hubble rate;
* **Varying-G from the lattice** `G_eff(φ) = φ^α` (with `G₀ = H₀ = 1`, so `G_eff(1) = 1`);
* **Friedmann constraint** `(3 − γ)·H(φ)² = 8π·G_eff(φ)·(ρ_m + ρ_r)`;
* **Gravitational action** `S_grav = (3 − γ)φ² − 8π·G_eff(φ)·(ρ_m + ρ_r)`, whose
  **stationarity** `S_grav = 0` is exactly the Friedmann equation;
* **Total action** `S = S_OMaxwell + S_grav`, whose joint stationarity is the pair
  (inhomogeneous O-Maxwell, Friedmann).

The gravitational sector is anchored to the **now slice**: its `φ` is the Hubble rate
entering the constraint, so gravity reads out of the spine's single physical input
rather than a separate parameter.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-! ## The monogamy split and the Friedmann prefactor

`γ = 2/5` (`gammaHQIV`) is the α-partner defined in `Physics.Shell`; here we record the
unit split and the Friedmann prefactor `3 − γ`. -/

/-- **Unit split** `α + γ = 1`: imprint plus monogamy fill the unit. -/
theorem alphaEM_add_gammaHQIV : alphaEM + gammaHQIV = 1 := by
  rw [alphaEM_eq, gammaHQIV_eq]; norm_num

/-- **The Friedmann prefactor** `3 − γ = 13/5`. -/
theorem three_minus_gammaHQIV : (3 : ℝ) - gammaHQIV = 13 / 5 := by
  rw [gammaHQIV_eq]; norm_num

/-! ## Homogeneous Hubble rate and varying gravitational coupling -/

/-- **Homogeneous Hubble rate** `H(φ) = φ`: the expansion-rate curvature is the
Hubble rate in the homogeneous limit. -/
def hubble (φ : ℝ) : ℝ := φ

theorem hubble_eq (φ : ℝ) : hubble φ = φ := rfl

/-- **Effective gravitational coupling** `G_eff(φ) = φ^α` (lattice-`α` varying-G with
`G₀ = H₀ = 1`). -/
noncomputable def gEff (φ : ℝ) : ℝ := φ ^ alphaEM

/-- The coupling exponent is the lattice imprint exponent `α = 3/5`. -/
theorem gEff_eq (φ : ℝ) : gEff φ = φ ^ (3 / 5 : ℝ) := by rw [gEff, alphaEM_eq]

/-- **Normalisation** `G_eff(1) = 1` (`G₀ = H₀ = 1`). -/
theorem gEff_one : gEff 1 = 1 := by rw [gEff, Real.one_rpow]

/-- **Positivity** `G_eff(φ) > 0` for `φ > 0`. -/
theorem gEff_pos {φ : ℝ} (hφ : 0 < φ) : 0 < gEff φ := Real.rpow_pos_of_pos hφ alphaEM

/-! ## Two fixed points — the horizon and the Planck pole

The curvature flow is **not** a single continuum attractor: on the discrete lattice
the varying-G map `φ ↦ φ^α` (`α = 3/5`) has **exactly two** non-negative fixed
points, and they are the two ends of a tug-of-war:

* `φ = 0` — the **horizon** (outer end, vanishing curvature);
* `φ = 1` — the **Planck pole** (inner end, `G₀ = H₀ = 1`).

The flow runs *both ways*. On the open interval `0 < φ < 1` the inward Ricci
contraction `G_eff(φ) = φ^α > φ` pulls curvature **up toward the Planck pole**,
while the outward expansion `φ^(1/α) = φ^(5/3) < φ` pulls it **down toward the
horizon** (`tug_of_war_interior`). Every interior shell is squeezed between the two
attractors; the lock-in is the discrete balance of that tension, not a continuum
limit (`Foundation.shellNumer_second_difference` says the lattice carries constant
discrete curvature, so it cannot be smoothed into a continuum). -/

/-- `G_eff` **strengthens monotonically** with the curvature `φ` (for `φ ≥ 0`). -/
theorem gEff_strictMonoOn : StrictMonoOn gEff (Set.Ici 0) := by
  intro a ha b _ hab
  exact Real.rpow_lt_rpow (Set.mem_Ici.mp ha) hab (by rw [alphaEM_eq]; norm_num)

/-- **Horizon fixed point** `G_eff(0) = 0`: the vanishing-curvature outer end. -/
theorem gEff_zero : gEff 0 = 0 := by
  rw [gEff]; exact Real.zero_rpow (by rw [alphaEM_eq]; norm_num)

/-- **Unique positive fixed point** `G_eff(φ) = φ ↔ φ = 1` (the Planck pole): the sole
positive curvature at which the varying coupling equals the Hubble rate it drives. -/
theorem gEff_fixed_iff {φ : ℝ} (hφ : 0 < φ) : gEff φ = φ ↔ φ = 1 := by
  constructor
  · intro h
    have hlog : Real.log (gEff φ) = Real.log φ := by rw [h]
    rw [gEff, alphaEM_eq, Real.log_rpow hφ] at hlog
    have hL : Real.log φ = 0 := by linarith
    rcases Real.log_eq_zero.mp hL with h0 | h1 | hm1
    · exact absurd h0 (ne_of_gt hφ)
    · exact h1
    · exact absurd hm1 (by linarith)
  · rintro rfl; exact gEff_one

/-- **The two ends.** On `φ ≥ 0` the flow `φ ↦ φ^α` has exactly the two fixed points
`0` (horizon) and `1` (Planck pole) — nothing in between is fixed, so interior
curvature always feels a net pull. -/
theorem gEff_fixed_iff_nonneg {φ : ℝ} (hφ : 0 ≤ φ) : gEff φ = φ ↔ φ = 0 ∨ φ = 1 := by
  rcases eq_or_lt_of_le hφ with h0 | hpos
  · subst h0
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact gEff_zero
  · rw [gEff_fixed_iff hpos]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h (ne_of_gt hpos)
      · exact h

/-- Above the Planck pole gravity no longer outpaces expansion: `1 < φ → G_eff φ < φ`. -/
theorem gEff_lt_self {φ : ℝ} (hφ : 1 < φ) : gEff φ < φ := by
  rw [gEff, alphaEM_eq]
  have h : φ ^ (3 / 5 : ℝ) < φ ^ (1 : ℝ) := (Real.rpow_lt_rpow_left_iff hφ).mpr (by norm_num)
  rwa [Real.rpow_one] at h

/-- Below the Planck pole gravity outpaces expansion: `0 < φ < 1 → φ < G_eff φ`. -/
theorem self_lt_gEff {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) : φ < gEff φ := by
  rw [gEff, alphaEM_eq]
  have h : φ ^ (1 : ℝ) < φ ^ (3 / 5 : ℝ) :=
    (Real.rpow_lt_rpow_left_iff_of_base_lt_one hφ0 hφ1).mpr (by norm_num)
  rwa [Real.rpow_one] at h

/-! ## The flow goes out as well as in -/

/-- **Outward expansion flow** `φ ↦ φ^(1/α) = φ^(5/3)` — the inverse of inward Ricci
contraction. On `0 < φ < 1` it dilutes curvature toward the horizon. -/
noncomputable def expansionFlow (φ : ℝ) : ℝ := φ ^ (1 / alphaEM)

theorem expansionFlow_eq (φ : ℝ) : expansionFlow φ = φ ^ (5 / 3 : ℝ) := by
  rw [expansionFlow, alphaEM_eq]; norm_num

/-- The expansion flow pulls interior curvature **down toward the horizon.** -/
theorem expansionFlow_lt_self {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) : expansionFlow φ < φ := by
  rw [expansionFlow]
  have h : φ ^ (1 / alphaEM) < φ ^ (1 : ℝ) :=
    (Real.rpow_lt_rpow_left_iff_of_base_lt_one hφ0 hφ1).mpr (by rw [alphaEM_eq]; norm_num)
  rwa [Real.rpow_one] at h

/-- **The tug of war.** At any interior curvature `0 < φ < 1`, expansion pulls
**out** toward the horizon (`φ^(5/3) < φ`) while Ricci contraction pulls **in**
toward the Planck pole (`φ < φ^(3/5)`): the two fixed points pull against each
other, and the lock-in shell sits where the discrete lattice balances them. -/
theorem tug_of_war_interior {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    expansionFlow φ < φ ∧ φ < gEff φ :=
  ⟨expansionFlow_lt_self hφ0 hφ1, self_lt_gEff hφ0 hφ1⟩

/-! ## The Friedmann constraint and its action form -/

/-- **Friedmann equation** `(3 − γ)·H(φ)² = 8π·G_eff(φ)·(ρ_m + ρ_r)`. -/
def friedmann (φ rhoM rhoR : ℝ) : Prop :=
  (3 - gammaHQIV) * hubble φ ^ 2 = 8 * Real.pi * gEff φ * (rhoM + rhoR)

/-- **Gravitational action** (constraint form) `S_grav = (3 − γ)φ² − 8π·G_eff(φ)·ρ_tot`. -/
noncomputable def gravAction (φ rhoM rhoR : ℝ) : ℝ :=
  (3 - gammaHQIV) * φ ^ 2 - 8 * Real.pi * gEff φ * (rhoM + rhoR)

/-- **Stationarity = Friedmann.** The gravitational action vanishes exactly when the
Friedmann constraint holds. -/
theorem gravAction_zero_iff_friedmann (φ rhoM rhoR : ℝ) :
    gravAction φ rhoM rhoR = 0 ↔ friedmann φ rhoM rhoR := by
  unfold gravAction friedmann hubble; rw [sub_eq_zero]

/-! ## Anchoring gravity to the now slice

The gravitational sector takes no new parameter: its `φ` is the now-slice expansion
curvature, so Friedmann reads out of the spine's single physical anchor. -/

/-- The now-slice expansion curvature `φ` **is** the homogeneous Hubble rate. -/
theorem nowSlice_hubble (s : NowSlice) : hubble s.phi = s.phi := rfl

/-- The now slice's gravitational action vanishes exactly when its expansion curvature
satisfies the Friedmann constraint. -/
theorem nowSlice_gravAction_zero_iff_friedmann (s : NowSlice) (rhoM rhoR : ℝ) :
    gravAction s.phi rhoM rhoR = 0 ↔ friedmann s.phi rhoM rhoR :=
  gravAction_zero_iff_friedmann s.phi rhoM rhoR

/-! ## The total action: O-Maxwell + gravity -/

/-- **Total action** `S = S_OMaxwell + S_grav`. -/
noncomputable def totalAction (J : Current) (A : Potential) (φ rhoM rhoR : ℝ) : ℝ :=
  action J A + gravAction φ rhoM rhoR

theorem totalAction_eq (J : Current) (A : Potential) (φ rhoM rhoR : ℝ) :
    totalAction J A φ rhoM rhoR = action J A + gravAction φ rhoM rhoR := rfl

/-- **Joint equations of motion.** Stationarity of the total action splits into the two
independent sectors: the gauge variation gives the inhomogeneous O-Maxwell equation,
the metric variation gives the Friedmann equation. -/
structure TotalActionClosure : Prop where
  gamma_split : alphaEM + gammaHQIV = 1
  hubble_is_phi : ∀ φ : ℝ, hubble φ = φ
  gEff_normalised : gEff 1 = 1
  gauge_eom : ∀ (J : Current) (A : Potential) (a : Fin 8) (ν : Fin 4),
    EL J A a ν = 0 ↔ divergence A a ν = 4 * Real.pi * J a ν
  gravity_eom : ∀ φ rhoM rhoR : ℝ, gravAction φ rhoM rhoR = 0 ↔ friedmann φ rhoM rhoR

/-- **The total HQIV action principle is discharged** — gauge sector (O-Maxwell) and
gravitational sector (Friedmann) together, both as stationarity conditions. -/
theorem total_action_closure : TotalActionClosure where
  gamma_split := alphaEM_add_gammaHQIV
  hubble_is_phi := hubble_eq
  gEff_normalised := gEff_one
  gauge_eom := EL_eq_zero_iff_maxwell
  gravity_eom := gravAction_zero_iff_friedmann

end HqivSpine.Physics
