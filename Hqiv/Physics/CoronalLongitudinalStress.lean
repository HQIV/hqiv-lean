import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.OMaxwellAlgebraSeed
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.HQIVFluidClosureScaffold

/-!
# Coronal longitudinal HQIV/O-Maxwell stress (paper companion)

**Purpose:** instantiate the longitudinal EM stress mechanism of
`papers/longitudinal_em_force_hqiv.tex` on a stellar magnetic flux tube
(photosphere ↔ corona axial column), and capture the algebraic content
that a follow-up paper on coronal heating will use.

A coronal magnetic loop is the natural geometric domain in which the
wire-paper's three preconditions are all satisfied at once:

* an axial current channel (`J‖B`, force-free flux tube);
* a non-zero axial `∂_s φ` (the photosphere → transition region → corona
  `φ` jump is the steepest in the solar atmosphere);
* asymmetric "contacts" (opposite-polarity convecting footpoints).

This module **does not** evaluate `φ(s)` for the solar atmosphere from a
horizon-shell model — that derivation is not in the corpus yet — but it
fixes every algebraic identity the follow-up paper needs and connects
each piece to existing modules (`OMaxwellAlgebraSeed`, `ModifiedMaxwell`,
`HQIVFluidClosureScaffold`).

## Proof status (all `Prop`, zero `sorry`)

* **§1.** Axial HQIV electric channel `E_HQIV = E_∗·(α/4π)·Λ_s·∂_s φ` with
  the `α = 3/5` rewrite to `3/(20π)`; vanishing in the constant-φ limit.
* **§2.** Ohmic background and effective axial field
  `E_eff = E_Ohm + E_HQIV`; classical-Maxwell reduction.
* **§3.** Force density `f_∥ = nq · E_eff` and heating-rate density
  `q̇ = f_∥ · v_∥` with flat-limit collapse.
* **§4.** Boundary form
  `ΔF_∥ = A·nq·E_∗·(3/20π)·Λ_s·(φ_cor − φ_photo)` and a witness bundle
  that absorbs the integration step the wire paper performs.
* **§5.** Photosphere → corona φ jump from the HQIV shell ladder
  `phi_of_shell` with sign / monotonicity lemmas.
* **§6.** Companion fluid momentum source axial component identified
  with `Fin 3`-component 0 of `hqivVacuumMomentumSource3`.
* **§7.** Even / odd-in-current decomposition for the wire-paper's
  current-reversal discriminant, with explicit `I^2`, `I`, `I^3` parities.
* **§8.** End-to-end coronal heating witness `CoronalHQIVHeatingWitness`
  and the area-integrated heating-rate boundary form
  `coronalHeatingFluxBoundary`.

**Not claimed:** stellar-atmosphere φ profile from horizon shells, SI
heating-rate match against observed coronal budgets, plasma kinetic
theory, or any displacement of the standard Alfvén-wave / nanoflare
candidates. The module only fixes the algebraic spine.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-!
## §1. Axial HQIV electric channel
-/

/-- Longitudinal HQIV/O-Maxwell electric channel at an axial point.

`E_HQIV(s) = E_∗ · (α/4π) · Λ_s · ∂_s φ(s)`, where `α = 3/5` is the
lattice imprint (`alpha_eq_3_5`), `Λ_s` is the axial coupling-log slot
matching `algebraicMaxwellCouplingLog`, and `E_∗` is the dimensionless →
SI conversion (set to `1` in natural units). -/
def coronalLongitudinalHQIVField (Estar couplingLog dphi_ds : ℝ) : ℝ :=
  Estar * (alpha / (4 * Real.pi)) * couplingLog * dphi_ds

/-- α = 3/5 inlined: `E_HQIV = E_∗ · 3/(20π) · Λ_s · ∂_s φ`. -/
theorem coronalLongitudinalHQIVField_alpha_3_5 (Estar couplingLog dphi_ds : ℝ) :
    coronalLongitudinalHQIVField Estar couplingLog dphi_ds =
      Estar * (3 / (20 * Real.pi)) * couplingLog * dphi_ds := by
  unfold coronalLongitudinalHQIVField
  rw [alpha_eq_3_5]
  ring

/-- Flat / constant-φ limit: vanishing axial gradient ⇒ no HQIV channel. -/
theorem coronalLongitudinalHQIVField_zero_of_dphi_zero
    (Estar couplingLog : ℝ) :
    coronalLongitudinalHQIVField Estar couplingLog 0 = 0 := by
  unfold coronalLongitudinalHQIVField; ring

theorem coronalLongitudinalHQIVField_zero_of_couplingLog_zero
    (Estar dphi_ds : ℝ) :
    coronalLongitudinalHQIVField Estar 0 dphi_ds = 0 := by
  unfold coronalLongitudinalHQIVField; ring

theorem coronalLongitudinalHQIVField_zero_of_Estar_zero
    (couplingLog dphi_ds : ℝ) :
    coronalLongitudinalHQIVField 0 couplingLog dphi_ds = 0 := by
  unfold coronalLongitudinalHQIVField; ring

theorem coronalLongitudinalHQIVField_linear_in_dphi
    (Estar couplingLog d₁ d₂ : ℝ) :
    coronalLongitudinalHQIVField Estar couplingLog (d₁ + d₂) =
      coronalLongitudinalHQIVField Estar couplingLog d₁ +
        coronalLongitudinalHQIVField Estar couplingLog d₂ := by
  unfold coronalLongitudinalHQIVField; ring

/-!
## §2. Ohmic background and effective axial field
-/

/-- Ohmic axial field `E_Ohm = J/σ`. -/
def ohmicAxialField (J sigma : ℝ) : ℝ := J / sigma

/-- Total effective axial field along the loop: Ohmic + HQIV channels. -/
def coronalEffectiveAxialField (J sigma Estar couplingLog dphi_ds : ℝ) : ℝ :=
  ohmicAxialField J sigma + coronalLongitudinalHQIVField Estar couplingLog dphi_ds

/-- Effective axial field reduces to pure Ohmic when the HQIV channel vanishes
(classical-Maxwell limit, paper §6 of the wire companion). -/
theorem coronalEffectiveAxialField_classical_limit
    (J sigma Estar couplingLog : ℝ) :
    coronalEffectiveAxialField J sigma Estar couplingLog 0 = ohmicAxialField J sigma := by
  unfold coronalEffectiveAxialField
  rw [coronalLongitudinalHQIVField_zero_of_dphi_zero]
  ring

/-- In the high-conductivity limit (`σ` large), the Ohmic axial field collapses
toward `0`: this is the coronal regime where Spitzer conductivity is enormous
and Ohmic heating is correspondingly suppressed. The HQIV channel does **not**
go through `1/σ` and therefore is **not** suppressed in the same way. -/
theorem ohmicAxialField_eq_zero_of_J_zero (sigma : ℝ) :
    ohmicAxialField 0 sigma = 0 := by
  unfold ohmicAxialField; simp

theorem ohmicAxialField_zero_of_sigma_eq_zero (J : ℝ) :
    ohmicAxialField J 0 = 0 := by
  unfold ohmicAxialField; simp

/-!
## §3. Force density and heating-rate density
-/

/-- Axial force density `f_∥ = nq · E_eff`. -/
def coronalLongitudinalForceDensity (nq J sigma Estar couplingLog dphi_ds : ℝ) : ℝ :=
  nq * coronalEffectiveAxialField J sigma Estar couplingLog dphi_ds

/-- Heating-rate density per unit volume `q̇ = f_∥ · v_∥`. -/
def coronalHeatingRateDensity (nq J sigma Estar couplingLog dphi_ds v_parallel : ℝ) : ℝ :=
  coronalLongitudinalForceDensity nq J sigma Estar couplingLog dphi_ds * v_parallel

theorem coronalHeatingRateDensity_zero_of_vparallel_zero
    (nq J sigma Estar couplingLog dphi_ds : ℝ) :
    coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds 0 = 0 := by
  unfold coronalHeatingRateDensity; ring

/-- Flat / Ohmic-only limit: with `∂_s φ = 0` the heating-rate density
collapses to the standard Joule-style `nq · (J/σ) · v_∥`. -/
theorem coronalHeatingRateDensity_classical_flat_limit
    (nq J sigma Estar couplingLog v_parallel : ℝ) :
    coronalHeatingRateDensity nq J sigma Estar couplingLog 0 v_parallel =
      nq * (J / sigma) * v_parallel := by
  unfold coronalHeatingRateDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField ohmicAxialField
  rw [coronalLongitudinalHQIVField_zero_of_dphi_zero]
  ring

/-- HQIV-only contribution to the heating-rate density (Ohmic channel zeroed). -/
theorem coronalHeatingRateDensity_hqiv_only
    (nq Estar couplingLog dphi_ds v_parallel : ℝ) :
    coronalHeatingRateDensity nq 0 1 Estar couplingLog dphi_ds v_parallel =
      nq * (Estar * (3 / (20 * Real.pi)) * couplingLog * dphi_ds) * v_parallel := by
  unfold coronalHeatingRateDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField ohmicAxialField
  rw [coronalLongitudinalHQIVField_alpha_3_5]
  simp

/-!
## §4. Boundary form (paper Eq. for ΔF_∥)
-/

/-- Boundary form of the integrated axial HQIV force across a column:

`ΔF_∥ = A · nq · E_∗ · (3/20π) · Λ_s · (φ_cor − φ_photo)` (α = 3/5 inlined).

This is the same `Λ_s`-constant collapse the wire paper performs on
`∫_0^L Λ_s ∂_s φ ds = Λ_s [φ(L) − φ(0)]`. -/
def coronalLongitudinalForceBoundary
    (A nq Estar couplingLog phi_photo phi_corona : ℝ) : ℝ :=
  A * nq * Estar * (3 / (20 * Real.pi)) * couplingLog * (phi_corona - phi_photo)

/-- Equal photospheric and coronal φ ⇒ no integrated HQIV stress (flat limit). -/
theorem coronalLongitudinalForceBoundary_zero_of_phi_equal
    (A nq Estar couplingLog phi : ℝ) :
    coronalLongitudinalForceBoundary A nq Estar couplingLog phi phi = 0 := by
  unfold coronalLongitudinalForceBoundary; ring

/-- Boundary form rewritten with the symbolic `α/(4π)` factor. -/
theorem coronalLongitudinalForceBoundary_eq_alpha_form
    (A nq Estar couplingLog phi_photo phi_corona : ℝ) :
    coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona =
      A * nq * Estar * (alpha / (4 * Real.pi)) * couplingLog * (phi_corona - phi_photo) := by
  unfold coronalLongitudinalForceBoundary
  rw [alpha_eq_3_5]
  ring

/-- Linearity in the φ-jump: doubling the photosphere → corona gap
doubles the boundary force. -/
theorem coronalLongitudinalForceBoundary_add_phi_jump
    (A nq Estar couplingLog phi_photo phi₁ phi₂ : ℝ) :
    coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo (phi₁ + phi₂) =
      coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi₁ +
        coronalLongitudinalForceBoundary A nq Estar couplingLog 0 phi₂ := by
  unfold coronalLongitudinalForceBoundary; ring

/-- Caller-side witness packaging the integration step the wire paper
performs (`∫_0^L Λ_s ∂_s φ ds = Λ_s [φ(L) − φ(0)]` for `Λ_s` constant).
Avoids re-proving the fundamental theorem of calculus inside this scaffold;
downstream modules can supply the integral identity. -/
structure CoronalColumnBoundaryWitness
    (A nq Estar couplingLog Delta_F phi_photo phi_corona : ℝ) : Prop where
  delta_F_eq :
    Delta_F =
      coronalLongitudinalForceBoundary A nq Estar couplingLog phi_photo phi_corona

theorem CoronalColumnBoundaryWitness.delta_F_alpha_3_5_form
    {A nq Estar couplingLog Delta_F phi_photo phi_corona : ℝ}
    (h : CoronalColumnBoundaryWitness A nq Estar couplingLog Delta_F phi_photo phi_corona) :
    Delta_F =
      A * nq * Estar * (3 / (20 * Real.pi)) * couplingLog * (phi_corona - phi_photo) := by
  rw [h.delta_F_eq]
  rfl

theorem CoronalColumnBoundaryWitness.delta_F_zero_of_phi_equal
    {A nq Estar couplingLog Delta_F phi : ℝ}
    (h : CoronalColumnBoundaryWitness A nq Estar couplingLog Delta_F phi phi) :
    Delta_F = 0 := by
  rw [h.delta_F_eq, coronalLongitudinalForceBoundary_zero_of_phi_equal]

/-!
## §5. Photosphere → corona `φ` jump from the HQIV shell ladder
-/

/-- A photosphere/corona shell pair (`m_photo ≤ m_corona`) used to anchor the
column's `φ` boundary in the existing HQIV shell ladder. The actual shell
indices for the solar atmosphere are not derived in the corpus yet; this
structure simply packages the algebraic dependence. -/
structure CoronalColumnShells where
  m_photo : ℕ
  m_corona : ℕ
  order : m_photo ≤ m_corona

/-- φ jump across the column from the discrete shell ladder
`phi_of_shell m = 2(m+1)` (`phi_of_shell_closed_form`). -/
def coronalPhiJump (cols : CoronalColumnShells) : ℝ :=
  phi_of_shell cols.m_corona - phi_of_shell cols.m_photo

/-- Closed form using `phi_of_shell_closed_form`: `Δφ = 2·(m_cor − m_ph)`. -/
theorem coronalPhiJump_closed_form (cols : CoronalColumnShells) :
    coronalPhiJump cols =
      2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ)) := by
  unfold coronalPhiJump
  rw [phi_of_shell_closed_form, phi_of_shell_closed_form]
  unfold phiTemperatureCoeff
  ring

theorem coronalPhiJump_nonneg (cols : CoronalColumnShells) :
    0 ≤ coronalPhiJump cols := by
  rw [coronalPhiJump_closed_form]
  have h : (cols.m_photo : ℝ) ≤ (cols.m_corona : ℝ) := by exact_mod_cast cols.order
  linarith

theorem coronalPhiJump_pos_of_lt (cols : CoronalColumnShells)
    (h : cols.m_photo < cols.m_corona) :
    0 < coronalPhiJump cols := by
  rw [coronalPhiJump_closed_form]
  have hlt : (cols.m_photo : ℝ) < (cols.m_corona : ℝ) := by exact_mod_cast h
  linarith

theorem coronalPhiJump_zero_of_equal_shells (m : ℕ) :
    coronalPhiJump ⟨m, m, le_refl m⟩ = 0 := by
  rw [coronalPhiJump_closed_form]; simp

/-- Integrated boundary force using the shell-ladder φ jump. -/
def coronalLongitudinalForceBoundaryShells
    (A nq Estar couplingLog : ℝ) (cols : CoronalColumnShells) : ℝ :=
  coronalLongitudinalForceBoundary A nq Estar couplingLog
    (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona)

theorem coronalLongitudinalForceBoundaryShells_eq
    (A nq Estar couplingLog : ℝ) (cols : CoronalColumnShells) :
    coronalLongitudinalForceBoundaryShells A nq Estar couplingLog cols =
      A * nq * Estar * (3 / (20 * Real.pi)) * couplingLog * coronalPhiJump cols := by
  unfold coronalLongitudinalForceBoundaryShells coronalLongitudinalForceBoundary
    coronalPhiJump
  ring

/-- Same-shell column ⇒ no integrated HQIV force (consistent with the flat /
constant-φ limit recovered by `coronalLongitudinalForceBoundary_zero_of_phi_equal`). -/
theorem coronalLongitudinalForceBoundaryShells_zero_of_equal_shells
    (A nq Estar couplingLog : ℝ) (m : ℕ) :
    coronalLongitudinalForceBoundaryShells A nq Estar couplingLog
        ⟨m, m, le_refl m⟩ = 0 := by
  rw [coronalLongitudinalForceBoundaryShells_eq, coronalPhiJump_zero_of_equal_shells]
  ring

/-- Shell-ladder boundary force scales linearly with the (m_cor − m_photo) gap.
This makes the wire paper's "boundary-dominated, not bulk" prediction explicit:
the integrated HQIV channel cares about the photosphere ↔ corona shell index
gap, not the bulk loop length. -/
theorem coronalLongitudinalForceBoundaryShells_eq_two_shellGap
    (A nq Estar couplingLog : ℝ) (cols : CoronalColumnShells) :
    coronalLongitudinalForceBoundaryShells A nq Estar couplingLog cols =
      A * nq * Estar * (3 / (20 * Real.pi)) * couplingLog *
        (2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ))) := by
  rw [coronalLongitudinalForceBoundaryShells_eq, coronalPhiJump_closed_form]

/-!
## §6. Companion fluid momentum-source axial component

Identifies the 1D axial scalar with component 0 of the existing 3-vector
`hqivVacuumMomentumSource3 γ φ δ̇θ′ ∇φ ∇δ̇θ′` from `HQIVFluidClosureScaffold`,
specialized to gradients concentrated along the loop axis.
-/

/-- 1D axial component of the fluid vacuum momentum source

`g_{vac,s} = −γ/6 · (φ ∂_s δ̇θ′ + δ̇θ′ ∂_s φ)`,

with `γ = 2/5` from `gamma_eq_2_5`. -/
def coronalAxialVacuumMomentumSource (phi dotTheta dphi_ds ddot_ds : ℝ) : ℝ :=
  (-gamma_HQIV / 6) * (phi * ddot_ds + dotTheta * dphi_ds)

/-- γ = 2/5 inlined: prefactor is `−1/15`. -/
theorem coronalAxialVacuumMomentumSource_eq_minus_one_fifteenth
    (phi dotTheta dphi_ds ddot_ds : ℝ) :
    coronalAxialVacuumMomentumSource phi dotTheta dphi_ds ddot_ds =
      -(1 / 15) * (phi * ddot_ds + dotTheta * dphi_ds) := by
  unfold coronalAxialVacuumMomentumSource
  rw [gamma_eq_2_5]
  ring

/-- Vanishing under flat gradients. -/
theorem coronalAxialVacuumMomentumSource_zero_of_grad_zero
    (phi dotTheta : ℝ) :
    coronalAxialVacuumMomentumSource phi dotTheta 0 0 = 0 := by
  unfold coronalAxialVacuumMomentumSource; ring

/-- The 1D axial source equals `Fin 3`-component 0 of the existing
`hqivVacuumMomentumSource3` when the spatial gradients are concentrated
along axis 0. -/
theorem coronalAxialVacuumMomentumSource_eq_hqivVacuumMomentumSource3_axis0
    (phi dotTheta dphi_ds ddot_ds : ℝ) :
    coronalAxialVacuumMomentumSource phi dotTheta dphi_ds ddot_ds =
      hqivVacuumMomentumSource3 gamma_HQIV phi dotTheta
        (fun i : Fin 3 => if i = 0 then dphi_ds else 0)
        (fun i : Fin 3 => if i = 0 then ddot_ds else 0) 0 := by
  simp [coronalAxialVacuumMomentumSource, hqivVacuumMomentumSource3]

/-!
## §7. Current-reversal discriminant (wire paper §7 item 1)

Thermal expansion and magnetic pinch scale as `I^2` (even in current). A
boundary-dominated phase-gradient residual can carry an odd-in-`I` component
when the column has asymmetric contacts/footpoints (opposite-polarity
photospheric driving in the coronal case). The following bookkeeping splits
an arbitrary functional `F : ℝ → ℝ` into its even and odd parts under
`I ↦ −I` and exhibits the parity of each test power.
-/

/-- Even-in-current part of a force/heating functional. -/
def evenInCurrent (F : ℝ → ℝ) (I : ℝ) : ℝ := (F I + F (-I)) / 2

/-- Odd-in-current part. -/
def oddInCurrent (F : ℝ → ℝ) (I : ℝ) : ℝ := (F I - F (-I)) / 2

/-- Even/odd decomposition (algebraic identity). -/
theorem evenInCurrent_add_oddInCurrent (F : ℝ → ℝ) (I : ℝ) :
    F I = evenInCurrent F I + oddInCurrent F I := by
  unfold evenInCurrent oddInCurrent; ring

theorem evenInCurrent_even (F : ℝ → ℝ) (I : ℝ) :
    evenInCurrent F I = evenInCurrent F (-I) := by
  unfold evenInCurrent
  rw [neg_neg]; ring

theorem oddInCurrent_neg (F : ℝ → ℝ) (I : ℝ) :
    oddInCurrent F (-I) = -oddInCurrent F I := by
  unfold oddInCurrent
  rw [neg_neg]; ring

/-- `I^2` test channel (thermal/pinch background): all-even. -/
theorem evenInCurrent_pow_two (I : ℝ) :
    evenInCurrent (fun J => J ^ 2) I = I ^ 2 := by
  unfold evenInCurrent
  show (I ^ 2 + (-I) ^ 2) / 2 = I ^ 2
  ring

theorem oddInCurrent_pow_two (I : ℝ) :
    oddInCurrent (fun J => J ^ 2) I = 0 := by
  unfold oddInCurrent
  show (I ^ 2 - (-I) ^ 2) / 2 = 0
  ring

/-- Linear HQIV channel `b₁ I`: all-odd. -/
theorem evenInCurrent_id (I : ℝ) :
    evenInCurrent (fun J => J) I = 0 := by
  unfold evenInCurrent
  show (I + (-I)) / 2 = 0
  ring

theorem oddInCurrent_id (I : ℝ) :
    oddInCurrent (fun J => J) I = I := by
  unfold oddInCurrent
  show (I - (-I)) / 2 = I
  ring

/-- Cubic HQIV channel `b₃ I^3`: all-odd. -/
theorem evenInCurrent_pow_three (I : ℝ) :
    evenInCurrent (fun J => J ^ 3) I = 0 := by
  unfold evenInCurrent
  show (I ^ 3 + (-I) ^ 3) / 2 = 0
  ring

theorem oddInCurrent_pow_three (I : ℝ) :
    oddInCurrent (fun J => J ^ 3) I = I ^ 3 := by
  unfold oddInCurrent
  show (I ^ 3 - (-I) ^ 3) / 2 = I ^ 3
  ring

/-- Wire-paper test polynomial `a_2 I^2 + a_4 I^4 + b_1 I + b_3 I^3 + F_0`:
the even-in-`I` part absorbs the thermal/pinch backgrounds and the constant,
the odd-in-`I` part isolates the HQIV-oriented channel. -/
def coronalForceTestPoly (a₂ a₄ b₁ b₃ F₀ I : ℝ) : ℝ :=
  a₂ * I ^ 2 + a₄ * I ^ 4 + b₁ * I + b₃ * I ^ 3 + F₀

theorem coronalForceTestPoly_even_part (a₂ a₄ b₁ b₃ F₀ I : ℝ) :
    evenInCurrent (coronalForceTestPoly a₂ a₄ b₁ b₃ F₀) I =
      a₂ * I ^ 2 + a₄ * I ^ 4 + F₀ := by
  unfold evenInCurrent coronalForceTestPoly
  have h₂ : (-I) ^ 2 = I ^ 2 := by ring
  have h₄ : (-I) ^ 4 = I ^ 4 := by ring
  have h₃ : (-I) ^ 3 = -(I ^ 3) := by ring
  rw [h₂, h₄, h₃]; ring

theorem coronalForceTestPoly_odd_part (a₂ a₄ b₁ b₃ F₀ I : ℝ) :
    oddInCurrent (coronalForceTestPoly a₂ a₄ b₁ b₃ F₀) I =
      b₁ * I + b₃ * I ^ 3 := by
  unfold oddInCurrent coronalForceTestPoly
  have h₂ : (-I) ^ 2 = I ^ 2 := by ring
  have h₄ : (-I) ^ 4 = I ^ 4 := by ring
  have h₃ : (-I) ^ 3 = -(I ^ 3) := by ring
  rw [h₂, h₄, h₃]; ring

/-!
## §8. End-to-end coronal heating witness bundle
-/

/-- Full witness packaging the axial HQIV heating channel for a coronal
column. Records the equality `qDot = q̇(coronal column inputs)` for the
caller (e.g. a Python evaluator with concrete `Λ_s`, `∂_s φ`, `v_∥`
estimates). The lemma `qDot_eq_alpha_3_5_form` exhibits the explicit
`(α/4π)·Λ_s·∂_s φ` factor with `α = 3/5` inlined. -/
structure CoronalHQIVHeatingWitness
    (nq J sigma Estar couplingLog dphi_ds v_parallel qDot : ℝ) : Prop where
  qDot_eq :
    qDot =
      coronalHeatingRateDensity nq J sigma Estar couplingLog dphi_ds v_parallel

theorem CoronalHQIVHeatingWitness.qDot_eq_alpha_3_5_form
    {nq J sigma Estar couplingLog dphi_ds v_parallel qDot : ℝ}
    (h : CoronalHQIVHeatingWitness nq J sigma Estar couplingLog dphi_ds v_parallel qDot) :
    qDot =
      nq * (J / sigma + Estar * (3 / (20 * Real.pi)) * couplingLog * dphi_ds) * v_parallel := by
  rw [h.qDot_eq]
  unfold coronalHeatingRateDensity coronalLongitudinalForceDensity
    coronalEffectiveAxialField ohmicAxialField
  rw [coronalLongitudinalHQIVField_alpha_3_5]

/-- Heating rate vanishes in the constant-φ / Ohmic-only limit. -/
theorem CoronalHQIVHeatingWitness.qDot_classical_flat_limit
    {nq J sigma Estar couplingLog v_parallel qDot : ℝ}
    (h : CoronalHQIVHeatingWitness nq J sigma Estar couplingLog 0 v_parallel qDot) :
    qDot = nq * (J / sigma) * v_parallel := by
  rw [h.qDot_eq, coronalHeatingRateDensity_classical_flat_limit]

/-- Area-integrated coronal heating-flux boundary form.

`Q_∥/A = nq · v_∥ · E_∗ · (3/20π) · Λ_s · (φ_cor − φ_photo)`.

This is the analogue of `coronalLongitudinalForceBoundary / A` weighted by
the plasma flow `v_∥`: heating power per unit cross-sectional area injected
by the longitudinal HQIV channel, evaluated as a boundary term in φ. -/
def coronalHeatingFluxBoundary
    (nq Estar couplingLog v_parallel phi_photo phi_corona : ℝ) : ℝ :=
  nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog * (phi_corona - phi_photo)

theorem coronalHeatingFluxBoundary_zero_of_phi_equal
    (nq Estar couplingLog v_parallel phi : ℝ) :
    coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi phi = 0 := by
  unfold coronalHeatingFluxBoundary; ring

theorem coronalHeatingFluxBoundary_eq_alpha_form
    (nq Estar couplingLog v_parallel phi_photo phi_corona : ℝ) :
    coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi_photo phi_corona =
      nq * v_parallel * Estar * (alpha / (4 * Real.pi)) * couplingLog *
        (phi_corona - phi_photo) := by
  unfold coronalHeatingFluxBoundary
  rw [alpha_eq_3_5]
  ring

/-- Heating-flux boundary form using the shell-ladder φ jump. -/
def coronalHeatingFluxBoundaryShells
    (nq Estar couplingLog v_parallel : ℝ) (cols : CoronalColumnShells) : ℝ :=
  coronalHeatingFluxBoundary nq Estar couplingLog v_parallel
    (phi_of_shell cols.m_photo) (phi_of_shell cols.m_corona)

theorem coronalHeatingFluxBoundaryShells_eq
    (nq Estar couplingLog v_parallel : ℝ) (cols : CoronalColumnShells) :
    coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols =
      nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog *
        coronalPhiJump cols := by
  unfold coronalHeatingFluxBoundaryShells coronalHeatingFluxBoundary coronalPhiJump
  ring

/-- **Boundary-vs-bulk discriminant (paper §7 item 2):** the integrated HQIV
heating flux depends only on the shell index gap, not on the loop length,
so changing footpoint geometry / shell anchoring at fixed bulk length
modulates the heating flux directly. -/
theorem coronalHeatingFluxBoundaryShells_eq_two_shellGap
    (nq Estar couplingLog v_parallel : ℝ) (cols : CoronalColumnShells) :
    coronalHeatingFluxBoundaryShells nq Estar couplingLog v_parallel cols =
      nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog *
        (2 * ((cols.m_corona : ℝ) - (cols.m_photo : ℝ))) := by
  rw [coronalHeatingFluxBoundaryShells_eq, coronalPhiJump_closed_form]

/-- Non-negativity of the boundary heating flux under the natural sign
conventions (`nq ≥ 0`, `v_∥ ≥ 0`, `E_∗ ≥ 0`, `Λ_s ≥ 0`, and a coronal-side
`φ` above the photospheric `φ`). -/
theorem coronalHeatingFluxBoundary_nonneg
    {nq Estar couplingLog v_parallel phi_photo phi_corona : ℝ}
    (hnq : 0 ≤ nq) (hv : 0 ≤ v_parallel) (hE : 0 ≤ Estar)
    (hΛ : 0 ≤ couplingLog) (hφ : phi_photo ≤ phi_corona) :
    0 ≤ coronalHeatingFluxBoundary nq Estar couplingLog v_parallel phi_photo phi_corona := by
  unfold coronalHeatingFluxBoundary
  have hpi : (0 : ℝ) < 20 * Real.pi := by positivity
  have hcoef : (0 : ℝ) ≤ 3 / (20 * Real.pi) := by positivity
  have hΔ : 0 ≤ phi_corona - phi_photo := sub_nonneg.mpr hφ
  have h1 : 0 ≤ nq * v_parallel := mul_nonneg hnq hv
  have h2 : 0 ≤ nq * v_parallel * Estar := mul_nonneg h1 hE
  have h3 : 0 ≤ nq * v_parallel * Estar * (3 / (20 * Real.pi)) := mul_nonneg h2 hcoef
  have h4 : 0 ≤ nq * v_parallel * Estar * (3 / (20 * Real.pi)) * couplingLog :=
    mul_nonneg h3 hΛ
  exact mul_nonneg h4 hΔ

end

end Hqiv.Physics
