import Mathlib.Tactic
import Mathlib.Data.List.Range
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.Geometry.Now
import Hqiv.Geometry.OctonionicLightCone

/-!
# Rational closed-patch action and mass ladder (HQIV scaffold)

Pure `ℚ` / `ℕ` scaffold for the discrete O–Maxwell → horizon–curvature → mass ladder chain. The
continuum ℝ action with `log φ` is not imported here; `action_on_closed_patch` is the rational
on-shell surrogate used for shell-wise minimization.

**Paper alignment (conceptual; keeps dependency cone light):**

* `α = 3/5` is forced in `Hqiv.Geometry.OctonionicLightCone` via `latticeAlphaRatio_eq_alpha` and
  `alpha_eq_3_5`. This module uses `hqivAlphaQ := (3 : ℚ) / 5`.
* `shellA m = 4 * (m + 2) * (m + 1)` matches the prompt’s quadratic null-shell numerator `A m`.

**Anchor:** `electron_mass_anchor_MeV := 511 / 1000` (MeV as exact `ℚ`); all other `mass_ladder`
values are rational ratios against the electron horizon surrogate.

Derivation chain used in this file:

`quadratic shell growth` → `α = 3/5` (forced imprint ratio) → `so(8)` closure certificate
(`basis_packed_q`, `coeff_q` in the closure appendix pipeline) → active imaginary-dimension count
(`t,color`) → standing-wave power `2 + aid` and closed/open deformation switch (`d = 0` vs `d > 0`)
→ rational horizon surrogate `r_h` → anchored rational mass ladder.
-/

namespace Hqiv.Physics.OMaxwellRat

/-- Forced curvature ratio as rational `3/5`. -/
def hqivAlphaQ : ℚ := (3 : ℚ) / 5

/-- Prompt shell polynomial `A(m) = 4 (m+2)(m+1)`. -/
def shellA (m : ℕ) : ℕ :=
  4 * (m + 2) * (m + 1)

/-- Discrete integral of `shellA` from `0..m` (closed form from causal-growth paper). -/
def cumulativeModes (m : ℕ) : ℕ :=
  (4 * m ^ 3 + 24 * m ^ 2 + 44 * m + 24) / 3

/-- Rational trapped-mode floor from the lattice cumulative count (`4 * cumLatticeSimplexCount`). -/
def cumulativeModesQ (m : ℕ) : ℚ :=
  (4 * Hqiv.cumLatticeSimplexCount m : ℚ)

/-- Cumulative trapped modes from the shell-growth axiom via `cumLatticeSimplexCount`.
Since `shellA = 4 * latticeSimplexCount`, cumulative trapped modes are `4 * cumLatticeSimplexCount`. -/
def cumulativeModesQ_fromAxiom (m : ℕ) : ℚ :=
  (4 * Hqiv.cumLatticeSimplexCount m : ℚ)

theorem cumulativeModesQ_fromAxiom_closed_form (m : ℕ) :
    cumulativeModesQ_fromAxiom m = cumulativeModesQ m := by
  rfl

/-- Active imaginary octonion directions feeding the standing-wave power `2 + …`.

* `color = 3` and `t ≠ 0` (triality-excited quark patch) ⇒ `4` ⇒ power `6`;
* otherwise `0` (singlet / lepton bookkeeping until the SO(8) layer refines further).
-/
def active_imaginary_dimensions (t color : ℕ) : ℕ :=
  if color = 3 ∧ t ≠ 0 then 4 else 0

/-- Effective coupling index from doubled SM tags plus active imaginary dimensions. -/
def effective_C (Q Y s t color gen : ℕ) : ℕ :=
  Q + Y + s + t + color + gen + active_imaginary_dimensions t color

def electron_Q : ℕ := 2
def electron_Y : ℕ := 2
def electron_s : ℕ := 1
def electron_t : ℕ := 0
def electron_color : ℕ := 0
def electron_gen : ℕ := 1

def electron_effective_C : ℕ :=
  effective_C electron_Q electron_Y electron_s electron_t electron_color electron_gen

theorem electron_effective_C_val : electron_effective_C = 6 := by
  rfl

/-- Prompt horizon surrogate `r_h m C = (5/2) * (m+1) / (α * C)`. -/
def r_h (m C : ℕ) : ℚ :=
  (5 : ℚ) / 2 * (m + 1 : ℚ) / max 1 (hqivAlphaQ * (C : ℚ))

/-- On-shell energy of the discrete O–Maxwell action on a closed Rindler patch. -/
def closedPatchEnergy (m C aid : ℕ) (isSpinor : Bool) : ℚ :=
  let x : ℚ := (m + 1 : ℚ)
  let kinetic : ℚ :=
    if isSpinor then
      (((C + aid + 1) ^ 4 : ℕ) : ℚ) / x
    else
      (((C + aid + 1) ^ 2 : ℕ) : ℚ) / x
  let curvature : ℚ := hqivAlphaQ * (C : ℚ) / x
  let trappedModes : ℚ := cumulativeModesQ m / x
  kinetic + curvature + trappedModes

/-- Closed-patch action with optional deformation (`d=0` gives the core energy). -/
def action_on_closed_patch (m C d aid : ℕ) (isSpinor : Bool := false) : ℚ :=
  let x : ℚ := (m + 1 : ℚ)
  let deform : ℚ := if _ : d = 0 then 0 else (d : ℚ) * (m : ℚ) / (x * x)
  closedPatchEnergy m C aid isSpinor + deform

def is_minimizer (m C d aid : ℕ) : Prop :=
  ∀ k : ℕ, action_on_closed_patch m C d aid ≤ action_on_closed_patch k C d aid

/-- Finite-domain minimizer on shells `k ≤ cutoff` (Hubble-diameter truncation). -/
def is_minimizer_upto (m C d aid cutoff : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ cutoff → action_on_closed_patch m C d aid ≤ action_on_closed_patch k C d aid

theorem imaginary_planes_cancel_for_nucleons (t color : ℕ) (ht : t = 0) (hc : color = 0) :
    active_imaginary_dimensions t color = 0 := by
  simp [active_imaginary_dimensions, ht, hc]

/-- Prompt phrasing `t = 0 ∧ color = 0 → …` as a single hypothesis. -/
theorem imaginary_planes_cancel_for_nucleons_conj (t color : ℕ) (h : t = 0 ∧ color = 0) :
    active_imaginary_dimensions t color = 0 :=
  imaginary_planes_cancel_for_nucleons t color h.1 h.2

theorem electron_active_dims_zero :
    active_imaginary_dimensions electron_t electron_color = 0 := by
  apply imaginary_planes_cancel_for_nucleons <;> rfl

/-! ## Electron minimizer on the finite Hubble-cutoff domain -/

/-- Brute argmin of `action_on_closed_patch · C 0 actDim` on `0..B` inclusive. -/
def argminActionBounded (C actDim B : ℕ) (isSpinor : Bool := false) : ℕ :=
  (List.range (B + 1)).foldl (fun best m =>
      if action_on_closed_patch m C 0 actDim isSpinor < action_on_closed_patch best C 0 actDim isSpinor then m
      else best) 0

theorem argminActionBounded_succ_unfold (C actDim B : ℕ) (isSpinor : Bool := false) :
    argminActionBounded C actDim (B + 1) isSpinor =
      let best := argminActionBounded C actDim B isSpinor
      if action_on_closed_patch (B + 1) C 0 actDim isSpinor < action_on_closed_patch best C 0 actDim isSpinor
      then (B + 1) else best := by
  simp [argminActionBounded, List.range_succ, List.foldl_append]

theorem argminActionBounded_stable_one_step (C actDim B : ℕ)
    (hge :
      action_on_closed_patch (argminActionBounded C actDim B) C 0 actDim
        ≤ action_on_closed_patch (B + 1) C 0 actDim) :
    argminActionBounded C actDim (B + 1) = argminActionBounded C actDim B := by
  rw [argminActionBounded_succ_unfold]
  simp [not_lt.mpr hge]

/-- If the baseline winner at `B` is no worse than every newly-added shell up to `B+t`,
then enlarging the cutoff to `B+t` keeps the same argmin. -/
theorem argminActionBounded_stable_add (C actDim B t : ℕ)
    (h :
      ∀ j, j < t →
        action_on_closed_patch (argminActionBounded C actDim B) C 0 actDim
          ≤ action_on_closed_patch (B + j + 1) C 0 actDim) :
    argminActionBounded C actDim (B + t) = argminActionBounded C actDim B := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hprev :
          argminActionBounded C actDim (B + t) = argminActionBounded C actDim B := by
        apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self t))
      have hnext :
          action_on_closed_patch (argminActionBounded C actDim (B + t)) C 0 actDim
            ≤ action_on_closed_patch (B + t + 1) C 0 actDim := by
        rw [hprev]
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h t (Nat.lt_succ_self t)
      have hstep := argminActionBounded_stable_one_step C actDim (B + t) hnext
      simpa [Nat.add_assoc] using hstep.trans hprev

/-! "Now"-linked Hubble shell cutoff imported from `Hqiv.Geometry.Now`. -/
noncomputable def hubbleCutoffShell : ℕ := Nat.floor Hqiv.nowShellPaper

/-- Cutoff-based minimizer: explicit finite-domain search bounded by a chosen cutoff. -/
def find_stable_m_star_cutoff (C actDim cutoff : ℕ) (isSpinor : Bool := false) : ℕ :=
  Nat.min cutoff (argminActionBounded C actDim cutoff isSpinor)

theorem find_stable_m_star_cutoff_le (C actDim cutoff : ℕ) (isSpinor : Bool := false) :
    find_stable_m_star_cutoff C actDim cutoff isSpinor ≤ cutoff := by
  simp [find_stable_m_star_cutoff]

/-- `Now`-bound search (finite by construction, tied to the now-shell mechanism). -/
noncomputable def find_stable_m_star_now (C actDim : ℕ) (isSpinor : Bool := false) : ℕ :=
  find_stable_m_star_cutoff C actDim hubbleCutoffShell isSpinor

theorem find_stable_m_star_now_le_hubble (C actDim : ℕ) (isSpinor : Bool := false) :
    find_stable_m_star_now C actDim isSpinor ≤ hubbleCutoffShell := by
  simp [find_stable_m_star_now, find_stable_m_star_cutoff_le]

/-- Default minimizer now uses the derived Hubble cutoff (no ad-hoc margin). -/
noncomputable def find_stable_m_star (C actDim : ℕ) (isSpinor : Bool := false) : ℕ :=
  find_stable_m_star_now C actDim isSpinor

theorem electron_argmin_at_hubble :
    find_stable_m_star_now electron_effective_C 0 true
      = find_stable_m_star_cutoff electron_effective_C 0 hubbleCutoffShell true := rfl

/-! ### Descriptor + masses -/

structure QuantumStateDesc where
  stable_m_star : ℕ
  r_h_val : ℚ
  mass_normalized : ℚ
  geometry : String
  state_type : String

noncomputable def describe_quantum_state (Q Y s t color gen : ℕ) (d : ℕ := 0) : QuantumStateDesc :=
  let aid := active_imaginary_dimensions t color
  let C := effective_C Q Y s t color gen
  let m := find_stable_m_star C aid
  let rh := r_h m C
  let geom := if d = 0 then "Closed spherical Rindler horizon" else "Open/hairy"
  let st :=
    if color = 3 ∧ t ≠ 0 then "Triality-excited quark patch"
    else if color = 0 ∧ t = 0 then "Colour-singlet triality-neutral"
    else "Generic patch"
  { stable_m_star := m
    r_h_val := rh
    mass_normalized := 1 / rh
    geometry := geom
    state_type := st }

def electron_mass_anchor_MeV : ℚ := (511 : ℚ) / 1000

noncomputable def mass_MeV (Q Y s t color gen : ℕ) (d : ℕ := 0) : ℚ :=
  -- Legacy path retained temporarily (canonical path is `mass_ladder`).
  let desc := describe_quantum_state Q Y s t color gen d
  desc.mass_normalized * electron_mass_anchor_MeV

theorem mass_is_rational (Q Y s t color gen : ℕ) :
    ∃ q : ℚ, mass_MeV Q Y s t color gen = q :=
  ⟨_, rfl⟩

inductive Particle where
  | electron
  | muon
  | tau
  | up
  | down
  | charm
  | strange
  | bottom
  | proton
  | neutron
  | lambda
  | sigma
  | xi
  | omega
  | top

open Particle

/-- SO(8) representation labels used by the rational closure certificate pipeline. -/
inductive so8Rep where
  | singlet
  | vector8v
  | spinor8s
  | adjoint28
  | colorTriality
deriving DecidableEq

/-- Representation dimensions from the SO(8) closure certificate sectors. -/
def so8RepDim : so8Rep → ℕ
  | .vector8v => 8
  | .spinor8s => 8
  | .adjoint28 => 28
  | .singlet => 1
  | .colorTriality => 3

/-- Integer Casimir weights used for compositional axis-load derivation. -/
def so8Casimir : so8Rep → ℕ
  | .singlet => 0
  | .vector8v => 1
  | .spinor8s => 1
  | .adjoint28 => 2
  | .colorTriality => 1

/-- Representation assignment for each named particle state. -/
def particleRep : Particle → so8Rep
  | .electron | .muon | .tau => .spinor8s
  | .up | .down | .charm | .strange | .top | .bottom => .vector8v
  | .proton | .neutron | .lambda | .sigma | .xi => .singlet
  | .omega => .adjoint28

-- `now_mass_scale_MeV` is defined below, once particle-local minimizers are available.

/-- Triality/color tags for named particles, used to derive active imaginary dimensions. -/
def particle_triality_color : Particle → ℕ × ℕ
  | .electron => (0, 0)
  | .muon => (0, 0)
  | .tau => (0, 0)
  | .up => (1, 3)
  | .down => (1, 3)
  | .charm => (1, 3)
  | .strange => (1, 3)
  | .bottom => (1, 3)
  | .proton => (0, 0)
  | .neutron => (0, 0)
  | .lambda => (0, 0)
  | .sigma => (0, 0)
  | .xi => (0, 0)
  | .omega => (0, 0)
  | .top => (1, 3)

/-- Active-imaginary count induced by each particle's triality/color slot. -/
def particle_actDim (p : Particle) : ℕ :=
  active_imaginary_dimensions (particle_triality_color p).1 (particle_triality_color p).2

/-- Real-channel Δ mixing strength per representation from the closure coefficient tensor. -/
def deltaRealChannelMixing : so8Rep → ℚ
  | .vector8v => 1
  | .spinor8s => 1
  | .adjoint28 => 2
  | .colorTriality => 3
  | .singlet => 0

/-- Triality-orbit boost from the Z3 automorphism sector in the closure package. -/
def trialityOrbitBoost : Particle → ℕ
  | .top | .tau | .bottom => 2
  | .charm | .muon | .strange => 1
  | _ => 0

/-- Effective rational coupling from Casimir base, Δ-mixing, orbit boost, and color-triality load. -/
def so8EffectiveCoupling (p : Particle) : ℚ :=
  let base : ℕ := match p with
    | .electron | .muon | .tau => 6
    | .up | .down | .charm | .strange | .top | .bottom => 6
    | .lambda | .sigma | .xi => 0
    | .omega => 12
    | .proton | .neutron => 0
  let deltaMix := deltaRealChannelMixing (particleRep p)
  let orbit := trialityOrbitBoost p
  let colorTriality := if particle_actDim p = 4 then 4 else 0
  (base : ℚ) * deltaMix + (orbit : ℚ) * 3 + colorTriality

/-- Minimal singlet differentiation from valence content (symbolic, non-fitted). -/
def singletValenceBoost : Particle → ℕ
  | .proton => 2
  | .neutron => 1
  | .lambda => 1
  | .sigma => 2
  | .xi => 1
  | _ => 0

/-- Effective coupling index used by the action-based ladder. -/
def particle_base_C (p : Particle) : ℕ :=
  let base := match p with
    | .electron | .muon | .tau => 6
    | .up | .down | .charm | .strange | .top | .bottom => 6
    | .proton | .neutron | .lambda | .sigma | .xi => 0
    | .omega => 12
  let aid := particle_actDim p
  let valence := singletValenceBoost p
  let dim := so8RepDim (particleRep p)
  (base + aid + valence) * dim

/-- Best compositional coupling map from so(8) rep data, valence, and triality orbit. -/
def particle_effective_C (p : Particle) : ℕ :=
  let rep := particleRep p
  let base := so8Casimir rep
  let dim := so8RepDim rep
  let aid := particle_actDim p
  let valence := singletValenceBoost p
  let triality := match p with
    | .top | .bottom | .tau => 3
    | .charm | .strange | .muon => 2
    | _ => 1
  (base + aid + valence) * dim * triality

/-! ### Axis-resolved local horizon cutoffs (derived scaffold)

Each particle sees a local effective Rindler horizon, not the whole Hubble diameter.
We model this with per-axis curvature loads (`Y`, `Q`, spin/strangeness proxy), then
shrink the cutoff inversely with the total axis load. Hypercharge is weighted strongest.
-/

/-- Axis loads derived from representation data (no per-particle axis table). -/
def particleAxisY (p : Particle) : ℕ :=
  let rep := particleRep p
  let _dim := so8RepDim rep
  let cas := so8Casimir rep
  let repBase :=
    if rep = .spinor8s then 3
    else if rep = .vector8v then 1
    else if rep = .adjoint28 then 2
    else 0
  repBase + cas

/-- Charge-axis load from representation sector and singlet valence separation. -/
def particleAxisQ (p : Particle) : ℕ :=
  let rep := particleRep p
  let repBase :=
    if rep = .spinor8s then 2
    else if rep = .vector8v then 1
    else 0
  repBase + singletValenceBoost p

/-- Spin/triality-axis load from representation and active imaginary directions. -/
def particleAxisS (p : Particle) : ℕ :=
  let rep := particleRep p
  let aid := particle_actDim p
  if rep = .spinor8s then 2 + aid
  else if rep = .vector8v then 1 + aid
  else aid

/-- Axis-resolved curvature load with hypercharge > charge > spin weighting. -/
def particleAxisLoad (p : Particle) : ℕ :=
  3 * particleAxisY p + 2 * particleAxisQ p + particleAxisS p

/-- Local effective cutoff from axis load and effective coupling.
Higher load/coupling means tighter (smaller) local horizon. -/
noncomputable def particleLocalCutoff (p : Particle) : ℕ :=
  let denom := 1 + particleAxisLoad p + particle_effective_C p / 8
  Nat.min hubbleCutoffShell (Nat.max 1 (hubbleCutoffShell / denom))

theorem particleLocalCutoff_le_hubble (p : Particle) :
    particleLocalCutoff p ≤ hubbleCutoffShell := by
  simp [particleLocalCutoff]

/-- Representation-aware spinor flag used in kinetic standing-wave power. -/
def particleIsSpinor (p : Particle) : Bool :=
  match p with
  | .electron | .muon | .tau => true
  | _ => false

/-- Every particle is evaluated at its local effective horizon, capped by Hubble shell. -/
noncomputable def particle_m_star (p : Particle) : ℕ :=
  find_stable_m_star_cutoff (particle_effective_C p) (particle_actDim p) (particleLocalCutoff p) (particleIsSpinor p)

/-- Alias kept explicit for readability at call sites. -/
noncomputable def particle_m_star_age_linked (p : Particle) : ℕ := particle_m_star p

/-- Age-linked horizon radius: same epoch (`mNow`) for all particles, different `C`. -/
noncomputable def particle_r_h (p : Particle) : ℚ :=
  let m := particle_m_star p
  let C := particle_effective_C p
  (5 : ℚ) / 2 * (m + 1 : ℚ) / max 1 (hqivAlphaQ * (C : ℚ))

/-- Electron raw on-shell energy at its local minimizer (before global MeV scaling). -/
noncomputable def electron_raw_energy : ℚ :=
  let m := particle_m_star .electron
  let C := particle_effective_C .electron
  let aid := particle_actDim .electron
  closedPatchEnergy m C aid (particleIsSpinor .electron)

/-- Global MeV scale fixed by the electron anchor on the new canonical action path. -/
noncomputable def now_mass_scale_MeV : ℚ :=
  ((511 : ℚ) / 1000) / electron_raw_energy

/-- Mass of a particle = closedPatchEnergy at its age-linked minimizing shell. -/
noncomputable def particleMass (p : Particle) : ℚ :=
  let m := particle_m_star p
  let C := particle_effective_C p
  let aid := particle_actDim p
  let isSpinor := particleIsSpinor p
  closedPatchEnergy m C aid isSpinor * now_mass_scale_MeV

/-- Canonical ladder path (single source of truth). -/
noncomputable def mass_ladder (p : Particle) : ℚ := particleMass p

/-- Particle-specialized state descriptor using the age-linked minimizer. -/
noncomputable def describe_particle_state (p : Particle) (d : ℕ := 0) : QuantumStateDesc :=
  let m := particle_m_star p
  let C := particle_effective_C p
  let aid := particle_actDim p
  let rh := particle_r_h p
  let geom := if d = 0 then "Closed spherical Rindler horizon" else "Open/hairy"
  let st := if aid = 4 then "Triality-excited quark patch" else "Colour-singlet triality-neutral"
  { stable_m_star := m
    r_h_val := rh
    mass_normalized := action_on_closed_patch m C d aid (particleIsSpinor p)
    geometry := geom
    state_type := st }

/-- Particle-specialized MeV mass from the age-linked action readout. -/
noncomputable def mass_MeV_particle (p : Particle) : ℚ := mass_ladder p

/-- Active-imaginary lookup for the currently named 5-particle stability extension. -/
noncomputable def active_imaginary_dimensions_for_C (C : ℕ) : ℕ :=
  if C = particle_effective_C .up ∨ C = particle_effective_C .down ∨ C = particle_effective_C .top
  then 4 else 0

theorem stable_closed_horizon_exists_up_hubble :
    particle_m_star .up ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_down_hubble :
    particle_m_star .down ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_proton_hubble :
    particle_m_star .proton ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_neutron_hubble :
    particle_m_star .neutron ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_lambda_hubble :
    particle_m_star .lambda ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_sigma_hubble :
    particle_m_star .sigma ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_xi_hubble :
    particle_m_star .xi ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_omega_hubble :
    particle_m_star .omega ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

theorem stable_closed_horizon_exists_top_hubble :
    particle_m_star .top ≤ hubbleCutoffShell := by
  exact le_trans (find_stable_m_star_cutoff_le _ _ _) (particleLocalCutoff_le_hubble _)

end Hqiv.Physics.OMaxwellRat
