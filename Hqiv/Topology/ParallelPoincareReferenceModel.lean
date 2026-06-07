import Mathlib.Data.Real.Basic

import Hqiv.Topology.ParallelPoincareScaffold

/-!
# Reference model: template-pinned flow on `S3NullReference`

Sanity check: the **template track** of discrete parallel Poincaré is fully proved on
template-pinned evolution at `S3NullReference n`. The **χ track** is obstructed on the
vertex-only reference (see `reference_chi_obstructed`).

**Note:** `step = none` off the template class, so there is no `RealLyapunovDescent` with
strict `some`-steps; termination is supplied directly as `flowTerminates`.
-/

namespace Hqiv.Topology

open Hqiv RhFourierLift Classical

/-- Evolution that fixes template states and pinches off-template complexes. -/
noncomputable def templatePinnedStep (n : ℕ) (M : Discrete3Complex NullShellVertex) :
    Option (Discrete3Complex NullShellVertex) :=
  if IsS3NullVertexTemplate M n then some M else none

noncomputable def templatePinnedEvolution (n : ℕ) (α : ℝ) (href : 0 < K n α) :
    DiscreteCurvatureEvolution where
  α := α
  mStar := n
  href := href
  step := templatePinnedStep n
  lyapunov_nonincreasing := by
    intro M
    by_cases h : IsS3NullVertexTemplate M n
    · simp [templatePinnedStep, h, le_refl]
    · simp [templatePinnedStep, h]

theorem templatePinned_equilibrium_iff (n : ℕ) (α : ℝ) (href : 0 < K n α)
    (M : Discrete3Complex NullShellVertex) :
    (templatePinnedEvolution n α href).IsEquilibrium M ↔ IsS3NullVertexTemplate M n := by
  unfold DiscreteCurvatureEvolution.IsEquilibrium templatePinnedEvolution templatePinnedStep
  by_cases h : IsS3NullVertexTemplate M n <;> simp [h]

theorem templatePinned_step_s3 (n : ℕ) (α : ℝ) (href : 0 < K n α) :
    (templatePinnedEvolution n α href).step (S3NullReference n) = some (S3NullReference n) := by
  simp [templatePinnedEvolution, templatePinnedStep, S3NullReference_is_template n]

theorem templatePinned_iterate_some (n : ℕ) (α : ℝ) (href : 0 < K n α) (k : ℕ) :
    (templatePinnedEvolution n α href).iterate k (S3NullReference n) = some (S3NullReference n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [DiscreteCurvatureEvolution.iterate_succ_of_step (templatePinnedEvolution n α href) k
      (S3NullReference n) (S3NullReference n) (templatePinned_step_s3 n α href)]
    exact ih

theorem templatePinned_terminates (n : ℕ) (α : ℝ) (href : 0 < K n α) :
    FlowTerminatesAt (templatePinnedEvolution n α href) (S3NullReference n) :=
  ⟨0, Or.inr ⟨S3NullReference n, templatePinned_iterate_some n α href 0,
    (templatePinned_equilibrium_iff n α href (S3NullReference n)).mpr
      (S3NullReference_is_template n)⟩⟩

def referenceSO8Admissible (_n : ℕ) (M : Discrete3Complex NullShellVertex) :
    SO8AdmissibleHolonomy M where
  fields_g2_delta_recoverable := True
  uses_six_pack_middle_chart := True
  two_e1_e4_rotations := True
  triality_three_slots := True
  diophantine_phase_readout := True
  delta_resolves_pinched_links := True
  bracket_closure_symbolic := so8_bracket_closure_symbolic

noncomputable def referenceCurvatureChannel (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    UsesCurvatureChannel (templatePinnedEvolution n (1 : ℝ) href) where
  positive_coupling := by simp [templatePinnedEvolution]
  hqiv_step := { step_eq := rfl }
  phase_readout_eq_omega := fun _ => rfl
  delta_suture_antisymmetric := delta_antisymmetric

/-- Proved template certificate (no χ field). -/
noncomputable def referenceTemplateCertificate (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    ParallelPoincareTemplateCertificate (templatePinnedEvolution n (1 : ℝ) href)
      (S3NullReference n) n where
  growth := S3NullReference_quadratic_on_horizon n
  holonomy := referenceSO8Admissible n (S3NullReference n)
  extinction_excluded := fun k => by
    rw [templatePinned_iterate_some n (1 : ℝ) href k]
    intro hnone
    cases hnone
  equilibrium_template heq :=
    (templatePinned_equilibrium_iff n (1 : ℝ) href (S3NullReference n)).mp heq
  terminal_eq k M' hiter _heq := by
    rw [templatePinned_iterate_some n (1 : ℝ) href k] at hiter
    exact Option.some.inj hiter.symm

theorem reference_chi_obstructed (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    ¬ ∃ cert : ParallelPoincareChiCertificate (templatePinnedEvolution n (1 : ℝ) href)
        (S3NullReference n) n, True := by
  rintro ⟨cert, _⟩ 
  have heq := (templatePinned_equilibrium_iff n (1 : ℝ) href (S3NullReference n)).mpr
    (S3NullReference_is_template n)
  exact S3NullReference_not_combinatorially_spherical n (cert.equilibrium_chi_zero _ heq)

noncomputable def referenceParallelPoincareHypothesis (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    DiscreteParallelPoincareHypothesis where
  evo := templatePinnedEvolution n (1 : ℝ) href
  data := {
    M := S3NullReference n
    no_boundary := by intro e he; simp [S3NullReference] at he
    maxShell := n
    quadraticGrowthOnHorizon := S3NullReference_quadratic_on_horizon n
    so8Admissible := referenceSO8Admissible n (S3NullReference n)
  }
  curvatureChannel := referenceCurvatureChannel n href
  flowTerminates := templatePinned_terminates n (1 : ℝ) href
  templateCertificate := referenceTemplateCertificate n href

theorem discrete_parallel_poincare_reference (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    ∃ k M',
      (templatePinnedEvolution n (1 : ℝ) href).iterate k (S3NullReference n) = some M' ∧
        IsS3NullVertexTemplate M' n :=
  discrete_parallel_poincare (referenceParallelPoincareHypothesis n href)

theorem parallel_poincare_template_track_live (n : ℕ) (href : 0 < K n (1 : ℝ)) :
    ∃ H : DiscreteParallelPoincareHypothesis,
      ∃ k M', H.evo.iterate k H.data.M = some M' ∧ IsS3NullVertexTemplate M' n :=
  ⟨referenceParallelPoincareHypothesis n href, discrete_parallel_poincare_reference n href⟩

theorem parallel_poincare_chi_track_obstructed_on_reference (n : ℕ) :
    ¬ IsCombinatoriallySpherical (S3NullReference n) :=
  S3NullReference_not_combinatorially_spherical n

end Hqiv.Topology
