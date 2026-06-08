import Mathlib.Data.Real.Basic

import Hqiv.Geometry.SATRapidityDirectionSelection

/-!
# SAT rapidity gap bridge

This file is the explicit "prove the bridge" step: it packages the remaining
geometric/combinatorial obligation as a single hypothesis record showing that
the rapidity gap itself controls the direction-selection layer.

The philosophy is the same as elsewhere in the repo:

- do not overclaim the final theorem,
- isolate the exact bridge assumptions,
- prove the strongest downstream consequence once those assumptions are given.
-/

namespace Hqiv.Geometry

noncomputable section

/--
Single-record bridge from a rapidity gap to canonical direction selection.

This is the formal place where the remaining work now lives.
-/
structure SATRapidityGapBridge (M : Type*) where
  shared : SATSharedManifold M
  residuals : List (SATResidual M)
  threshold : ℝ
  annulusModel : LocalShellAnnulusModel
  residualPoint : SATResidual M → ResidualPoint M
  canonicalDir : SATResidual M → UnitVector shared.rapiditySphere
  effectiveDim : ℕ
  logBoundConst : ℕ
  sphereCodeBound : ℕ → ℝ
  /-- Gap-to-direction hypothesis: every residual admits a shell-intersection realization. -/
  hDirRealization :
    ∀ r : SATResidual M,
      ∃ I : ShellIntersectionSet M,
        I = localShellIntersections shared annulusModel (residualPoint r)
  /-- Distinct residual points induce distinct canonical directions. -/
  hDistinctDir :
    ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂
  /-- The rapidity gap / annulus width enforces minimum angular separation. -/
  hMinAngle :
    ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0
  /-- Geometric collapse: effective dimension is logarithmic in combined size. -/
  hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1)
  /-- Packing/counting bound at the collapsed dimension. -/
  hSphereLen : (residuals.length : ℝ) ≤ sphereCodeBound effectiveDim

/--
The gap bridge yields the direction-selection certificate directly.
-/
def SATRapidityGapBridge.toDirectionSelectionCertificate
    {M : Type*}
    (G : SATRapidityGapBridge M) :
    DirectionSelectionCertificate M where
  shared := G.shared
  residuals := G.residuals
  threshold := G.threshold
  annulusModel := G.annulusModel
  residualPoint := G.residualPoint
  canonicalDir := G.canonicalDir
  distinctDirs := G.hDistinctDir
  minAngleFromTip := G.hMinAngle
  effectiveDim := G.effectiveDim
  logBoundConst := G.logBoundConst
  hEffectiveDim := G.hEffectiveDim
  sphereCodeBound := G.sphereCodeBound
  hSphereLen := G.hSphereLen

/-!
### Scaffold-level discharges

With the current definitions, `localShellIntersections` is a named function and
`angle` is a placeholder constant; the existential in `hDirRealization` and the
nonnegativity in `hMinAngle` are therefore provable without further geometry.

The obligations that still require a nontrivial mathematical argument in a
future refinement are: injectivity of `canonicalDir` on the residual list,
logarithmic `effectiveDim`, and the sphere-code length bound.

The lemmas below shrink that story: injective `canonicalDir` discharges
`hDistinctDir`; choosing `effectiveDim` equal to the log-compression discharges
`hEffectiveDim`; empty residuals discharge the pairwise hypotheses vacuously; the
sphere-code inequality is still an explicit input unless a bound is derived from
geometry.
-/

theorem exists_eq_localShellIntersections
    {M : Type*} (S : SATSharedManifold M) (A : LocalShellAnnulusModel) (p : ResidualPoint M) :
    ∃ I : ShellIntersectionSet M, I = localShellIntersections S A p :=
  ⟨_, rfl⟩

theorem angle_nonneg_of_scaffold
    {M : Type*} (S : SATSharedManifold M) (u v : UnitVector S.rapiditySphere) :
    angle S u v ≥ 0 := by
  simp [angle]

/-- Canonical “log-collapsed” effective dimension used in `hEffectiveDim`. -/
def defaultLogCollapsedEffectiveDim {M : Type*} (shared : SATSharedManifold M) (logBoundConst : ℕ) :
    ℕ :=
  logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1)

theorem defaultLogCollapsedEffectiveDim_le (shared : SATSharedManifold M) (logBoundConst : ℕ) :
    defaultLogCollapsedEffectiveDim shared logBoundConst ≤
      logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1) :=
  le_rfl

/--
If `canonicalDir` is injective on `ℕ`, distinct residuals in the list have distinct
directions. This is the usual algebraic sufficient condition for `hDistinctDir`.
-/
theorem hDistinctDir_of_injective {M : Type*} {shared : SATSharedManifold M}
    {residuals : List (SATResidual M)} {canonicalDir : SATResidual M → UnitVector shared.rapiditySphere}
    (hinj : Function.Injective canonicalDir) :
    ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ → canonicalDir r₁ ≠ canonicalDir r₂ :=
  fun _r₁ _hr₁ _r₂ _hr₂ hne => hinj.ne hne

/--
Gap-bridge packaging: injective `canonicalDir` implies `hDistinctDir` on the bridge.
-/
theorem SATRapidityGapBridge.hDistinctDir_of_injective {M : Type*} (G : SATRapidityGapBridge M)
    (hinj : Function.Injective G.canonicalDir) :
    ∀ r₁ ∈ G.residuals, ∀ r₂ ∈ G.residuals, r₁ ≠ r₂ → G.canonicalDir r₁ ≠ G.canonicalDir r₂ :=
  fun _r₁ _hr₁ _r₂ _hr₂ hne => hinj.ne hne

/--
Scaffold-only: the placeholder `angle` is globally nonnegative, so the minimum-angle
field is derivable without any annulus-width argument.
-/
theorem hMinAngle_of_scaffold {M : Type*} (shared : SATSharedManifold M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere) (residuals : List (SATResidual M)) :
    ∀ r₁ ∈ residuals, ∀ r₂ ∈ residuals, r₁ ≠ r₂ →
      angle shared (canonicalDir r₁) (canonicalDir r₂) ≥ 0 :=
  fun _ _ _ _ _ => angle_nonneg_of_scaffold shared _ _

/--
Fully explicit empty-residual bridge: pairwise hypotheses are vacuous; only
`hEffectiveDim`, nonnegative sphere-code at `effectiveDim`, and the ambient data
remain.
-/
def SATRapidityGapBridge.mkEmpty {M : Type*} (shared : SATSharedManifold M) (threshold : ℝ)
    (annulusModel : LocalShellAnnulusModel) (residualPoint : SATResidual M → ResidualPoint M)
    (canonicalDir : SATResidual M → UnitVector shared.rapiditySphere) (logBoundConst effectiveDim : ℕ)
    (sphereCodeBound : ℕ → ℝ)
    (hEffectiveDim : effectiveDim ≤ logBoundConst * Nat.log 2 (shared.varDim + shared.clauseDim + 1))
    (hSphereLen : (0 : ℝ) ≤ sphereCodeBound effectiveDim) : SATRapidityGapBridge M where
  shared := shared
  residuals := []
  threshold := threshold
  annulusModel := annulusModel
  residualPoint := residualPoint
  canonicalDir := canonicalDir
  effectiveDim := effectiveDim
  logBoundConst := logBoundConst
  sphereCodeBound := sphereCodeBound
  hDirRealization := fun _ => ⟨_, rfl⟩
  hDistinctDir := fun r₁ hr₁ _ _ _ => absurd hr₁ List.not_mem_nil
  hMinAngle := fun r₁ hr₁ _ _ _ => absurd hr₁ List.not_mem_nil
  hEffectiveDim := hEffectiveDim
  hSphereLen := by
    simpa [Nat.cast_zero] using hSphereLen

/--
Every direction-selection certificate lifts to a gap bridge: shell realization
holds by reflexivity, and the remaining fields are copied.

This makes precise the sense in which `hDirRealization` is not independent
content at the scaffold: it is automatic once `localShellIntersections` is a
total definition.
-/
def DirectionSelectionCertificate.toSATRapidityGapBridge
    {M : Type*}
    (D : DirectionSelectionCertificate M) :
    SATRapidityGapBridge M where
  shared := D.shared
  residuals := D.residuals
  threshold := D.threshold
  annulusModel := D.annulusModel
  residualPoint := D.residualPoint
  canonicalDir := D.canonicalDir
  effectiveDim := D.effectiveDim
  logBoundConst := D.logBoundConst
  sphereCodeBound := D.sphereCodeBound
  hDirRealization := fun _r => ⟨_, rfl⟩
  hDistinctDir := D.distinctDirs
  hMinAngle := D.minAngleFromTip
  hEffectiveDim := D.hEffectiveDim
  hSphereLen := D.hSphereLen

theorem DirectionSelectionCertificate.toSATRapidityGapBridge_toDirectionSelectionCertificate
    {M : Type*} (D : DirectionSelectionCertificate M) :
    D.toSATRapidityGapBridge.toDirectionSelectionCertificate = D :=
  rfl

/--
Combine the gap bridge with the local shell-intersection slot from
`SATRapidityDirectionSelection`.
-/
def SATRapidityGapBridge.toLocalDirectionSelectionRealization
    {M : Type*}
    (G : SATRapidityGapBridge M) :
    LocalDirectionSelectionRealization M where
  base := G.toDirectionSelectionCertificate
  canonicalDirFromIntersections := G.hDirRealization

/--
Main bridge theorem: once the rapidity gap is shown to control canonical shell
directions, the geometric collapse statement follows.

This theorem is intentionally the narrow formal bottleneck.
-/
theorem sat_rapidity_gap_bridge_implies_geometric_collapse
    {M : Type*}
    (G : SATRapidityGapBridge M) :
    G.effectiveDim ≤ G.logBoundConst * Nat.log 2 (G.shared.varDim + G.shared.clauseDim + 1) ∧
    (G.residuals.length : ℝ) ≤ sphere_code_bound G.sphereCodeBound G.effectiveDim := by
  exact direction_selection_implies_geometric_collapse G.toDirectionSelectionCertificate

/--
The same bridge gives a `SATRapidityGeometricCollapse` witness once a concrete
successor-step residual-control record is available.
-/
def SATRapidityGapBridge.toGeometricCollapse
    {M : Type*}
    (G : SATRapidityGapBridge M)
    (control : SuccessorStepResidualControl M)
    (hShared : control.shared = G.shared)
    (hLen : G.residuals.length = control.arityResiduals.length)
    (hPoly : G.sphereCodeBound G.effectiveDim ≤ G.sphereCodeBound (control.shared.varDim + control.shared.clauseDim)) :
    SATRapidityGeometricCollapse M :=
  (G.toDirectionSelectionCertificate).toGeometricCollapse control hShared hLen hPoly

end

end Hqiv.Geometry
