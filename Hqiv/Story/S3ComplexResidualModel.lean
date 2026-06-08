import Hqiv.Story.S3PoleZeroChannel

/-!
# Sound complex residual model (repair of the real-valued model)

The earlier `S3ZetaResidualModel` / `S3CenteredZetaResidualModel` are
**unsatisfiable**: their `zeta_eq_residual` field demands

`riemannZeta s = (criticalProj _ : ℂ)`,

i.e. that `riemannZeta s` is real for every `s`, which is false (e.g.
`riemannZeta (2 + I)` is not real).  No honest term can inhabit them.

This module repairs the shape by letting the residual be **complex-valued** and
by restricting the critical-line lock to **nontrivial** zeros (matching Mathlib's
`RiemannHypothesis`).  The repaired model is sound in the precise sense that it
is inhabited **iff** the Riemann Hypothesis holds:

`Nonempty S3ComplexResidualModel ↔ RiemannHypothesis`.

So this is an honest conditional packaging — it does not prove RH, it is
*equivalent* to RH.  The genuine analytic work (constructing a residual whose
nontrivial zero set is forced onto `Re = 1/2`) is exactly RH and is not supplied
here.
-/

namespace Hqiv.Story

noncomputable section

/--
A complex residual detector for `riemannZeta`.

* `residual` is any `ℂ → ℂ` map;
* `zeta_eq_residual` identifies it with `riemannZeta`;
* `nontrivial_zero_locks_re_half` is the critical-line lock, restricted to
  nontrivial zeros (so trivial negative-even zeros and the pole slot are
  excluded, exactly as in Mathlib's `RiemannHypothesis`).
-/
structure S3ComplexResidualModel where
  residual : ℂ → ℂ
  zeta_eq_residual : ∀ s : ℂ, riemannZeta s = residual s
  nontrivial_zero_locks_re_half :
    ∀ s : ℂ, IsNontrivialZetaZero s → residual s = 0 → s.re = (1 / 2 : ℝ)

/-- A complex residual model yields Mathlib's `RiemannHypothesis`. -/
theorem RiemannHypothesis_of_complexResidualModel
    (M : S3ComplexResidualModel) :
    RiemannHypothesis := by
  intro s hz hNotTrivial hNotOne
  have hzz : IsNontrivialZetaZero s := ⟨hz, hNotTrivial, hNotOne⟩
  have hres : M.residual s = 0 := by
    rw [← M.zeta_eq_residual s]; exact hz
  exact M.nontrivial_zero_locks_re_half s hzz hres

/--
Conversely, if RH holds then the identity residual (`residual = riemannZeta`)
inhabits the model.  This shows the model is **not** vacuously false: it is a
faithful repackaging of RH.
-/
def complexResidualModel_of_RiemannHypothesis
    (hRH : RiemannHypothesis) :
    S3ComplexResidualModel where
  residual := riemannZeta
  zeta_eq_residual := fun _ => rfl
  nontrivial_zero_locks_re_half := by
    intro s hzz _
    exact hRH s hzz.1 hzz.2.1 hzz.2.2

/--
**Soundness/honesty theorem.**

The repaired complex residual model is inhabited exactly when the Riemann
Hypothesis is true.  Equivalently: constructing an inhabitant *is* proving RH.
-/
theorem nonempty_complexResidualModel_iff_RiemannHypothesis :
    Nonempty S3ComplexResidualModel ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨M⟩
    exact RiemannHypothesis_of_complexResidualModel M
  · intro hRH
    exact ⟨complexResidualModel_of_RiemannHypothesis hRH⟩

/--
Geometric bridge slot (still complex-valued and sound):
the *real part* of the residual is allowed to carry the S³ critical-line
deviation `Re(s) - 1/2`, while the imaginary part stays free.  This records the
intended HQIV picture without forcing `riemannZeta` to be real.
-/
def ResidualRealPartCenters (M : S3ComplexResidualModel) : Prop :=
  ∀ s : ℂ, (M.residual s).re = s.re - (1 / 2 : ℝ)

/--
If the residual's real part is centered on the critical-line deviation, then any
zero of the residual lies on `Re = 1/2` automatically — the lock field becomes
derivable rather than assumed.  (Constructing such a residual equal to
`riemannZeta` remains RH-hard; this only shows the centered shape is internally
consistent.)
-/
theorem nontrivial_zero_locks_re_half_of_realPartCenters
    (residual : ℂ → ℂ)
    (hCenter : ∀ s : ℂ, (residual s).re = s.re - (1 / 2 : ℝ))
    (s : ℂ) (hZero : residual s = 0) :
    s.re = (1 / 2 : ℝ) := by
  have hre : (residual s).re = 0 := by rw [hZero]; simp
  have : s.re - (1 / 2 : ℝ) = 0 := by rw [← hCenter s]; exact hre
  linarith

end

end Hqiv.Story
