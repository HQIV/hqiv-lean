import Hqiv.Physics.FanoDetuningFirstOrder
import Hqiv.Physics.FanoLine

namespace Hqiv.Physics

open Hqiv

/-!
# Fano-line + triality narrative for the detuning denominator (scaffold)

The affine law `1 + (γ/2) m` in `rindlerDetuningShared` is **proved** as algebra in
`FanoDetuningFirstOrder.lean`. The **research** claim is stronger: the leading constant `1` should
ultimately come from **triality-normalized projection** onto a Fano line (octonionic skeleton), not
from an independent normalization knob—see `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md` §2.1–2.2.

This module introduces **named hooks** so downstream lemmas can cite
`trialityProjectedDenominator` (indexed by `FanoLine`) and the quotient identity **today**, while the
Spin(8) triality representation cycle (`Hqiv.Algebra.Triality`) is **not** yet wired to prove
invariance of that constant across cycled lines.

**Proved now:** for every `FanoLine` and the tag API `trialityProjectedDenominatorTag`, the value agrees
with `rindlerDetuningShared` (hence the affine law), via the direct O-Maxwell spectral scaffold in
`FanoOmaxwellSpectrum.lean`: a named spectral mode, Fano-line restriction, and projected `Δ` 1-jet.
Public `FanoLineTag = FanoVertex` APIs are now **incidence-driven** through `FanoLine.ofTag`.

**Open:** show the *same* functional form with constant `1` is **forced** by triality equivariance
on the projected line (not merely consistent with the chosen normalization at `m = 0`).
-/

/-- Tag for a Fano line in the narrative (vertex / line bookkeeping in algebra layer). -/
abbrev FanoLineTag := FanoVertex

/--
**Target interface** (indexed by combinatorial `FanoLine`).

Current direct source: the Fano-projected O-Maxwell spectral 1-jet on the chosen line.
This is now the public denominator body, not just an external comparison theorem.
-/
noncomputable def trialityProjectedDenominator (L : FanoLine) (m : ℕ) : ℝ :=
  spectralFanoRindler1Jet L m

/-- Public tag API: vertex tags choose their canonical incident line via `FanoLine.ofTag`. -/
noncomputable def trialityProjectedDenominatorTag (t : FanoLineTag) (m : ℕ) : ℝ :=
  trialityProjectedDenominator (FanoLine.ofTag t) m

theorem trialityProjectedDenominator_eq_rindler (L : FanoLine) (m : ℕ) :
    trialityProjectedDenominator L m = rindlerDetuningShared (m : ℝ) := by
  exact spectralFanoRindler1Jet_eq_rindler L m

theorem trialityProjectedDenominatorTag_eq_rindler (t : FanoLineTag) (m : ℕ) :
    trialityProjectedDenominatorTag t m = rindlerDetuningShared (m : ℝ) := by
  simpa using trialityProjectedDenominator_eq_rindler (FanoLine.ofTag t) m

theorem trialityProjectedDenominator_fanoLine_eq_fanoLineTag (t : FanoLineTag) (m : ℕ) :
    trialityProjectedDenominator (FanoLine.ofTag t) m = trialityProjectedDenominatorTag t m := rfl

/-- Alias for migration notes / paper cross-refs (`eq_old` = tag API matches `ofTag` line). -/
theorem trialityProjectedDenominator_eq_old (t : FanoLineTag) (m : ℕ) :
    trialityProjectedDenominator (FanoLine.ofTag t) m = trialityProjectedDenominatorTag t m := rfl

/--
Quotient form matching the user-facing target: `detunedShellSurface` equals `S(m)` over the named
projected denominator (any line tag — currently the same real for all tags).
-/
theorem detunedShellSurface_eq_shell_div_trialityProjectedDenominator
    (line : FanoLineTag) (m : ℕ) :
    detunedShellSurface m = shellSurface m / trialityProjectedDenominatorTag line m := by
  rw [detunedShellSurface_eq_shell_div_affine_den]
  congr 1
  rw [trialityProjectedDenominatorTag_eq_rindler line m]
  simp [rindlerDetuningShared, c_rindler_shared]

/--
**Unit constant at shell 0:** for every Fano line tag, the scaffold denominator evaluates to `1`
at `m = 0`. This is the easy part of the “constant term is 1” story; the **triality-forcing** step is
still open (see module doc).
-/
theorem trialityProjected_denominator_at_shell_zero_eq_one (line : FanoLineTag) :
    trialityProjectedDenominatorTag line 0 = 1 := by
  rw [trialityProjectedDenominatorTag_eq_rindler line 0]
  simp [rindlerDetuningShared]

/-!
With the current direct spectral scaffold, the first-order **affine** law comes from the named
O-Maxwell/Fano 1-jet source, not from directly expanding a rapidity stub.
-/
theorem trialityProjectedDenominator_stub_eq_affine_shell
    (L : FanoLine) (m : ℕ) :
    trialityProjectedDenominator L m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  exact spectralFanoRindler1Jet_eq_one_plus_half_gamma L m

theorem trialityProjectedDenominator_firstOrder
    (L : FanoLine) (m : ℕ) :
    trialityProjectedDenominator L m = 1 + (gamma_HQIV / 2) * (m : ℝ) := by
  exact trialityProjectedDenominator_stub_eq_affine_shell L m

end Hqiv.Physics
