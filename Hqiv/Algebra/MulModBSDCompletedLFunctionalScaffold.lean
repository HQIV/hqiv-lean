import Hqiv.Algebra.MulModBSDLSeriesScaffold
import Hqiv.Algebra.ThetaCompletedLFunctionalScaffold

/-!
# Completed L-function targets for the mul-mod BSD channel

The **proved** analytic object is `mulModBSDLSeries` on `Re s > 1`
(`MulModBSDLSeriesScaffold`).  Classical BSD concerns the completed L-function of a
**weight-`2`** modular form / elliptic curve, with involution `s ↦ 2 - s` (up to root
number).

This file names that **target** shape as explicit hypothesis records — no claim that
`mulModBSDLocalCoeff` is modular or equals Hecke data of a specified form.

Reuses `CompletedLFunctionalInvolutionHypothesis` from `ThetaCompletedLFunctionalScaffold`.
-/

namespace Hqiv.Algebra

open Complex

/-- Weight-`2` involution target (`s ↦ 2 - s`) — the BSD / elliptic-curve normalization. -/
abbrev WeightTwoCompletedLInvolutionHypothesis (Λ : ℂ → ℂ) : Prop :=
  CompletedLFunctionalInvolutionHypothesis Λ (2 : ℂ)

/--
**BSD L-object hypothesis (honest).**  A completed L-function built from the mul-mod
coefficient stream matches a specified weight-`2` involution — to be proved only after
a modularity / Hecke identification exists.
-/
structure MulModBSDLObjectHypothesis where
  completed : ℂ → ℂ
  involution : WeightTwoCompletedLInvolutionHypothesis completed
  agrees_on_half_plane :
    ∀ {s : ℂ}, 1 < s.re → completed s = mulModBSDLSeries s

end Hqiv.Algebra
