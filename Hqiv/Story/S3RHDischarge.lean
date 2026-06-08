import Hqiv.Story.S3ZetaClosedForm

/-!
# Discharging the conditional RH packaging

See `S3ZetaClosedForm` for closed forms and the interior factorization capstone.

**Unconditionally discharged:** FE slot, open-strip confinement, regional closed forms.

**Interior capstone:** `InteriorStripZetaCriticalFactorization` — supply `h` from the
harmonic–Δ–SO(4) channel split to close `RiemannHypothesis`.
-/

namespace Hqiv.Story

noncomputable section

theorem conditionals_discharged_of_interior_pinning
    (hPin : InteriorStripZetaEqExactTwiddleReadout) :
    RiemannHypothesis ∧ Nonempty S3ComplexResidualModel :=
  conditionals_discharged_of_interior_factorization
    (interior_factorization_of_readout_pinning hPin)

end

end Hqiv.Story
