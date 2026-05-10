import Problems.YangMills.Quantum
import Problems.YangMills.Millennium
import Problems.NavierStokes.Millennium
import Problems.NavierStokes.MillenniumBoundedDomain
import Problems.NavierStokes.MillenniumRDomain

/-!
# Clay Millennium (YM + NS) — copy for `Hqiv/BridgeClayMinimal`

**Copied from** `Hqiv.Bridge.LeanDojoClayMillennium` with namespace `Hqiv.BridgeClayMinimal.LeanDojo`
so this minimal spine is self-contained under one folder (same theorems, same vendored targets).
-/

namespace Hqiv.BridgeClayMinimal.LeanDojo

open MillenniumYangMills
open MillenniumYangMillsDefs
open MillenniumNS_BoundedDomain
open MillenniumNSRDomain
open MillenniumNavierStokes

/-!
### Yang–Mills — problem statement and witness elimination
-/

/-- Restatement of the official Clay YM / mass-gap conjecture for a fixed gauge group. -/
abbrev YangMillsMillenniumTarget (G : Type) [CompactSimpleGaugeGroup G] : Prop :=
  YangMillsExistenceAndMassGap G

theorem yangMills_millennium_of_witness
    (G : Type) [CompactSimpleGaugeGroup G]
    (qft : QuantumYangMillsTheory G) (Δ : ℝ)
    (hE : ClayExistence qft) (hGap : HasMassGapSpectrum G qft Δ) (hF : FiniteMassSpectrum G qft) :
    YangMillsMillenniumTarget G := by
  exact
    Exists.intro qft
      (Exists.intro Δ (And.intro hE (And.intro hGap hF)))

/-!
### Navier–Stokes — Fefferman (A)–(D) as a single disjunction
-/

abbrev NavierStokesMillenniumTarget : Prop :=
  NavierStokesMillenniumProblem

theorem navier_stokes_millennium_unfold :
    NavierStokesMillenniumTarget = (FeffermanA ∨ FeffermanB ∨ FeffermanC ∨ FeffermanD) := rfl

theorem navier_stokes_millennium_of_fefferman_A (hA : FeffermanA) : NavierStokesMillenniumTarget :=
  Or.inl hA

theorem navier_stokes_millennium_of_fefferman_B (hB : FeffermanB) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inl hB)

theorem navier_stokes_millennium_of_fefferman_C (hC : FeffermanC) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inr (Or.inl hC))

theorem navier_stokes_millennium_of_fefferman_D (hD : FeffermanD) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inr (Or.inr hD))

end Hqiv.BridgeClayMinimal.LeanDojo
