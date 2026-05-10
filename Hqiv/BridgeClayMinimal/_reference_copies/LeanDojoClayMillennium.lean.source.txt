import Problems.YangMills.Quantum
import Problems.YangMills.Millennium
import Problems.NavierStokes.Millennium
import Problems.NavierStokes.MillenniumBoundedDomain
import Problems.NavierStokes.MillenniumRDomain

/-!
# Clay Millennium statements ↔ HQIV wiring (Lean Dojo formalizations)

This file connects the **vendored** [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems)
Yang–Mills and Navier–Stokes *problem statements* to the work already in this repository.

- **Yang–Mills:** the Clay `Prop` is `MillenniumYangMills.YangMillsExistenceAndMassGap` for a given
  `G` with `CompactSimpleGaugeGroup G`.  It requires a full
  `MillenniumYangMillsDefs.QuantumYangMillsTheory G` and spectral-gap data.  The HQIV story that is
  meant to meet that **spectral / mass** side in this repo is the **discrete shell mass spectrum**
  (temperature ladder, binding scales, baryogenesis readouts) — see in particular
  `Hqiv.Physics.HarmonicLadderMass`, `Hqiv.Physics.ConservedContentMassBridge`, and the shell ladder
  in `Hqiv.Physics.BaryogenesisCore` / `Hqiv.Physics.TrialityRapidityWellEquivalence` — *not* the
  separate SM–GR unification `Prop` bundle.  This file only gives witness elimination; bridging those
  layers to a `QuantumYangMillsTheory` remains future work.
- **Navier–Stokes:** the single official `NavierStokesMillenniumProblem` re-export is Fefferman’s
  disjunction (A)–(D) (`FeffermanMillenniumProblem` in `MillenniumNS_BoundedDomain`).

Solving a Millennium problem in the mathematical sense is providing the **missing constructions**
(quantum YM measure + gap; or global NS regularity in one of the Fefferman settings).  This module
**does not** supply those constructions: it is the “socket” the rest of the proof is meant to plug
into.
-/

namespace Hqiv.Bridge.LeanDojo

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

/--
**Sufficient condition (trivial but precise):** the Clay YM / mass gap problem is solved for `G` as
soon as you exhibit a nontrivial `QuantumYangMillsTheory G` with a **positive** spectral gap
`HasMassGapSpectrum` and a finite-mass (upper bound) condition `FiniteMassSpectrum`.
This is exactly how `YangMillsExistenceAndMassGap` is defined in
`Vendored/LeanDojoMillennium/Problems/YangMills/Millennium.lean`.
-/
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

/-- Official combined statement (A ∨ B ∨ C ∨ D) from the Clay PDF. -/
abbrev NavierStokesMillenniumTarget : Prop :=
  NavierStokesMillenniumProblem

theorem navier_stokes_millennium_unfold :
    NavierStokesMillenniumTarget = (FeffermanA ∨ FeffermanB ∨ FeffermanC ∨ FeffermanD) := rfl

/-- `∨` associates to the right in this problem statement. -/

theorem navier_stokes_millennium_of_fefferman_A (hA : FeffermanA) : NavierStokesMillenniumTarget := Or.inl hA

theorem navier_stokes_millennium_of_fefferman_B (hB : FeffermanB) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inl hB)

theorem navier_stokes_millennium_of_fefferman_C (hC : FeffermanC) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inr (Or.inl hC))

theorem navier_stokes_millennium_of_fefferman_D (hD : FeffermanD) : NavierStokesMillenniumTarget :=
  Or.inr (Or.inr (Or.inr hD))

end Hqiv.Bridge.LeanDojo
