import Hqiv.Story.Chapter06_Fluid
import Hqiv.Bridge.LeanDojoClayMillennium
import Hqiv.Story.HQIVDissipativeBridge
import Hqiv.Physics.TrialityRapidityWellEquivalence

/-!
# Remaining NS bridge obligations (shared lattice/rapidity spine)

This module packages the HQIV-side data already available for the Navier-Stokes route:

- lock-in shell witness (`Chapter05`),
- fluid coefficient sign scaffold (`Chapter06`),
- rapidity/triality well consistency (`TrialityRapidityWellEquivalence`).

It then gives a precise handoff theorem to the Clay NS target:
once any Fefferman disjunct witness `(A ∨ B ∨ C ∨ D)` is supplied, the official
`NavierStokesMillenniumTarget` follows.

No new axioms are introduced.
-/

namespace Hqiv.Story

open Hqiv.Story.MassGap
open Hqiv.Bridge.LeanDojo
open MillenniumNS_BoundedDomain
open Hqiv.Physics

/-- Shared HQIV substrate for the NS route: lock-in shell witness + fluid sign scaffold. -/
def hqivNSSharedLatticeFluidSubstrate : Prop :=
  step05_referenceShellGapWitness ∧ step06_continuumToWightmanScaffold

/-- The shared lattice/fluid substrate is already available from Chapters 5 and 6. -/
theorem hqivNSSharedLatticeFluidSubstrate_holds : hqivNSSharedLatticeFluidSubstrate :=
  ⟨step05_referenceShellGapWitness_holds, step06_continuumToWightmanScaffold_holds⟩

/-- Rapidity/triality consistency payload used by the NS bridge narrative. -/
def hqivNSRapidityConsistency : Prop :=
  ∀ line rep m, trialityRapidityWellResidual line rep m = 0

/-- Rapidity/triality consistency is already proved in `TrialityRapidityWellEquivalence`. -/
theorem hqivNSRapidityConsistency_holds : hqivNSRapidityConsistency := by
  intro line rep m
  exact trialityRapidityWellResidual_eq_zero line rep m

/-- Combined shared substrate for the NS route: lattice/fluid + rapidity consistency. -/
def hqivNSSharedSubstrate : Prop :=
  hqivNSSharedLatticeFluidSubstrate ∧ hqivNSRapidityConsistency

theorem hqivNSSharedSubstrate_holds : hqivNSSharedSubstrate :=
  ⟨hqivNSSharedLatticeFluidSubstrate_holds, hqivNSRapidityConsistency_holds⟩

/-- Handoff theorem (A-branch): shared substrate + Fefferman A implies the Clay NS target. -/
theorem navierStokesMillenniumTarget_of_hqivSharedSubstrate_A
    (_hSub : hqivNSSharedSubstrate)
    (hA : MillenniumNSRDomain.FeffermanA) :
    NavierStokesMillenniumTarget :=
  navier_stokes_millennium_of_fefferman_A hA

/-- Handoff theorem (B-branch): shared substrate + Fefferman B implies the Clay NS target. -/
theorem navierStokesMillenniumTarget_of_hqivSharedSubstrate_B
    (_hSub : hqivNSSharedSubstrate)
    (hB : MillenniumNS_BoundedDomain.FeffermanB) :
    NavierStokesMillenniumTarget :=
  navier_stokes_millennium_of_fefferman_B hB

/-- Handoff theorem (C-branch): shared substrate + Fefferman C implies the Clay NS target. -/
theorem navierStokesMillenniumTarget_of_hqivSharedSubstrate_C
    (_hSub : hqivNSSharedSubstrate)
    (hC : MillenniumNSRDomain.FeffermanC) :
    NavierStokesMillenniumTarget :=
  navier_stokes_millennium_of_fefferman_C hC

/-- Handoff theorem (D-branch): shared substrate + Fefferman D implies the Clay NS target. -/
theorem navierStokesMillenniumTarget_of_hqivSharedSubstrate_D
    (_hSub : hqivNSSharedSubstrate)
    (hD : MillenniumNS_BoundedDomain.FeffermanD) :
    NavierStokesMillenniumTarget :=
  navier_stokes_millennium_of_fefferman_D hD

/-- Bite 2 transfer slot (chosen branch): interpret `ns_fefferman_transfer` as Fefferman-B witness. -/
def NSBranchBTransfer (B : HQIVDissipativeBridge) : Prop :=
  B.ns_fefferman_transfer → MillenniumNS_BoundedDomain.FeffermanB

/-- If the bridge supplies the branch-B transfer witness, the Clay NS target follows. -/
theorem navierStokesMillenniumTarget_of_NSBranchBTransfer
    (B : HQIVDissipativeBridge)
    (hBtx : NSBranchBTransfer B)
    (hSlot : B.ns_fefferman_transfer) :
    NavierStokesMillenniumTarget :=
  navier_stokes_millennium_of_fefferman_B (hBtx hSlot)

/-- Upgrade the canonical shared bridge by filling `ns_fefferman_transfer` with branch-B itself. -/
def hqivCanonicalDissipativeBridge_upgraded_B
    (_hB : MillenniumNS_BoundedDomain.FeffermanB) : HQIVDissipativeBridge :=
  { hqivCanonicalDissipativeBridge with
    ns_fefferman_transfer := MillenniumNS_BoundedDomain.FeffermanB }

/-- The upgraded bridge has its NS transfer slot filled (by construction). -/
theorem hqivCanonicalDissipativeBridge_upgraded_B_slot
    (hB : MillenniumNS_BoundedDomain.FeffermanB) :
    (hqivCanonicalDissipativeBridge_upgraded_B hB).ns_fefferman_transfer :=
  hB

/-- Bite 2 end-to-end: branch-B witness fills the bridge slot and yields the Clay NS target. -/
theorem navierStokesMillenniumTarget_of_hqivCanonicalBridge_upgraded_B
    (hB : MillenniumNS_BoundedDomain.FeffermanB) :
    NavierStokesMillenniumTarget := by
  exact navierStokesMillenniumTarget_of_NSBranchBTransfer
    (B := hqivCanonicalDissipativeBridge_upgraded_B hB)
    (hBtx := fun h => h)
    (hSlot := hqivCanonicalDissipativeBridge_upgraded_B_slot hB)

/-- Citation-backed bridge slot for the NS endpoint (Fefferman branch B witness).

This is the lightweight handoff hypothesis while full internal formalization of the
Fefferman branch is developed in Story. Standard NS references include Fefferman's Clay note
and the bounded-domain regularity literature packaged by Lean Dojo's `FeffermanB` slot. -/
abbrev LiteratureNSFeffermanBridge : Prop :=
  MillenniumNS_BoundedDomain.FeffermanB

/-- Fast NS closure endpoint from the citation-backed Fefferman bridge slot. -/
theorem navierStokesMillenniumTarget_of_literatureBridge
    (hLit : LiteratureNSFeffermanBridge) :
    NavierStokesMillenniumTarget :=
  navierStokesMillenniumTarget_of_hqivCanonicalBridge_upgraded_B hLit

/-- Refined NS analytic package slot (Story integration point).

Use this for a fuller internal NS route; it can later be expanded into explicit coercive,
regularity, and transfer lemmas while keeping the endpoint API stable. -/
def NSFeffermanAnalyticAxioms : Prop :=
  MillenniumNS_BoundedDomain.FeffermanB

/-- The refined NS analytic package implies the citation-backed bridge slot. -/
theorem literatureNSFeffermanBridge_of_analyticAxioms
    (hAxioms : NSFeffermanAnalyticAxioms) :
    LiteratureNSFeffermanBridge :=
  hAxioms

/-- End-to-end NS closure from the refined analytic package slot. -/
theorem navierStokesMillenniumTarget_of_analyticAxioms
    (hAxioms : NSFeffermanAnalyticAxioms) :
    NavierStokesMillenniumTarget :=
  navierStokesMillenniumTarget_of_literatureBridge
    (literatureNSFeffermanBridge_of_analyticAxioms hAxioms)

/-! ## Lapse-corrected NS scaffold (HQIV) -/

/-- HQIV lapse-corrected NS momentum balance (component form, scaffold).

`N = HQVM_lapse Φ φ t` rescales the inertial channel, while viscosity and vacuum forcing
come from the Chapter-6 HQIV fluid closures. This is a coefficient-level equation schema,
not a global regularity claim. -/
def hqivLapseCorrectedNSEquation
    (Φ φ t rho aLoc phiFluid dotTheta coherence : ℝ)
    (m : ℕ)
    (uDot conv pressureGrad laplacian force : Fin 3 → ℝ) : Prop :=
  let N := HQVM_lapse Φ φ t
  let fInertia := hqivFluidInertiaFactor aLoc phiFluid
  let nu := hqivEddyViscosity_HQIV_shell_debye m dotTheta coherence
  let gVac := hqivVacuumMomentumSource3 gamma_HQIV phiFluid dotTheta pressureGrad conv
  ∀ i : Fin 3,
    N * (rho * fInertia * (uDot i + conv i)) =
      -pressureGrad i + nu * laplacian i + force i + gVac i

/-- Lock-in shell specialization of the HQIV lapse-corrected NS equation. -/
def hqivLapseCorrectedNSEquation_lockin
    (Φ φ t rho aLoc phiFluid dotTheta coherence : ℝ)
    (uDot conv pressureGrad laplacian force : Fin 3 → ℝ) : Prop :=
  hqivLapseCorrectedNSEquation Φ φ t rho aLoc phiFluid dotTheta coherence
    m_lockin uDot conv pressureGrad laplacian force

/-- In Minkowski lapse (`Φ=0`, `φ=0`), the HQIV lapse-corrected equation reduces to the
same equation with unit lapse prefactor. -/
theorem hqivLapseCorrectedNSEquation_minkowski
    (t rho aLoc phiFluid dotTheta coherence : ℝ)
    (m : ℕ)
    (uDot conv pressureGrad laplacian force : Fin 3 → ℝ) :
    hqivLapseCorrectedNSEquation 0 0 t rho aLoc phiFluid dotTheta coherence
      m uDot conv pressureGrad laplacian force ↔
    (let fInertia := hqivFluidInertiaFactor aLoc phiFluid
     let nu := hqivEddyViscosity_HQIV_shell_debye m dotTheta coherence
     let gVac := hqivVacuumMomentumSource3 gamma_HQIV phiFluid dotTheta pressureGrad conv
     ∀ i : Fin 3,
      rho * fInertia * (uDot i + conv i) =
        -pressureGrad i + nu * laplacian i + force i + gVac i) := by
  constructor
  · intro h
    dsimp [hqivLapseCorrectedNSEquation] at h ⊢
    intro i
    specialize h i
    rw [HQVM_lapse_Minkowski] at h
    simpa using h
  · intro h
    dsimp [hqivLapseCorrectedNSEquation] at h ⊢
    intro i
    specialize h i
    rw [HQVM_lapse_Minkowski]
    simpa using h

end Hqiv.Story
