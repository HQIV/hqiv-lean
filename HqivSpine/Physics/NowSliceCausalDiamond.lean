import HqivSpine.Physics.NowSlice
import HqivSpine.Physics.NowSliceFromLattice
import HqivSpine.Physics.Gravity
import HqivSpine.Physics.Curvature
import HqivSpine.Physics.Age
import HqivSpine.Physics.BulkHyperboloidDynamics
import HqivSpine.Physics.ContinuousHorizon
import HqivSpine.Physics.Baryogenesis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.NowSliceCausalDiamond` — the now slice as a causal diamond

In familiar spacetime language, an observer's **causal diamond** is the finite region
`I⁺(p) ∩ I⁻(q)` between an earlier and a later event on their worldline — the largest
causally accessible patch at a **time and place**. HQIV replaces the smooth manifold with
the **null lattice**, but the same role is played by a **local event** plus its **apex chart**:

| Familiar causal diamond | HQIV formal object |
|-------------------------|-------------------|
| Apex event `p` (here-and-now) | `Event` on shell `m` with null 3-complex `M` |
| Comoving Hubble rate at apex | `NowSlice.phi` (`hubbleReference = 1` at natural now) |
| Interior Newtonian potential | `NowSlice.bigPhi` = weak-field ledger `Φ(m)` |
| Spatial curvature budget used | `NowSlice.omegaK` = discrete `Ω_k(m\|4)` (`omegaKPartial`) |
| Coordinate age along worldline | `NowSlice.apparentAge` = shell index `m` |
| ADM lapse / diamond opening `N` | `NowSlice.massUnit` = `1 + Φ + φ·t` |
| Proper-time rate `dτ/dt` | `BulkHyperboloidDynamics` — derivative of wall-clock age = `N` |

**What the diamond does *not* carry:** the global imprint partition **(α, γ) = (3/5, 2/5)**.
That is **lattice glue** — the same everywhere — entering through

* `G_eff(φ) = φ^α` (`Gravity.gEff`), and
* `shellShape m = (1/(m+1))·(1 + α·ln(m+1))` inside `δ_E(m)` (`Curvature`).

The **evaluation map** `evaluate` applies this glue at a local event: the slice is the diamond
chart; `imprintGlue` is the fixed light-cone geometry; readouts are `massUnit × ratio` and
`Ω_k · δ_E(k)`.

**Ω_k ontology:** the slice carries the **discrete** horizon ratio `omegaKPartial m` from the
null-lattice sum. The continuous `ξ` chart is an export coordinate for coupling readouts — not a
second curvature field (no parallel superposition of charts).

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.CausalDiamond

open HqivSpine.Topology
open HqivSpine.Physics
open HqivSpine.Physics.NowSliceFromLattice
open ContinuousHorizon

/-! ## Local event on the null lattice -/

/-- **Causal-diamond event:** a shell depth plus combinatorial null-lattice data —
the discrete analogue of an apex `p` on the worldline. -/
structure Event where
  /-- Shell index = coordinate age on the ladder. -/
  shell : ℕ
  /-- Null-lattice 3-complex at this shell. -/
  complex : Discrete3Complex NullShellVertex

/-- The **apex chart** carried by the event (the `NowSlice`). -/
noncomputable def Event.slice (e : Event) : NowSlice :=
  nowSliceOf ⟨e.shell, e.complex⟩

theorem Event.toLatticeObserver_slice (e : Event) :
    Event.slice e = nowSliceOf ⟨e.shell, e.complex⟩ := rfl

/-- Lock-in reference event on `S³` null template at `referenceM = 4`. -/
noncomputable def lockinEvent : Event :=
  { shell := referenceM, complex := S3NullReference referenceM }

theorem lockinEvent_slice_eq : lockinEvent.slice = lockinNowSlice := rfl

/-! ## Apex chart = familiar diamond opening -/

/-- **Apex chart** — the causal-diamond data at the top of the patch, without global glue. -/
structure ApexChart where
  hubble : ℝ
  potential : ℝ
  omegaK : ℝ
  coordinateAge : ℝ

/-- Extract the apex chart from any now slice. -/
def ApexChart.ofNowSlice (s : NowSlice) : ApexChart :=
  ⟨s.phi, s.bigPhi, s.omegaK, s.apparentAge⟩

theorem ApexChart.ofNowSlice_fields (s : NowSlice) :
    (ApexChart.ofNowSlice s).hubble = s.phi ∧
    (ApexChart.ofNowSlice s).potential = s.bigPhi ∧
    (ApexChart.ofNowSlice s).omegaK = s.omegaK ∧
    (ApexChart.ofNowSlice s).coordinateAge = s.apparentAge :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Diamond opening** `N = 1 + Φ + H·t` at the apex. -/
noncomputable def ApexChart.diamondLapse (a : ApexChart) : ℝ :=
  lapse a.potential a.hubble a.coordinateAge

theorem ApexChart.diamondLapse_eq (a : ApexChart) :
    a.diamondLapse = 1 + a.potential + a.hubble * a.coordinateAge := rfl

theorem ApexChart.diamondLapse_of_slice (s : NowSlice) :
    (ApexChart.ofNowSlice s).diamondLapse = s.massUnit := rfl

noncomputable def Event.admOpening (e : Event) : ℝ := (ApexChart.ofNowSlice e.slice).diamondLapse

theorem Event.admOpening_eq_massUnit (e : Event) : Event.admOpening e = e.slice.massUnit :=
  ApexChart.diamondLapse_of_slice e.slice

/-- **Wall-clock age** along the comoving worldline through the diamond (`Age`). -/
noncomputable def Event.wallClockAge (e : Event) : ℝ := e.slice.wallClockAge

/-- Homogeneous bulk chart: `dτ/dt = N(t)` when `Φ = 0` on the flow (`BulkHyperboloidDynamics`). -/
theorem Event.wallClock_rate_eq_homogeneous_lapse (e : Event) :
    deriv (fun t => wallClockHomogeneous e.slice.phi t) e.slice.apparentAge =
      lapse 0 e.slice.phi e.slice.apparentAge :=
  wallClockHomogeneous_deriv_eq_lapse e.slice.phi e.slice.apparentAge

theorem balancedEvent_wallClock_rate_eq_massUnit (e : Event) (hΦ : e.slice.bigPhi = 0) :
    deriv (fun t => wallClockHomogeneous e.slice.phi t) e.slice.apparentAge = e.slice.massUnit := by
  rw [Event.wallClock_rate_eq_homogeneous_lapse, NowSlice.massUnit_eq, hΦ, lapse]

theorem lockinEvent_wallClock_rate_eq_massUnit :
    deriv (fun t => wallClockHomogeneous lockinNowSlice.phi t) lockinNowSlice.apparentAge =
      lockinNowSlice.massUnit :=
  lockin_wallClock_deriv_eq_massUnit

/-! ## Global glue — not on the slice -/

/-- **Imprint glue** `(α, γ)`: how sectors stitch; forced on the lattice, identical at every diamond. -/
structure ImprintGlue where
  alpha : ℝ
  gamma : ℝ

/-- The proved HQIV partition `α = 3/5`, `γ = 2/5`. -/
noncomputable def imprintGlue : ImprintGlue :=
  ⟨alphaEM, gammaHQIV⟩

theorem imprintGlue_alpha : imprintGlue.alpha = 3 / 5 := alphaEM_eq

theorem imprintGlue_gamma : imprintGlue.gamma = 2 / 5 := gammaHQIV_eq

theorem imprintGlue_partition : imprintGlue.alpha + imprintGlue.gamma = 1 :=
  alphaEM_add_gammaHQIV

/-- **Varying-G** uses the same exponent as the curvature imprint: `G_eff = φ^α`. -/
theorem gEff_eq_imprintGlue_power (φ : ℝ) :
    gEff φ = φ ^ imprintGlue.alpha := by
  rw [gEff_eq, imprintGlue_alpha]

/-- **Per-shell shape** uses the same `α` as `gEff`. -/
theorem shellShape_eq_imprintGlue (m : ℕ) :
    shellShape m =
      imprintWeight m * (1 + imprintGlue.alpha * Real.log ((m : ℝ) + 1)) := by
  unfold shellShape imprintGlue
  simp [alphaEM_eq]

/-! ## Evaluation map: glue × local chart -/

/-- **Readout bundle** after evaluating global laws at a local event. -/
structure EventReadout where
  event : Event
  slice : NowSlice
  /-- `G_eff(H)` at the diamond apex. -/
  gEff_at_apex : ℝ
  /-- Curvature imprint `Ω_k · δ_E(k)` on the slice. -/
  imprint : ℕ → ℝ

/-- **Evaluation map** — the only way global `(α,γ)` and `δ_E` meet the local diamond. -/
noncomputable def evaluate (e : Event) : EventReadout where
  event := e
  slice := e.slice
  gEff_at_apex := gEff e.slice.phi
  imprint := fun m => e.slice.curvatureImprint m

theorem evaluate_slice (e : Event) : (evaluate e).slice = e.slice := rfl

theorem evaluate_gEff (e : Event) : (evaluate e).gEff_at_apex = gEff e.slice.phi := rfl

theorem evaluate_imprint (e : Event) (m : ℕ) :
    (evaluate e).imprint m = e.slice.curvatureImprint m := rfl

/-- **Primary `Ω_k`:** the slice value is the discrete lattice ratio, not a continuum parallel field. -/
theorem event_omegaK_is_discrete (e : Event) :
    e.slice.omegaK = omegaKPartial e.shell := by
  unfold Event.slice nowSliceOf
  simp

/-- Emission coordinate `ξ = m+1` at the observer shell. -/
noncomputable def Event.xi (e : Event) : ℝ := xiOfShell e.shell

theorem lockinEvent_xi : Event.xi lockinEvent = xiLockin := by
  unfold Event.xi lockinEvent xiLockin
  rfl

/-! ## Shell ladder on the reference horizon -/

/-- **Balanced-horizon event** at shell `m` on the `S³` null template through lock-in. -/
noncomputable def horizonEventAtShell (m : ℕ) : Event :=
  { shell := m, complex := S3NullReference referenceM }

theorem horizonEventAtShell_lockin : horizonEventAtShell referenceM = lockinEvent := rfl

theorem horizonEventAtShell_slice_omegaK (m : ℕ) :
    (horizonEventAtShell m).slice.omegaK = omegaKPartial m :=
  event_omegaK_is_discrete (horizonEventAtShell m)

theorem horizonEventAtShell_bigPhi_zero (m : ℕ) (hm : m ≤ referenceM) :
    (horizonEventAtShell m).slice.bigPhi = 0 := by
  unfold horizonEventAtShell Event.slice nowSliceOf weakFieldPotential
  rw [S3NullReference_shell_budget_zero referenceM m hm]
  simp

theorem horizonEventAtShell_apparentAge (m : ℕ) :
    (horizonEventAtShell m).slice.apparentAge = m := by
  unfold horizonEventAtShell Event.slice nowSliceOf
  simp

/-- **Shell-ladder readout** — `evaluate` at a horizon event plus the baryogenesis slot. -/
structure ShellLadderReadout where
  event : Event
  shell : ℕ
  readout : EventReadout
  /-- Baryon asymmetry `η = Ω_k · δ_E(m)` at the observer shell. -/
  eta_at_shell : ℝ

/-- **Evaluation map at shell `m`** on the balanced reference horizon. -/
noncomputable def readoutAtShell (m : ℕ) : ShellLadderReadout :=
  let e := horizonEventAtShell m
  { event := e
    shell := m
    readout := evaluate e
    eta_at_shell := baryonAsymmetry e.slice m }

theorem readoutAtShell_eta (m : ℕ) :
    (readoutAtShell m).eta_at_shell = baryonAsymmetry (horizonEventAtShell m).slice m := rfl

theorem readoutAtShell_imprint (m : ℕ) :
    (readoutAtShell m).readout.imprint m = (readoutAtShell m).eta_at_shell := by
  unfold readoutAtShell evaluate
  rfl

theorem readoutAtShell_gEff (m : ℕ) :
    (readoutAtShell m).readout.gEff_at_apex = gEff hubbleReference := by
  unfold readoutAtShell evaluate
  simp [horizonEventAtShell, Event.slice, nowSliceOf, hubbleReference]

theorem lockin_apex_chart :
    ApexChart.ofNowSlice lockinNowSlice =
      ⟨1, 0, 1, 4⟩ := by
  rcases lockinNowSlice_fields with ⟨hφ, hΦ, hΩ, ht⟩
  dsimp [ApexChart.ofNowSlice]
  rw [hφ, hΦ, hΩ, ht]

theorem lockin_lapse_eq_five :
    ApexChart.diamondLapse (ApexChart.ofNowSlice lockinNowSlice) = 5 := by
  rw [ApexChart.diamondLapse_of_slice, lockinNowSlice_massUnit]

theorem lockin_gEff_eq_hubble :
    gEff lockinNowSlice.phi = lockinNowSlice.phi := by
  rcases lockinNowSlice_fields with ⟨hφ, _, _, _⟩
  rw [hφ, gEff_one]

theorem lockin_imprint_is_deltaE (m : ℕ) :
    lockinNowSlice.curvatureImprint m = deltaE m := by
  rcases lockinNowSlice_fields with ⟨_, _, hΩ, _⟩
  rw [NowSlice.curvatureImprint, hΩ, one_mul]

/-! ## Capstone -/

/-- **Causal-diamond closure:** local chart + global glue + evaluation map, discharged at lock-in. -/
structure CausalDiamondClosure where
  /-- Apex lapse is the familiar ADM opening. -/
  lapse_is_massUnit : ∀ s : NowSlice, (ApexChart.ofNowSlice s).diamondLapse = s.massUnit
  /-- Glue partition `α+γ=1`. -/
  glue_partition : imprintGlue.alpha + imprintGlue.gamma = 1
  /-- `G_eff` and `shellShape` share one exponent `α`. -/
  gEff_power : ∀ φ : ℝ, gEff φ = φ ^ imprintGlue.alpha
  /-- Discrete `Ω_k` on the slice. -/
  omegaK_discrete : ∀ e : Event, e.slice.omegaK = omegaKPartial e.shell
  /-- Lock-in diamond: `(H,Φ,Ω_k,t)=(1,0,1,4)`, `N=5`, `G_eff(H)=H`, `ξ_lock=5`. -/
  lockin_apex :
    lockinNowSlice.phi = 1 ∧
    lockinNowSlice.bigPhi = 0 ∧
    lockinNowSlice.omegaK = 1 ∧
    lockinNowSlice.apparentAge = 4 ∧
    lockinNowSlice.massUnit = 5 ∧
    gEff lockinNowSlice.phi = lockinNowSlice.phi ∧
    Event.xi lockinEvent = xiLockin

noncomputable def causalDiamondClosure : CausalDiamondClosure where
  lapse_is_massUnit := ApexChart.diamondLapse_of_slice
  glue_partition := imprintGlue_partition
  gEff_power := gEff_eq_imprintGlue_power
  omegaK_discrete := event_omegaK_is_discrete
  lockin_apex :=
    ⟨lockinNowSlice_fields.1,
      lockinNowSlice_fields.2.1,
      lockinNowSlice_fields.2.2.1,
      lockinNowSlice_fields.2.2.2,
      lockinNowSlice_massUnit,
      lockin_gEff_eq_hubble,
      lockinEvent_xi⟩

end HqivSpine.Physics.CausalDiamond
