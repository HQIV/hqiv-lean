import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.Thermodynamics
import HqivSpine.Topology.ShellBudget

/-!
# `HqivSpine.Physics.ThermalArrow` — the arrow of time from shell opening

The shell index `m` is the discrete cosmic clock. Along it two monotone quantities run in
opposite directions, pinning a thermodynamic arrow with **no extra input**:

* **Entropy increases.** Boltzmann entropy `S(m) = log N_m` of the accessible mode content
  `N_m = 8(m+1)` is *strictly increasing* (`boltzmannEntropy_strictMono`), hence monotone
  (second-law arrow) and *injective* — the ladder never revisits a coarse-grained state
  (`boltzmannEntropy_injective`).
* **Temperature decreases.** The ladder temperature `T_m = 1/(m+1)` is *strictly antitone*
  (`shellTemp_strictAnti`) — inner shells are hotter (`Thermodynamics.thirdLaw_hotter_inside`).

Bundled: outward on the clock, entropy goes up **and** temperature goes down (`thermal_arrow`).
The arrow's **equilibrium terminus** is the zero-deficit reference of `Topology.ShellBudget`
(`arrow_terminus_equilibrium`): the closed-shell Lyapunov front vanishes exactly there.

Honest scope: this is the monotone-Lyapunov *direction* of the discrete ladder, built on the
already-derived mode count and temperature — not a continuum coarse-graining theorem. Mathlib-only;
no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics.ThermalArrow

open HqivSpine.Physics HqivSpine.Physics.Thermodynamics

/-! ## Entropy increases -/

/-- The accessible mode content `N_m = 8(m+1)` is strictly increasing in the shell clock. -/
theorem shellModeMultiplicity_strictMono : StrictMono shellModeMultiplicity := by
  intro a b h
  rw [shellModeMultiplicity_eq, shellModeMultiplicity_eq]
  have : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  linarith

/-- **Boltzmann entropy** of the shell mode content: `S(m) = log N_m`. -/
noncomputable def boltzmannEntropy (m : ℕ) : ℝ := Real.log (shellModeMultiplicity m)

/-- Anchor value at the Planck pole: `S(0) = log 8` (the carrier multiplicity). -/
theorem boltzmannEntropy_zero : boltzmannEntropy 0 = Real.log 8 := by
  unfold boltzmannEntropy; rw [shellModeMultiplicity_eq]; norm_num

/-- **Second-law arrow:** entropy is strictly increasing along the shell clock. -/
theorem boltzmannEntropy_strictMono : StrictMono boltzmannEntropy := by
  intro a b h
  unfold boltzmannEntropy
  exact Real.log_lt_log (shellModeMultiplicity_pos a) (shellModeMultiplicity_strictMono h)

/-- Entropy never decreases. -/
theorem boltzmannEntropy_mono : Monotone boltzmannEntropy :=
  boltzmannEntropy_strictMono.monotone

/-- **Irreversibility:** distinct shells have distinct entropy — the ladder never returns to a
previously occupied coarse-grained state. -/
theorem boltzmannEntropy_injective : Function.Injective boltzmannEntropy :=
  boltzmannEntropy_strictMono.injective

/-! ## Temperature decreases -/

/-- The ladder temperature `T_m = 1/(m+1)` is strictly antitone along the clock. -/
theorem shellTemp_strictAnti : StrictAnti shellTemp := by
  intro a b h
  show shellTemp b < shellTemp a
  unfold shellTemp shellOmega
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hab : (a : ℝ) + 1 < (b : ℝ) + 1 := by
    have : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
    linarith
  exact one_div_lt_one_div_of_lt ha hab

/-! ## The bundled arrow and its terminus -/

/-- **The thermodynamic arrow:** moving outward on the shell clock, entropy strictly increases and
temperature strictly decreases. -/
theorem thermal_arrow {m m' : ℕ} (h : m < m') :
    boltzmannEntropy m < boltzmannEntropy m' ∧ shellTemp m' < shellTemp m :=
  ⟨boltzmannEntropy_strictMono h, shellTemp_strictAnti h⟩

/-- **Equilibrium terminus:** the closed-shell deficit Lyapunov front of `Topology.ShellBudget`
vanishes on the canonical horizon reference — the arrow points at the on-horizon quadratic-growth
equilibrium. -/
theorem arrow_terminus_equilibrium (n : ℕ) :
    HqivSpine.Topology.totalNegativeBudget (HqivSpine.Topology.S3NullReference n) = 0 :=
  HqivSpine.Topology.S3NullReference_totalNegativeBudget_zero n

end HqivSpine.Physics.ThermalArrow
