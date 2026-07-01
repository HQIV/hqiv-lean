import HqivSpine.Physics.BBN
import HqivSpine.Physics.ThermalArrow
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `HqivSpine.Physics.WeakDecay` — β-decay and the freeze-out `n/p` ratio

The weak sector that **closes the abstract `n/p` ratio left open by `BBN`**, built structurally from a
single positive `Q`-value (the neutron–proton energy release) — no PDG lifetime or mass literal.

* **Sargent's rule.** The decay rate `Γ(Q) = g·Q⁵` is positive and strictly increasing in `Q`
  (`sargentRate_strictMono_in_Q`), so the lifetime `τ = 1/Γ` is positive and strictly *decreasing* in
  `Q` (`lifetime_antitone_in_Q`) — a larger energy release decays faster.
* **Freeze-out `n/p`.** The neutron-to-proton ratio is the Boltzmann factor `r = e^{−Q/T}`: always in
  `(0,1)` for `Q,T > 0` (`npRatio_pos`, `npRatio_lt_one`), decreasing with the splitting
  (`npRatio_antitone_in_Q`) and increasing with temperature (`npRatio_monotone_in_T`). On the shell
  clock `T_m = 1/(m+1)` it is `e^{−Q(m+1)}` (`npRatioAtShell_eq`), suppressed on colder outer shells
  (`npRatioAtShell_antitone`).
* **Closes `BBN`.** Feeding the weak Boltzmann ratio into `BBN.helium4MassFraction` gives a physical
  `Y_p < 1` (`helium_fraction_lt_one_from_weak`, `helium_fraction_lt_one_at_shell`) — the previously
  abstract `r` is now the weak freeze-out factor.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.WeakDecay

open HqivSpine.Physics HqivSpine.Physics.Thermodynamics

/-! ## Sargent's rule -/

/-- **Decay rate** by Sargent's rule `Γ(Q) = g·Q⁵`. -/
noncomputable def sargentRate (g Q : ℝ) : ℝ := g * Q ^ 5

/-- **Mean lifetime** `τ = 1/Γ`. -/
noncomputable def lifetime (g Q : ℝ) : ℝ := 1 / sargentRate g Q

theorem sargentRate_pos (g Q : ℝ) (hg : 0 < g) (hQ : 0 < Q) : 0 < sargentRate g Q := by
  unfold sargentRate; positivity

theorem lifetime_pos (g Q : ℝ) (hg : 0 < g) (hQ : 0 < Q) : 0 < lifetime g Q := by
  unfold lifetime; exact one_div_pos.mpr (sargentRate_pos g Q hg hQ)

/-- **Sargent scaling:** the rate strictly increases with the `Q`-value. -/
theorem sargentRate_strictMono_in_Q (g : ℝ) (hg : 0 < g) {Q Q' : ℝ} (hQ : 0 < Q) (h : Q < Q') :
    sargentRate g Q < sargentRate g Q' := by
  unfold sargentRate
  have hpow : Q ^ 5 < Q' ^ 5 := by gcongr
  exact mul_lt_mul_of_pos_left hpow hg

/-- **A larger energy release decays faster:** the lifetime strictly decreases with `Q`. -/
theorem lifetime_antitone_in_Q (g : ℝ) (hg : 0 < g) {Q Q' : ℝ} (hQ : 0 < Q) (h : Q < Q') :
    lifetime g Q' < lifetime g Q := by
  unfold lifetime
  exact one_div_lt_one_div_of_lt (sargentRate_pos g Q hg hQ) (sargentRate_strictMono_in_Q g hg hQ h)

/-! ## Freeze-out neutron-to-proton ratio -/

/-- **Freeze-out `n/p` ratio** as the Boltzmann factor `e^{−Q/T}`. -/
noncomputable def npRatio (Q T : ℝ) : ℝ := Real.exp (-(Q / T))

theorem npRatio_pos (Q T : ℝ) : 0 < npRatio Q T := Real.exp_pos _

/-- The ratio is below `1` whenever the splitting and temperature are positive (neutron-poor). -/
theorem npRatio_lt_one (Q T : ℝ) (hQ : 0 < Q) (hT : 0 < T) : npRatio Q T < 1 := by
  unfold npRatio
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  have : 0 < Q / T := div_pos hQ hT
  linarith

/-- More splitting ⇒ fewer neutrons: `r` strictly decreases in `Q`. -/
theorem npRatio_antitone_in_Q (T : ℝ) (hT : 0 < T) {Q Q' : ℝ} (h : Q < Q') :
    npRatio Q' T < npRatio Q T := by
  unfold npRatio
  rw [Real.exp_lt_exp]
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  have hdiv : Q / T < Q' / T := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_lt_mul_of_pos_right h hTinv
  linarith

/-- Hotter ⇒ more neutrons: `r` strictly increases in `T`. -/
theorem npRatio_monotone_in_T (Q : ℝ) (hQ : 0 < Q) {T T' : ℝ} (hT : 0 < T) (h : T < T') :
    npRatio Q T < npRatio Q T' := by
  unfold npRatio
  rw [Real.exp_lt_exp]
  have hrec : 1 / T' < 1 / T := one_div_lt_one_div_of_lt hT h
  have hdiv : Q / T' < Q / T := by
    rw [div_eq_mul_one_div Q T', div_eq_mul_one_div Q T]
    exact mul_lt_mul_of_pos_left hrec hQ
  linarith

/-! ## On the shell clock -/

/-- The freeze-out ratio at shell `m`, using the ladder temperature `T_m = 1/(m+1)`. -/
noncomputable def npRatioAtShell (Q : ℝ) (m : ℕ) : ℝ := npRatio Q (shellTemp m)

/-- Closed form `e^{−Q(m+1)}` (the `1/T` of the shell temperature is the horizon depth `m+1`). -/
theorem npRatioAtShell_eq (Q : ℝ) (m : ℕ) :
    npRatioAtShell Q m = Real.exp (-(Q * ((m : ℝ) + 1))) := by
  unfold npRatioAtShell npRatio shellTemp shellOmega
  congr 1
  rw [one_div, div_inv_eq_mul]

theorem npRatioAtShell_lt_one (Q : ℝ) (hQ : 0 < Q) (m : ℕ) : npRatioAtShell Q m < 1 :=
  npRatio_lt_one Q (shellTemp m) hQ (shellTemp_pos m)

/-- **Colder outer shells suppress neutrons:** the shell `n/p` ratio strictly decreases outward. -/
theorem npRatioAtShell_antitone (Q : ℝ) (hQ : 0 < Q) {m m' : ℕ} (h : m < m') :
    npRatioAtShell Q m' < npRatioAtShell Q m :=
  npRatio_monotone_in_T Q hQ (shellTemp_pos m') (ThermalArrow.shellTemp_strictAnti h)

/-! ## Closing the `BBN` input -/

/-- **Closes `BBN`:** the helium mass fraction from the weak Boltzmann ratio is physical (`< 1`). -/
theorem helium_fraction_lt_one_from_weak (Q T : ℝ) (hQ : 0 < Q) (hT : 0 < T) :
    BBN.helium4MassFraction (npRatio Q T) < 1 :=
  (BBN.helium4MassFraction_lt_one_iff _ (npRatio_pos Q T).le).mpr (npRatio_lt_one Q T hQ hT)

/-- The same closure on the shell clock. -/
theorem helium_fraction_lt_one_at_shell (Q : ℝ) (hQ : 0 < Q) (m : ℕ) :
    BBN.helium4MassFraction (npRatioAtShell Q m) < 1 :=
  (BBN.helium4MassFraction_lt_one_iff _ (npRatio_pos Q (shellTemp m)).le).mpr
    (npRatioAtShell_lt_one Q hQ m)

end HqivSpine.Physics.WeakDecay
