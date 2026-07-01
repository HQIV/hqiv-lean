import HqivSpine.Physics.Shell
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `HqivSpine.Physics.CurvatureKernel` — the unified curvature log kernel

Both strong-sector readout slots the gluon-curvature note distinguishes —
the Hopf **contact** amplification and the binding **ladder** trace selection —
are the *same* machine-checked kernel

`K(x, c) = 1 + c · α · log x`,  `α = 3/5`,

evaluated at two different chart coordinates:

* **contact** coordinate `1 + (φ(w)/6)·α` (phase-lift torsion slot);
* **ladder** coordinate `φ(m) + 1` (auxiliary-field / `α_eff` slot).

The spine's effective inverse coupling is literally `1/α_GUT · K(ladder, c)`, and
because the contact coordinate is strictly below the ladder coordinate at every
shell, monotonicity of `K` forces **contact amplification strictly below ladder
amplification** — a general theorem, not a numerical check.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation

/-- **The single strong-sector curvature log kernel** `K(x,c) = 1 + c·α·log x`. -/
noncomputable def curvatureLogKernel (x c : ℝ) : ℝ := 1 + c * alphaEM * Real.log x

/-- **Contact chart coordinate:** phase-lift slot `1 + (φ(w)/6)·α`. -/
noncomputable def contactArg (w : ℕ) : ℝ := 1 + ((phi w : ℝ) / 6) * alphaEM

/-- **Ladder chart coordinate:** auxiliary-field slot `φ(m) + 1`. -/
noncomputable def ladderArg (m : ℕ) : ℝ := (phi m : ℝ) + 1

/-- At zero running coefficient the kernel is `1` (unification start of the ladder). -/
theorem curvatureLogKernel_zero (x : ℝ) : curvatureLogKernel x 0 = 1 := by
  unfold curvatureLogKernel; ring

/-- **The spine's effective inverse coupling is the bare coupling times the ladder
kernel:** `1/α_eff(m) = 1/α_GUT · K(φ(m)+1, c)`. -/
theorem oneOverAlphaEffAtShell_eq_bare_mul_ladderKernel (m : ℕ) (c : ℝ) :
    oneOverAlphaEffAtShell m c = oneOverAlphaBare * curvatureLogKernel (ladderArg m) c := by
  unfold oneOverAlphaEffAtShell curvatureLogKernel ladderArg; ring

theorem phi_cast_pos (m : ℕ) : 0 < (phi m : ℝ) := by
  have : 0 < phi m := by unfold phi; omega
  exact_mod_cast this

/-- **The contact coordinate exceeds `1`** (so its log is positive). -/
theorem one_lt_contactArg (w : ℕ) : 1 < contactArg w := by
  unfold contactArg
  rw [alphaEM_eq]
  have := phi_cast_pos w
  nlinarith

/-- **Contact coordinate is strictly below the ladder coordinate** at every shell
(`1 + φ/10 < φ + 1`). -/
theorem contactArg_lt_ladderArg (m : ℕ) : contactArg m < ladderArg m := by
  unfold contactArg ladderArg
  rw [alphaEM_eq]
  have := phi_cast_pos m
  nlinarith

/-- **The kernel is strictly increasing in its coordinate** for positive running
coefficient (monotonicity of `log`). -/
theorem curvatureLogKernel_lt_of_arg_lt (c x y : ℝ) (hc : 0 < c) (hx : 0 < x) (hxy : x < y) :
    curvatureLogKernel x c < curvatureLogKernel y c := by
  unfold curvatureLogKernel
  have hlog : Real.log x < Real.log y := Real.log_lt_log hx hxy
  have hα : 0 < alphaEM := by rw [alphaEM_eq]; norm_num
  have := mul_lt_mul_of_pos_left hlog (mul_pos hc hα)
  linarith

/-- **Contact amplification strictly below ladder amplification** — the gluon-curvature
note's kernel ordering, here a general consequence of `contactArg < ladderArg` and
monotonicity of `K`. -/
theorem contactKernel_lt_ladderKernel (m : ℕ) (c : ℝ) (hc : 0 < c) :
    curvatureLogKernel (contactArg m) c < curvatureLogKernel (ladderArg m) c :=
  curvatureLogKernel_lt_of_arg_lt c (contactArg m) (ladderArg m) hc
    (by have := one_lt_contactArg m; linarith) (contactArg_lt_ladderArg m)

end HqivSpine.Physics
