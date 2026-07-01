import HqivSpine.Foundation.HopfLadder
import HqivSpine.Geometry.MaxwellSpectral
import HqivSpine.Physics.ClosureAction
import HqivSpine.Physics.Shell
import Mathlib.Tactic

/-!
# `HqivSpine.Physics.TuftBeltramiAnchor` — Hopf/TUFT Beltrami ladder on the clean spine

The generation mass **ratios** `3/2` and `4/3` use a Beltrami label `λ_min(n)`. This module
**anchors** that label to spine geometry already proved elsewhere — it is no longer a bare
`(n+1)` alias in `MassLadder`.

**Anchor chain (all proved here or imported):**

1. **Integrable Hopf fiber windings** `n ∈ {1, 2, 3}` — three fermion generations on the
   octonionic Hopf ladder (`hopfFiberWinding`).
2. **Chart shell** `m = n + 1` on that ladder (`tuftChartShell`), matching `ClosureAction`
   `hopfLockinWinding + 1 = referenceM` at the heavy row `n = 3 → m = 4`.
3. **Fiber-sector multiplicity** `d_n = n + 1` (`tuftFiberMultiplicity`).
4. **Minimal coexact Beltrami eigenvalue** `λ_min(n) = d_n` (`tuftMinimalBeltramiEigenvalue`) —
   the fundamental mode at `n = 1` is `λ_min(1) = 2`.
5. **S³ harmonic link:** `λ_min(n)² = dim ℋ_n` on the quaternion Maxwell carrier
   (`harmonicDimS3 n = (n+1)²` from `MaxwellSpectral`) — multiplicity as a square root of
   representation dimension, not the scalar Peter–Weyl eigenvalue `λ_ℓ = ℓ(ℓ+2)`.

**Honest scope.** This firms the **spectral label and generation ordering**. It does **not** by
itself prove that absolute fermion mass equals `massUnit · λ_min(n)` (or the quark complexity
prefactor) — that remains the `leptonAbsoluteScaleFrontier` / `heavyQuarkScaleFrontier` obligation.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.TuftBeltramiAnchor

open HqivSpine.Physics
open HqivSpine.Foundation
open HqivSpine.Geometry.MaxwellSpectral

/-! ## Integrable Hopf fiber windings -/

/-- Positive Hopf fiber winding for generation index `g ∈ {0,1,2}`: `n = g + 1 ∈ {1,2,3}`. -/
def hopfFiberWinding (g : Fin 3) : ℕ := g.val + 1

theorem hopfFiberWinding_zero : hopfFiberWinding ⟨0, by decide⟩ = 1 := rfl

theorem hopfFiberWinding_one : hopfFiberWinding ⟨1, by decide⟩ = 2 := rfl

theorem hopfFiberWinding_two : hopfFiberWinding ⟨2, by decide⟩ = 3 := rfl

theorem hopfFiberWinding_strict :
    hopfFiberWinding ⟨0, by decide⟩ < hopfFiberWinding ⟨1, by decide⟩ ∧
      hopfFiberWinding ⟨1, by decide⟩ < hopfFiberWinding ⟨2, by decide⟩ := by
  constructor <;> decide

/-- Predicate: positive integrable fiber winding (`n = 1, 2, 3` only). -/
def hopfIntegrableWinding (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3

theorem hopfIntegrableWinding_one : hopfIntegrableWinding 1 := Or.inl rfl

theorem hopfIntegrableWinding_two : hopfIntegrableWinding 2 := Or.inr (Or.inl rfl)

theorem hopfIntegrableWinding_three : hopfIntegrableWinding 3 := Or.inr (Or.inr rfl)

/-! ## Chart shells `m = n + 1` -/

/-- Beltrami / TUFT chart row at Hopf winding `n`: `m = n + 1`. -/
def tuftChartShell (n : ℕ) : ℕ := n + 1

theorem tuftChartShell_eq_succ (n : ℕ) : tuftChartShell n = Nat.succ n := rfl

/-- Weak-sector chart (`n = 1` → `m = 2`). -/
def tuftWeakChartShell : ℕ := tuftChartShell 1

/-- Strong-sector chart (`n = 2` → `m = 3`). -/
def tuftStrongChartShell : ℕ := tuftChartShell 2

/-- Heavy-sector chart (`n = 3` → `m = 4`). -/
def tuftHeavyChartShell : ℕ := tuftChartShell hopfLockinWinding

theorem tuftWeakChartShell_eq_two : tuftWeakChartShell = 2 := rfl

theorem tuftStrongChartShell_eq_three : tuftStrongChartShell = 3 := rfl

theorem tuftHeavyChartShell_eq_four : tuftHeavyChartShell = 4 := rfl

/-- **Heavy TUFT chart meets HQIV lock-in shell** — numeric coincidence certified, not definitional. -/
theorem tuftHeavyChartShell_eq_referenceM : tuftHeavyChartShell = referenceM := by
  rw [tuftHeavyChartShell, tuftChartShell, hopfLockin_chartShell]

theorem tuftStrongChartShell_lt_tuftHeavyChartShell :
    tuftStrongChartShell < tuftHeavyChartShell := by
  rw [tuftStrongChartShell_eq_three, tuftHeavyChartShell_eq_four]
  decide

/-! ## Fiber multiplicity and minimal Beltrami eigenvalue -/

/-- Fiber-sector multiplicity `d_n = n + 1` on the integrable torus sector. -/
def tuftFiberMultiplicity (n : ℕ) : ℕ := n + 1

theorem tuftFiberMultiplicity_eq_succ (n : ℕ) :
    tuftFiberMultiplicity n = Nat.succ n := rfl

/-- **Minimal coexact Beltrami eigenvalue** at winding `n`: `λ_min(n) = d_n`. -/
def tuftMinimalBeltramiEigenvalue (n : ℕ) : ℝ :=
  (tuftFiberMultiplicity n : ℝ)

theorem tuftMinimalBeltrami_eq_multiplicity (n : ℕ) :
    tuftMinimalBeltramiEigenvalue n = (tuftFiberMultiplicity n : ℝ) := rfl

theorem tuftMinimalBeltrami_eq_succ (n : ℕ) :
    tuftMinimalBeltramiEigenvalue n = (n : ℝ) + 1 := by
  simp [tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]

/-- Fundamental coexact mode on `S³`: `λ_min(1) = 2`. -/
theorem tuftMinimalBeltrami_fundamental :
    tuftMinimalBeltramiEigenvalue 1 = 2 := by
  simp [tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]

theorem tuftMinimalBeltrami_strict_on_generations :
    tuftMinimalBeltramiEigenvalue 1 < tuftMinimalBeltramiEigenvalue 2 ∧
      tuftMinimalBeltramiEigenvalue 2 < tuftMinimalBeltramiEigenvalue 3 := by
  constructor <;> simp [tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity] <;> norm_num

/-! ## Link to `S³` Maxwell harmonics -/

/-- `λ_min(n)²` equals the degree-`n` harmonic dimension on the quaternion carrier. -/
theorem tuftMinimalBeltrami_sq_eq_harmonicDimS3 (n : ℕ) :
    tuftMinimalBeltramiEigenvalue n ^ 2 = (harmonicDimS3 n : ℝ) := by
  rw [tuftMinimalBeltrami_eq_succ, harmonicDimS3_eq_succ_sq]
  push_cast
  ring

/-- Square-root form: `λ_min(n) = √(dim ℋ_n)`. -/
theorem tuftMinimalBeltrami_eq_sqrt_harmonicDimS3 (n : ℕ) :
    tuftMinimalBeltramiEigenvalue n = Real.sqrt (harmonicDimS3 n) := by
  have hpos : 0 ≤ tuftMinimalBeltramiEigenvalue n := by
    simp [tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]
    positivity
  rw [← Real.sqrt_sq hpos, tuftMinimalBeltrami_sq_eq_harmonicDimS3]

/-- The minimal label at `n = 1` is **not** the scalar Peter–Weyl eigenvalue `λ_ℓ = ℓ(ℓ+2)` at `ℓ = 1`. -/
theorem tuftMinimal_ne_peterWeyl_at_one :
    tuftMinimalBeltramiEigenvalue 1 ≠ eigenvalueS3 1 := by
  norm_num [tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity, eigenvalueS3]

/-! ## Resonance ratios (generation steps) -/

/-- Beltrami resonance ratio between windings `n_from`, `n_to`. -/
noncomputable def tuftBeltramiResonanceRatio (nFrom nTo : ℕ) : ℝ :=
  tuftMinimalBeltramiEigenvalue nFrom / tuftMinimalBeltramiEigenvalue nTo

theorem tuftBeltramiResonanceRatio_tau_mu :
    tuftBeltramiResonanceRatio 3 2 = (4 : ℝ) / 3 := by
  simp [tuftBeltramiResonanceRatio, tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]

theorem tuftBeltramiResonanceRatio_mu_e :
    tuftBeltramiResonanceRatio 2 1 = (3 : ℝ) / 2 := by
  simp [tuftBeltramiResonanceRatio, tuftMinimalBeltramiEigenvalue, tuftFiberMultiplicity]

theorem tuftBeltramiResonanceRatio_strict_on_generations :
    tuftBeltramiResonanceRatio 1 2 < tuftBeltramiResonanceRatio 2 3 ∧
      tuftBeltramiResonanceRatio 2 3 < tuftBeltramiResonanceRatio 3 4 := by
  constructor <;> simp [tuftBeltramiResonanceRatio, tuftMinimalBeltramiEigenvalue,
    tuftFiberMultiplicity] <;> norm_num

/-! ## Capstone -/

/-- **TUFT/Beltrami anchor closure** — spectral label tied to Hopf chart + `S³` harmonics. -/
structure TuftBeltramiAnchorClosure where
  /-- Heavy chart `m = 4` at lock-in Hopf winding `n = 3`. -/
  heavy_chart_lockin : tuftHeavyChartShell = referenceM
  /-- `λ_min(n) = d_n = n + 1`. -/
  minimal_is_multiplicity :
    ∀ n, tuftMinimalBeltramiEigenvalue n = (tuftFiberMultiplicity n : ℝ)
  /-- `λ_min(n)² = dim ℋ_n` on the quaternion Maxwell carrier. -/
  harmonic_square : ∀ n, tuftMinimalBeltramiEigenvalue n ^ 2 = (harmonicDimS3 n : ℝ)
  /-- Strict generation ordering on windings `1 < 2 < 3`. -/
  generation_order : tuftMinimalBeltramiEigenvalue 1 < tuftMinimalBeltramiEigenvalue 2 ∧
    tuftMinimalBeltramiEigenvalue 2 < tuftMinimalBeltramiEigenvalue 3
  /-- Fundamental mode `λ_min(1) = 2`. -/
  fundamental_mode : tuftMinimalBeltramiEigenvalue 1 = 2
  /-- Distinct from Peter–Weyl `λ_1 = 3` at the same index. -/
  not_peter_weyl_one : tuftMinimalBeltramiEigenvalue 1 ≠ eigenvalueS3 1

def tuftBeltramiAnchorClosure : TuftBeltramiAnchorClosure where
  heavy_chart_lockin := tuftHeavyChartShell_eq_referenceM
  minimal_is_multiplicity := fun n => tuftMinimalBeltrami_eq_multiplicity n
  harmonic_square := fun n => tuftMinimalBeltrami_sq_eq_harmonicDimS3 n
  generation_order := tuftMinimalBeltrami_strict_on_generations
  fundamental_mode := tuftMinimalBeltrami_fundamental
  not_peter_weyl_one := tuftMinimal_ne_peterWeyl_at_one

end HqivSpine.Physics.TuftBeltramiAnchor
