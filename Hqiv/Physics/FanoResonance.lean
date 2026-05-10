import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Hqiv.Geometry.HQVMetric

namespace Hqiv.Physics

/-!
**Detuned surfaces (status).** `detunedShellSurface` and `rindlerDetuningShared` are the **current**
closed-form **effective** ladder: same monogamy coefficient \(\gamma/2\) as in `c_rindler_shared`.
The **long-term** target (see `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md` §2.1) is to show this law is
**emergent**—e.g. leading term of a standing-wave / localization or dispersion expansion from the full
**8-channel** O-Maxwell + \(\varphi\) dynamics after Fano projection—so that the denominator
\(1 + \frac{\gamma}{2}m\) is **derived**, not a parallel axiom. The formalization is not there yet: this
file keeps the **definition** used by all resonance ratios until that bridge exists.
-/

/-- Fano-plane vertex index: `0` for EM/lepton axis, `1..6` for quark lines.

**Open:** each direction should eventually have its **own** motivated Fano-prime / shell ladder;
`ResonanceAxis.anchorShell` is the bookkeeping hook per vertex, but those anchors are not yet
uniquely fixed by the discrete null-lattice axiom alone (see `OctonionicZeta` module doc). -/
abbrev FanoVertex := Fin 7

/-- Resonance ladder orientation on a given vertex. -/
inductive LadderDirection
  | internal
  | reverse
deriving DecidableEq, Repr

/-- Shared metadata for a resonance axis on one Fano vertex. -/
structure ResonanceAxis where
  vertex : FanoVertex
  anchorShell : ℕ
  direction : LadderDirection
  /-- Integer hypercharge sign witness (`+1` or `-1`). -/
  hyperchargeSign : Int

/-- Generation index (`.two` heavy, `.one` middle, `.zero` light). -/
abbrev ResonanceGeneration := Fin 3

/-- Discrete shell surface leading term shared by lepton/quark ladders. -/
def shellSurface (m : ℕ) : ℝ :=
  (m + 1 : ℝ) * (m + 2 : ℝ)

/-- Shared Rindler detuning coefficient (`c = γ/2`). -/
noncomputable def c_rindler_shared : ℝ := gamma_HQIV / 2

/-- Rindler detuning factor used by resonance surfaces. -/
noncomputable def rindlerDetuningShared (x : ℝ) : ℝ := 1 + c_rindler_shared * x

/-- Detuned surface evaluated on the shell index itself. -/
noncomputable def detunedShellSurface (m : ℕ) : ℝ :=
  shellSurface m / rindlerDetuningShared (m : ℝ)

/--
Lock-in-centered shell coordinate used for higher-order detuning jets.
It vanishes at `referenceM` and stays bounded as `m → ∞`.
-/
noncomputable def lockinCenteredShellCoordinate (m : ℕ) : ℝ :=
  ((m : ℝ) - (referenceM : ℝ)) / ((m : ℝ) + (referenceM : ℝ) + 1)

/--
Second-jet detuning coefficient for the curved denominator extension.
The `2/5` factor mirrors the current `Δ`-quadratic normalization `(3+2)/5` split.
-/
noncomputable def c_rindler_2jet : ℝ := gamma_HQIV * (2 / 5 : ℝ)

/--
Third-jet detuning coefficient for the curved denominator extension.
The `2/5` factor mirrors the same normalization channel as `c_rindler_2jet`.
-/
noncomputable def c_rindler_3jet : ℝ := alpha * (2 / 5 : ℝ)

/--
Three-jet detuning denominator: affine Rindler term plus lock-in-centered curvature jets.
This is a parallel candidate ladder and does not replace `rindlerDetuningShared`.
-/
noncomputable def rindlerDetuningThreeJet (m : ℕ) : ℝ :=
  let u := lockinCenteredShellCoordinate m
  rindlerDetuningShared (m : ℝ) + c_rindler_2jet * u ^ 2 + c_rindler_3jet * u ^ 3

/-- Three-jet detuned shell surface candidate. -/
noncomputable def detunedShellSurfaceThreeJet (m : ℕ) : ℝ :=
  shellSurface m / rindlerDetuningThreeJet m

/-- Three-jet geometric resonance step candidate. -/
noncomputable def geometricResonanceStepThreeJet (m_from m_to : ℕ) : ℝ :=
  detunedShellSurfaceThreeJet m_from / detunedShellSurfaceThreeJet m_to

theorem lockinCenteredShellCoordinate_at_referenceM :
    lockinCenteredShellCoordinate referenceM = 0 := by
  unfold lockinCenteredShellCoordinate
  ring

theorem rindlerDetuningThreeJet_at_referenceM :
    rindlerDetuningThreeJet referenceM = rindlerDetuningShared (referenceM : ℝ) := by
  unfold rindlerDetuningThreeJet
  simp [lockinCenteredShellCoordinate_at_referenceM]

theorem detunedShellSurfaceThreeJet_at_referenceM :
    detunedShellSurfaceThreeJet referenceM = detunedShellSurface referenceM := by
  unfold detunedShellSurfaceThreeJet detunedShellSurface
  rw [rindlerDetuningThreeJet_at_referenceM]

/-- Positivity of the detuned shell surface. -/
theorem detunedShellSurface_pos (m : ℕ) : 0 < detunedShellSurface m := by
  unfold detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
  apply div_pos
  · norm_cast
    exact mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  ·
    rw [gamma_eq_2_5]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

/-- Resonance step as a quotient of detuned shell surfaces. -/
noncomputable def geometricResonanceStep (m_from m_to : ℕ) : ℝ :=
  detunedShellSurface m_from / detunedShellSurface m_to

/-- Positive geometric resonance step. -/
theorem geometricResonanceStep_pos (m_from m_to : ℕ) :
    0 < geometricResonanceStep m_from m_to := by
  unfold geometricResonanceStep
  exact div_pos (detunedShellSurface_pos m_from) (detunedShellSurface_pos m_to)

/--
Generic 3-generation resonance product.
`k21` is the heavy→middle step, `k10` is the middle→light step.
-/
def resonanceProductFromSteps (k21 k10 : ℝ) (gen : ResonanceGeneration) : ℝ :=
  match gen with
  | ⟨2, _⟩ => 1
  | ⟨1, _⟩ => k21
  | ⟨0, _⟩ => k21 * k10

/-- Any Fin-3 based axis has exactly three generations and no fourth. -/
theorem exactly_three_generations_fano :
    ¬ ∃ fourthGen : ResonanceGeneration,
      fourthGen ≠ ⟨0, by decide⟩ ∧
        fourthGen ≠ ⟨1, by decide⟩ ∧
          fourthGen ≠ ⟨2, by decide⟩ := by
  intro h
  rcases h with ⟨g, hg⟩
  fin_cases g <;> simp at hg

/-- Canonical lepton (EM) axis metadata. -/
def leptonAxis (anchorShell : ℕ) : ResonanceAxis :=
  { vertex := ⟨0, by decide⟩
    anchorShell := anchorShell
    direction := .reverse
    hyperchargeSign := 1 }

/-- Canonical up-type quark axis metadata. -/
def upQuarkAxis (vertex : Fin 3) (anchorShell : ℕ) : ResonanceAxis :=
  { vertex := ⟨vertex.val + 1, by
      have hv : vertex.val < 3 := vertex.isLt
      omega⟩
    anchorShell := anchorShell
    direction := .internal
    hyperchargeSign := 1 }

/-- Canonical down-type quark axis metadata. -/
def downQuarkAxis (vertex : Fin 3) (anchorShell : ℕ) : ResonanceAxis :=
  { vertex := ⟨vertex.val + 4, by
      have hv : vertex.val < 3 := vertex.isLt
      omega⟩
    anchorShell := anchorShell
    direction := .internal
    hyperchargeSign := -1 }

end Hqiv.Physics
