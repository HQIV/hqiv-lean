import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.FanoResonance

namespace Hqiv
namespace Physics
namespace ContinuousXiMixingGeometry

open Hqiv

/-!
# Mixing geometry rows (adjacent to the 7×7 coupling solve)

Python `scripts/hqiv_coupling_linear_system.py` extends the overdetermined system with
rows derived from the same detuned-surface ladder as `geometricResonanceStep`:

* **Monogamy:** `Σ_v w_v c_v = 1` (Fano weights).
* **Generation ladders:** `c_{v+1} / c_v = geometricResonanceStep(m_v, m_{v+1})` on up/down vertices.
* **Weak / EM:** `c₃ / c₀` tied to triality Weinberg slot × detuned imprint on Fano lines `{0,3,4}` vs `{0,1,2}`.
* **Strong slot:** `1/α_eff` at the down-g0 ξ from a φ-slope ratio (no PDG in the row).

This module records the **Lean names** for those targets; numeric solve stays in Python.
-/

/-- Fano line indices in the standard PG(2,2) table (Python `FANO_LINE_*`). -/
def fanoLineEmUp : Fin 7 := ⟨0, by decide⟩

def fanoLineWeak : Fin 7 := ⟨1, by decide⟩

def fanoLineScalar : Fin 7 := ⟨2, by decide⟩

/-- Triality bare hypercharge fraction: `g₁²/(g₁²+g₂²)` with `g₂=1/3`, `g₁=γ/3`. -/
noncomputable def sin2ThetaWTriality : ℝ :=
  let g2 := (1 : ℝ) / 3
  let g1 := (1 - alpha) / 3
  g1 ^ 2 / (g1 ^ 2 + g2 ^ 2)

theorem sin2ThetaWTriality_pos : 0 < sin2ThetaWTriality := by
  unfold sin2ThetaWTriality
  rw [alpha_eq_3_5]
  norm_num

/-- Weak-line vs EM-line detuned imprint factor (shell chart `m` only; ξ chart in Python). -/
noncomputable def weakEmDetunedImprint (mWeak mEm : ℕ) : ℝ :=
  geometricResonanceStep mWeak mEm

/-- Geometric target for the `c₃/c₀` mixing row coefficient. -/
noncomputable def sin2ThetaWGeometricShell (mWeak mEm : ℕ) : ℝ :=
  sin2ThetaWTriality * weakEmDetunedImprint mWeak mEm

/-- Generation-ladder ratio between adjacent Fano vertices (same combinatorics as quark ladders). -/
noncomputable def generationCoeffRatio (mHi mLo : ℕ) : ℝ :=
  geometricResonanceStep mHi mLo

theorem generationCoeffRatio_pos (mHi mLo : ℕ) :
    0 < generationCoeffRatio mHi mLo :=
  geometricResonanceStep_pos mHi mLo

end ContinuousXiMixingGeometry
end Physics
end Hqiv
