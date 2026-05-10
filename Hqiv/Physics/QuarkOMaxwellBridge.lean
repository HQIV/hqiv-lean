import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.Action

/-!
# Quark sector ↔ lifted O-Maxwell (proved structural links)

This module does **not** derive quark shell integers or GeV anchors from eigenmodes of the full
coupled dynamics (that program is documented in `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md`).

What it **does** prove is the already-implemented **algebraic spine** shared between:

* the quark meta-horizon ladder (`QuarkMetaResonance`, via `FanoResonance.geometricResonanceStep`), and
* the discrete O-Maxwell Euler–Lagrange slot (`Hqiv.EL_O_general`) packaged in `Action.lean`.

**Takeaway:** color/up/down ladders are assigned to **non-EM Fano vertices** (`ResonanceAxis`),
generation steps are **literal** `geometricResonanceStep` ratios of `detunedShellSurface`, and the
same **monogamy split** `α + γ = 1` feeds **both** the Rindler detuning coefficient `c_rindler_shared = γ/2`
inside those steps and the **`α` prefactor** on the O-Maxwell `a = 0` channel in `EL_O_general`.

---

**Mathematical summary (paper-style; matches Lean names).**

1. **Fano placement.** `upResonanceAxis.vertex = 1`, `downResonanceAxis.vertex = 4` (Fin 7 / `FanoVertex`);
   EM/lepton axis uses vertex `0`. Theorems: `upResonanceAxis_vertex_eq`, `downResonanceAxis_vertex_eq`,
   `upResonanceAxis_vertex_ne_em_vertex`, `downResonanceAxis_vertex_ne_em_vertex`.

2. **Shared detuned-step combinator.** For readout indices `m_from, m_to : ℕ`,
   `geometricResonanceStep m_from m_to = detunedShellSurface m_from / detunedShellSurface m_to`
   with `detunedShellSurface m = shellSurface m / (1 + (γ/2)·m)` and `shellSurface m = (m+1)(m+2)`.
   Quark internal factors are **not** differences `S(m_1)-S(m_0)`; they are **ratios of detuned surfaces**
   at the witness endpoints, e.g. `resonanceK_internal_zero_eq` expands to
   `geometricResonanceStep m_quark_up_top_shell m_quark_up_charm_shell` (and analogously for the
   down ladder and `crossChannelHeavyShellDetuning_eq`).

3. **Monogamy bridge (complementary roles, not one identical term).** Lattice monogamy gives
   `α + γ = 1` (`alpha_add_gamma`). Meta-horizon resonance uses **γ** only via `c_rindler_shared = γ/2`
   in `detunedShellSurface`. The lifted O-Maxwell EL on octonion channel `a = 0` carries an
   **informational** correction proportional to **`α`·log(φ+1)·∇φ** (`EL_O_general_zero_eq`).
   The bundled theorem `quark_detuning_and_omaxwell_em_slot_share_monogamy_split` records **both**
   coefficients as consequences of the **same** split—it does **not** identify the Rindler detuning
   denominator with the `α` φ-gradient term (they are different slots: **γ/2** in surface detuning,
   **α** in the EM-slot EL coupling).

4. **Emergence (research target, not proved here).** The closed form
   `detunedShellSurface m = S(m) / (1 + (γ/2)·m)` is **implemented** as a definition in
   `FanoResonance.lean`. The intended long-term picture is that this is a **first-order effective**
   law from full 8-component O-Maxwell + φ dynamics (standing-wave / localization on the seven
   imaginaries, then Fano-line projection)—so the factor `1 + (γ/2)·m` would be **derived**, not an
   independent postulate. See `AGENTS/O_MAXWELL_EIGEN_SHELL_SELECTION.md` §2.1.
-/

namespace Hqiv.Physics

open Hqiv

/-! ## Fano-plane placement (quark lines vs EM vertex) -/

theorem upResonanceAxis_vertex_eq : upResonanceAxis.vertex = (⟨1, by decide⟩ : FanoVertex) := by
  rfl

theorem downResonanceAxis_vertex_eq : downResonanceAxis.vertex = (⟨4, by decide⟩ : FanoVertex) := by
  rfl

theorem upResonanceAxis_vertex_ne_em_vertex : upResonanceAxis.vertex ≠ (⟨0, by decide⟩ : FanoVertex) := by
  rw [upResonanceAxis_vertex_eq]
  decide

theorem downResonanceAxis_vertex_ne_em_vertex : downResonanceAxis.vertex ≠ (⟨0, by decide⟩ : FanoVertex) := by
  rw [downResonanceAxis_vertex_eq]
  decide

/-! ## Quark internal steps are the same `geometricResonanceStep` combinator -/

theorem resonanceK_internal_zero_eq :
    resonanceK_internal ⟨0, by decide⟩ =
      geometricResonanceStep m_quark_up_top_shell m_quark_up_charm_shell := by
  rfl

theorem resonanceK_internal_one_eq :
    resonanceK_internal ⟨1, by decide⟩ =
      geometricResonanceStep m_quark_up_charm_shell m_quark_up_light_shell := by
  rfl

theorem resonanceK_internal_down_zero_eq :
    resonanceK_internal_down ⟨0, by decide⟩ =
      geometricResonanceStep m_quark_down_bottom_shell m_quark_down_strange_shell := by
  rfl

theorem resonanceK_internal_down_one_eq :
    resonanceK_internal_down ⟨1, by decide⟩ =
      geometricResonanceStep m_quark_down_strange_shell m_quark_down_light_shell := by
  rfl

theorem crossChannelHeavyShellDetuning_eq :
    crossChannelHeavyShellDetuning =
      geometricResonanceStep m_quark_up_top_shell m_quark_down_bottom_shell := by
  rfl

/-! ## Monogamy: `α` in O-Maxwell φ-slot vs `γ` in detuned resonance steps -/

/--
**Complementary monogamy coefficients.** The quark ladder uses `gamma_HQIV` only through
`c_rindler_shared` in `detunedShellSurface`; the O-Maxwell EL on channel `a = 0` subtracts a term
proportional to `alpha`. The pair satisfies `alpha + gamma_HQIV = 1`.
-/
theorem quark_detuning_and_omaxwell_em_slot_share_monogamy_split :
    alpha + gamma_HQIV = 1 ∧
      c_rindler_shared = gamma_HQIV / 2 ∧
        ∀ (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (ν : Fin 4),
          EL_O_general J_src A φ_val 0 ν =
            F_divergence_sum A 0 ν - 4 * Real.pi * J_src 0 ν -
              alpha * Real.log (φ_val + 1) * grad_phi ν :=
  ⟨alpha_add_gamma, rfl, fun J_src A φ_val ν =>
    EL_O_general_zero_eq J_src A φ_val ν⟩

end Hqiv.Physics
