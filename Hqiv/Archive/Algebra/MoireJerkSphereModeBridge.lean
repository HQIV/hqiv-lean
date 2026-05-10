import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

import Hqiv.Algebra.OctonionAxisAngles
import Hqiv.Algebra.OctonionSphereConstruction
import Hqiv.Algebra.OctonionSphereFourierPatch

open scoped ArithmeticFunction.Omega
open ArithmeticFunction

/-!
# Moiré jerk ↔ patch phasor frequency, and the `A₇ = dV₈/dr` surface proxy

Integer-shell embeddings (`embedNatFour`, `quaternionEmbed`, `sumSqInt8` — see
`OctonionSphereFourierAxis` / `OctonionSphereConstruction`) appear in **encoding** pipelines for the
scalar `M` in scripts. **Patch search** is **one-dimensional** in the index `j`: moiré cumulative
variation, cusps, and BST (`MoireCuspBracket`, `MoireToyThresholdSearch`) — not a spatial vector or
“quantum ray” search in a slice.

This file proves a **purely analytic** statement needed for the slope–**jerk** story:

* For a score sampled as a **sinusoid in the patch index** `j` with frequency `β`,
  `moirePatchSlopeStep` is the discrete second difference, hence a **closed form**
  `−4 sin(α + β(j+1)) · sin²(β/2)`.

So the **mode frequency** `β` is **visible in the jerk** through the factor `sin²(β/2)` (and in the
oscillating prefactor). When `β` is the **intrinsic axis angle** `π/(2Ω m)` (`intrinsicShellAxisAngle`),
the small-angle content is **explicitly tied to** `Ω m` — the same arithmetic label used in the Fourier
patch phasor elsewhere.

Separately, `OctonionSphereConstruction` already proves **`deriv continuousBallVolume8 = continuousSphereArea7`**, i.e. the classical **`A₇(r) = dV₈/dr`** identification for the ambient `ℝ⁸` ball / sphere
proxies. Any pipeline that wraps **bulk** `V₈` into a phase and then compares **radial** increments
samples **`A₇`** at `r = √m`; this lemma bank does **not** identify that pipeline with `moirePatchSlopeStep`
without an explicit definition of the score map (see roadmap in `OctonionSphereFourierPatch`).

## Which way the implication goes (common pitfall)

What is **proved** here is **analytic forward implication** on a **fixed model**:

> If `S` is this intrinsic sinusoid on the patch index, **then** `moirePatchSlopeStep` has the stated
> closed form (hence Ω enters the formula in a **controlled** way).

That is **not** the converse

> at every index where the discrete jerk is nonzero, some separate “result” / witness / mode must hold,

nor “every slope jerk **contains** a result.” Jerks from noise, harmonics, discretization, or wrong
score models can all produce nonzero `moirePatchSlopeStep` without encoding the statement you care about.

The **narrative** you want for applications is often the **other** direction — *if* genuine encoded
information is present in the signal *as modeled*, *then* it should be **visible** in jerk (or in a
chosen jerk band) — which would need **extra hypotheses** tying your pipeline’s `S` to that model and
stating **injectivity** / non-degeneracy. None of that is a theorem in this file; only the forward
sinusoid algebra is.

## Encoding bridge (open) vs **moiré–cusp patch search** (formal)

Whether an independent notion of solution (e.g. CNF on `M`) is equivalent to a
`FourierPatchConcentration`-style bundle is the **encoding bridge** flagged in
`AGENTS/archive/OCTONION_SAT_PIPELINE.md` / Target~0 in `AGENTS/archive/FT_PATCH_CLOSED_TARGET.md`.

Independently, the **supported Lean story for searching the patch** is **one-dimensional** in `j`:
**monotone cumulative absolute variation**, **cusp / threshold crossing**, **BST**
(`MoireCuspBracket`, `MoireToyThresholdSearch`). Fourier correlations and Ω-axis phasors feed the **same**
ordered-index score; they do **not** define a second “vector search” in an auxiliary plane.

## Same *shape* as Euclid’s primes (construction + forcing — analogy)

**Euclid (infinitude of primes):** For each `n : ℕ`, build `N = n! + 1`; any prime divisor of `N` cannot
divide `n!`, so you get prime content **beyond** any finite list packaged in `n!`. Mathlib:
`Nat.exists_infinite_primes` (`Mathlib.Data.Nat.Prime.Infinite`). The logical **mold** is:
**∀** finite combinatorial input **→** **construct** one integer **→** **force** a consequence by
divisibility / factorization (here: a new prime).

**HQIV encoding (same mold, different conclusion — mostly narrative):** For a given CNF over a finite
literal alphabet, the scripts **construct** a single exact integer `M` as a **product** of per-clause
prime-power data (`encode_formula_to_M` in `scripts/hqiv_geometric_3sat_demo.py`), with embeddings into
shell bookkeeping (`quaternionEmbed`, `embedNatFour`, `sumSqInt8`).

The **open** step — the would-be analog of “`minFac(N)` contradicts the old list” — is a **theorem**
that this `M` **forces** your target property `X` (e.g. a rigid encoding identity linking solutions to
the moiré pipeline). Pure
**factorization of `M`** is not the HQIV oracle (Ω is summed from literals without factoring `M` in the
demo); the **forcing** statement you want is exactly the **encoding bridge** / FT-intersection bridge
above, not yet a Euclidean-style contradiction in Lean.

So: the *narrative* “for any finite `p`-data, construct `m` such that … satisfies `X`” is deliberately
parallel to Euclid; the **formal** `X` is still to be stated as a single `Prop` and proved without
circularity.

## `k` and the intrinsic axis `π/(2k)` (proved hooks for the **1D** score)

When `Ω m = k`, `intrinsicShellAxisAngle m hm` equals `axisAngle k hk`, i.e. **`π/(2k)`**
(`intrinsicShellAxisAngle_eq_axisAngle_of_Omega`, `axisAngle`). Advancing the patch index `j` multiplies
the intrinsic phasor by that rate (`OctonionSphereFourierPatch`). Algebraically,
`two_mul_axisAngle_eq_pi_div_k` records **`2 · (π/(2k)) = π/k`**. This feeds the **same** ordered patch
score used for moiré slope/jerk — not a separate spatial “ray search.”

## Proof-by-contradiction packaging (intrinsic sinusoid on the arc)

Under the **same** model `S(j) = sin(α + intrinsicShellAxisAngle m · j)` and `Ω m = k`, the jerk is
**forced** to the closed form in `moirePatchSlopeStep_sin_intrinsic_of_Omega`: it is a product of an
oscillating sine at the patch midpoint and the factor **`sin²(π/(4k))`**, which depends **only** on
`k = Ω m`. So:

* To deny that the observed jerk “carries Ω” in this model is to deny that identity — **contradicted**
  by the theorem once the score is assumed to be that intrinsic sinusoid on `Fin n`.
* **`moirePatchSlopeStep_sin_intrinsic_eq_zero_iff`** spells out when the jerk vanishes: either the
  midpoint sine hits zero or **`sin(π/(4k)) = 0`** (degenerate `k` / index).

## What BST does *not* formalize here

**Unproved** in this file (and acceptable as a separate layer): that there is **only one** interior
index of maximal `|moirePatchSlopeStep|` on a given patch — a **global** unicity of “the” jerk.

**Closed Target B (BST / cumulative variation):** `MoireToyThresholdSearch` / `MoireCuspBracket` pin a
**different** unicity — the **least** `j` with `cum[j] ≥ T` for **monotone** cumulative variation
(`exists_isLeast_moire_cum_ge`, upward closure). That is the right tool for a **threshold crossing**,
not for uniqueness of a discrete second-difference maximum unless you add extra hypotheses tying `cum`
to `|Δ²S|`.
-/

noncomputable section

open Real

namespace Hqiv.Algebra

/-- Discrete second difference at `j`: `S(j+2) − 2·S(j+1) + S(j)` (interior patch indices). -/
noncomputable def moireSecondDiff {n : ℕ} (hn : 2 < n) (S : MoirePatchScore n) (j : Fin (n - 2)) : ℝ :=
  S ⟨j.val + 2, by omega⟩ - 2 * S ⟨j.val + 1, by omega⟩ + S ⟨j.val, by omega⟩

theorem moirePatchSlopeStep_eq_second_diff {n : ℕ} (hn : 2 < n) (S : MoirePatchScore n)
    (j : Fin (n - 2)) :
    moirePatchSlopeStep hn S j = moireSecondDiff hn S j := by
  have hn1 : 1 < n := by omega
  dsimp [moirePatchSlopeStep, moirePatchScoreSlope, moireSecondDiff]
  ring

/-! ## Sinusoid: jerk factorizes through `sin² (β/2)` -/

theorem real_second_diff_sin (α β : ℝ) (t : ℝ) :
    sin (α + β * (t + 2)) - 2 * sin (α + β * (t + 1)) + sin (α + β * t) =
      -4 * sin (α + β * (t + 1)) * sin (β / 2) ^ 2 := by
  have hsin2 :
      sin (α + β * (t + 2)) + sin (α + β * t) = 2 * sin (α + β * (t + 1)) * cos β := by
    have h1 : α + β * (t + 2) = α + β * (t + 1) + β := by ring
    have h2 : α + β * t = α + β * (t + 1) - β := by ring
    rw [h1, h2, sin_add, sin_sub]
    ring
  have hcos : cos β - 1 = -2 * sin (β / 2) ^ 2 := by
    have h1 := cos_two_mul (β / 2)
    have hβ : (2 : ℝ) * (β / 2) = β := by ring
    rw [hβ] at h1
    rw [cos_sq'] at h1
    linarith
  calc
    sin (α + β * (t + 2)) - 2 * sin (α + β * (t + 1)) + sin (α + β * t)
        = (sin (α + β * (t + 2)) + sin (α + β * t)) - 2 * sin (α + β * (t + 1)) := by ring
    _ = 2 * sin (α + β * (t + 1)) * cos β - 2 * sin (α + β * (t + 1)) := by rw [hsin2]
    _ = 2 * sin (α + β * (t + 1)) * (cos β - 1) := by ring
    _ = -4 * sin (α + β * (t + 1)) * sin (β / 2) ^ 2 := by rw [hcos]; ring

theorem moirePatchSlopeStep_sin {n : ℕ} (hn : 2 < n) (α β : ℝ) (j : Fin (n - 2)) :
    moirePatchSlopeStep hn (fun i : Fin n => sin (α + β * (i.val : ℝ))) j =
      -4 * sin (α + β * ((j.val : ℝ) + 1)) * sin (β / 2) ^ 2 := by
  rw [moirePatchSlopeStep_eq_second_diff]
  dsimp [moireSecondDiff]
  simpa [Nat.cast_add, add_mul, mul_add, add_assoc] using
    (real_second_diff_sin α β (j.val : ℝ) :)

/-- Axis-angle phasor along the patch: same formula with `β = axisAngle k`. -/
theorem moirePatchSlopeStep_sin_axisAngle {n : ℕ} (hn : 2 < n) (α : ℝ) {k : ℕ} (hk : 0 < k)
    (j : Fin (n - 2)) :
    moirePatchSlopeStep hn (fun i : Fin n => sin (α + axisAngle k hk * (i.val : ℝ))) j =
      -4 *
          sin (α + axisAngle k hk * ((j.val : ℝ) + 1)) *
        sin (axisAngle k hk / 2) ^ 2 := by
  simpa using moirePatchSlopeStep_sin hn α (axisAngle k hk) j

theorem sin_sq_axisAngle_div_two {k : ℕ} (hk : 0 < k) :
    sin (axisAngle k hk / 2) ^ 2 = sin (π / (4 * k)) ^ 2 := by
  dsimp [axisAngle]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  field_simp [hk0]
  ring_nf

/-- With `β = intrinsicShellAxisAngle m` and `Ω m = k`, the jerk carries the factor `sin²(π/(4k))`. -/
theorem moirePatchSlopeStep_sin_intrinsic_of_Omega {n : ℕ} (hn : 2 < n) (α : ℝ) {m k : ℕ}
    (hm : 1 < m) (hΩ : Ω m = k) (j : Fin (n - 2)) :
    moirePatchSlopeStep hn (fun i : Fin n => sin (α + intrinsicShellAxisAngle m hm * (i.val : ℝ))) j =
      -4 *
          sin (α + intrinsicShellAxisAngle m hm * ((j.val : ℝ) + 1)) *
        sin (π / (4 * k)) ^ 2 := by
  have hk : 0 < k := by rw [← hΩ]; exact Omega_pos_of_one_lt hm
  rw [intrinsicShellAxisAngle_eq_axisAngle_of_Omega hm hk hΩ, moirePatchSlopeStep_sin_axisAngle]
  simp_rw [sin_sq_axisAngle_div_two hk]

/-- When `Ω m = k` and the score is the intrinsic-axis sinusoid, the jerk vanishes **iff** either the
midpoint sine vanishes or **`sin(π/(4·k))` vanishes** — there is no third “Ω-free” mechanism in this
closed form. This is the sharp **contradiction hook**: denying Ω’s appearance in the amplitude factor
while keeping the intrinsic sinusoid model contradicts this identity. -/
theorem moirePatchSlopeStep_sin_intrinsic_eq_zero_iff {n : ℕ} (hn : 2 < n) (α : ℝ) {m k : ℕ}
    (hm : 1 < m) (hΩ : Ω m = k) (j : Fin (n - 2)) :
    moirePatchSlopeStep hn (fun i : Fin n => sin (α + intrinsicShellAxisAngle m hm * (i.val : ℝ))) j = 0 ↔
      sin (α + intrinsicShellAxisAngle m hm * ((j.val : ℝ) + 1)) = 0 ∨ sin (π / (4 * k)) = 0 := by
  rw [moirePatchSlopeStep_sin_intrinsic_of_Omega hn α hm hΩ j]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h11 | h12
      · norm_num at h11
      · left
        exact h12
    · right
      simpa [sq_eq_zero_iff] using h2
  · rintro (h | h)
    · simp [h]
    · simp [h]

/-! ## Surface-area proxy (already in `OctonionSphereConstruction`): `A₇ = dV₈/dr` -/

theorem continuousSphereArea7_eq_deriv_volume (r : ℝ) :
    continuousSphereArea7 r = deriv continuousBallVolume8 r :=
  (deriv_continuousBallVolume8 r).symm

end Hqiv.Algebra

end
