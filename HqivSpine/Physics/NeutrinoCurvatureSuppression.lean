import HqivSpine.Physics.Shell
import HqivSpine.Physics.NeutrinoSeesaw

/-!
# `HqivSpine.Physics.NeutrinoCurvatureSuppression` — the **HQIV-native** neutrino-mass mechanism

The textbook **type-I seesaw** (`NeutrinoSeesaw`) is a graft: it postulates a sterile right-handed
state with a *free* heavy Majorana mass `M_R` and a *free* Dirac coupling `m_D`, and reads off
`m_ν = m_D²/M_R`. Mathematically clean, but **two free parameters tied to nothing in HQIV**. This
module pulls the suppression out of the HQIV structure itself. It **rhymes** with the seesaw — small
mass = (scale) ÷ (big geometric factor) — but it is **not identical**: there is no free `M_R`.

## Why the neutrino is light, natively

In the discrete O-Maxwell action (`Physics.Action`) there is **no mass term**: a fermion gets mass
as `M = M_constituent − E_bind` — a **curvature well** dug by its charge/colour (`Physics.Binding`,
`Physics.Curvature`). The neutrino is the chargeless, colourless, weak-singlet mode (`Hqiv.Algebra`
`SMEmbedding`: the `ν_R` singlet has `Y = 0`, `Q = 0`), carrying the **minimal** content
(`MassLadder.intrinsicWaveComplexity .neutrino = 1`, one conserved Fano triple). With no charge there
is **no inner curvature well to bind against**, so its tree-level binding mass vanishes
(`neutrinoTreeMass = 0`). It is the chirally-protected **would-be-zero mode** of
`TextureZeroDerivation` (`p = 0`).

So whatever mass it has is not a well — it is the **residual it feels from the *outer* horizon**. The
outer horizon at shell `m` has area `S(m) = (m+1)(m+2) = latticeSimplexCount m` (native shell
geometry). The neutrino couples to it only through the **informational-monogamy complement** `γ = 2/5`
(`Shell.gammaHQIV`, the partner of `α` under `α+γ=1`). The native suppression factor is therefore the
**parameter-free** ratio

  `suppression(m) = γ / S(m)`,

and the neutrino mass is a charged-sector anchor scale `m_χ` (a ladder rung) damped by it:

  `m_ν = m_χ · γ / S(m)`,   with tree term `0`.

## What is and is not claimed

* **Uniquely derived from foundations (no fit, no free choice — `neutrinoSuppression_unique_from_foundations`):**
  every ingredient of `γ / S(m)` at the closure shell is forced by foundation constants:
  - numerator `γ = 1 − α` is the *unique* chargeless complement under the unit split `α + γ = 1`
    (`gammaHQIV_eq_one_sub_alphaEM`);
  - denominator is the lattice area, *strictly monotone hence injective* (`latticeSimplexCount_strictMono`);
  - the closure shell `m = referenceM+2` is the *unique* shell whose outer-horizon area is the
    **octonionic carrier surface** `imaginaryDim · carrierMultiplicity = 7·8 = 56`, equivalently the
    shell radially bracketed by `(imaginaryDim, carrierMultiplicity) = (7,8)`
    (`outerHorizonArea_closure_eq_carrier`, `closureShell_radial_bracket`, `neutrinoClosureShell_unique`).
  These force `suppression = (1−α)/(imaginaryDim·carrierMultiplicity) = 1/140`.
* **Structure (parameter-free):** positivity, `< 1`, strict decrease with shell (deeper horizon ⇒
  lighter ν), vanishing as `m → ∞`.
* **The "rhymes but isn't identical" theorem (`neutrino_rhymes_seesaw`):** the native mass equals the
  seesaw ratio `m_χ² / M_eff` with `M_eff = m_χ · S(m) / γ` a **derived horizon scale**, not a free
  `M_R`. HQIV thus *forces* the value the seesaw would have to put in by hand: `M_R = m_χ S(m)/γ`.
* **The one physical posit (now in foundation constants):** that the chargeless neutrino relaxes to the
  shell whose horizon area *saturates the octonionic carrier surface* `7·8`. This selection principle is
  the input; given it, the shell and the factor are unique.
* **Honest open frontier (not claimed solved):** the *absolute normalization* of the charged anchor
  `m_χ` and the generation *ordering*. With the legacy `M_Z`-like witness the `1/140` factor overshoots
  the cosmological `Σm_ν < 0.12 eV` bound by ~`10⁸` and the naive cascade inverts ordering. The
  **suppression factor is now uniquely pinned**; the **calibration of `m_χ` and the ordering remain open**.

Combined with `NeutrinoMixing` (`θ = π/4`, `δ = π/5`, genuinely native *numbers*), the neutrino
sector is: native mixing angle + phase, and a native *mechanism* for the mass with an open
normalization. No PMNS entry, no measured `m_ν` imported.

Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`, no PDG input.
-/

namespace HqivSpine.Physics.NeutrinoCurvatureSuppression

open HqivSpine.Foundation HqivSpine.Physics

/-! ## The outer-horizon area and the native suppression factor -/

/-- **Outer-horizon area** at shell `m`: `S(m) = (m+1)(m+2)`, identical to the native lattice
simplex count `latticeSimplexCount m = shellNumer m`. This is the geometric "surface" the chargeless
neutrino feels from outside, in place of an inner curvature well. -/
noncomputable def outerHorizonArea (m : ℕ) : ℝ := (latticeSimplexCount m : ℝ)

theorem outerHorizonArea_eq (m : ℕ) :
    outerHorizonArea m = ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
  unfold outerHorizonArea latticeSimplexCount shellNumer
  push_cast; ring

theorem outerHorizonArea_pos (m : ℕ) : 0 < outerHorizonArea m := by
  unfold outerHorizonArea; exact_mod_cast latticeSimplexCount_pos m

/-- The area is at least `2` (the `m = 0` floor `1·2`). -/
theorem two_le_outerHorizonArea (m : ℕ) : (2 : ℝ) ≤ outerHorizonArea m := by
  rw [outerHorizonArea_eq]
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [this]

/-- The area strictly grows with the shell (the horizon recedes). -/
theorem outerHorizonArea_strictMono {m m' : ℕ} (h : m < m') :
    outerHorizonArea m < outerHorizonArea m' := by
  rw [outerHorizonArea_eq, outerHorizonArea_eq]
  have hlt : (m : ℝ) < (m' : ℝ) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [hlt, h0]

/-- **Native neutrino-mass suppression factor** `γ / S(m)` — the monogamy complement over the
outer-horizon area. Parameter-free: both `γ = 2/5` and `S(m)` are HQIV shell invariants. -/
noncomputable def neutrinoSuppression (m : ℕ) : ℝ := gammaHQIV / outerHorizonArea m

theorem neutrinoSuppression_pos (m : ℕ) : 0 < neutrinoSuppression m := by
  unfold neutrinoSuppression
  rw [gammaHQIV_eq]
  exact div_pos (by norm_num) (outerHorizonArea_pos m)

/-- The suppression is genuine: `γ/S(m) < 1` (well below the charged scale). -/
theorem neutrinoSuppression_lt_one (m : ℕ) : neutrinoSuppression m < 1 := by
  unfold neutrinoSuppression
  rw [gammaHQIV_eq, div_lt_one (outerHorizonArea_pos m)]
  have := two_le_outerHorizonArea m
  linarith

/-- **Deeper horizon ⇒ lighter neutrino:** the suppression strictly decreases as the shell grows. -/
theorem neutrinoSuppression_strictAnti {m m' : ℕ} (h : m < m') :
    neutrinoSuppression m' < neutrinoSuppression m := by
  unfold neutrinoSuppression
  rw [gammaHQIV_eq]
  have hS := outerHorizonArea_strictMono h
  have hSpos := outerHorizonArea_pos m
  rw [div_eq_mul_one_div (2/5 : ℝ), div_eq_mul_one_div (2/5 : ℝ)]
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hSpos hS) (by norm_num)

/-- **Exact native value at the neutrino closure shell** `m = referenceM + 2 = 6`:
`γ / S(6) = (2/5)/56 = 1/140`. The legacy `outerHorizonNeutrinoSuppression_eq_inv_140`, now from
spine objects only. -/
theorem neutrinoSuppression_referenceM_plus_two :
    neutrinoSuppression (referenceM + 2) = 1 / 140 := by
  unfold neutrinoSuppression outerHorizonArea
  rw [gammaHQIV_eq]
  norm_num [latticeSimplexCount, shellNumer, referenceM]

/-! ## Uniqueness: every ingredient is forced by foundation constants

The factor `γ/S(m)` at `m = referenceM+2` is not a fit — each piece is pinned:

* **Numerator `γ`** is the *unique* chargeless complement of the EM/curvature exponent `α` under the
  foundation unit split `α + γ = 1` (`gammaHQIV_eq_one_sub_alphaEM`). A charged mode couples through
  `α`; the chargeless neutrino can only carry the complement `γ = 1 − α`.
* **Denominator `S(m)`** is the lattice area `latticeSimplexCount m`, strictly monotone in `m`
  (`latticeSimplexCount_strictMono`), hence injective.
* **Closure shell `m = referenceM+2`** is the *unique* shell whose outer-horizon area equals the
  **octonionic carrier surface** `imaginaryDim · carrierMultiplicity = 7·8 = 56`
  (`outerHorizonArea_closure_eq_carrier`, `neutrinoClosureShell_unique`): the neutrino relaxes to the
  first horizon that wraps the full `7` imaginary directions over the `8`-component carrier.

Together (`neutrinoSuppression_unique_from_foundations`) these force
`neutrinoSuppression(referenceM+2) = (1−α)/(imaginaryDim·carrierMultiplicity) = 1/140`. -/

/-- **Numerator is the unique chargeless complement.** `γ = 1 − α` from the foundation unit split
`alphaRat d + gammaRat d = 1` at `d = transverseDim = 3`. The charged sector couples through the
curvature-imprint exponent `α`; the neutral mode carries only the complement. -/
theorem gammaHQIV_eq_one_sub_alphaEM : gammaHQIV = 1 - alphaEM := by
  have h : alphaRat transverseDim + gammaRat transverseDim = 1 :=
    alpha_add_gamma transverseDim (by decide)
  unfold gammaHQIV alphaEM
  have hc : ((alphaRat transverseDim : ℝ)) + ((gammaRat transverseDim : ℝ)) = 1 := by
    exact_mod_cast h
  linarith

/-- The outer-horizon area is strictly monotone in the shell (the horizon recedes one step at a
time), hence the shell ↦ area map is injective. -/
theorem latticeSimplexCount_strictMono : StrictMono latticeSimplexCount := by
  apply strictMono_nat_of_lt_succ
  intro n
  show latticeSimplexCount n < latticeSimplexCount (n + 1)
  unfold latticeSimplexCount
  rw [shellNumer_increment]
  omega

/-- **The closure shell's area is the octonionic carrier surface:** `S(referenceM+2) = 7·8 =
imaginaryDim · carrierMultiplicity`. The `7` imaginary directions wrap the `8`-component carrier. -/
theorem outerHorizonArea_closure_eq_carrier :
    latticeSimplexCount (referenceM + 2) = imaginaryDim * carrierMultiplicity := by
  rw [imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]
  norm_num [latticeSimplexCount, shellNumer, referenceM]

/-- **The closure shell is unique.** `referenceM+2` is the *only* shell whose outer-horizon area
equals the octonionic carrier surface `imaginaryDim · carrierMultiplicity`. -/
theorem neutrinoClosureShell_unique {m : ℕ}
    (h : latticeSimplexCount m = imaginaryDim * carrierMultiplicity) :
    m = referenceM + 2 :=
  latticeSimplexCount_strictMono.injective
    (h.trans outerHorizonArea_closure_eq_carrier.symm)

/-- **Radial bracket of the closure shell.** Its two consecutive radial indices are exactly the
algebra dimensions: `(m+1, m+2) = (imaginaryDim, carrierMultiplicity) = (7, 8)`. The neutrino horizon
is the shell bracketed by the `7` imaginary directions (inner) and the `8`-component carrier (outer).
Because `carrierMultiplicity = imaginaryDim + 1` by construction, this bracket is self-consistent and
realized by a single shell. -/
theorem closureShell_radial_bracket :
    (referenceM + 2) + 1 = imaginaryDim ∧ (referenceM + 2) + 2 = carrierMultiplicity := by
  rw [imaginaryDim_eq_seven, carrierMultiplicity_eq_eight]
  refine ⟨?_, ?_⟩ <;> norm_num [referenceM]

/-- The bracket pins the shell uniquely: any shell whose inner radial index is the imaginary
dimension is `referenceM + 2`. -/
theorem closureShell_unique_of_inner {m : ℕ} (h : m + 1 = imaginaryDim) :
    m = referenceM + 2 := by
  rw [imaginaryDim_eq_seven] at h
  unfold referenceM
  omega

/-- **The suppression at the closure shell, in pure foundation constants:**
`(1 − α) / (imaginaryDim · carrierMultiplicity)`. -/
theorem neutrinoSuppression_closure_foundational :
    neutrinoSuppression (referenceM + 2)
      = (1 - alphaEM) / ((imaginaryDim : ℝ) * (carrierMultiplicity : ℝ)) := by
  unfold neutrinoSuppression outerHorizonArea
  rw [gammaHQIV_eq_one_sub_alphaEM]
  congr 1
  exact_mod_cast outerHorizonArea_closure_eq_carrier

/-- **Unique derivation from foundations.** Numerator forced (chargeless complement `γ = 1−α`);
denominator forced (lattice area, strictly monotone hence injective); closure shell forced (unique
shell whose horizon area is the octonionic carrier surface `7·8`); ⇒ the suppression is the unique
value `(1−α)/(imaginaryDim·carrierMultiplicity) = 1/140`. No fit, no free choice. -/
theorem neutrinoSuppression_unique_from_foundations :
    gammaHQIV = 1 - alphaEM ∧
    StrictMono latticeSimplexCount ∧
    (∀ m, latticeSimplexCount m = imaginaryDim * carrierMultiplicity → m = referenceM + 2) ∧
    neutrinoSuppression (referenceM + 2)
      = (1 - alphaEM) / ((imaginaryDim : ℝ) * (carrierMultiplicity : ℝ)) ∧
    neutrinoSuppression (referenceM + 2) = 1 / 140 :=
  ⟨gammaHQIV_eq_one_sub_alphaEM, latticeSimplexCount_strictMono,
   fun _ h => neutrinoClosureShell_unique h,
   neutrinoSuppression_closure_foundational,
   neutrinoSuppression_referenceM_plus_two⟩

/-! ## Neutrino mass: tree well is zero, all mass is the horizon residual -/

/-- The chargeless neutrino has **no inner curvature well**, so its tree-level binding mass is `0`
(the chirally-protected would-be-zero mode `p = 0` of `TextureZeroDerivation`). -/
def neutrinoTreeMass : ℝ := 0

/-- **Native neutrino mass:** a charged-sector anchor scale `m_χ` (a ladder rung) damped by the
horizon suppression. The whole mass is the outer-horizon residual; there is no inner well. -/
noncomputable def neutrinoMass (mχ : ℝ) (m : ℕ) : ℝ := mχ * neutrinoSuppression m

/-- The mass is exactly tree (`= 0`) plus the horizon residual. -/
theorem neutrinoMass_eq_tree_add_residual (mχ : ℝ) (m : ℕ) :
    neutrinoMass mχ m = neutrinoTreeMass + mχ * neutrinoSuppression m := by
  unfold neutrinoMass neutrinoTreeMass; ring

/-- For a positive charged anchor the neutrino mass is positive but strictly below that anchor:
the horizon suppresses, it does not vanish. -/
theorem neutrinoMass_lt_charged {mχ : ℝ} (hχ : 0 < mχ) (m : ℕ) :
    0 < neutrinoMass mχ m ∧ neutrinoMass mχ m < mχ := by
  refine ⟨mul_pos hχ (neutrinoSuppression_pos m), ?_⟩
  calc neutrinoMass mχ m = mχ * neutrinoSuppression m := rfl
    _ < mχ * 1 := by
        exact mul_lt_mul_of_pos_left (neutrinoSuppression_lt_one m) hχ
    _ = mχ := by ring

/-! ## How it rhymes with — but is not — the type-I seesaw -/

/-- **Effective heavy scale forced by HQIV.** Where the textbook seesaw inserts a *free* `M_R`, the
native mechanism *derives* it: `M_eff = m_χ · S(m) / γ` — the charged anchor times the outer-horizon
area over the monogamy complement. A horizon scale, not a parameter. -/
noncomputable def effectiveHeavyScale (mχ : ℝ) (m : ℕ) : ℝ :=
  mχ * outerHorizonArea m / gammaHQIV

/-- **The rhyme.** The native mass is exactly the seesaw ratio `m_χ² / M_eff`, but with the heavy
scale `M_eff = m_χ S(m)/γ` *derived* from horizon geometry rather than a free Majorana mass. This is
"it rhymes but it won't be identical": same `mass² / scale` shape, native (non-free) heavy scale. -/
theorem neutrino_rhymes_seesaw (mχ : ℝ) (m : ℕ) (hχ : mχ ≠ 0) :
    neutrinoMass mχ m = mχ ^ 2 / effectiveHeavyScale mχ m := by
  unfold neutrinoMass neutrinoSuppression effectiveHeavyScale
  have hγ : gammaHQIV ≠ 0 := by rw [gammaHQIV_eq]; norm_num
  have hS : outerHorizonArea m ≠ 0 := ne_of_gt (outerHorizonArea_pos m)
  field_simp

/-- The forced heavy scale dominates the charged anchor (`M_eff > m_χ`), so the would-be Majorana
mass HQIV produces is genuinely a *heavy* scale — consistent with the seesaw hierarchy `m_D ≪ M_R`,
with `m_D = m_χ` here. -/
theorem effectiveHeavyScale_gt_charged {mχ : ℝ} (hχ : 0 < mχ) (m : ℕ) :
    mχ < effectiveHeavyScale mχ m := by
  unfold effectiveHeavyScale
  rw [gammaHQIV_eq]
  have hS := two_le_outerHorizonArea m
  have hrw : mχ * outerHorizonArea m / (2 / 5) = mχ * outerHorizonArea m * (5 / 2) := by ring
  rw [hrw]
  nlinarith [hS, hχ, mul_pos hχ (outerHorizonArea_pos m)]

/-! ## Closure -/

/-- **Native neutrino-mass mechanism, bundled.** The suppression `γ/S(m)` is parameter-free
(positive, `< 1`, strictly decreasing, `= 1/140` at the closure shell); the tree well is `0`; and the
whole thing rhymes with the seesaw via a *derived* heavy scale `M_eff = m_χ S(m)/γ`, never a free
`M_R`. -/
theorem NeutrinoCurvatureSuppressionClosure :
    neutrinoTreeMass = 0 ∧
    (∀ m, 0 < neutrinoSuppression m ∧ neutrinoSuppression m < 1) ∧
    neutrinoSuppression (referenceM + 2) = 1 / 140 ∧
    (∀ m m', m < m' → neutrinoSuppression m' < neutrinoSuppression m) ∧
    (∀ mχ : ℝ, mχ ≠ 0 → ∀ m,
      neutrinoMass mχ m = mχ ^ 2 / effectiveHeavyScale mχ m) := by
  refine ⟨rfl, ?_, neutrinoSuppression_referenceM_plus_two, ?_, ?_⟩
  · exact fun m => ⟨neutrinoSuppression_pos m, neutrinoSuppression_lt_one m⟩
  · exact fun m m' h => neutrinoSuppression_strictAnti h
  · exact fun mχ hχ m => neutrino_rhymes_seesaw mχ m hχ

end HqivSpine.Physics.NeutrinoCurvatureSuppression
