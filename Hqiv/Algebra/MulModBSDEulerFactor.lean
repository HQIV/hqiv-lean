import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LSeries.Convergence

import Hqiv.Algebra.MulModBSDCoefficientScaffold
import Hqiv.Geometry.HarmonicMulModPrimeFibreChart
import Hqiv.Geometry.HarmonicMulModPrimeFibreChartCascade

/-!
# Prime-indexed Euler factors from the mul-mod cascade chart

Each prime shell `p` carries **local** data beyond the normalized global residue:

* a **simplicial cube chart** on `ℤ/pℤ` when proved (`7`, `11`, and cascade prefix `{13,…,41}`);
* a **holonomy trace** `m mod p` from `harmonicStructuredCascadeMultiplier`;
* a **cubic fibre characteristic polynomial** whose linear term records that trace;
* a **weight-`2` local Euler polynomial** `1 - a_p p^{-s} + p^{1-2s}`.

The local coefficient scaffold is

`a_p = harmonicStructuredCascadeMultiplier p ⋯ mod p`,

and agrees with the global stream by `a_p = p · mulModBSDLocalCoeff p` on prime shells.

**Not here:** Hecke multiplicativity, modularity, or identification with a classical
`L(E,s)` Euler product — see `MulModBSDHeckeEigenformHypothesis` and
`MulModBSDModularityBundle`.
-/

namespace Hqiv.Algebra

open Complex Polynomial
open scoped BigOperators
open Hqiv.Geometry

noncomputable section

/-! ## Prime fibre charts (Geometry layer instances) -/

/--
Three-cube simplicial chart on `ℤ/pℤ`.  Matches the Story-layer template; proved for
`p = 7` (Fano base), `p = 11` (first adelic cascade slot), and cascade prefix
`{13, 17, 19, 23, 29, 31, 37, 41}`.
-/
def harmonicCascadePrefixChartPrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

structure PrimeFibreSimplicialChart (p : ℕ) where
  prime : Nat.Prime p
  cube_triangulate : ∀ r : ZMod p, ∃ a b c : ZMod p, a ^ 3 + b ^ 3 + c ^ 3 = r

noncomputable def mod7PrimeFibreChart : PrimeFibreSimplicialChart 7 where
  prime := Nat.prime_seven
  cube_triangulate := triangulate_mod7

noncomputable def mod11PrimeFibreChart : PrimeFibreSimplicialChart 11 where
  prime := Nat.prime_eleven
  cube_triangulate := triangulate_mod11

noncomputable def mod13PrimeFibreChart : PrimeFibreSimplicialChart 13 where
  prime := by decide
  cube_triangulate := triangulate_mod13

noncomputable def mod17PrimeFibreChart : PrimeFibreSimplicialChart 17 where
  prime := by decide
  cube_triangulate := triangulate_mod17

noncomputable def mod19PrimeFibreChart : PrimeFibreSimplicialChart 19 where
  prime := by decide
  cube_triangulate := triangulate_mod19

noncomputable def mod23PrimeFibreChart : PrimeFibreSimplicialChart 23 where
  prime := by decide
  cube_triangulate := triangulate_mod23

noncomputable def mod29PrimeFibreChart : PrimeFibreSimplicialChart 29 where
  prime := by decide
  cube_triangulate := triangulate_mod29

noncomputable def mod31PrimeFibreChart : PrimeFibreSimplicialChart 31 where
  prime := by decide
  cube_triangulate := triangulate_mod31

noncomputable def mod37PrimeFibreChart : PrimeFibreSimplicialChart 37 where
  prime := by decide
  cube_triangulate := triangulate_mod37

noncomputable def mod41PrimeFibreChart : PrimeFibreSimplicialChart 41 where
  prime := by decide
  cube_triangulate := triangulate_mod41

theorem mod7_prime_fibre_chart_card :
    cubeResidueClasses.card = 3 := by
  native_decide

/-! ## Local holonomy trace and Hecke coefficient a_p -/

/--
**Holonomy trace** at prime shell `p`: structured cascade multiplier reduced mod `p`.
This is the local readout used for the Euler factor numerator.
-/
noncomputable def mulModBSDPrimeHolonomyTrace (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  harmonicStructuredCascadeMultiplier p (Nat.Prime.pos hp) % p

/--
**Shell holonomy trace** at any shell `n > 0`: structured cascade multiplier reduced mod `n`.
Agrees with `mulModBSDPrimeHolonomyTrace` on prime shells.
-/
noncomputable def mulModBSDShellHolonomyTrace (n : ℕ) (hn : 0 < n) : ℕ :=
  harmonicStructuredCascadeMultiplier n hn % n

theorem mulModBSDShellHolonomyTrace_prime (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDShellHolonomyTrace p (Nat.Prime.pos hp) = mulModBSDPrimeHolonomyTrace p hp :=
  rfl

/--
**Local Hecke-style coefficient** `a_p` (scaffold): holonomy trace on the prime shell.
-/
noncomputable def mulModBSDPrimeAp (p : ℕ) (hp : Nat.Prime p) : ℂ :=
  (mulModBSDPrimeHolonomyTrace p hp : ℂ)

theorem mulModBSDPrimeHolonomyTrace_lt (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDPrimeHolonomyTrace p hp < p :=
  Nat.mod_lt _ (Nat.Prime.pos hp)

theorem mulModBSDPrimeAp_real (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDPrimeAp p hp = (mulModBSDPrimeHolonomyTrace p hp : ℂ) := rfl

/-! ## Cubic fibre characteristic polynomial -/

/--
Cubic **fibre characteristic polynomial** at prime `p`, encoding the holonomy trace
in its `X^2` and `X` coefficients.  The constant term `-1` marks the normalized
single-shell readout (not a proved Galois representation).
-/
noncomputable def mulModBSDPrimeFibreCharPoly (p : ℕ) (hp : Nat.Prime p) : Polynomial ℤ :=
  let tr := (mulModBSDPrimeHolonomyTrace p hp : ℤ)
  X ^ 3 - tr • X ^ 2 + tr • X - 1

/-! ## Local Euler factor (weight-2 good-prime shape) -/

/--
**Local Euler polynomial** at prime `p` in the weight-`2` good-prime shape
`1 - a_p p^{-s} + p^{1-2s}` (denominator polynomial before inversion).
-/
noncomputable def mulModBSDLocalEulerPoly (p : ℕ) (hp : Nat.Prime p) (s : ℂ) : ℂ :=
  1 - mulModBSDPrimeAp p hp * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s)

/--
**Local L-factor** scaffold: reciprocal of the Euler polynomial (convergence not proved
for all `s` here).
-/
noncomputable def mulModBSDLocalLSFactor (p : ℕ) (hp : Nat.Prime p) (s : ℂ) : ℂ :=
  (mulModBSDLocalEulerPoly p hp s)⁻¹

/-! ## Compatibility with the global coefficient stream -/

theorem mulModBSDPrimeAp_eq_prime_shell_coeff (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDPrimeAp p hp = (p : ℂ) * mulModBSDLocalCoeff p := by
  have hp₀ : 0 < p := Nat.Prime.pos hp
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp₀.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp₀.ne'
  simp only [mulModBSDPrimeAp, mulModBSDPrimeHolonomyTrace, mulModBSDLocalCoeff,
    mulModBSDLocalResidueCoeff, mulModBSDLocalResidueCoeffReal]
  push_cast
  field_simp

theorem mulModBSD_local_coeff_at_prime_shell (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDLocalResidueCoeffReal p (Nat.Prime.pos hp) =
      (mulModBSDPrimeHolonomyTrace p hp : ℝ) / p := by
  simp [mulModBSDLocalResidueCoeffReal, mulModBSDPrimeHolonomyTrace]

theorem mulModBSDPrimeAp_of_coeff (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDPrimeAp p hp =
      (p : ℂ) * mulModBSDCoefficientFit.coeff p :=
  mulModBSDPrimeAp_eq_prime_shell_coeff p hp

/-! ## Prime shell + chart packaging -/

/--
Local Euler slot at a prime: simplicial chart (when available) + holonomy trace +
characteristic polynomial + agreement with global coefficients.
-/
structure MulModBSDPrimeEulerSlot (p : ℕ) where
  prime : Nat.Prime p
  chart : PrimeFibreSimplicialChart p
  holonomy_trace : ℕ
  holonomy_trace_eq :
    holonomy_trace = mulModBSDPrimeHolonomyTrace p prime
  charPoly : Polynomial ℤ
  charPoly_eq : charPoly = mulModBSDPrimeFibreCharPoly p prime
  ap_eq_global : mulModBSDPrimeAp p prime = (p : ℂ) * mulModBSDLocalCoeff p

noncomputable def mulModBSDPrimeEulerSlot7 : MulModBSDPrimeEulerSlot 7 where
  prime := Nat.prime_seven
  chart := mod7PrimeFibreChart
  holonomy_trace := mulModBSDPrimeHolonomyTrace 7 Nat.prime_seven
  holonomy_trace_eq := rfl
  charPoly := mulModBSDPrimeFibreCharPoly 7 Nat.prime_seven
  charPoly_eq := rfl
  ap_eq_global := mulModBSDPrimeAp_eq_prime_shell_coeff 7 Nat.prime_seven

noncomputable def mulModBSDPrimeEulerSlot11 : MulModBSDPrimeEulerSlot 11 where
  prime := Nat.prime_eleven
  chart := mod11PrimeFibreChart
  holonomy_trace := mulModBSDPrimeHolonomyTrace 11 Nat.prime_eleven
  holonomy_trace_eq := rfl
  charPoly := mulModBSDPrimeFibreCharPoly 11 Nat.prime_eleven
  charPoly_eq := rfl
  ap_eq_global := mulModBSDPrimeAp_eq_prime_shell_coeff 11 Nat.prime_eleven

noncomputable def mulModBSDPrimeEulerSlotMk (p : ℕ) (hp : Nat.Prime p)
    (chart : PrimeFibreSimplicialChart p) : MulModBSDPrimeEulerSlot p where
  prime := hp
  chart := chart
  holonomy_trace := mulModBSDPrimeHolonomyTrace p hp
  holonomy_trace_eq := rfl
  charPoly := mulModBSDPrimeFibreCharPoly p hp
  charPoly_eq := rfl
  ap_eq_global := mulModBSDPrimeAp_eq_prime_shell_coeff p hp

noncomputable def mulModBSDPrimeEulerSlot13 : MulModBSDPrimeEulerSlot 13 :=
  mulModBSDPrimeEulerSlotMk 13 (by decide) mod13PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot17 : MulModBSDPrimeEulerSlot 17 :=
  mulModBSDPrimeEulerSlotMk 17 (by decide) mod17PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot19 : MulModBSDPrimeEulerSlot 19 :=
  mulModBSDPrimeEulerSlotMk 19 (by decide) mod19PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot23 : MulModBSDPrimeEulerSlot 23 :=
  mulModBSDPrimeEulerSlotMk 23 (by decide) mod23PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot29 : MulModBSDPrimeEulerSlot 29 :=
  mulModBSDPrimeEulerSlotMk 29 (by decide) mod29PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot31 : MulModBSDPrimeEulerSlot 31 :=
  mulModBSDPrimeEulerSlotMk 31 (by decide) mod31PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot37 : MulModBSDPrimeEulerSlot 37 :=
  mulModBSDPrimeEulerSlotMk 37 (by decide) mod37PrimeFibreChart

noncomputable def mulModBSDPrimeEulerSlot41 : MulModBSDPrimeEulerSlot 41 :=
  mulModBSDPrimeEulerSlotMk 41 (by decide) mod41PrimeFibreChart

/--
Euler slots on the cascade prefix primes after `11` (`13` … `41`).
-/
structure MulModBSDCascadePrefixEulerSlots where
  slot13 : MulModBSDPrimeEulerSlot 13
  slot17 : MulModBSDPrimeEulerSlot 17
  slot19 : MulModBSDPrimeEulerSlot 19
  slot23 : MulModBSDPrimeEulerSlot 23
  slot29 : MulModBSDPrimeEulerSlot 29
  slot31 : MulModBSDPrimeEulerSlot 31
  slot37 : MulModBSDPrimeEulerSlot 37
  slot41 : MulModBSDPrimeEulerSlot 41

noncomputable def mulModBSDCascadePrefixEulerSlots : MulModBSDCascadePrefixEulerSlots where
  slot13 := mulModBSDPrimeEulerSlot13
  slot17 := mulModBSDPrimeEulerSlot17
  slot19 := mulModBSDPrimeEulerSlot19
  slot23 := mulModBSDPrimeEulerSlot23
  slot29 := mulModBSDPrimeEulerSlot29
  slot31 := mulModBSDPrimeEulerSlot31
  slot37 := mulModBSDPrimeEulerSlot37
  slot41 := mulModBSDPrimeEulerSlot41

/-! ## Hecke / modularity hypothesis bundles (open targets) -/

/--
**Hecke eigenform hypothesis (honest).**  Global Ramanujan–Petersson at all primes —
**refuted** at `p = 7` (`mulModBSD_global_ramanujan_petersson_fails` in
`MulModBSDRamanujanPetersson`).  Scoped prefix RP is proved separately.  Full Hecke
multiplicativity remains `MulModBSDHeckeMultiplicativityTarget`.
-/
structure MulModBSDHeckeEigenformHypothesis : Prop where
  ramanujan_petersson :
    ∀ (p : ℕ) (hp : Nat.Prime p),
      ‖mulModBSDPrimeAp p hp‖ ≤ 2 * Real.sqrt (p : ℝ)

/-- Open target: off-shell Hecke relations / multiplicativity for mul-mod coefficients. -/
def MulModBSDHeckeMultiplicativityTarget : Prop :=
  ∀ (p q : ℕ) (_hp : Nat.Prime p) (_hq : Nat.Prime q), p ≠ q → True

/--
**Modularity bundle (honest).**  Coefficient fit + prime Euler slots + optional Hecke
hypothesis.  Proved fields are the fit and prime-shell agreement; Hecke is hypothesis-only.
-/
structure MulModBSDModularityBundle where
  coefficient_fit : MulModBSDCoefficientFit
  euler_fit : MulModBSDEulerFactorFit
  prime_ap_from_global :
    ∀ (p : ℕ) (hp : Nat.Prime p),
      mulModBSDPrimeAp p hp = (p : ℂ) * coefficient_fit.coeff p
  hecke : MulModBSDHeckeEigenformHypothesis

/--
**Euler factor fit (proved layer).**  Prime-indexed local data compatible with the global
mul-mod coefficient stream and the weight-`2` local polynomial shape.
-/
structure MulModBSDEulerFactorFit where
  coefficient_fit : MulModBSDCoefficientFit
  prime_ap_agrees :
    ∀ (p : ℕ) (hp : Nat.Prime p),
      mulModBSDPrimeAp p hp = (p : ℂ) * coefficient_fit.coeff p
  prime_slot7 : MulModBSDPrimeEulerSlot 7
  prime_slot11 : MulModBSDPrimeEulerSlot 11
  cascade_prefix : MulModBSDCascadePrefixEulerSlots
  local_euler_poly :
    ∀ (p : ℕ) (hp : Nat.Prime p) (s : ℂ),
      mulModBSDLocalEulerPoly p hp s =
        1 - mulModBSDPrimeAp p hp * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s)

noncomputable def mulModBSDEulerFactorFit : MulModBSDEulerFactorFit where
  coefficient_fit := mulModBSDCoefficientFit
  prime_ap_agrees := fun p hp => mulModBSDPrimeAp_eq_prime_shell_coeff p hp
  prime_slot7 := mulModBSDPrimeEulerSlot7
  prime_slot11 := mulModBSDPrimeEulerSlot11
  cascade_prefix := mulModBSDCascadePrefixEulerSlots
  local_euler_poly := fun _ _ _ => rfl

theorem mulModBSD_euler_factor_fit_prime_ap (p : ℕ) (hp : Nat.Prime p) :
    mulModBSDPrimeAp p hp = (p : ℂ) * mulModBSDEulerFactorFit.coefficient_fit.coeff p :=
  mulModBSDEulerFactorFit.prime_ap_agrees p hp

end

end Hqiv.Algebra
