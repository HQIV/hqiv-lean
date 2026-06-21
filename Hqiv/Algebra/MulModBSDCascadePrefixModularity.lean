import Hqiv.Algebra.MulModBSDEulerFactor
import Hqiv.Algebra.MulModBSDRamanujanPetersson

/-!
# Cascade-prefix modularity object (good primes from `11`)

Classical modularity / global Hecke eigenform hypotheses are **too strong** for the
mul-mod stream: Ramanujan–Petersson fails at the Fano base shell `p = 7`
(`mulModBSD_global_ramanujan_petersson_fails`).

This module packages the **proved prefix arithmetic** on the **good** cascade shells
`{11, 13, 17, 19, 23, 29, 31, 37, 41}`:

* simplicial cube charts and Euler slots (`MulModBSDEulerFactorFit`);
* uniform holonomy trace `a_p = 6` and weight-`2` local Euler shape;
* Ramanujan–Petersson on the prefix (`MulModBSDRamanujanPeterssonCascadePrefixHypothesis`);
* isolated **bad** shell data at `p = 7` (RP failure, chart retained).

**Open (explicit targets):** off-shell Hecke multiplicativity and identification with a
classical newform or `L(E,s)` — see `MulModBSDHeckeGoodPrimeMultiplicativityTarget`.
-/

namespace Hqiv.Algebra

open Polynomial

noncomputable section

/-! ## Good / bad prime shell classification -/

/--
**Good cascade shells:** prefix chart primes after the Fano base `7`, with proved cube
triangulation and prefix Ramanujan–Petersson.
-/
def harmonicCascadeGoodPrimeShells : List ℕ :=
  [11, 13, 17, 19, 23, 29, 31, 37, 41]

/-- **Bad cascade shell:** Fano obstruction fibre; global RP fails here. -/
def harmonicCascadeBadPrimeShell : ℕ := 7

def IsHarmonicCascadeGoodPrimeShell (p : ℕ) : Prop :=
  p ∈ harmonicCascadeGoodPrimeShells

def IsHarmonicCascadeBadPrimeShell (p : ℕ) : Prop :=
  p = harmonicCascadeBadPrimeShell

theorem mem_harmonicCascadeGoodPrimeShells_iff (p : ℕ) :
    p ∈ harmonicCascadeGoodPrimeShells ↔
      p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨
        p = 41 := by
  simp [harmonicCascadeGoodPrimeShells, List.mem_cons, List.mem_nil_iff, or_false]

theorem harmonicCascadeGoodPrimeShells_prime {p : ℕ} (h : IsHarmonicCascadeGoodPrimeShell p) :
    Nat.Prime p := by
  rcases mem_harmonicCascadeGoodPrimeShells_iff p |>.mp h with
    h11 | h13 | h17 | h19 | h23 | h29 | h31 | h37 | h41
  all_goals subst_vars; decide

theorem harmonicCascadeGoodPrimeShells_ge_eleven {p : ℕ}
    (h : IsHarmonicCascadeGoodPrimeShell p) : 11 ≤ p := by
  rcases mem_harmonicCascadeGoodPrimeShells_iff p |>.mp h with
    h11 | h13 | h17 | h19 | h23 | h29 | h31 | h37 | h41
  all_goals subst_vars; decide

/-! ## Characteristic polynomial local data -/

/--
Cubic fibre char poly is `X³ - a_p X² + a_p X - 1` on prime shells; linear and quadratic
coefficients are determined by the holonomy trace.
-/
theorem mulModBSD_charpoly_trace_coeffs (p : ℕ) (hp : Nat.Prime p) :
    (mulModBSDPrimeFibreCharPoly p hp).coeff 1 =
        (mulModBSDPrimeHolonomyTrace p hp : ℤ) ∧
      (mulModBSDPrimeFibreCharPoly p hp).coeff 2 =
        -(mulModBSDPrimeHolonomyTrace p hp : ℤ) := by
  dsimp [mulModBSDPrimeFibreCharPoly]
  simp [coeff_X_pow, coeff_C, coeff_add, coeff_sub, coeff_one, coeff_mul_X, coeff_smul,
    mul_one, neg_mul, one_mul]

theorem mulModBSD_charpoly_constant_term (p : ℕ) (hp : Nat.Prime p) :
    (mulModBSDPrimeFibreCharPoly p hp).coeff 0 = -1 := by
  dsimp [mulModBSDPrimeFibreCharPoly]
  simp [coeff_X_pow, coeff_C, coeff_add, coeff_sub, coeff_one, coeff_mul_X, coeff_smul]

theorem mulModBSD_good_shell_charpoly_uniform {p : ℕ} (hp : Nat.Prime p)
    (h : IsHarmonicCascadeGoodPrimeShell p) :
    (mulModBSDPrimeFibreCharPoly p hp).coeff 1 = 6 ∧
      (mulModBSDPrimeFibreCharPoly p hp).coeff 2 = -6 := by
  have htrace := mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime hp
    (harmonicCascadeGoodPrimeShells_ge_eleven h)
  rcases mulModBSD_charpoly_trace_coeffs p hp with ⟨h1, h2⟩
  exact ⟨by rw [h1, htrace]; norm_cast, by rw [h2, htrace]; norm_cast⟩

/-! ## Uniform holonomy on good shells -/

theorem mulModBSD_good_shell_holonomy_six {p : ℕ} (hp : Nat.Prime p)
    (h : IsHarmonicCascadeGoodPrimeShell p) :
    mulModBSDPrimeHolonomyTrace p hp = 6 :=
  mulModBSDPrimeHolonomyTrace_eq_six_at_cascade_prime hp
    (harmonicCascadeGoodPrimeShells_ge_eleven h)

theorem mulModBSD_good_shell_ap_six {p : ℕ} (hp : Nat.Prime p)
    (h : IsHarmonicCascadeGoodPrimeShell p) :
    mulModBSDPrimeAp p hp = 6 := by
  rw [mulModBSDPrimeAp_real, mulModBSD_good_shell_holonomy_six hp h]
  norm_cast

theorem mulModBSD_good_shells_holonomy_rigid {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpgood : IsHarmonicCascadeGoodPrimeShell p) (hqgood : IsHarmonicCascadeGoodPrimeShell q) :
    mulModBSDPrimeHolonomyTrace p hp = mulModBSDPrimeHolonomyTrace q hq := by
  rw [mulModBSD_good_shell_holonomy_six hp hpgood,
    mulModBSD_good_shell_holonomy_six hq hqgood]

/-! ## Bad shell (Fano base) record -/

/--
**Bad prime shell data** at `p = 7`: holonomy trace and chart are proved; Ramanujan–Petersson
fails — the honest analog of a **bad reduction** / Tamagawa-sensitive local slot.
-/
structure MulModBSDBadPrimeShellRecord where
  prime : Nat.Prime 7
  euler_slot : MulModBSDPrimeEulerSlot 7
  holonomy_trace_seven : mulModBSDPrimeHolonomyTrace 7 Nat.prime_seven = 6
  ramanujan_fails : ¬ MulModBSDRamanujanPeterssonAt 7 Nat.prime_seven

noncomputable def mulModBSD_bad_prime_shell_record : MulModBSDBadPrimeShellRecord where
  prime := Nat.prime_seven
  euler_slot := mulModBSDPrimeEulerSlot7
  holonomy_trace_seven := mulModBSDPrimeHolonomyTrace_seven
  ramanujan_fails := mulModBSD_ramanujan_petersson_fails_at_seven

/-! ## Prefix Hecke / modularity targets and proved object -/

/--
**Prefix Hecke eigenform hypothesis (scoped).**  Ramanujan–Petersson only on good cascade
shells; does **not** claim global eigenform properties or bad-prime bounds.
-/
structure MulModBSDCascadePrefixHeckeEigenformHypothesis : Prop where
  ramanujan_on_good :
    ∀ {p : ℕ} (hp : Nat.Prime p), IsHarmonicCascadeGoodPrimeShell p →
      MulModBSDRamanujanPeterssonAt p hp
  uniform_holonomy :
    ∀ {p : ℕ} (hp : Nat.Prime p), IsHarmonicCascadeGoodPrimeShell p →
      mulModBSDPrimeHolonomyTrace p hp = 6

/--
**Open target:** classical-style Hecke multiplicativity / off-diagonal relations on good
shells only.  The proved **rigidity** lemma
`mulModBSD_good_shells_holonomy_rigid` is the diagonal trace coincidence special case.
-/
def MulModBSDHeckeGoodPrimeMultiplicativityTarget : Prop :=
  ∀ {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q),
    IsHarmonicCascadeGoodPrimeShell p → IsHarmonicCascadeGoodPrimeShell q →
      mulModBSDPrimeAp p hp * mulModBSDPrimeAp q hq =
        (6 : ℂ) * (6 : ℂ)

theorem mulModBSD_hecke_good_prime_multiplicativity_diagonal :
    MulModBSDHeckeGoodPrimeMultiplicativityTarget := by
  intro p q hp hq hpg hqgood
  rw [mulModBSD_good_shell_ap_six hp hpg, mulModBSD_good_shell_ap_six hq hqgood]

/--
**Proved cascade-prefix modularity object.**  Not classical `Γ₀(N)` modularity — the
honest bundle of prefix local Euler data, uniform good-prime traces, prefix RP, and the
isolated bad shell at `7`.
-/
structure MulModBSDCascadePrefixModularityObject where
  coefficient_fit : MulModBSDCoefficientFit
  euler_fit : MulModBSDEulerFactorFit
  prefix_hecke : MulModBSDCascadePrefixHeckeEigenformHypothesis
  bad_shell : MulModBSDBadPrimeShellRecord
  prime_ap_from_global :
    ∀ (p : ℕ) (hp : Nat.Prime p),
      mulModBSDPrimeAp p hp = (p : ℂ) * coefficient_fit.coeff p
  good_prime_multiplicativity_diagonal :
    MulModBSDHeckeGoodPrimeMultiplicativityTarget

theorem mulModBSD_cascade_prefix_hecke_eigenform :
    MulModBSDCascadePrefixHeckeEigenformHypothesis where
  ramanujan_on_good := fun hp hgood =>
    mulModBSD_ramanujan_petersson_of_holonomy_six hp
      (mulModBSD_good_shell_holonomy_six hp hgood)
      (harmonicCascadeGoodPrimeShells_ge_eleven hgood)
  uniform_holonomy := fun hp h => mulModBSD_good_shell_holonomy_six hp h

noncomputable def mulModBSD_cascade_prefix_modularity : MulModBSDCascadePrefixModularityObject where
  coefficient_fit := mulModBSDCoefficientFit
  euler_fit := mulModBSDEulerFactorFit
  prefix_hecke := mulModBSD_cascade_prefix_hecke_eigenform
  bad_shell := mulModBSD_bad_prime_shell_record
  prime_ap_from_global := mulModBSDPrimeAp_eq_prime_shell_coeff
  good_prime_multiplicativity_diagonal := mulModBSD_hecke_good_prime_multiplicativity_diagonal

theorem mulModBSD_cascade_prefix_modularity_has_uniform_good_ap :
    ∀ {p : ℕ} (hp : Nat.Prime p), IsHarmonicCascadeGoodPrimeShell p →
      mulModBSDPrimeAp p hp = 6 :=
  fun hp h => mulModBSD_good_shell_ap_six hp h

end

end Hqiv.Algebra
