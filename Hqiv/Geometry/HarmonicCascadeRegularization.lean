import Hqiv.Geometry.ScaleOrbitMulMod
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

/-!
# Harmonic mul-mod cascade regularization

The **raw** cascade (`harmonicOrbitMulModMultiplier`) is a finite trial tower
`6 → 5 → 11 → 7` — the arithmetic analogue of a **truncated partial sum**.
It fails at `n = 770` (`7 ∣ 770`).

The **regularized** multiplier extends the tower: keep the `6/5` harmonic shadow
on the prefix, then select the first **prime unit** ≥ `13` that is coprime to
`n` — the adelic/p-adic "first local unit outside the obstruction ideal."

This mirrors the HQIV harmonic–ζ split:

| Harmonic side | Regularized / closed side |
|---------------|---------------------------|
| `H_n = ∑_{k≤n} 1/k` (divergent partial sum) | `K(n) = H_n + α·log` (curvature channel) |
| raw cascade multiplier (dies at 770) | `harmonicOrbitMulModMultiplierReg` (always coprime) |
| inverse-power tail before closure | `ζ(2)−1`, `ζ(3)−1` tails (Story layer) |

Lie promotion consumes the **regularized** obstruction; the raw cascade remains
as the honest finite-prefix experiment.
-/

namespace Hqiv.Geometry

open Nat

instance harmonicMulModObstructionDecidable (n : ℕ) :
    Decidable (HarmonicMulModMultiplierCoprimeObstruction n) := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction]
  infer_instance

/-! ## Raw obstruction (770 witness) -/

theorem harmonic_raw_not_coprime_770 :
    ¬ HarmonicMulModMultiplierCoprimeObstruction 770 := by
  dsimp [HarmonicMulModMultiplierCoprimeObstruction, harmonicOrbitMulModMultiplier]
  decide

theorem harmonic_raw_multiplier_770_eq_seven :
    harmonicOrbitMulModMultiplier 770 = 7 := by
  native_decide

/-! ## Prime step above shell (regularization fallback) -/

/--
There is always a prime ≥ `13` coprime to `n` once the finite prefix fails.
This is the arithmetic regularization step (Euclid: a prime larger than `n`
cannot divide `n`).
-/
theorem exists_prime_ge_thirteen_coprime (n : ℕ) (hn : 0 < n) :
    ∃ p, 13 ≤ p ∧ Nat.Prime p ∧ Nat.Coprime p n := by
  obtain ⟨p, hge, hp⟩ := Nat.exists_infinite_primes (n + 13)
  have hgt : n < p := by omega
  have hcop : Nat.Coprime p n := Nat.coprime_of_lt_prime hn.ne' hgt hp
  refine ⟨p, ?_, hp, hcop⟩
  omega

/-- Canonical regularized prime unit once the raw prefix is blocked. -/
noncomputable def harmonicRegularizedPrimeStep (n : ℕ) (hn : 0 < n) : ℕ :=
  Classical.choose (exists_prime_ge_thirteen_coprime n hn)

theorem harmonicRegularizedPrimeStep_ge_thirteen (n : ℕ) (hn : 0 < n) :
    13 ≤ harmonicRegularizedPrimeStep n hn :=
  (Classical.choose_spec (exists_prime_ge_thirteen_coprime n hn)).1

theorem harmonicRegularizedPrimeStep_prime (n : ℕ) (hn : 0 < n) :
    Nat.Prime (harmonicRegularizedPrimeStep n hn) :=
  (Classical.choose_spec (exists_prime_ge_thirteen_coprime n hn)).2.1

theorem harmonicRegularizedPrimeStep_coprime (n : ℕ) (hn : 0 < n) :
    Nat.Coprime (harmonicRegularizedPrimeStep n hn) n :=
  (Classical.choose_spec (exists_prime_ge_thirteen_coprime n hn)).2.2

/-! ## Regularized multiplier -/

/--
**Regularized cascade multiplier.**

* If the raw `6/5`-seeded prefix already yields a coprime unit, keep it.
* Otherwise take the canonical prime regularization step ≥ `13`.

At `n = 770` this selects a prime ≥ `13` coprime to `770` (e.g. `13`), not the
raw value `7`.
-/
noncomputable def harmonicOrbitMulModMultiplierReg (n : ℕ) (hn : 0 < n) : ℕ :=
  if HarmonicMulModMultiplierCoprimeObstruction n then
    harmonicOrbitMulModMultiplier n
  else
    harmonicRegularizedPrimeStep n hn

def HarmonicMulModMultiplierCoprimeObstructionReg (n : ℕ) (hn : 0 < n) : Prop :=
  Nat.Coprime (harmonicOrbitMulModMultiplierReg n hn) n

theorem harmonic_reg_multiplier_coprime (n : ℕ) (hn : 0 < n) :
    HarmonicMulModMultiplierCoprimeObstructionReg n hn := by
  dsimp [HarmonicMulModMultiplierCoprimeObstructionReg, harmonicOrbitMulModMultiplierReg]
  split_ifs with h
  · exact h
  · exact harmonicRegularizedPrimeStep_coprime n hn

theorem harmonic_reg_extends_raw (n : ℕ) (hn : 0 < n)
    (h : HarmonicMulModMultiplierCoprimeObstruction n) :
    harmonicOrbitMulModMultiplierReg n hn = harmonicOrbitMulModMultiplier n := by
  unfold harmonicOrbitMulModMultiplierReg
  rw [if_pos h]

theorem harmonic_reg_fixes_770 (hn : 0 < 770 := by decide) :
    HarmonicMulModMultiplierCoprimeObstructionReg 770 hn ∧
      ¬ HarmonicMulModMultiplierCoprimeObstruction 770 ∧
      harmonicOrbitMulModMultiplierReg 770 hn ≠ harmonicOrbitMulModMultiplier 770 := by
  have hreg := harmonicRegularizedPrimeStep_ge_thirteen 770 hn
  have hreg_eq : harmonicOrbitMulModMultiplierReg 770 hn =
      harmonicRegularizedPrimeStep 770 hn := by
    unfold harmonicOrbitMulModMultiplierReg
    rw [if_neg harmonic_raw_not_coprime_770]
  refine ⟨harmonic_reg_multiplier_coprime 770 hn, harmonic_raw_not_coprime_770, ?_⟩
  intro heq
  rw [hreg_eq] at heq
  rw [heq, harmonic_raw_multiplier_770_eq_seven] at hreg
  omega

/--
**Global regularized promotion availability** — always true for `n > 0`.
Contrast with `GlobalHarmonicLiePromotion` on the raw finite prefix.
-/
def GlobalHarmonicLiePromotionReg : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), HarmonicMulModMultiplierCoprimeObstructionReg n hn

theorem global_harmonic_lie_promotion_reg : GlobalHarmonicLiePromotionReg := by
  intro n hn
  exact harmonic_reg_multiplier_coprime n hn

noncomputable def harmonic_mul_mod_sweep_reg (n : ℕ) (hn : 0 < n) :
    MulModScaleOrbitSweep n (harmonicOrbitMulModMultiplierReg n hn) :=
  mulModScaleOrbitSweep n (harmonicOrbitMulModMultiplierReg n hn) hn <|
    show Nat.Coprime (harmonicOrbitMulModMultiplierReg n hn) n from
      harmonic_reg_multiplier_coprime n hn

end Hqiv.Geometry
