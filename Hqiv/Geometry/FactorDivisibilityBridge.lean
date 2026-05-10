import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

/-!
# GCD and division: one divisibility certificate

In `ℕ`, certifying a factor is **one** predicate — **divisibility** — under three common faces:

* **Remainder test** `n % d = 0` (the monolithic script’s gate).
* **Exact division** `n = d * (n / d)` (same data as `d ∣ n`; see `dvd_iff_mul_div`).
* **GCD** `gcd(x, n)`: by definition of gcd, `gcd(x, n) ∣ n` (`Nat.gcd_dvd_right`). Any nontrivial
  `gcd` strictly between `1` and `n` is therefore the **same** kind of witness as a direct modular
  hit — not a different mathematical object.

This module only packages those equivalences for the factor-search story. It does **not** prove that
any particular search (OSH, monolithic walk, or Shor sampling) **finds** such a witness.
-/

namespace Hqiv.Geometry

open Nat
open Hqiv.Geometry.HQIVOSHIntegratedFactorDriver

/-- `d ∣ n` iff `n` is exact integer quotient with divisor `d`. -/
theorem dvd_iff_mul_div {d n : ℕ} : d ∣ n ↔ n = d * (n / d) := by
  constructor
  · intro h
    exact (Nat.mul_div_cancel' h).symm
  · intro h
    rw [h]
    exact dvd_mul_right _ _

/-- Shor-style gcd output packaged as the same `OddCoreFactorWitness` as a remainder hit. -/
def oddCoreWitness_of_gcd {odd x : ℕ} (h₁ : 1 < x.gcd odd) (h₂ : x.gcd odd < odd) :
    OddCoreFactorWitness odd :=
  ⟨x.gcd odd, h₁, h₂, Nat.gcd_dvd_right x odd⟩

/--
If `d` already divides `odd`, then `gcd(d, odd) = d`: the gcd route and the “division” route carry
the **same** distinguished divisor.
-/
theorem gcd_eq_left_of_dvd {d odd : ℕ} (hdvd : d ∣ odd) : d.gcd odd = d :=
  dvd_antisymm (Nat.gcd_dvd_left d odd) (Nat.dvd_gcd (dvd_refl d) hdvd)

end Hqiv.Geometry
