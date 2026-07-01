import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.LonePairs` — lone pairs forced by the electron budget

Each part of a system is its own system with identical rules. The closed valence shell has `s`
pair-slots (octet → `s = 4`); each slot is either **shared** (a σ-bond) or **unshared** (a lone
pair). With `V` valence electrons the atom supplies `1 e⁻` to a shared slot and `2 e⁻` to an
unshared one. Once the bonding capacity `B = min(V, 2s − V)` fixes the shared slots, the leftover
`V − B` electrons pair into lone pairs `L = (V − B)/2`. The leftover is always even and the budget
`2L + B = V` closes exactly — so the lone-pair count (and hence the VSEPR domain count) is a
**consequence of electron conservation**, not an injected Lewis rule.

Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.LonePairs

/-- Shared slots (σ-bonds): bonds to the nearest closed shell, `min(V, 2s − V)`. -/
def bondCap (V s : ℕ) : ℕ := min V (2 * s - V)

/-- Unshared slots (lone pairs): the leftover valence electrons, paired. -/
def lonePairs (V s : ℕ) : ℕ := (V - bondCap V s) / 2

/-- VSEPR electron-domain count = shared + unshared slots. -/
def stericDomains (V s : ℕ) : ℕ := bondCap V s + lonePairs V s

theorem bondCap_le (V s : ℕ) : bondCap V s ≤ V := min_le_left _ _

/-- The electrons left after bonding always pair cleanly (even leftover). -/
theorem leftover_even (V s : ℕ) (h : V ≤ 2 * s) : 2 ∣ (V - bondCap V s) := by
  unfold bondCap; omega

/-- **Electron conservation closes.** `2·(lone pairs) + (σ-bonds) = V`: every valence electron is
accounted for, 2 per lone pair and 1 per bond. This is the derivation of the lone-pair count. -/
theorem electron_budget_closes (V s : ℕ) (h : V ≤ 2 * s) :
    2 * lonePairs V s + bondCap V s = V := by
  unfold lonePairs bondCap; omega

/-- Electron-deficient (left) side `V ≤ s`: no lone pairs, domains = electron count. -/
theorem domains_left (V s : ℕ) (h : V ≤ s) : stericDomains V s = V := by
  unfold stericDomains lonePairs bondCap; omega

/-- Octet-completing (right) side `s ≤ V ≤ 2s`: domains pin to `s`. -/
theorem domains_right (V s : ℕ) (h1 : s ≤ V) (h2 : V ≤ 2 * s) :
    stericDomains V s = s := by
  unfold stericDomains lonePairs bondCap; omega

/-- Every right-side second-row atom has four electron domains (octet `s = 4`). -/
theorem octet_domains_right (V : ℕ) (h1 : 4 ≤ V) (h2 : V ≤ 8) :
    stericDomains V 4 = 4 := domains_right V 4 h1 h2

-- worked examples: water (O), ammonia (N), methane (C), neon, boron
example : lonePairs 6 4 = 2 := by decide
example : lonePairs 5 4 = 1 := by decide
example : lonePairs 4 4 = 0 := by decide
example : lonePairs 8 4 = 4 := by decide
example : stericDomains 3 4 = 3 := by decide

end HqivSpine.Chemistry.LonePairs
