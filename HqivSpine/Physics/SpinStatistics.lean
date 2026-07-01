import HqivSpine.Physics.Exclusion
import HqivSpine.Algebra.Gauge
import Mathlib.Data.Nat.Choose.Basic

/-!
# `HqivSpine.Physics.SpinStatistics` — spin, statistics, and the quantum mechanics of
identical particles on the carrier

`Physics.Exclusion` showed the *inward wall* (no collapse to the Planck pole) is an
injectivity/pigeonhole fact. This module supplies the **quantum-mechanical content behind
it**: spin from the `Spin(8)` double cover, the spin–statistics dichotomy, and the
identical-particle Fock spaces in which **Pauli exclusion is a vanishing dimension**.

* **Spin from the double cover.** The carrier rotation group `SO(8)` has the genuine double
  cover `Spin(8)`. Its two chiral spinors `8s⁺, 8s⁻` (`Algebra.Triality`) flip sign under a
  `2π` rotation (`rotation2piPhase = −1`), while the vector `8v` does not — this two-
  valuedness *is* half-integer spin. The angular-momentum algebra is the concrete
  `su(2) ≅ so(3)` closure of the carrier's weak plane-rotations (`spin_su2_closure`, from
  `Algebra.Gauge.weak_su2_closes`).

* **Spin–statistics connection.** `spin_statistics_connection`: the `2π` phase equals the
  exchange sign — the spinor double-cover sign `−1` *is* the fermionic antisymmetry.

* **Statistics as Fock-space dimension.** The antisymmetric `N`-particle space on `K`
  single-particle states has dimension `fermionicDim K N = C(K, N)` (Slater determinants);
  the symmetric one `bosonicDim K N = C(K+N−1, N)`. Then:
  - `pauli_exclusion : 0 < fermionicDim K N ↔ N ≤ K` — **Pauli exclusion as a nonempty
    dimension**: more fermions than states ⇒ the space is *literally zero-dimensional*;
  - `bosonicDim_pos` — bosons never exclude (any number condense).

* **The wall, quantum-mechanically.** Because the carrier is fermionic,
  `chiral_fermionicDim_pole_zero` says the chiral content (`48` Weyl slots) has a
  zero-dimensional antisymmetric space on the pole's `8` states — the dimensional form of
  `Exclusion.chiral_content_no_collapse_to_pole`.

Honest scope: this is the QM of *identical particles* (statistics, exclusion, the spin
algebra), built from the carrier — not full wavefunction dynamics. It earns the no-collapse
wall as a vanishing dimension; it does not by itself single out `referenceM = 4`.

Mathlib-only; no legacy `Hqiv.*` imports, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Physics

open HqivSpine.Foundation HqivSpine.Algebra

/-! ## Spin from the `Spin(8)` double cover -/

/-- **Genuine spinor flag.** The vector `8v` (index `0`) is single-valued (integer spin);
the two chiral spinors `8s⁺, 8s⁻` (indices `1, 2`) are the genuine double-cover reps
(half-integer spin). -/
def isSpinorRep : So8RepIndex → Bool
  | 0 => false
  | _ => true

/-- **`2π`-rotation phase.** A genuine spinor flips sign under one full turn (the
double-cover `−1`); a tensor returns to `+1`. This two-valuedness is half-integer spin. -/
def rotation2piPhase (r : So8RepIndex) : ℤ := if isSpinorRep r then -1 else 1

theorem rotation2piPhase_vector : rotation2piPhase rep8V = 1 := rfl
theorem rotation2piPhase_spinorPlus : rotation2piPhase rep8SPlus = -1 := rfl
theorem rotation2piPhase_spinorMinus : rotation2piPhase rep8SMinus = -1 := rfl

/-- The genuine spinors are exactly the two chiral slots. -/
theorem isSpinorRep_iff (r : So8RepIndex) :
    isSpinorRep r = true ↔ r = rep8SPlus ∨ r = rep8SMinus := by
  fin_cases r <;> decide

/-! ## The spin–statistics dichotomy -/

/-- Exchange statistics of identical quanta. -/
inductive Statistics
  | fermion
  | boson
  deriving DecidableEq, Repr

/-- **Exchange sign** of two identical particles: fermions antisymmetric (`−1`), bosons
symmetric (`+1`). -/
def exchangeSign : Statistics → ℤ
  | .fermion => -1
  | .boson => 1

theorem exchangeSign_sq (s : Statistics) : exchangeSign s ^ 2 = 1 := by cases s <;> decide

/-- **Spin–statistics map:** half-integer spin (genuine spinor) ⇒ fermion; integer ⇒ boson. -/
def statisticsOfRep (r : So8RepIndex) : Statistics :=
  if isSpinorRep r then .fermion else .boson

theorem spinorPlus_is_fermion : statisticsOfRep rep8SPlus = .fermion := rfl
theorem spinorMinus_is_fermion : statisticsOfRep rep8SMinus = .fermion := rfl
theorem vector_is_boson : statisticsOfRep rep8V = .boson := rfl

/-- **Spin–statistics connection:** the `2π`-rotation phase equals the exchange sign. The
double-cover sign of a spinor *is* its fermionic antisymmetry. -/
theorem spin_statistics_connection (r : So8RepIndex) :
    rotation2piPhase r = exchangeSign (statisticsOfRep r) := by
  unfold rotation2piPhase statisticsOfRep
  rcases Bool.eq_false_or_eq_true (isSpinorRep r) with h | h <;>
    simp [h, exchangeSign]

/-! ## Spin angular momentum: the `su(2) ≅ so(3)` algebra on the carrier -/

/-- **Spin-½ angular-momentum generators** are the weak `su(2) ≅ so(3)` plane rotations of
the carrier (`Algebra.weakL₁,₂,₃`). The double cover `SU(2) → SO(3)` is exactly what makes
spin half-integer — the same two-valuedness as `rotation2piPhase` on the spinors. -/
theorem spin_su2_closure :
    bracket weakL1 weakL2 = -weakL3 ∧
    bracket weakL1 weakL3 = weakL2 ∧
    bracket weakL2 weakL3 = -weakL1 :=
  weak_su2_closes

/-! ## Identical-particle Fock spaces: where Pauli is a vanishing dimension -/

/-- **Antisymmetric (fermionic) `N`-particle dimension** on `K` single-particle states —
the number of Slater determinants `C(K, N)`. -/
def fermionicDim (K N : ℕ) : ℕ := Nat.choose K N

/-- **Symmetric (bosonic) `N`-particle dimension** on `K` states — `C(K+N−1, N)`. -/
def bosonicDim (K N : ℕ) : ℕ := Nat.choose (K + N - 1) N

/-- **Pauli exclusion as a dimension count:** the fermionic `N`-particle space is nonempty
iff there are at least `N` single-particle states. -/
theorem pauli_exclusion (K N : ℕ) : 0 < fermionicDim K N ↔ N ≤ K := by
  unfold fermionicDim
  rw [Nat.pos_iff_ne_zero, ne_eq, Nat.choose_eq_zero_iff, not_lt]

/-- **Overfilling kills the fermionic space:** `K < N ⇒ dim = 0`. There is *no*
antisymmetric state for more fermions than states. -/
theorem fermionicDim_eq_zero (K N : ℕ) (h : K < N) : fermionicDim K N = 0 :=
  Nat.choose_eq_zero_of_lt h

/-- **Bosons never exclude:** with at least one state, the symmetric `N`-particle space is
always nonempty — arbitrarily many bosons condense into the same states. -/
theorem bosonicDim_pos (K N : ℕ) (hK : 0 < K) : 0 < bosonicDim K N := by
  unfold bosonicDim
  exact Nat.choose_pos (by omega)

/-! ## The carrier is fermionic — the no-collapse wall is a vanishing dimension -/

/-- The carrier states are spinor (half-integer spin), hence fermionic: occupation is
antisymmetric, so `cumulativeModes m` caps the content (`Exclusion.pauli_pigeonhole` in
dimensional form). -/
theorem carrier_fermionicDim_pos_iff (N m : ℕ) :
    0 < fermionicDim (cumulativeModes m) N ↔ N ≤ cumulativeModes m :=
  pauli_exclusion _ _

/-- **No collapse to the Planck pole, as a zero-dimensional fermionic space.** The chiral
content (`48` Weyl slots) has *no* antisymmetric state on the pole's `8` carrier states:
`fermionicDim 8 48 = 0`. Dimensional form of `Exclusion.chiral_content_no_collapse_to_pole`. -/
theorem chiral_fermionicDim_pole_zero :
    fermionicDim (cumulativeModes 0) chiralSlotCount = 0 := by
  apply fermionicDim_eq_zero
  rw [cumulativeModes_zero, carrierMultiplicity_eq_eight, chiralSlotCount_eq_48]
  norm_num

/-! ## Capstone -/

/-- **Spin–statistics in the spine.**
1. The carrier's genuine spinors flip sign under `2π` (`rotation2piPhase rep8SPlus = −1`),
   the double-cover face of half-integer spin, whose algebra is the `su(2) ≅ so(3)` closure;
2. that sign *is* the fermionic exchange sign (`spin_statistics_connection`);
3. fermionic exchange = antisymmetric occupation, whose `N`-particle dimension `C(K,N)`
   vanishes once `K < N` (`pauli_exclusion`) — Pauli exclusion as a vanishing dimension —
   while bosons never exclude (`bosonicDim_pos`);
4. so the inward wall is a *zero-dimensional* space: the chiral content cannot occupy the
   pole (`chiral_fermionicDim_pole_zero`). -/
theorem spin_statistics_spine :
    rotation2piPhase rep8SPlus = -1 ∧
    (∀ r : So8RepIndex, rotation2piPhase r = exchangeSign (statisticsOfRep r)) ∧
    (∀ K N : ℕ, 0 < fermionicDim K N ↔ N ≤ K) ∧
    (∀ K N : ℕ, 0 < K → 0 < bosonicDim K N) ∧
    fermionicDim (cumulativeModes 0) chiralSlotCount = 0 :=
  ⟨rotation2piPhase_spinorPlus, spin_statistics_connection, pauli_exclusion,
   bosonicDim_pos, chiral_fermionicDim_pole_zero⟩

end HqivSpine.Physics
