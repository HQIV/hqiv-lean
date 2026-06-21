import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Scale orbit as `x ↦ (x · m) mod n`

The locked `G₂`/Δ holonomy story in `GoldbachG2Parity` packages a **scale orbit**
(`LockedScaleOrbit`) that should sweep every integer tangency position `k` with
`1 ≤ k < n` and complementary radii `k + (n − k) = n`.

Multiplication mod `n` by a coprime multiplier `m` is the clean arithmetic model:

* `scaleOrbitMulMod n m x = (x * m) % n` is a **permutation** of `ℤ/nℤ` when
  `Nat.Coprime m n`;
* iterating `x, x·m, x·m², …` is the holonomy **transport** along the scale axis;
* every residue — hence every positive position below `n` — is hit by some step.

This module proves that permutation/sweep layer.  It does **not** by itself
construct a full `LockedScaleOrbit` (that still needs the `G₂` pole-lock data);
it supplies the modular tool the holonomy proof can invoke once `m` is locked.
-/

namespace Hqiv.Geometry

open Function

/-! ## Basic mul-mod readout -/

/-- One scale-orbit step: multiply by `m` and reduce mod `n`. -/
def scaleOrbitMulMod (n m x : ℕ) : ℕ :=
  (x * m) % n

@[simp] theorem scaleOrbitMulMod_zero (n m : ℕ) : scaleOrbitMulMod n m 0 = 0 := by
  simp [scaleOrbitMulMod]

theorem scaleOrbitMulMod_lt (n m x : ℕ) (hn : 0 < n) : scaleOrbitMulMod n m x < n := by
  simp [scaleOrbitMulMod, Nat.mod_lt _ hn]

/-! ## Coprime multiplier ⇒ bijection on `ZMod n` -/

theorem scaleOrbitMulMod_zmod (n m x : ℕ) (hn : 0 < n) :
    (scaleOrbitMulMod n m x : ZMod n) = (m : ZMod n) * (x : ZMod n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  simp [scaleOrbitMulMod, Nat.mul_mod, mul_comm]

theorem coprime_implies_mulMod_unit {n m : ℕ} (hn : 0 < n) (hcop : Nat.Coprime m n) :
    IsUnit (m : ZMod n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [ZMod.isUnit_iff_coprime]
  exact hcop

theorem scaleOrbitMulMod_bijective {n m : ℕ} (hn : 0 < n) (hcop : Nat.Coprime m n) :
    Bijective (fun x : ZMod n => (m : ZMod n) * x) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hu := Units.mulLeft_bijective (ZMod.unitOfCoprime m hcop)
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · exact hu.1 (by simpa [ZMod.coe_unitOfCoprime] using h)
  · obtain ⟨y, hy⟩ := hu.2 x
    refine ⟨y, ?_⟩
    simpa [ZMod.coe_unitOfCoprime] using hy

/-! ## Every positive position below `n` is hit -/

theorem scaleOrbitMulMod_hits_position {n m k : ℕ} (hn : 0 < n) (hcop : Nat.Coprime m n)
    (_hk₀ : 0 < k) (hk : k < n) :
    ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hb := scaleOrbitMulMod_bijective hn hcop
  obtain ⟨y, hy⟩ := hb.2 (k : ZMod n)
  refine ⟨y.val, y.val_lt, ?_⟩
  have hzm : (scaleOrbitMulMod n m y.val : ZMod n) = (k : ZMod n) := by
    rw [scaleOrbitMulMod_zmod n m y.val hn, ZMod.natCast_zmod_val y]
    exact hy
  have hnat : scaleOrbitMulMod n m y.val % n = k % n :=
    (ZMod.natCast_eq_natCast_iff' _ _ n).1 hzm
  rw [Nat.mod_eq_of_lt (scaleOrbitMulMod_lt n m y.val hn), Nat.mod_eq_of_lt hk] at hnat
  exact hnat

theorem scaleOrbitMulMod_hits_position_fin {n m : ℕ} (hn : 0 < n) (hcop : Nat.Coprime m n)
    (k : Fin n) (_hk₀ : 0 < k.val) :
    ∃ x : Fin n, scaleOrbitMulMod n m x.val = k.val := by
  obtain ⟨x, hxlt, heq⟩ :=
    scaleOrbitMulMod_hits_position (k := k.val) hn hcop _hk₀ k.isLt
  exact ⟨⟨x, hxlt⟩, heq⟩

/-! ## Complementary radii (Goldbach / bilateral pole geometry) -/

theorem scaleOrbitMulMod_complementary_sum (n k : ℕ) (hk : k ≤ n) :
    k + (n - k) = n := Nat.add_sub_of_le hk

theorem scaleOrbitMulMod_bilateral_complement {n k : ℕ} (_hk₀ : 0 < k) (hk : k < n) :
    k + (n - k) = n ∧ (n - k) + k = n := by
  refine ⟨scaleOrbitMulMod_complementary_sum n k (Nat.le_of_lt hk), ?_⟩
  rw [Nat.add_comm]
  exact scaleOrbitMulMod_complementary_sum n k (Nat.le_of_lt hk)

/-! ## Packaging for holonomy consumers -/

/--
Arithmetic scale-orbit certificate: coprime mul-mod sweep captures every
positive integer position below `n`.
-/
structure MulModScaleOrbitSweep (n m : ℕ) where
  pos : 0 < n
  coprime : Nat.Coprime m n
  hits :
    ∀ k : ℕ, 0 < k → k < n → ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k

noncomputable def mulModScaleOrbitSweep (n m : ℕ) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    MulModScaleOrbitSweep n m where
  pos := hn
  coprime := hcop
  hits := fun k hk₀ hk => scaleOrbitMulMod_hits_position (k := k) hn hcop hk₀ hk

theorem mulModScaleOrbitSweep_hits (S : MulModScaleOrbitSweep n m) {k : ℕ}
    (hk₀ : 0 < k) (hk : k < n) :
    ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n m x = k :=
  S.hits k hk₀ hk

/-!
## Link to `LockedScaleOrbit` integer capture

The geometric `LockedScaleOrbit.integer_positions` field currently uses the
identity scale `k ↦ k`.  Any holonomy proof that locks a coprime multiplier `m`
can replace transport by `scaleOrbitMulMod n m` and cite `MulModScaleOrbitSweep`
for existence of a preimage at each tangency position.
-/

/-- Mul-mod sweep implies the bilateral complementary-radius identity at every hit. -/
theorem mulModScaleOrbitSweep_bilateral {n m : ℕ} (_S : MulModScaleOrbitSweep n m)
    {k : ℕ} (_hk₀ : 0 < k) (hk : k < n) :
    k + (n - k) = n :=
  scaleOrbitMulMod_complementary_sum n k (Nat.le_of_lt hk)

/-! ## Nested quotients (Hopf sub-fibration layer) -/

/--
**Mul-mod descends to stack quotients.**  When `r ∣ n`, the full-shell transport
mod `r` agrees with mul-mod on the smaller circle — the arithmetic shadow of a
nested Hopf chart restriction.
-/
theorem scaleOrbitMulMod_respects_quotient {n m x r : ℕ} (hr : r ∣ n) :
    scaleOrbitMulMod n m x % r = scaleOrbitMulMod r (m % r) (x % r) := by
  unfold scaleOrbitMulMod
  rw [Nat.mod_mod_of_dvd (x * m) hr, Nat.mul_mod]

/-- Slot-index transport on `Fin n` induced by coprime mul-mod. -/
def mulModSlot (n m : ℕ) (hn : 0 < n) (_hcop : Nat.Coprime m n) (k : Fin n) : Fin n :=
  ⟨(scaleOrbitMulMod n m k.val), scaleOrbitMulMod_lt n m k.val hn⟩

theorem mulModSlot_val (n m : ℕ) (hn : 0 < n) (hcop : Nat.Coprime m n) (k : Fin n) :
    (mulModSlot n m hn hcop k).val = scaleOrbitMulMod n m k.val := rfl

/-!
Bijection of `mulModSlot` on coprime shells is packaged in
`Hqiv.Story.S3HopfMulModTransport.hopf_mul_mod_slot_bijective`.
-/

/-! ## Harmonic orbit multiplier `6/5` → integer mul-mod step -/

/--
Integer mul-mod step shadowing the harmonic orbit multiplier `6/5`.

Try `6` (numerator), then `5` (denominator), then `11` (first fallback when both
fail — e.g. `n = 105 = 3·5·7` blocks `6`, `5`, and `7`).
-/
def harmonicOrbitMulModMultiplier (n : ℕ) : ℕ :=
  if Nat.Coprime 6 n then 6
  else if Nat.Coprime 5 n then 5
  else if Nat.Coprime 11 n then 11
  else 7

theorem harmonicOrbitMulModMultiplier_eq_six {n : ℕ} (h : Nat.Coprime 6 n) :
    harmonicOrbitMulModMultiplier n = 6 := by
  simp [harmonicOrbitMulModMultiplier, h]

theorem harmonicOrbitMulModMultiplier_eq_five {n : ℕ} (h6 : ¬ Nat.Coprime 6 n)
    (h : Nat.Coprime 5 n) :
    harmonicOrbitMulModMultiplier n = 5 := by
  simp [harmonicOrbitMulModMultiplier, h6, h]

theorem harmonicOrbitMulModMultiplier_eq_eleven {n : ℕ} (h6 : ¬ Nat.Coprime 6 n)
    (h5 : ¬ Nat.Coprime 5 n) (h : Nat.Coprime 11 n) :
    harmonicOrbitMulModMultiplier n = 11 := by
  simp [harmonicOrbitMulModMultiplier, h6, h5, h]

theorem harmonicOrbitMulModMultiplier_eq_seven {n : ℕ} (h6 : ¬ Nat.Coprime 6 n)
    (h5 : ¬ Nat.Coprime 5 n) (h11 : ¬ Nat.Coprime 11 n) :
    harmonicOrbitMulModMultiplier n = 7 := by
  simp [harmonicOrbitMulModMultiplier, h6, h5, h11]

/-- Certified Goldbach shells `2N` from the small-composite witness route. -/
def certifiedGoldbachShells : List ℕ :=
  [8, 12, 16, 18, 20, 30]

theorem mem_certifiedGoldbachShells_iff (n : ℕ) :
    n ∈ certifiedGoldbachShells ↔ n = 8 ∨ n = 12 ∨ n = 16 ∨ n = 18 ∨ n = 20 ∨ n = 30 := by
  simp [certifiedGoldbachShells]

/--
**Documented obstruction.**  The `{6,5,11,7}` cascade fails exactly on
`harmonicRawObstructionShell n` (`385 ∣ n` and `2 ∣ n ∨ 3 ∣ n`; first at `770`).
See `harmonic_raw_not_coprime_iff_obstruction_shell` in
`HarmonicMulModCubeTriangulation`.
-/
def HarmonicMulModMultiplierCoprimeObstruction (n : ℕ) : Prop :=
  Nat.Coprime (harmonicOrbitMulModMultiplier n) n

theorem harmonic_multiplier_coprime_certified (n : ℕ)
    (h : n ∈ certifiedGoldbachShells) :
    Nat.Coprime (harmonicOrbitMulModMultiplier n) n := by
  rcases mem_certifiedGoldbachShells_iff n |>.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/--
**General harmonic sweep.**  Whenever the locked cascade multiplier is coprime to `n`,
mul-mod sweeps every positive position below `n`.
-/
noncomputable def harmonic_mul_mod_sweep_of_coprime (n : ℕ) (hn : 0 < n)
    (hcop : HarmonicMulModMultiplierCoprimeObstruction n) :
    MulModScaleOrbitSweep n (harmonicOrbitMulModMultiplier n) :=
  mulModScaleOrbitSweep n (harmonicOrbitMulModMultiplier n) hn hcop

theorem harmonic_mul_mod_sweep_of_coprime_hits (n : ℕ) (hn : 0 < n)
    (hcop : HarmonicMulModMultiplierCoprimeObstruction n) {k : ℕ}
    (hk₀ : 0 < k) (hk : k < n) :
    ∃ x : ℕ, x < n ∧ scaleOrbitMulMod n (harmonicOrbitMulModMultiplier n) x = k :=
  mulModScaleOrbitSweep_hits (harmonic_mul_mod_sweep_of_coprime n hn hcop) hk₀ hk

theorem harmonic_mul_mod_sweep_certified (n : ℕ) (h : n ∈ certifiedGoldbachShells) :
    MulModScaleOrbitSweep n (harmonicOrbitMulModMultiplier n) :=
  harmonic_mul_mod_sweep_of_coprime n
    (by
      rcases mem_certifiedGoldbachShells_iff n |>.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide)
    (harmonic_multiplier_coprime_certified n h)

theorem harmonic_mul_mod_multiplier_coprime_certified_shells :
    ∀ n ∈ certifiedGoldbachShells, HarmonicMulModMultiplierCoprimeObstruction n := by
  intro n h
  exact harmonic_multiplier_coprime_certified n h

end Hqiv.Geometry
