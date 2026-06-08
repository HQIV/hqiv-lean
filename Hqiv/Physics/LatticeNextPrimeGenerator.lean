import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Geometry.EuclideanBallHorizontalSlice
import Hqiv.Physics.DivisionAlgebraZetaScaffold
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.OctonionicZeta

/-!
# Lattice-native next-“prime” generator (ℝ¹ shell ladder only)

## Status: **not a working end-to-end algorithm**

The names below were introduced as **scaffold** pieces. **Composing them does not yield** a correct
procedure for “decompose \(x\) → inspect packing → apply rapidity → get the meaningful next shell” in any
proved sense:

* **`decompose_to_fano_moduli`** multiplies a **real** running product by `eff^l_f` until `acc ≥ (x : ℝ)`
  or **fuel** runs out. This is **not** a factorization of `x`, not a unique expansion in Fano moduli,
  and **not** guaranteed to reach `acc ≥ x` (fuel can stop early with an empty or partial trace).
* **`phi_t_step` is ignored** in the decomposition (only the API carries it); rapidity does not steer
  the greedy walk in this file.
* **`spherePackingAtShell` and `rapidity_effect_on_sphere` are not used** by `next_prime_generator`;
  the four-stage story is **not** wired in code.
* **`next_prime_generator`** is literally `next_lattice_prime (decompose_last_shell …) …`: the shell
  `last_m` from the greedy trace is an **ad hoc** starting point for `Nat.find` on `eff` ratios. There
  is **no** theorem that this output is determined by \(x\) in a number-theoretic way, nor that it
  agrees with any desired “prime gap” semantics beyond the **existing** meaning of `next_lattice_prime`.

Use these definitions only as **typed hooks** for future work or as **counterexamples** to over-reading
the narrative. For the honest quantum-circuit note (also **not** claiming a working QC implementation),
see `AGENTS/QUANTUM_CIRCUIT_NEXT_PRIME_PROBE.md`.

---

## What the definitions still are (probe-level)

On the **same** discrete `m : ℕ` ladder as `effCorrected` and `next_lattice_prime`:

1. **Greedy trace** `decompose_to_fano_moduli` — as above (not a validated decomposition of `x`).
2. **`decompose_last_shell`** — last shell index in that trace, or `0` if empty.
3. **`spherePackingAtShell`** (re-exported from geometry) and **`rapidity_effect_on_sphere`** — standalone
   numeric probes at a chosen `m`.
4. **`next_prime_generator`** — `next_lattice_prime` from `decompose_last_shell` (composition only).

**Not claimed:** classical primes in `ℤ`, rational factorization, RH, or an octonionic Euler product.

## Defect-peak usage (candidate-only)

This file also exposes a **candidate-selector bridge** to geometry defect profiles:
use `next_prime_generator` only to pick a shell index `m`, then evaluate
`Hqiv.Geometry.sliceAreaDefectAt ... m z`.

This does **not** prove that the selected shell is the true global maximum/argmax of defect; it only
provides typed objects and predicates for checking that hypothesis.
-/

namespace Hqiv.Physics

open Finset
open scoped BigOperators

noncomputable section

/-- One step in the greedy Fano-weighted `eff` product along shells. -/
structure FanoModulusStep where
  shell : ℕ
  eff : ℝ
  lf : ℕ
  factor : ℝ

/-- Auxiliary loop (fuel-decreasing). -/
noncomputable def decompose_to_fano_moduli_loop (δ : ℝ) (target : ℝ) (m : ℕ) (acc : ℝ) (fuel : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (rev : List FanoModulusStep) : List FanoModulusStep :=
  match fuel with
  | 0 => rev
  | fuel' + 1 =>
    if _hstop : acc ≥ target then
      rev
    else
      let f := fano_vertex_of_shell m
      let lf := fanoLineWeight f
      let eff := effCorrected δ m
      let factor := eff ^ lf
      let step :=
        { shell := m, eff := eff, lf := lf, factor := factor : FanoModulusStep }
      let acc' := acc * factor
      decompose_to_fano_moduli_loop δ target (m + 1) acc' fuel' hden (step :: rev)

/-- Greedy ℝ¹ decomposition: multiply `acc` by `eff(m)^{l_f}` until `acc ≥ (x : ℝ)` or fuel empty.

`phi_t_step` is **ignored** here; detuning uses `h, φ, t, β_cum` only (same as `effCorrected` in zeta). -/
noncomputable def decompose_to_fano_moduli (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (_phi_t_step : ℕ → ℝ) (fuel : ℕ)
    (_hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m) :
    List FanoModulusStep :=
  let δ := delta_auxiliary_phi_per_shell h φ t β_cum
  if _hx : 0 < x then
    (decompose_to_fano_moduli_loop δ (x : ℝ) 0 1 fuel hden []).reverse
  else
    []

/-- Last shell index used in the decomposition trace, or `0` if the list is empty. -/
noncomputable def decompose_last_shell (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (fuel : ℕ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m) : ℕ :=
  let L := decompose_to_fano_moduli x h φ t β_cum phi_t_step fuel hδ hden
  match L with
  | [] => 0
  | a :: as => (List.getLast (a :: as) (by simp)).shell

/-- Stretch of `eff` across `m ↦ m+1`, divisor-mode enlargement, and rapidity–curvature slot. -/
structure SphereEffect where
  stretch_ratio : ℝ
  symmetry_enlargement : ℕ
  rapidity_slot : ℝ

/-- How the next shell compares to `m`, plus a scalar from step-wise rapidity and curvature slot.

`δ` is the same global detuning scalar as in `effCorrected`. -/
noncomputable def rapidity_effect_on_sphere (m : ℕ) (δ : ℝ) (_hden : RindlerDenDeltaPos δ m)
    (_hden' : RindlerDenDeltaPos δ (m + 1)) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) : SphereEffect where
  stretch_ratio := effCorrected δ (m + 1) / effCorrected δ m
  symmetry_enlargement :=
    max (Finset.card (Nat.divisors (m + 1))) (Finset.card (Nat.divisors (m + 2)))
  rapidity_slot := phi_t_step m * δslot m

/-- Main generator: advance from the decomposition’s last shell to the next lattice-prime shell. -/
noncomputable def next_prime_generator (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (_δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) : ℕ :=
  let last_m := decompose_last_shell x h φ t β_cum phi_t_step fuel hδ hden
  next_lattice_prime last_m h φ t β_cum threshold hδ (hden last_m) hth

/-!
### Bridge: next-shell candidate vs slice-defect profile
-/

/-- Slice-defect profile at a fixed slice height `z`, indexed by shell `m`. -/
noncomputable def sliceDefectProfileAtZ (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ) : ℕ → ℝ :=
  fun m => Hqiv.Geometry.sliceAreaDefectAt r observedArea m z

/-- Absolute slice-defect profile at fixed `z`. -/
noncomputable def absSliceDefectProfileAtZ (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ) : ℕ → ℝ :=
  fun m => |sliceDefectProfileAtZ r observedArea z m|

/-- Candidate shell selected by `next_prime_generator` for defect-profile evaluation. -/
noncomputable def nextShellDefectCandidate (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) : ℕ :=
  next_prime_generator x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth

/-- Defect value at the shell selected by `next_prime_generator`. -/
noncomputable def nextShellDefectValue
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ)
    (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) : ℝ :=
  sliceDefectProfileAtZ r observedArea z
    (nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth)

/-- Predicate: shell `m` is a global peak of a shell profile. -/
def IsGlobalPeak (f : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n : ℕ, f n ≤ f m

/-- Predicate: shell `m` is a global peak for absolute defect magnitude. -/
def IsGlobalAbsPeak (f : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n : ℕ, |f n| ≤ |f m|

/-- Predicate: shell `m` is a peak on the bounded window `{n | n < N}`. -/
def IsWindowPeak (f : ℕ → ℝ) (N m : ℕ) : Prop :=
  ∀ n : ℕ, n < N → f n ≤ f m

/-- Predicate: shell `m` is an absolute-magnitude peak on the window `{n | n < N}`. -/
def IsWindowAbsPeak (f : ℕ → ℝ) (N m : ℕ) : Prop :=
  ∀ n : ℕ, n < N → |f n| ≤ |f m|

theorem isWindowAbsPeak_iff_range (f : ℕ → ℝ) (N m : ℕ) :
    IsWindowAbsPeak f N m ↔
      ∀ n ∈ Finset.range N, |f n| ≤ |f m| := by
  constructor
  · intro h n hn
    exact h n (Finset.mem_range.mp hn)
  · intro h n hn
    exact h n (Finset.mem_range.mpr hn)

theorem isGlobalPeak_implies_isWindowPeak (f : ℕ → ℝ) (m N : ℕ)
    (hglob : IsGlobalPeak f m) : IsWindowPeak f N m := by
  intro n _hn
  exact hglob n

theorem isGlobalAbsPeak_implies_isWindowAbsPeak (f : ℕ → ℝ) (m N : ℕ)
    (hglob : IsGlobalAbsPeak f m) : IsWindowAbsPeak f N m := by
  intro n _hn
  exact hglob n

theorem nextShellDefectCandidate_eq_next_prime_generator
    (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth =
      next_prime_generator x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth := by
  rfl

theorem nextShellDefectValue_eq_profile_eval
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ)
    (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    nextShellDefectValue r observedArea z x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth =
      sliceDefectProfileAtZ r observedArea z
        (next_prime_generator x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth) := by
  rfl

theorem candidate_isWindowAbsPeak_of_hyp
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ)
    (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) (N : ℕ)
    (hpeak :
      ∀ n : ℕ, n < N →
        |sliceDefectProfileAtZ r observedArea z n| ≤
          |sliceDefectProfileAtZ r observedArea z
            (nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth)|) :
    IsWindowAbsPeak (sliceDefectProfileAtZ r observedArea z) N
      (nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth) := by
  intro n hn
  exact hpeak n hn

theorem candidate_isWindowAbsPeak_of_rangeHyp
    (r : ℕ → ℝ) (observedArea : ℕ → ℝ → ℝ) (z : ℝ)
    (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) (N : ℕ)
    (hpeak :
      ∀ n ∈ Finset.range N,
        |sliceDefectProfileAtZ r observedArea z n| ≤
          |sliceDefectProfileAtZ r observedArea z
            (nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth)|) :
    IsWindowAbsPeak (sliceDefectProfileAtZ r observedArea z) N
      (nextShellDefectCandidate x h φ t β_cum phi_t_step δslot fuel threshold hδ hden hth) := by
  intro n hn
  exact hpeak n (Finset.mem_range.mpr hn)

/-!
### Congruence / collapse lemmas
-/

theorem decompose_to_fano_moduli_eq_of_const_phi_t (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (φ₁ φ₂ : ℕ → ℝ) (fuel : ℕ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m) :
    decompose_to_fano_moduli x h φ t β_cum φ₁ fuel hδ hden =
      decompose_to_fano_moduli x h φ t β_cum φ₂ fuel hδ hden := by
  simp [decompose_to_fano_moduli]

theorem decompose_last_shell_eq_of_const_phi_t (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (φ₁ φ₂ : ℕ → ℝ) (fuel : ℕ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m) :
    decompose_last_shell x h φ t β_cum φ₁ fuel hδ hden =
      decompose_last_shell x h φ t β_cum φ₂ fuel hδ hden := by
  dsimp [decompose_last_shell]
  rw [decompose_to_fano_moduli_eq_of_const_phi_t x h φ t β_cum φ₁ φ₂ fuel hδ hden]

theorem spherePackingAtShell_eq_of_const_phi_t (m : ℕ) (δ : ℝ) (hden : RindlerDenDeltaPos δ m) :
    Hqiv.Geometry.spherePackingAtShell m δ hden = Hqiv.Geometry.spherePackingAtShell m δ hden :=
  rfl

theorem rapidity_effect_on_sphere_eq_of_const_slot (m : ℕ) (δ : ℝ) (hden : RindlerDenDeltaPos δ m)
    (hden' : RindlerDenDeltaPos δ (m + 1)) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (φ t : ℝ)
    (hc : ∀ m : ℕ, phi_t_step m = φ) (hδs : ∀ m : ℕ, δslot m = t) :
    rapidity_effect_on_sphere m δ hden hden' phi_t_step δslot =
      rapidity_effect_on_sphere m δ hden hden' (fun _ => φ) (fun _ => t) := by
  simp [rapidity_effect_on_sphere, hc m, hδs m]

theorem next_prime_generator_eq_of_const_phi_t (x : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (φ₁ φ₂ : ℕ → ℝ) (δslot : ℕ → ℝ) (fuel : ℕ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    next_prime_generator x h φ t β_cum φ₁ δslot fuel threshold hδ hden hth =
      next_prime_generator x h φ t β_cum φ₂ δslot fuel threshold hδ hden hth := by
  simp only [next_prime_generator]
  rw [decompose_last_shell_eq_of_const_phi_t x h φ t β_cum φ₁ φ₂ fuel hδ hden]

end

end Hqiv.Physics
