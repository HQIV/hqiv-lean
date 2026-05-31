import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.SurfaceWaveSelfClock
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold

/-!
# Rapidity-modulated lattice zeta on the shell line (ℝ¹ in ℝ⁸ / 𝕆)

This packages a **Dirichlet-style** sum over integer shells `m : ℕ` using the same
`effCorrected` surface as `GlobalDetuning` / `SurfaceWaveSelfClock`, with:

**Interpretation (narrative, not yet a separate Lean structure):** one can read the shell label `m`
as a **composite** of contributions along the seven Fano directions — packaging the discrete
quantum-information content that closes on the null lattice — while the formal development here
still indexes that composite by a **single** `m : ℕ` and only **splits** the sum via residue mod `7`
(Fano vertices). A future formalization might expose an explicit encoding `m ↔` tuple / product along
lines; today `m` is primitive in the types and the seven-way split is **additive** (partition of
the sum), not a uniqueness theorem for “factoring” `m` into line-primes.

* **δ** from `delta_auxiliary_phi_per_shell` (global detuning + `β_cum · φ·t` via `phi_t_cum`);
* **rapidity phase** `φ * t * delta_theta_prime (m : ℝ)` (Maxwell tipping angle; shell-indexed
  surrogate channel `E′ = m` in natural units). **Same exponent as polar scaffold:** see
  `Hqiv.Physics.RapidityZetaPhaseBridge` (`zetaHQIVTerm_eq_effCorrected_mul_cexp_polarAngleFromRapidity`).
* **Fano “primes”**: the seven vertices `FanoVertex = Fin 7` match the modulus in
  `Nat.sumByResidueClasses` — the shell sum **partitions** into seven arithmetic progressions
  (lattice-native analogue of Euler factors; no classical `∏_p (1-p^{-s})^{-1}` claim).

**Design target (not yet formalized):** each Fano **direction** should carry its **own** motivated
shell ladder and its **own** Fano-prime slot (seven independent ℕ tracks or seven distinguished
arithmetic progressions tied to geometry), not only a **single** global shell `m` classified by
`m % 7`. Today we have **one** ladder `m : ℕ` and residue mod `7`; explicit shell numerals in
resonance modules are phenomenological tables (`archive/abandoned/MASS_LADDER_PHENOMENOLOGY.md`) —
**motivated shells per vertex** are still open.

Continuum context: the same shell index feeds `Hqiv.QM.ShellToHarmonicLimit` / mode-ratio bridge.

**Lattice “prime gap”:** `next_lattice_prime` is the **smallest** `m' > current_m` with
`eff(m')/eff(current_m) ≥ threshold` (default `1.5`). Same `effCorrected` as the zeta sum; **not** a
statement about rational primes in `ℤ`, and **not** per-vertex until a per-direction ladder exists.
-/

namespace Hqiv.Physics

open scoped BigOperators Topology
open Complex Filter

noncomputable section

open Classical

variable {φ t β_cum : ℝ}

/-- One-based Fano-line label `1 … 7` for each vertex (`0 … 6` in `Fin 7`).

This names the **vertex / direction**, not a separately derived arithmetic prime per line: the zeta
sum still runs over one global `m` and only **tags** terms by `m % 7`. A future layer should attach
a motivated shell sub-ladder (or prime slot) **per** `FanoVertex`. -/
def fano_prime (f : FanoVertex) : ℕ :=
  f.val + 1

theorem fano_prime_eq_val_add_one (f : FanoVertex) : fano_prime f = f.val + 1 :=
  rfl

theorem fano_prime_pos (f : FanoVertex) : 0 < fano_prime f := by
  simp [fano_prime]

/-- Complex shell term: `eff^{-s}` times the rapidity-modulated phase. -/
noncomputable def zetaHQIVTerm (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s) *
    cexp (I * φ * t * (delta_theta_prime (m : ℝ)))

theorem zetaHQIVTerm_eq (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) :
    zetaHQIVTerm δ φ t s m =
      (effCorrected δ m : ℂ) ^ (-s) * cexp (I * φ * t * delta_theta_prime (m : ℝ)) := by
  simp [zetaHQIVTerm]

/-- Rapidity-modulated zeta sum over all shells (discrete ℝ¹ ladder in the octonionic story). -/
noncomputable def zeta_HQIV (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s m

theorem zeta_HQIV_eq_tsum (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ) :
    zeta_HQIV h φ t β_cum s =
      ∑' m : ℕ, zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s m :=
  rfl

/-!
### Formal Euler-style denominator slot per Fano vertex (single-shell template)

Not claimed equal to `zeta_HQIV`; bookkeeping for the seven-line “prime” labels. Uses shell index
`f.val` only as a **template** — **not** the per-direction motivated shells we ultimately want
(one ladder per Fano direction).
-/

noncomputable def zetaHQIVFormalEulerFactor (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ)
    (f : FanoVertex) : ℂ :=
  (1 : ℂ) - (effCorrected (delta_auxiliary_phi_per_shell h φ t β_cum) (fano_prime f - 1) : ℂ) ^ (-s) *
    cexp (I * φ * t * delta_theta_prime (f.val : ℝ))

theorem zetaHQIVFormalEulerFactor_eq (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ)
    (f : FanoVertex) :
    zetaHQIVFormalEulerFactor h φ t β_cum s f =
      (1 : ℂ) - (effCorrected (delta_auxiliary_phi_per_shell h φ t β_cum) f.val : ℂ) ^ (-s) *
        cexp (I * φ * t * delta_theta_prime (f.val : ℝ)) := by
  simp [zetaHQIVFormalEulerFactor, fano_prime]

/-!
### Seven residue classes mod 7 (Fano vertices ↔ `Fin 7`)
-/

theorem zeta_HQIV_eq_sum_residue_ZMod7 (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ)
    (hf : Summable fun m : ℕ => zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s m) :
    zeta_HQIV h φ t β_cum s =
      ∑ j : ZMod 7, ∑' m : ℕ,
        zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s (j.val + 7 * m) := by
  dsimp [zeta_HQIV]
  exact Nat.sumByResidueClasses hf 7

theorem zeta_HQIV_eq_sum_Fano_residue_classes (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ)
    (hf : Summable fun m : ℕ => zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s m) :
    zeta_HQIV h φ t β_cum s =
      ∑ f : FanoVertex, ∑' k : ℕ,
        zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s (f.val + 7 * k) := by
  classical
  rw [zeta_HQIV_eq_sum_residue_ZMod7 h φ t β_cum s hf]
  rfl

/-!
### Hook to the continuum shell–harmonic ratio (`ContinuumManyBodyQFTScaffold`)

Same discrete shell ladder `m : ℕ` as in `Hqiv.QM.continuum_shell_harmonic_ratio_limit`.
-/

theorem zeta_HQIV_same_shell_axis_as_modeRatio_bridge :
    Hqiv.QM.ShellToHarmonicLimit :=
  Hqiv.QM.shell_to_harmonic_limit_holds

/-!
### Summability for `re s > 1`

`effCorrected δ m / (m+1) → 5` as `m → ∞`, so `‖(eff : ℂ)^{-s}‖` is eventually comparable to
`(m+1)^{-re s}`; phase factors have unit modulus (`norm_exp_I_mul_ofReal`).
-/

theorem norm_zetaHQIVTerm_eq (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) :
    ‖zetaHQIVTerm δ φ t s m‖ = (effCorrected δ m : ℝ) ^ (-s.re) := by
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcpow : ‖(effCorrected δ m : ℂ) ^ (-s)‖ = (effCorrected δ m : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos heff_pos _
  have hphase : ‖cexp (I * φ * t * delta_theta_prime (m : ℝ))‖ = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal (φ * t * delta_theta_prime (m : ℝ))
  simp [zetaHQIVTerm, hcpow, hphase]

theorem tendsto_effCorrected_div_succ (δ : ℝ) :
    Tendsto (fun m : ℕ => effCorrected δ m / (m + 1 : ℝ)) atTop (𝓝 5) := by
  have hform :
      ∀ m : ℕ,
        effCorrected δ m / (m + 1 : ℝ) =
          ((2 : ℝ) + (1 : ℝ) * (m : ℝ)) / ((1 + δ) + (1 / 5) * (m : ℝ)) := by
    intro m
    unfold effCorrected shellSurface rindlerDenWithDelta
    rw [c_rindler_shared_eq_one_fifth]
    field_simp
    ring_nf
  simp_rw [hform]
  simpa using
    tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) (a := 2) (b := 1 + δ) (c := 1) (d := (1 / 5 : ℝ))
      (by norm_num)

theorem eventually_eff_div_succ_gt_four (δ : ℝ) :
    ∀ᶠ m in atTop, (4 : ℝ) < effCorrected δ m / (m + 1 : ℝ) :=
  (tendsto_effCorrected_div_succ δ).eventually (eventually_gt_nhds (by norm_num : (4 : ℝ) < 5))

theorem exists_eff_gt (δ : ℝ) (_hδ : 0 ≤ δ) (C : ℝ) : ∃ m : ℕ, C < effCorrected δ m := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_eff_div_succ_gt_four δ)
  let N : ℕ := max M (Nat.ceil (max C 0 / 4 + 1))
  use N + 1
  have hNM : M ≤ N + 1 :=
    (Nat.le_max_left M _).trans (Nat.le_succ N)
  have h4 : (4 : ℝ) < effCorrected δ (N + 1) / ((N + 1 : ℝ) + 1) := by
    simpa [Nat.cast_add_one, add_assoc, add_comm, add_left_comm] using hM (N + 1) hNM
  have hpos : 0 < ((N + 1 : ℝ) + 1) := by positivity
  rw [lt_div_iff₀ hpos] at h4
  have hceil :
      (max C 0 / 4 + 1 : ℝ) ≤ (Nat.ceil (max C 0 / 4 + 1) : ℝ) := Nat.le_ceil _
  have hNle : (max C 0 / 4 + 1 : ℝ) ≤ (N : ℝ) := by
    have hmax : (Nat.ceil (max C 0 / 4 + 1) : ℝ) ≤ (max M (Nat.ceil (max C 0 / 4 + 1)) : ℝ) := by
      exact_mod_cast Nat.le_max_right _ _
    simpa [N] using hceil.trans hmax
  have hlower : max C 0 < (4 : ℝ) * (((N : ℝ) + 1) + 1) := by
    have h1 : max C 0 < (4 : ℝ) * (max C 0 / 4 + 1) := by
      have h0 : 0 ≤ max C 0 := le_max_right _ _
      nlinarith [h0]
    have h2 : (4 : ℝ) * (max C 0 / 4 + 1) ≤ (4 : ℝ) * ((N : ℝ) + 1 + 1) := by
      gcongr
      nlinarith [hNle]
    linarith [h1, h2]
  calc
    C ≤ max C 0 := le_max_left _ _
    _ < (4 : ℝ) * (((N : ℝ) + 1) + 1) := hlower
    _ < effCorrected δ (N + 1) := h4

/-! ### Lattice-native “next shell” (eff-ratio jump ≥ threshold; default 1.5) -/

theorem exists_next_shell_eff_ratio_ge (current_m : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (_hth : 1 < threshold) :
    ∃ m' : ℕ,
      current_m < m' ∧
        threshold ≤
          effCorrected (delta_auxiliary_phi_per_shell h φ t β_cum) m' /
            effCorrected (delta_auxiliary_phi_per_shell h φ t β_cum) current_m := by
  let δ := delta_auxiliary_phi_per_shell h φ t β_cum
  have heff0 : 0 < effCorrected δ current_m := effCorrected_pos δ current_m hden
  obtain ⟨m₀, hm₀⟩ := exists_eff_gt δ hδ (threshold * effCorrected δ current_m)
  let m' := max (current_m + 1) m₀
  use m'
  constructor
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  · have hm' : m₀ ≤ m' := Nat.le_max_right _ _
    have heff1 : effCorrected δ m₀ ≤ effCorrected δ m' := by
      by_cases hlt : m₀ < m'
      · exact (effCorrected_strictMono_nat hδ hlt).le
      · have hle' : m' ≤ m₀ := Nat.not_lt.mp hlt
        have heq : m₀ = m' := Nat.le_antisymm hm' hle'
        rw [heq]
    have hmul : threshold * effCorrected δ current_m < effCorrected δ m' :=
      lt_of_lt_of_le hm₀ heff1
    rw [le_div_iff₀ heff0]
    exact hmul.le

/-- Predicate for `Nat.find`: first shell after `current_m` with relative eff jump ≥ `threshold`. -/
def effJumpThresholdPred (δ : ℝ) (current_m : ℕ) (threshold : ℝ) (m' : ℕ) : Prop :=
  current_m < m' ∧ threshold ≤ effCorrected δ m' / effCorrected δ current_m

noncomputable instance decidable_effJumpThresholdPred (δ : ℝ) (current_m : ℕ) (threshold : ℝ)
    (m' : ℕ) : Decidable (effJumpThresholdPred δ current_m threshold m') :=
  inferInstance

/-- Smallest `m' > current_m` with `eff(m')/eff(current_m) ≥ threshold` (default `threshold = 1.5`). -/
noncomputable def next_lattice_prime (current_m : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (threshold : ℝ := 1.5)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) : ℕ :=
  Nat.find (exists_next_shell_eff_ratio_ge current_m h φ t β_cum threshold hδ hden hth)

theorem next_lattice_prime_spec (current_m : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (threshold : ℝ) (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    effJumpThresholdPred (delta_auxiliary_phi_per_shell h φ t β_cum) current_m threshold
      (next_lattice_prime current_m h φ t β_cum threshold hδ hden hth) :=
  Nat.find_spec (exists_next_shell_eff_ratio_ge current_m h φ t β_cum threshold hδ hden hth)

theorem next_lattice_prime_gt (current_m : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (threshold : ℝ) (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    current_m < next_lattice_prime current_m h φ t β_cum threshold hδ hden hth :=
  (next_lattice_prime_spec current_m h φ t β_cum threshold hδ hden hth).1

theorem next_lattice_prime_min (current_m : ℕ) (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ)
    (threshold : ℝ) (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) {m' : ℕ}
    (hm : effJumpThresholdPred (delta_auxiliary_phi_per_shell h φ t β_cum) current_m threshold m') :
    next_lattice_prime current_m h φ t β_cum threshold hδ hden hth ≤ m' :=
  Nat.find_min' (exists_next_shell_eff_ratio_ge current_m h φ t β_cum threshold hδ hden hth) hm

/-- Every shell index has a Fano vertex with the same mod-7 residue (same partition as `zeta_HQIV`). -/
theorem exists_fano_vertex_same_residue_mod_seven (m : ℕ) :
    ∃ f : FanoVertex, m % 7 = f.val := by
  refine ⟨⟨m % 7, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simp

/-- One-based Fano line label `1…7` for the shell residue: some vertex has `fano_prime f = (m % 7) + 1`. -/
theorem exists_fano_fano_prime_eq_shell_residue_succ (m : ℕ) :
    ∃ f : FanoVertex, fano_prime f = (m % 7) + 1 := by
  obtain ⟨f, hf⟩ := exists_fano_vertex_same_residue_mod_seven m
  refine ⟨f, ?_⟩
  rw [fano_prime_eq_val_add_one, hf]

theorem eventually_norm_zeta_le_mul_rpow (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    ∀ᶠ m in atTop,
      ‖zetaHQIVTerm δ φ t s m‖ ≤ (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by
  filter_upwards [eventually_eff_div_succ_gt_four δ] with m hm
  have hmpos : (0 : ℝ) < (m + 1 : ℝ) := Nat.cast_add_one_pos m
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcmp : (4 : ℝ) * (m + 1 : ℝ) < effCorrected δ m := by
    rwa [← lt_div_iff₀ hmpos]
  have hneg : (-s.re) < 0 := by linarith only [hs]
  have hlt :
      (effCorrected δ m : ℝ) ^ (-s.re) < (4 * (m + 1 : ℝ)) ^ (-s.re) :=
    Real.rpow_lt_rpow_of_neg (mul_pos (by norm_num) hmpos) hcmp hneg
  rw [norm_zetaHQIVTerm_eq δ φ t s m hden]
  have hsplit :
      (4 * (m + 1 : ℝ)) ^ (-s.re) = (4 : ℝ) ^ (-s.re) * ((m + 1 : ℝ) ^ (-s.re)) := by
    have hm' : (0 : ℝ) ≤ (m : ℝ) + 1 := (Nat.cast_add_one_pos m).le
    simpa using Real.mul_rpow (by norm_num : (0 : ℝ) ≤ (4 : ℝ)) hm'
  have hinv : ((m + 1 : ℝ) ^ (-s.re)) = (1 : ℝ) / ((m + 1 : ℝ) ^ s.re) := by
    have hm' : (0 : ℝ) ≤ (m : ℝ) + 1 := (Nat.cast_add_one_pos m).le
    rw [Real.rpow_neg hm', inv_eq_one_div]
  calc
    (effCorrected δ m : ℝ) ^ (-s.re)
        ≤ (4 * (m + 1 : ℝ)) ^ (-s.re) := hlt.le
    _ = (4 : ℝ) ^ (-s.re) * ((m + 1 : ℝ) ^ (-s.re)) := hsplit
    _ = (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by rw [hinv]

theorem zetaHQIVTerm_summable_of_re_gt_one (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    Summable (zetaHQIVTerm δ φ t s) := by
  have h1 : 1 < s.re := hs
  have hps :
      Summable fun m : ℕ => (1 : ℝ) / ((m + 1 : ℝ) ^ s.re) := by
    have h0 := (Real.summable_one_div_nat_add_rpow (a := (1 : ℝ)) (s := s.re)).mpr h1
    refine Summable.congr h0 ?_
    intro n
    have habs : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
      abs_of_nonneg (Nat.cast_add_one_pos n).le
    simp [div_eq_mul_inv, habs]
  have hg :
      Summable fun m : ℕ => (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) :=
    Summable.mul_left ((4 : ℝ) ^ (-s.re)) hps
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  exact (eventually_norm_zeta_le_mul_rpow δ φ t s hden hs).mono fun m hm => hm

theorem zeta_HQIV_summable_of_re_gt_one (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (s : ℂ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hs : 1 < s.re) :
    Summable fun m : ℕ => zetaHQIVTerm (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s m :=
  zetaHQIVTerm_summable_of_re_gt_one (delta_auxiliary_phi_per_shell h φ t β_cum) φ t s hδ hden hs

end

end Hqiv.Physics
