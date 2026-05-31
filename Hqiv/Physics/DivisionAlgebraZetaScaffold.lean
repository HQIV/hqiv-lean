import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Defs
import Hqiv.Algebra.CycleHodgeProbeScaffold
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.SpatialSliceContinuumBridge
import Hqiv.Geometry.SpatialSliceRapidityScaffold
import Hqiv.Physics.OctonionicZeta

/-!
# Division-algebra zeta **narrative** vs what is proved (ℝ¹ lattice only)

Paper-style tables sometimes align **ℝ, ℂ, ℍ, 𝕆** with different zeta pictures (ordinary primes,
Gaussian primes, Hurwitz/quaternionic analogues, Fano lines / octonionic non-associativity). In this
repository, the **only** analytic object with a full Lean treatment is the **single** discrete shell
line **`m : ℕ`** (ℝ¹ in the HQIV story) with:

* `effCorrected δ m` in the amplitude;
* optional **complex** rapidity phase `cexp (I * φ * t * delta_theta_prime (m : ℝ))` (`zetaHQIVTerm`);
* a **seven-way partition** of the same sum by `m mod 7` (`zeta_HQIV_eq_sum_Fano_residue_classes`), not a
  separate zeta per Cayley–Dickson stage.

**Formalized here**

* `zetaR1_latticeTerm` — the **no-phase** shell term `(eff : ℂ)^{-s}` (“restrict to the real axis” in
  the ℂ amplitude sense).
* `zetaR1_latticeTerm_deltaE` — same amplitude with **full** `φ·t` phase through combinatorial **`δ_E(m)`**
  (`Hqiv.deltaE`); summable for `Re s > 1` (same norm bound as `zetaHQIVTerm`).
* `zetaR1_latticeTerm_deltaESlot` — same with arbitrary per-shell phase slot `δslot : ℕ → ℝ`; **summable for
  every** `δslot` (phase has unit modulus). Matches `zetaR1_latticeTerm_deltaE` when `δslot m = deltaE m`
  or when `Hqiv.Geometry.deltaE_geometricModel R_vol` matches `deltaE` shellwise (explicit hypotheses).
* `fano_vertex_of_shell`, `fanoLineWeight`, `zetaHQIVTerm_fanoWeighted` — explicit **Fano residue** and
  cyclic `l_f ∈ {1,2,3}` scaffold on the shell line.
* `cexp_I_mul_add_three` — ℂ **ordered triple** of phases factors as a single exponential (commutative
  “abelian shadow”; not an octonion product).
* `next_lattice_prime_same_Fano_residue_class` / `next_lattice_prime_fano_vertex_of_shell_val` — the **next
  lattice prime** shell has the mod‑7 residue of `fano_vertex_of_shell` (Fano bookkeeping; not a cyclic
  order theorem on vertices).
* Equality with `zetaHQIVTerm` when `φ = 0` (phase trivial for every `m`), and the same `Summable`
  predicate as the modulated sum under `Re s > 1` for the baseline `zetaR1_latticeTerm`.
* **ℂ / ℚ / 𝕆 bridge (probe):** `criticalLineReHalf`, `rationalTilt`, `norm_zetaR1_latticeTerm_eq_zpow_re_half`,
  `fano_prime_pred_eq_val`, `CriticalLineRationalFanoOctonionProbe`,
  `zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_of_const_rat_tilt` — **no** RH, no rational factorization,
  no octonion-valued Euler product beyond existing `zetaHQIVFormalEulerFactor` bookkeeping.

### Design narrative vs. this file (simply connected Σ³, modular forms)

A **story** compatible with HQIV imagines `φ·t` as a **global** functional (e.g. an integral of an
auxiliary field along null paths through a spatial slice) and `δ_E(m)` as tied to **3-geometry**
(e.g. Ricci curvature integrated over patches). **None of that is in the types here.** In Lean,
`φ` and `t` are plain **real parameters**; `delta_theta_prime` is the **Maxwell tipping** surrogate
(`ModifiedMaxwell`); `Hqiv.deltaE` is the **fixed combinatorial** curvature imprint from
`OctonionicLightCone` — **not** a volume integral `∫ R √g d³x` over a Riemannian patch, and not an
FLRW-only log.

The shell index **`m : ℕ`** is **not** a radial coordinate on a chosen compactification of a
concrete Riemannian 3-manifold — it is the **same discrete ladder** as everywhere else in the zeta
modules. The geometry probe `Hqiv.Geometry.deltaE_geometricModel` is a **numeric formula** in a
user-supplied slot `R_vol m` (narrative: integrated scalar-curvature data); **equality** with
combinatorial `Hqiv.deltaE` is an explicit hypothesis (`∀ m, deltaE_geometricModel R_vol m = deltaE m`),
not a theorem from a 3-metric. Likewise `Hqiv.Geometry.FanoPeriodRapidityCoincidence` packages
`timeAngle φ t = fanoContourPeriodSum …` as **data**, not a consequence of simple connectivity. **Perelman / geometrization**, **holonomy** of `φ` on loops in a spatial slice, and
claims that “zeta becomes a modular form / L-function on Σ³” are **not** formalized; there is
no elliptic curve over a function field of a 3-manifold and no functional equation for a
rapidity-modulated Dirichlet series in this repository.

**`next_lattice_prime`** is **`Nat.find`** on a **ratio threshold** using `effCorrected` — existence
comes from the lemma `exists_next_shell_eff_ratio_ge` in `OctonionicZeta`; **uniqueness** is the
standard **minimal** property of `Nat.find`, **not** a theorem that “positive 3-curvature” forces a
unique jump. Monotonicity of `effCorrected` in `m` (at fixed `δ ≥ 0`) is proved in `GlobalDetuning`
and is **orthogonal** to replacing `deltaE` by Ricci data.

So: the scaffold **supports** the *language* of global rapidity and Fano shells, but **does not**
lift the lattice zeta to modular forms or to metric-dependent `δ_E` without a **large** new
layer (charts, measures, and explicit analytic objects in Mathlib’s sense).

**Not formalized (do not read the module doc as implying these)**

* Classical **Euler products** over rational / Gaussian / Hurwitz “primes” for these sums.
* **Riemann Hypothesis**, critical lines / **hypersurfaces of zeros**, or any **RH-like** statement.
* A separate **quaternionic** or **octonionic** Dirichlet series with **octonion-valued** factors; only
  the ℂ phase **abelianization** `cexp_I_mul_add_three` is proved here.
* Identifying **`φ * t * delta_theta_prime m`** with **`φ * t * δ_E(m)`** (distinct channels: tipping
  angle vs combinatorial curvature `Hqiv.deltaE` in `OctonionicLightCone`).
* **Conserved-content weights `l_f` per Fano line** in the **full** zeta sum: only `l²` appears in
  `ConservedContentMassBridge` / `massScalingAnsatz`; here `fanoLineWeight` / `zetaHQIVTerm_fanoWeighted`
  are explicit **scaffold** factors (cyclic `1,2,3` on vertices), not a uniqueness claim for SM sectors.
* **Factorization** of rational primes into Fano-line moduli.
* **3-manifold** Riemannian metrics, **null geodesic** integrals for `φ·t`, or **Ricci / scalar curvature**
  integrals as replacements for `deltaE` / `delta_auxiliary_phi_per_shell`.
* **Modular forms**, **elliptic curves**, **L-functions**, or a **functional equation** for the HQIV shell
  sums (beyond elementary `Summable` and norm bounds for `Re s > 1`).

For the **proved** mod‑7/Fano bookkeeping, see `OctonionicZeta`; for phenomenological mass tables, see
`archive/abandoned/MASS_LADDER_PHENOMENOLOGY.md`.
-/

namespace Hqiv.Physics

open scoped Topology
open Complex Filter
open Hqiv

noncomputable section

/-- **ℝ¹ lattice term** with curvature-imprint phase `exp(i φ t δ_E(m))` (`Hqiv.deltaE`).

Same amplitude `(effCorrected δ m)^{-s}` as `zetaR1_latticeTerm` / `zetaHQIVTerm`; the phase uses the
combinatorial **δ_E** shell slot from `OctonionicLightCone`, not `delta_theta_prime` (`ModifiedMaxwell`). -/
noncomputable def zetaR1_latticeTerm_deltaE (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s) * cexp (I * φ * t * (deltaE m : ℝ))

/-- Same zeta shell term, but with the quaternionic comparison imprint
`δ_E^H(m) = 6^3 * sqrt(3) * shell_shape(m)` in the phase slot. This is a
comparison candidate, not the canonical HQIV curvature ladder. -/
noncomputable def zetaR1_latticeTerm_deltaE_quaternionicCandidate
    (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s) * cexp (I * φ * t * (deltaE_quaternionicCandidate m : ℝ))

/-- Same amplitude as `zetaR1_latticeTerm_deltaE`, but the phase uses an arbitrary per-shell slot
`δslot : ℕ → ℝ` (e.g. `Hqiv.Geometry.deltaE_geometricModel R_vol` when bridging 3-manifold data). -/
noncomputable def zetaR1_latticeTerm_deltaESlot (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s) * cexp (I * φ * t * (δslot m : ℝ))

/-- **ℝ¹ lattice term** without rapidity phase: `(effCorrected δ m)^{-s}` as a complex power.

Narrative: “real-axis” amplitude on the same ℕ shell ladder as `zetaHQIVTerm`; not `ζ_ℝ(s)` in ℚ. -/
noncomputable def zetaR1_latticeTerm (δ : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s)

theorem zetaR1_latticeTerm_eq (δ : ℝ) (s : ℂ) (m : ℕ) :
    zetaR1_latticeTerm δ s m = (effCorrected δ m : ℂ) ^ (-s) :=
  rfl

theorem zetaR1_latticeTerm_deltaE_eq_zetaR1_of_phi_zero (δ : ℝ) (t : ℝ) (s : ℂ) (m : ℕ) :
    zetaR1_latticeTerm_deltaE δ 0 t s m = zetaR1_latticeTerm δ s m := by
  simp [zetaR1_latticeTerm_deltaE, zetaR1_latticeTerm]

theorem zetaR1_latticeTerm_eq_zetaR1_latticeTerm_deltaE_of_phase_zero (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hphase : φ * t * deltaE m = 0) :
    zetaR1_latticeTerm δ s m = zetaR1_latticeTerm_deltaE δ φ t s m := by
  simp [zetaR1_latticeTerm_deltaE, zetaR1_latticeTerm]
  have h0 : (φ * t * deltaE m : ℂ) = 0 := by exact_mod_cast hphase
  have harg : I * φ * t * (deltaE m : ℝ) = 0 := by
    calc
      I * φ * t * (deltaE m : ℝ) = I * (φ * t * deltaE m : ℂ) := by ring_nf
      _ = I * 0 := by rw [h0]
      _ = 0 := mul_zero _
  simp [harg]

theorem norm_zetaR1_latticeTerm_deltaE_eq (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) :
    ‖zetaR1_latticeTerm_deltaE δ φ t s m‖ = (effCorrected δ m : ℝ) ^ (-s.re) := by
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcpow : ‖(effCorrected δ m : ℂ) ^ (-s)‖ = (effCorrected δ m : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos heff_pos _
  have hphase : ‖cexp (I * φ * t * (deltaE m : ℝ))‖ = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal (φ * t * deltaE m)
  simp [zetaR1_latticeTerm_deltaE, hcpow, hphase]

theorem eventually_norm_zetaR1_deltaE_le_mul_rpow (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    ∀ᶠ m in atTop,
      ‖zetaR1_latticeTerm_deltaE δ φ t s m‖ ≤ (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by
  filter_upwards [eventually_eff_div_succ_gt_four δ] with m hm
  have hmpos : (0 : ℝ) < (m + 1 : ℝ) := Nat.cast_add_one_pos m
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcmp : (4 : ℝ) * (m + 1 : ℝ) < effCorrected δ m := by
    rwa [← lt_div_iff₀ hmpos]
  have hneg : (-s.re) < 0 := by linarith only [hs]
  have hlt :
      (effCorrected δ m : ℝ) ^ (-s.re) < (4 * (m + 1 : ℝ)) ^ (-s.re) :=
    Real.rpow_lt_rpow_of_neg (mul_pos (by norm_num) hmpos) hcmp hneg
  rw [norm_zetaR1_latticeTerm_deltaE_eq δ φ t s m hden]
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

theorem zetaR1_latticeTerm_deltaE_summable_of_re_gt_one (δ : ℝ) (φ t : ℝ) (s : ℂ)
    (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    Summable (zetaR1_latticeTerm_deltaE δ φ t s) := by
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
  exact (eventually_norm_zetaR1_deltaE_le_mul_rpow δ φ t s hden hs).mono fun m hm => hm

theorem zetaR1_latticeTerm_deltaESlot_eq_zetaR1_latticeTerm_deltaE (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ)
    (s : ℂ) (m : ℕ) (h : δslot m = deltaE m) :
    zetaR1_latticeTerm_deltaESlot δ φ t δslot s m = zetaR1_latticeTerm_deltaE δ φ t s m := by
  simp [zetaR1_latticeTerm_deltaESlot, zetaR1_latticeTerm_deltaE, h]

theorem zetaR1_latticeTerm_deltaESlot_eq_deltaE_fun (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) :
    zetaR1_latticeTerm_deltaESlot δ φ t deltaE s m = zetaR1_latticeTerm_deltaE δ φ t s m :=
  rfl

theorem zetaR1_latticeTerm_deltaE_eq_zetaR1_latticeTerm_deltaESlot_geometric (δ : ℝ) (φ t : ℝ)
    (R_vol : Hqiv.Geometry.GeometricScalarCurvatureSlot) (s : ℂ) (m : ℕ)
    (h : Hqiv.Geometry.deltaE_geometricModel R_vol m = deltaE m) :
    zetaR1_latticeTerm_deltaE δ φ t s m =
      zetaR1_latticeTerm_deltaESlot δ φ t (fun k => Hqiv.Geometry.deltaE_geometricModel R_vol k) s m := by
  simp [zetaR1_latticeTerm_deltaE, zetaR1_latticeTerm_deltaESlot, h]

theorem zetaR1_latticeTerm_deltaE_quaternionicCandidate_eq_deltaESlot
    (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) :
    zetaR1_latticeTerm_deltaE_quaternionicCandidate δ φ t s m =
      zetaR1_latticeTerm_deltaESlot δ φ t deltaE_quaternionicCandidate s m := by
  simp [zetaR1_latticeTerm_deltaE_quaternionicCandidate, zetaR1_latticeTerm_deltaESlot]

/-- The quaternionic comparison slot also passes through the geometric-model bridge, but lands on the
quaternionic target rather than the canonical combinatorial `δ_E`. -/
theorem zetaR1_latticeTerm_deltaE_quaternionicCandidate_eq_geometric
    (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ) :
    zetaR1_latticeTerm_deltaE_quaternionicCandidate δ φ t s m =
      zetaR1_latticeTerm_deltaESlot δ φ t
        (fun k =>
          Hqiv.Geometry.deltaE_geometricModel
            (fun j => Hqiv.Geometry.rVolFromGeometricModelTarget deltaE_quaternionicCandidate j) k) s m := by
  simp [zetaR1_latticeTerm_deltaE_quaternionicCandidate, zetaR1_latticeTerm_deltaESlot,
    Hqiv.Geometry.deltaE_geometricModel_rVolFromQuaternionicCandidate_eq]

/-- At the zeta phase-slot level, the quaternionic comparison target is not the canonical HQIV `δ_E`. -/
theorem zetaR1_deltaE_phaseSlot_ne_quaternionicCandidate (m : ℕ) :
    deltaE m ≠ deltaE_quaternionicCandidate m := by
  apply deltaE_ne_deltaE_quaternionicCandidate_of_shell_shape_ne_zero
  have hshape_pos : 0 < shell_shape m := by
    rw [shell_shape_eq_density_succ]
    exact curvatureDensity_pos_succ m
  exact ne_of_gt hshape_pos

/-- The quaternionic geometric slot does not reproduce the canonical `δ_E` at any shell. -/
theorem zetaR1_deltaE_geometricQuaternionicSlot_ne_deltaE (m : ℕ) :
    Hqiv.Geometry.deltaE_geometricModel
        (fun j => Hqiv.Geometry.rVolFromGeometricModelTarget deltaE_quaternionicCandidate j) m ≠
      deltaE m :=
  Hqiv.Geometry.deltaE_geometricModel_rVolFromQuaternionicCandidate_ne_deltaE m

theorem zetaR1_latticeTerm_deltaESlot_eq_zetaR1_of_phi_zero (δ : ℝ) (t : ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (m : ℕ) :
    zetaR1_latticeTerm_deltaESlot δ 0 t δslot s m = zetaR1_latticeTerm δ s m := by
  simp [zetaR1_latticeTerm_deltaESlot, zetaR1_latticeTerm]

theorem zetaHQIVTerm_eq_zetaR1_latticeTerm_deltaESlot_of_phi_zero (δ : ℝ) (t : ℝ) (δslot : ℕ → ℝ)
    (s : ℂ) (m : ℕ) :
    zetaHQIVTerm δ 0 t s m = zetaR1_latticeTerm_deltaESlot δ 0 t δslot s m := by
  simp [zetaHQIVTerm, zetaR1_latticeTerm_deltaESlot]

theorem norm_zetaR1_latticeTerm_deltaESlot_eq (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) :
    ‖zetaR1_latticeTerm_deltaESlot δ φ t δslot s m‖ = (effCorrected δ m : ℝ) ^ (-s.re) := by
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcpow : ‖(effCorrected δ m : ℂ) ^ (-s)‖ = (effCorrected δ m : ℝ) ^ (-s.re) :=
    Complex.norm_cpow_eq_rpow_re_of_pos heff_pos _
  have hphase : ‖cexp (I * φ * t * (δslot m : ℝ))‖ = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal (φ * t * δslot m)
  simp [zetaR1_latticeTerm_deltaESlot, hcpow, hphase]

theorem eventually_norm_zetaR1_deltaESlot_le_mul_rpow (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    ∀ᶠ m in atTop,
      ‖zetaR1_latticeTerm_deltaESlot δ φ t δslot s m‖ ≤ (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by
  filter_upwards [eventually_eff_div_succ_gt_four δ] with m hm
  have hmpos : (0 : ℝ) < (m + 1 : ℝ) := Nat.cast_add_one_pos m
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcmp : (4 : ℝ) * (m + 1 : ℝ) < effCorrected δ m := by
    rwa [← lt_div_iff₀ hmpos]
  have hneg : (-s.re) < 0 := by linarith only [hs]
  have hlt :
      (effCorrected δ m : ℝ) ^ (-s.re) < (4 * (m + 1 : ℝ)) ^ (-s.re) :=
    Real.rpow_lt_rpow_of_neg (mul_pos (by norm_num) hmpos) hcmp hneg
  rw [norm_zetaR1_latticeTerm_deltaESlot_eq δ φ t δslot s m hden]
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

theorem zetaR1_latticeTerm_deltaESlot_summable_of_re_gt_one (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    Summable (zetaR1_latticeTerm_deltaESlot δ φ t δslot s) := by
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
  exact (eventually_norm_zetaR1_deltaESlot_le_mul_rpow δ φ t δslot s hden hs).mono fun m hm => hm

theorem zetaR1_latticeTerm_deltaESlot_summable_of_geometric_matches_combinatorial (δ : ℝ) (φ t : ℝ)
    (R_vol : Hqiv.Geometry.GeometricScalarCurvatureSlot) (s : ℂ)
    (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re)
    (h : ∀ m : ℕ, Hqiv.Geometry.deltaE_geometricModel R_vol m = deltaE m) :
    Summable (zetaR1_latticeTerm_deltaESlot δ φ t (fun k => Hqiv.Geometry.deltaE_geometricModel R_vol k) s) :=
  Summable.congr (zetaR1_latticeTerm_deltaE_summable_of_re_gt_one δ φ t s _hδ hden hs) fun m => by
    simp [zetaR1_latticeTerm_deltaESlot, zetaR1_latticeTerm_deltaE, h]

/-- **Monogamic / step-wise rapidity** generalization:
`φ t` is now a per-shell function `phi_t_step : ℕ → ℝ`.

The curvature slot is an explicit per-shell `δslot : ℕ → ℝ` (e.g. `deltaE_geometricModel R_vol` or `deltaE`).

This is a *direct* lift of the `zetaR1_latticeTerm_deltaESlot` structure to step-wise rapidity. -/
noncomputable def zetaR1_latticeTerm_monogamic3DRamanujanTerm
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  (effCorrected δ m : ℂ) ^ (-s) *
    cexp (I * phi_t_step m * (δslot m : ℝ))

/-- The corresponding *monogamic* “3D Ramanujan” shell sum (discrete `m : ℕ` ladder). -/
noncomputable def zetaR1_monogamic3DRamanujanSum
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m

theorem zetaR1_monogamic3DRamanujanSum_eq_tsum
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ) :
    zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot s =
      ∑' m : ℕ, zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m :=
  rfl

/-- Constant-`φt` shell sum with an arbitrary curvature slot. -/
noncomputable def zetaR1_deltaESlotSum (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, zetaR1_latticeTerm_deltaESlot δ φ t δslot s m

theorem zetaR1_deltaESlotSum_eq_tsum (δ : ℝ) (φ t : ℝ) (δslot : ℕ → ℝ) (s : ℂ) :
    zetaR1_deltaESlotSum δ φ t δslot s = ∑' m : ℕ, zetaR1_latticeTerm_deltaESlot δ φ t δslot s m :=
  rfl

theorem norm_zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) :
    ‖zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m‖ =
      (effCorrected δ m : ℝ) ^ (-s.re) := by
  have heff_pos : 0 < effCorrected δ m := effCorrected_pos δ m (hden m)
  have hcpow : ‖(effCorrected δ m : ℂ) ^ (-s)‖ = (effCorrected δ m : ℝ) ^ (-s.re) := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos heff_pos _
  have hphase :
      ‖cexp (I * phi_t_step m * (δslot m : ℝ))‖ = 1 := by
    -- The exponential factor has unit modulus, so its norm is 1.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Complex.norm_exp_I_mul_ofReal (phi_t_step m * δslot m)
  simp [zetaR1_latticeTerm_monogamic3DRamanujanTerm, hcpow, hphase]

theorem eventually_norm_zetaR1_monogamic3DRamanujanTerm_le_mul_rpow
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    ∀ᶠ m in atTop,
      ‖zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m‖ ≤
        (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by
  -- Reuse the existing eventual bound for the `deltaE` phase:
  -- the phase has unit modulus, so the norm-bound depends only on `effCorrected`.
  refine (eventually_norm_zetaR1_deltaE_le_mul_rpow δ 0 0 s hden hs).mono ?_
  intro m hm
  -- Rewrite the left norm using the monogamic norm lemma, and close by the bound.
  simpa
    [norm_zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq δ phi_t_step δslot s m hden,
      norm_zetaR1_latticeTerm_deltaE_eq δ 0 0 s m hden] using hm

/-- Summability for step-wise rapidity “monogamic 3D Ramanujan” term
when `Re s > 1` and denominators are positive. -/
theorem zetaR1_latticeTerm_monogamic3DRamanujanTerm_summable_of_re_gt_one
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (_hδ : 0 ≤ δ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    Summable (fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m) := by
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
      Summable fun m : ℕ => (4 : ℝ) ^ (-s.re) * (1 / ((m + 1 : ℝ) ^ s.re)) := by
    refine Summable.mul_left ((4 : ℝ) ^ (-s.re)) hps
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  simpa using (eventually_norm_zetaR1_monogamic3DRamanujanTerm_le_mul_rpow δ phi_t_step δslot s hden hs)

theorem zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_zetaR1_latticeTerm_deltaESlot_of_const_phi_t
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ) (m : ℕ)
    (phi_t : ℝ) (hconst : ∀ m : ℕ, phi_t_step m = phi_t) :
    zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m =
      zetaR1_latticeTerm_deltaESlot δ phi_t 1 δslot s m := by
  have hphi : phi_t_step m = phi_t := hconst m
  simp [zetaR1_latticeTerm_monogamic3DRamanujanTerm, zetaR1_latticeTerm_deltaESlot, hphi]

theorem zetaR1_latticeTerm_deltaESlot_eq_of_slot_eq (δ : ℝ) (φ t : ℝ)
    (δslot₁ δslot₂ : ℕ → ℝ) (s : ℂ) (m : ℕ) (hslot : ∀ n : ℕ, δslot₁ n = δslot₂ n) :
    zetaR1_latticeTerm_deltaESlot δ φ t δslot₁ s m =
      zetaR1_latticeTerm_deltaESlot δ φ t δslot₂ s m := by
  simp [zetaR1_latticeTerm_deltaESlot, hslot m]

theorem zetaR1_deltaESlotSum_eq_of_slot_eq (δ : ℝ) (φ t : ℝ)
    (δslot₁ δslot₂ : ℕ → ℝ) (s : ℂ) (hslot : ∀ n : ℕ, δslot₁ n = δslot₂ n) :
    zetaR1_deltaESlotSum δ φ t δslot₁ s = zetaR1_deltaESlotSum δ φ t δslot₂ s := by
  have hfun :
      (fun m : ℕ => zetaR1_latticeTerm_deltaESlot δ φ t δslot₁ s m) =
        (fun m : ℕ => zetaR1_latticeTerm_deltaESlot δ φ t δslot₂ s m) := by
    funext m
    exact zetaR1_latticeTerm_deltaESlot_eq_of_slot_eq δ φ t δslot₁ δslot₂ s m hslot
  simpa [zetaR1_deltaESlotSum] using congrArg (fun f => ∑' m : ℕ, f m) hfun

theorem zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_of_slot_eq
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot₁ δslot₂ : ℕ → ℝ) (s : ℂ) (m : ℕ)
    (hslot : ∀ n : ℕ, δslot₁ n = δslot₂ n) :
    zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot₁ s m =
      zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot₂ s m := by
  simp [zetaR1_latticeTerm_monogamic3DRamanujanTerm, hslot m]

theorem zetaR1_monogamic3DRamanujanSum_eq_of_slot_eq
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot₁ δslot₂ : ℕ → ℝ) (s : ℂ)
    (hslot : ∀ n : ℕ, δslot₁ n = δslot₂ n) :
    zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot₁ s =
      zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot₂ s := by
  have hfun :
      (fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot₁ s m) =
        (fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot₂ s m) := by
    funext m
    exact zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_of_slot_eq δ phi_t_step δslot₁ δslot₂ s m hslot
  simpa [zetaR1_monogamic3DRamanujanSum] using congrArg (fun f => ∑' m : ℕ, f m) hfun

theorem zetaR1_monogamic3DRamanujanSum_eq_zetaR1_deltaESlotSum_of_const_phi_t
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (phi_t : ℝ) (hconst : ∀ m : ℕ, phi_t_step m = phi_t) :
    zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot s =
      zetaR1_deltaESlotSum δ phi_t 1 δslot s := by
  have hfun :
      (fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m) =
        (fun m : ℕ => zetaR1_latticeTerm_deltaESlot δ phi_t 1 δslot s m) := by
    funext m
    exact zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_zetaR1_latticeTerm_deltaESlot_of_const_phi_t
      δ phi_t_step δslot s m phi_t hconst
  simpa [zetaR1_monogamic3DRamanujanSum, zetaR1_deltaESlotSum] using
    congrArg (fun f => ∑' m : ℕ, f m) hfun

theorem zetaR1_monogamic3DRamanujanSum_eq_sum_residue_ZMod7
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (hf : Summable fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m) :
    zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot s =
      ∑ j : ZMod 7, ∑' m : ℕ,
        zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s (j.val + 7 * m) := by
  dsimp [zetaR1_monogamic3DRamanujanSum]
  exact Nat.sumByResidueClasses hf 7

theorem zetaR1_monogamic3DRamanujanSum_eq_sum_Fano_residue_classes
    (δ : ℝ) (phi_t_step : ℕ → ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (hf : Summable fun m : ℕ => zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m) :
    zetaR1_monogamic3DRamanujanSum δ phi_t_step δslot s =
      ∑ f : FanoVertex, ∑' k : ℕ,
        zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s (f.val + 7 * k) := by
  classical
  rw [zetaR1_monogamic3DRamanujanSum_eq_sum_residue_ZMod7 δ phi_t_step δslot s hf]
  rfl

/-- Fano vertex tagging shell `m` (same mod‑7 residue as in `exists_fano_vertex_same_residue_mod_seven`). -/
def fano_vertex_of_shell (m : ℕ) : FanoVertex :=
  ⟨m % 7, Nat.mod_lt m (by decide : 0 < 7)⟩

theorem fano_vertex_of_shell_val (m : ℕ) : (fano_vertex_of_shell m).val = m % 7 :=
  rfl

/-- Cyclic weights `1,2,3` on the seven vertices (scaffold for narrative `l_f`; not SM triple closure). -/
def fanoLineWeight (f : FanoVertex) : ℕ :=
  f.val % 3 + 1

theorem fanoLineWeight_pos (f : FanoVertex) : 0 < fanoLineWeight f := by
  simp [fanoLineWeight]

theorem fanoLineWeight_le_three (f : FanoVertex) : fanoLineWeight f ≤ 3 := by
  simp [fanoLineWeight]
  omega

/-- `l_f` for shell `m` is the cyclic scaffold `(m % 7) % 3 + 1` (bridge to `LatticeNextPrimeGenerator`). -/
theorem fanoLineWeight_fano_vertex_of_shell_eq (m : ℕ) :
    fanoLineWeight (fano_vertex_of_shell m) = (m % 7) % 3 + 1 := by
  simp [fano_vertex_of_shell, fanoLineWeight, Fin.val_mk]

/-- `zetaHQIVTerm` multiplied by the scaffold weight for the shell’s Fano residue class. -/
noncomputable def zetaHQIVTerm_fanoWeighted (δ φ t : ℝ) (s : ℂ) (m : ℕ) : ℂ :=
  zetaHQIVTerm δ φ t s m * (fanoLineWeight (fano_vertex_of_shell m) : ℂ)

/-- ℂ phases along three ordered slots **factor** when summed in the exponent (commutative group). -/
theorem cexp_I_mul_add_three (θ θ' θ'' : ℝ) :
    cexp (I * (θ + θ' + θ'')) = cexp (I * θ) * cexp (I * θ') * cexp (I * θ'') := by
  have hsum : I * (θ + θ' + θ'') = I * θ + (I * θ' + I * θ'') := by ring
  rw [hsum, Complex.exp_add, Complex.exp_add, mul_assoc]

theorem exists_fano_vertex_eq_fano_vertex_of_shell (m : ℕ) :
    ∃ f : FanoVertex, m % 7 = f.val ∧ f = fano_vertex_of_shell m :=
  ⟨fano_vertex_of_shell m, by simp [fano_vertex_of_shell], rfl⟩

theorem next_lattice_prime_same_Fano_residue_class (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ) (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    ∃ f : FanoVertex,
      next_lattice_prime current_m h φ t β_cum threshold hδ hden hth % 7 = f.val :=
  exists_fano_vertex_same_residue_mod_seven (next_lattice_prime current_m h φ t β_cum threshold hδ hden hth)

/-- Canonical Fano tag for the **next lattice prime** shell (same mod‑7 residue). -/
theorem next_lattice_prime_fano_vertex_of_shell_val (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ) (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    (fano_vertex_of_shell (next_lattice_prime current_m h φ t β_cum threshold hδ hden hth)).val =
      next_lattice_prime current_m h φ t β_cum threshold hδ hden hth % 7 :=
  fano_vertex_of_shell_val _

/-!
### Haugen-prime lift base layer (naming alias + iterates)

`haugenPrimeLift` is a transparent alias for `next_lattice_prime`, used to keep roadmap/narrative
wording local while preserving the exact Lean semantics from `OctonionicZeta`.
-/

/-- One Haugen-prime lift step: same object as `next_lattice_prime`. -/
noncomputable def haugenPrimeLift (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) : ℕ :=
  next_lattice_prime current_m h φ t β_cum threshold hδ hden hth

theorem haugenPrimeLift_eq_next_lattice_prime (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    haugenPrimeLift current_m h φ t β_cum threshold hδ hden hth =
      next_lattice_prime current_m h φ t β_cum threshold hδ hden hth := by
  rfl

theorem haugenPrimeLift_gt (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    current_m < haugenPrimeLift current_m h φ t β_cum threshold hδ hden hth := by
  simpa [haugenPrimeLift] using
    next_lattice_prime_gt current_m h φ t β_cum threshold hδ hden hth

theorem haugenPrimeLift_fano_vertex_val (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    (fano_vertex_of_shell (haugenPrimeLift current_m h φ t β_cum threshold hδ hden hth)).val =
      haugenPrimeLift current_m h φ t β_cum threshold hδ hden hth % 7 := by
  simpa [haugenPrimeLift] using
    next_lattice_prime_fano_vertex_of_shell_val current_m h φ t β_cum threshold hδ hden hth

/-- Iterate Haugen-prime lift `k` times from `start_m` (uses global positivity witness `hdenAll`). -/
noncomputable def haugenPrimeLiftIter (k start_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hdenAll : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) : ℕ :=
  Nat.rec start_m
    (fun _ acc => haugenPrimeLift acc h φ t β_cum threshold hδ (hdenAll acc) hth)
    k

@[simp]
theorem haugenPrimeLiftIter_zero (start_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hdenAll : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    haugenPrimeLiftIter 0 start_m h φ t β_cum threshold hδ hdenAll hth = start_m := by
  rfl

@[simp]
theorem haugenPrimeLiftIter_succ (k start_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hdenAll : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    haugenPrimeLiftIter (k + 1) start_m h φ t β_cum threshold hδ hdenAll hth =
      haugenPrimeLift (haugenPrimeLiftIter k start_m h φ t β_cum threshold hδ hdenAll hth)
        h φ t β_cum threshold hδ
        (hdenAll (haugenPrimeLiftIter k start_m h φ t β_cum threshold hδ hdenAll hth)) hth := by
  rfl

theorem haugenPrimeLiftIter_strict_step (k start_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hdenAll : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) m)
    (hth : 1 < threshold) :
    haugenPrimeLiftIter k start_m h φ t β_cum threshold hδ hdenAll hth <
      haugenPrimeLiftIter (k + 1) start_m h φ t β_cum threshold hδ hdenAll hth := by
  rw [haugenPrimeLiftIter_succ]
  exact haugenPrimeLift_gt
    (haugenPrimeLiftIter k start_m h φ t β_cum threshold hδ hdenAll hth)
    h φ t β_cum threshold hδ
    (hdenAll (haugenPrimeLiftIter k start_m h φ t β_cum threshold hδ hdenAll hth))
    hth

theorem zetaR1_latticeTerm_eq_zetaHQIVTerm_of_phi_zero (δ : ℝ) (t : ℝ) (s : ℂ) (m : ℕ) :
    zetaHQIVTerm δ 0 t s m = zetaR1_latticeTerm δ s m := by
  simp [zetaHQIVTerm, zetaR1_latticeTerm]

theorem zetaR1_latticeTerm_eq_zetaHQIVTerm_of_phase_zero (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hphase : φ * t * delta_theta_prime (m : ℝ) = 0) :
    zetaR1_latticeTerm δ s m = zetaHQIVTerm δ φ t s m := by
  simp [zetaHQIVTerm, zetaR1_latticeTerm]
  have h0 : (φ * t * delta_theta_prime (m : ℝ) : ℂ) = 0 := by exact_mod_cast hphase
  have harg : I * φ * t * delta_theta_prime (m : ℝ) = 0 := by
    calc
      I * φ * t * delta_theta_prime (m : ℝ) = I * (φ * t * delta_theta_prime (m : ℝ) : ℂ) := by ring_nf
      _ = I * 0 := by rw [h0]
      _ = 0 := mul_zero _
  simp [harg]

theorem norm_zetaR1_latticeTerm_eq (δ : ℝ) (s : ℂ) (m : ℕ) (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) :
    ‖zetaR1_latticeTerm δ s m‖ = (effCorrected δ m : ℝ) ^ (-s.re) := by
  simpa [← zetaR1_latticeTerm_eq_zetaHQIVTerm_of_phi_zero δ 0 s m] using
    norm_zetaHQIVTerm_eq δ (0 : ℝ) (0 : ℝ) s m hden

theorem zetaR1_latticeTerm_summable_of_re_gt_one (δ : ℝ) (s : ℂ) (_hδ : 0 ≤ δ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : 1 < s.re) :
    Summable (zetaR1_latticeTerm δ s) := by
  refine Summable.congr (zetaHQIVTerm_summable_of_re_gt_one δ (0 : ℝ) (0 : ℝ) s _hδ hden hs) ?_
  intro m
  exact zetaR1_latticeTerm_eq_zetaHQIVTerm_of_phi_zero δ 0 s m

/-- Full **phase-off** shell sum uses the same δ-auxiliary slot as `zeta_HQIV` but `φ = 0`. -/
noncomputable def zeta_R1_HQIV (h : GlobalDetuningHypothesis) (t β_cum : ℝ) (s : ℂ) : ℂ :=
  ∑' m : ℕ, zetaR1_latticeTerm (delta_auxiliary_phi_per_shell h 0 t β_cum) s m

theorem zeta_R1_HQIV_eq_tsum (h : GlobalDetuningHypothesis) (t β_cum : ℝ) (s : ℂ) :
    zeta_R1_HQIV h t β_cum s =
      ∑' m : ℕ, zetaR1_latticeTerm (delta_auxiliary_phi_per_shell h 0 t β_cum) s m :=
  rfl

theorem zeta_HQIV_eq_zeta_R1_HQIV_of_phi_zero (h : GlobalDetuningHypothesis) (t β_cum : ℝ) (s : ℂ)
    (_hf :
      Summable fun m : ℕ =>
        zetaHQIVTerm (delta_auxiliary_phi_per_shell h 0 t β_cum) 0 t s m) :
    zeta_HQIV h 0 t β_cum s = zeta_R1_HQIV h t β_cum s := by
  dsimp [zeta_HQIV, zeta_R1_HQIV]
  congr 1
  ext m
  exact zetaR1_latticeTerm_eq_zetaHQIVTerm_of_phi_zero _ _ _ _

theorem zeta_R1_HQIV_summable_of_re_gt_one (h : GlobalDetuningHypothesis) (t β_cum : ℝ) (s : ℂ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h 0 t β_cum)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h 0 t β_cum) m)
    (hs : 1 < s.re) :
    Summable fun m : ℕ => zetaR1_latticeTerm (delta_auxiliary_phi_per_shell h 0 t β_cum) s m :=
  zetaR1_latticeTerm_summable_of_re_gt_one (delta_auxiliary_phi_per_shell h 0 t β_cum) s hδ hden hs

/-- Same `m % 7` constructor as `Hqiv.Algebra.shellResidueFano` (algebra cycle probe). -/
theorem fano_vertex_of_shell_eq_algebra_shellResidueFano (m : ℕ) :
    fano_vertex_of_shell m = Hqiv.Algebra.shellResidueFano m :=
  rfl

/-- Each strand `f.val + 7·k` of the Fano residue partition carries vertex tag `f`
    (algebra cycles ↔ zeta summation index). -/
theorem fano_vertex_of_shell_f_val_add_seven_mul (f : FanoVertex) (k : ℕ) :
    fano_vertex_of_shell (f.val + 7 * k) = f := by
  rw [fano_vertex_of_shell_eq_algebra_shellResidueFano, Hqiv.Algebra.shellResidueFano_of_f_val_add_seven_mul]

/-!
### Temperature-ladder boundary scaffold (HQIV analogue, probe-level)

This section encodes the “boundary lock” intuition as explicit **HQIV hypotheses** and a
separate analogue parameter `lambdaHQIV` (not the classical de Bruijn–Newman constant).
-/

/-- Conserved-ladder baseline `T_ref/(m+1)` on shells. -/
noncomputable def tempLadderConserved (T_ref : ℝ) (m : ℕ) : ℝ :=
  T_ref / (m + 1 : ℝ)

/-- Dimensionless reciprocal shell coordinate `t = 1/(m+1)` (same shell index `m : ℕ`).

Then `tempLadderConserved T_ref m = T_ref * t` — conserved temperature is reference scale times `t`. -/
noncomputable def shellReciprocalCoord (m : ℕ) : ℝ :=
  (1 : ℝ) / (m + 1 : ℝ)

theorem tempLadderConserved_eq_T_ref_mul_shellReciprocalCoord (T_ref : ℝ) (m : ℕ) :
    tempLadderConserved T_ref m = T_ref * shellReciprocalCoord m := by
  simp [tempLadderConserved, shellReciprocalCoord, div_eq_mul_inv]

/-- `t = 1/(m+1)` is positive for every shell. -/
theorem shellReciprocalCoord_pos (m : ℕ) : 0 < shellReciprocalCoord m := by
  simp [shellReciprocalCoord]
  positivity

/-- Regularized variant corresponding to the shifted denominator (`m-1` style for `m≥1`). -/
noncomputable def tempLadderRegularized (T_ref : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then T_ref else T_ref / (m : ℝ)

/-- Effective HQIV heat-flow surrogate from shell index and conserved reference temperature. -/
noncomputable def tHQIV (T_ref : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0 else (m : ℝ) / T_ref

theorem tempLadderConserved_pos {T_ref : ℝ} (hT : 0 < T_ref) (m : ℕ) :
    0 < tempLadderConserved T_ref m := by
  dsimp [tempLadderConserved]
  exact div_pos hT (by positivity)

theorem tempLadderRegularized_zero (T_ref : ℝ) :
    tempLadderRegularized T_ref 0 = T_ref := by
  simp [tempLadderRegularized]

theorem tHQIV_zero (T_ref : ℝ) : tHQIV T_ref 0 = 0 := by
  simp [tHQIV]

theorem tHQIV_succ (T_ref : ℝ) (m : ℕ) :
    tHQIV T_ref (m + 1) = (m + 1 : ℝ) / T_ref := by
  simp [tHQIV]

/-- Hypothesis bundle for “temperature ladder forces boundary lock” in HQIV analogue form. -/
structure TempLadderBoundaryData where
  T_ref : ℝ
  shellWeight : ℕ → ℝ
  deltaEslot : ℕ → ℝ
  phi_t_from_ladder : ℕ → ℝ
  /-- Redistribution (not dissipation) hypothesis is carried as explicit data. -/
  conservedRedistribution : Prop
  /-- Explicit regularization guard near the horizon shell. -/
  regularizedBoundary : Prop

/-- Probe-level statement: under explicit HQIV ladder hypotheses, analogue boundary parameter is zero. -/
structure TempLadderForcesLambdaHQIVZero where
  data : TempLadderBoundaryData
  lambdaHQIV : ℝ
  lambdaHQIV_nonneg : 0 ≤ lambdaHQIV
  lambdaHQIV_eq_zero :
    data.conservedRedistribution → data.regularizedBoundary → lambdaHQIV = 0

theorem lambdaHQIV_eq_zero_of_boundary_hyp (B : TempLadderForcesLambdaHQIVZero) :
    B.data.conservedRedistribution → B.data.regularizedBoundary → B.lambdaHQIV = 0 :=
  B.lambdaHQIV_eq_zero

theorem lambdaHQIV_eq_zero_of_all_hyp (B : TempLadderForcesLambdaHQIVZero)
    (hcons : B.data.conservedRedistribution) (hreg : B.data.regularizedBoundary) :
    B.lambdaHQIV = 0 :=
  B.lambdaHQIV_eq_zero hcons hreg

/-- Finite-window witness package for practical checks before asymptotic upgrades. -/
structure TempLadderFiniteWindowWitness where
  N : ℕ
  T_ref : ℝ
  shellWeight : ℕ → ℝ
  deltaEslot : ℕ → ℝ
  phi_t_from_ladder : ℕ → ℝ
  /-- Verified conservation relation on `Finset.range N` (placeholder form, user-specified). -/
  conservedOnRange : Prop
  /-- Verified regularization relation on the same finite window. -/
  regularizedOnRange : Prop

/-- Convert a finite-window witness into boundary data (keeps assumptions explicit as `Prop` fields). -/
def TempLadderFiniteWindowWitness.toBoundaryData (W : TempLadderFiniteWindowWitness) :
    TempLadderBoundaryData where
  T_ref := W.T_ref
  shellWeight := W.shellWeight
  deltaEslot := W.deltaEslot
  phi_t_from_ladder := W.phi_t_from_ladder
  conservedRedistribution := W.conservedOnRange
  regularizedBoundary := W.regularizedOnRange

/-- Canonical probe instance from a finite-window witness: choose `lambdaHQIV = 0` by construction. -/
def TempLadderFiniteWindowWitness.toLambdaHQIVZero
    (W : TempLadderFiniteWindowWitness) : TempLadderForcesLambdaHQIVZero where
  data := W.toBoundaryData
  lambdaHQIV := 0
  lambdaHQIV_nonneg := by positivity
  lambdaHQIV_eq_zero := by
    intro _hcons _hreg
    rfl

@[simp]
theorem TempLadderFiniteWindowWitness.toLambdaHQIVZero_lambda (W : TempLadderFiniteWindowWitness) :
    (W.toLambdaHQIVZero).lambdaHQIV = 0 :=
  rfl

theorem lambdaHQIV_eq_zero_of_finiteWindowWitness (W : TempLadderFiniteWindowWitness) :
    (W.toLambdaHQIVZero).lambdaHQIV = 0 := by
  exact W.toLambdaHQIVZero_lambda

/-- Concrete finite-window witness with explicit `Finset.range N` equalities. -/
structure TempLadderFiniteWindowConcrete where
  N : ℕ
  T_ref : ℝ
  shellWeight : ℕ → ℝ
  deltaEslot : ℕ → ℝ
  phi_t_from_ladder : ℕ → ℝ
  hT_nonzero : T_ref ≠ 0
  /-- Explicit finite-window conservation equation (redistribution, not dissipation). -/
  conservedEq :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * shellWeight m) = T_ref
  /-- Explicit regularization anchor at shell `0`. -/
  regularizedEq0 : tempLadderRegularized T_ref 0 = T_ref
  /-- Explicit phase-lock relation on the finite window. -/
  phaseLockEq :
    ∀ m, m < N → phi_t_from_ladder m = (m : ℝ) * deltaEslot m / T_ref

/-- Forgetful map from concrete equalities to the abstract finite-window witness record. -/
def TempLadderFiniteWindowConcrete.toFiniteWindowWitness
    (W : TempLadderFiniteWindowConcrete) : TempLadderFiniteWindowWitness where
  N := W.N
  T_ref := W.T_ref
  shellWeight := W.shellWeight
  deltaEslot := W.deltaEslot
  phi_t_from_ladder := W.phi_t_from_ladder
  conservedOnRange :=
    Finset.sum (Finset.range W.N) (fun m => tempLadderConserved W.T_ref m * W.shellWeight m) = W.T_ref
  regularizedOnRange := tempLadderRegularized W.T_ref 0 = W.T_ref

theorem TempLadderFiniteWindowConcrete.toFiniteWindowWitness_conserved
    (W : TempLadderFiniteWindowConcrete) :
    W.toFiniteWindowWitness.conservedOnRange := by
  simpa [TempLadderFiniteWindowConcrete.toFiniteWindowWitness] using W.conservedEq

theorem TempLadderFiniteWindowConcrete.toFiniteWindowWitness_regularized
    (W : TempLadderFiniteWindowConcrete) :
    W.toFiniteWindowWitness.regularizedOnRange := by
  simpa [TempLadderFiniteWindowConcrete.toFiniteWindowWitness] using W.regularizedEq0

/-- Concrete finite-window witness yields a canonical `lambdaHQIV = 0` probe instance. -/
def TempLadderFiniteWindowConcrete.toLambdaHQIVZero
    (W : TempLadderFiniteWindowConcrete) : TempLadderForcesLambdaHQIVZero :=
  W.toFiniteWindowWitness.toLambdaHQIVZero

theorem lambdaHQIV_eq_zero_of_finiteWindowConcrete (W : TempLadderFiniteWindowConcrete) :
    (W.toLambdaHQIVZero).lambdaHQIV = 0 := by
  rfl

/-- Normalizer for dimension-indexed shell weights (`p = dim - 1`). -/
noncomputable def dimWeightNormalizer (p N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun m => ((m + 1 : ℝ) ^ p))

/-- Dimension-indexed shell weight template (`p = dim - 1`). -/
noncomputable def dimShellWeight (p N : ℕ) (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) ^ (p + 1)) / dimWeightNormalizer p N

/-- Stars-and-bars shell combinatorics in dimension `dim`: number of weak compositions of `m` into
`dim` nonnegative parts (`Nat.choose`).

**Not an extra “axiom”.** This is standard combinatorics. In the HQIV story, **curvature / shell
multiplicity** is read as **additional** discrete degrees **per unit shell step** (marginal new
configurations when `m ↦ m + 1`), not the cumulative total “everything inside a Euclidean disk of
radius `m`” (Gauss-circle scaling). The ladder indexes that **incremental** combinatorics — **not** a
new physical postulate beyond the framework.

* **ℝ³:** bridge to `Hqiv.latticeSimplexCount` is `shellCombinatoricWays_R3_eq_half_latticeSimplexCount`
  (integer points in the standard 3-part simplex model; same stars-and-bars as `x + y + z = m`).
* **ℝ² / one complex dimension (ℂ):** `shellCombinatoricWays_R2 m = m + 1` — two-part weak compositions,
  i.e. integer points on `x + y = m` with `x, y ≥ 0` (the discrete “radius‑`m`” line segment in the
  quadrant). Continuum “disk / ball” geometry (horizontal slices, `π`-baseline) lives in
  `Hqiv.Geometry.EuclideanBallHorizontalSlice`; **discrete** ball/simplex counts here use this
  combinatorics (different norm than Gauss’s Euclidean circle problem unless you specialize further).

See also `Hqiv.latticeSimplexCount` in `OctonionicLightCone`. -/
def shellCombinatoricWays (dim m : ℕ) : ℕ :=
  Nat.choose (m + dim - 1) (dim - 1)

/-- Named constructors for key dimensions. -/
def shellCombinatoricWays_R1 (m : ℕ) : ℕ := shellCombinatoricWays 1 m
def shellCombinatoricWays_R2 (m : ℕ) : ℕ := shellCombinatoricWays 2 m
def shellCombinatoricWays_R3 (m : ℕ) : ℕ := shellCombinatoricWays 3 m
def shellCombinatoricWays_R4 (m : ℕ) : ℕ := shellCombinatoricWays 4 m
def shellCombinatoricWays_R8 (m : ℕ) : ℕ := shellCombinatoricWays 8 m

@[simp] theorem shellCombinatoricWays_R1_eq (m : ℕ) :
    shellCombinatoricWays_R1 m = 1 := by
  simp [shellCombinatoricWays_R1, shellCombinatoricWays]

@[simp] theorem shellCombinatoricWays_R2_eq (m : ℕ) :
    shellCombinatoricWays_R2 m = m + 1 := by
  simp [shellCombinatoricWays_R2, shellCombinatoricWays]

/-- `R3` stars-and-bars count is the half-numerator `(m+2)(m+1)/2`. -/
theorem shellCombinatoricWays_R3_eq_half_latticeSimplexCount (m : ℕ) :
    2 * shellCombinatoricWays_R3 m = Hqiv.latticeSimplexCount m := by
  let n := m + 2
  have hdvd : 2 ∣ n * (n - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self n)
  have hcancel : (n * (n - 1)) / 2 * 2 = n * (n - 1) := by
    exact Nat.div_mul_cancel hdvd
  calc
    2 * shellCombinatoricWays_R3 m
        = shellCombinatoricWays_R3 m * 2 := by ring
    _ = (n * (n - 1)) / 2 * 2 := by
      simp [shellCombinatoricWays_R3, shellCombinatoricWays, n, Nat.choose_two_right]
    _ = n * (n - 1) := hcancel
    _ = Hqiv.latticeSimplexCount m := by
      simp [Hqiv.latticeSimplexCount, n]

/-- Real-cast versions of combinatoric constructors (convenient for analytic slots). -/
noncomputable def shellCombinatoricWaysReal (dim : ℕ) (m : ℕ) : ℝ :=
  (shellCombinatoricWays dim m : ℝ)

noncomputable def shellCombinatoricWaysReal_R1 (m : ℕ) : ℝ := shellCombinatoricWaysReal 1 m
noncomputable def shellCombinatoricWaysReal_R2 (m : ℕ) : ℝ := shellCombinatoricWaysReal 2 m
noncomputable def shellCombinatoricWaysReal_R3 (m : ℕ) : ℝ := shellCombinatoricWaysReal 3 m
noncomputable def shellCombinatoricWaysReal_R4 (m : ℕ) : ℝ := shellCombinatoricWaysReal 4 m
noncomputable def shellCombinatoricWaysReal_R8 (m : ℕ) : ℝ := shellCombinatoricWaysReal 8 m

@[simp] theorem shellCombinatoricWaysReal_R1_eq (m : ℕ) :
    shellCombinatoricWaysReal_R1 m = 1 := by
  simp [shellCombinatoricWaysReal_R1, shellCombinatoricWaysReal, shellCombinatoricWays]

@[simp] theorem shellCombinatoricWaysReal_R2_eq (m : ℕ) :
    shellCombinatoricWaysReal_R2 m = (m + 1 : ℝ) := by
  simp [shellCombinatoricWaysReal_R2, shellCombinatoricWaysReal, shellCombinatoricWays_R2,
    shellCombinatoricWays, Nat.choose_one_right]

/-- Candidate-count between current shell and one Haugen-prime lift step. -/
noncomputable def haugenPrimeStepCandidateCount (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) : ℕ :=
  haugenPrimeLift current_m h φ t β_cum threshold hδ hden hth - current_m

theorem haugenPrimeStepCandidateCount_pos (current_m : ℕ) (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) (threshold : ℝ)
    (hδ : 0 ≤ delta_auxiliary_phi_per_shell h φ t β_cum)
    (hden : RindlerDenDeltaPos (delta_auxiliary_phi_per_shell h φ t β_cum) current_m)
    (hth : 1 < threshold) :
    0 < haugenPrimeStepCandidateCount current_m h φ t β_cum threshold hδ hden hth := by
  dsimp [haugenPrimeStepCandidateCount]
  exact Nat.sub_pos_of_lt (haugenPrimeLift_gt current_m h φ t β_cum threshold hδ hden hth)

theorem tempLadderConserved_dimShellWeight (T_ref : ℝ) (p N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight p N m) = T_ref := by
  let Z := dimWeightNormalizer p N
  have hZpos : 0 < Z := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN) with ⟨N', rfl⟩
    have hsum_nonneg : 0 ≤ Finset.sum (Finset.range N') (fun m => ((m + 1 : ℝ) ^ p)) := by
      exact Finset.sum_nonneg (by intro m hm; positivity)
    have hterm_pos : 0 < ((N' + 1 : ℕ) : ℝ) ^ p := by positivity
    have hpos :
        0 < Finset.sum (Finset.range N') (fun m => ((m + 1 : ℝ) ^ p)) +
          (((N' + 1 : ℕ) : ℝ) ^ p) := by
      linarith
    simpa [Z, dimWeightNormalizer, Finset.sum_range_succ] using hpos
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  calc
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight p N m)
        = Finset.sum (Finset.range N) (fun m => T_ref * (((m + 1 : ℝ) ^ p) / Z)) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      dsimp [tempLadderConserved, dimShellWeight, Z, dimWeightNormalizer]
      have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hm1]
      ring
    _ = T_ref * Finset.sum (Finset.range N) (fun m => (((m + 1 : ℝ) ^ p) / Z)) := by
      simp [Finset.mul_sum]
    _ = T_ref * ((Finset.sum (Finset.range N) (fun m => ((m + 1 : ℝ) ^ p))) / Z) := by
      simp [Finset.sum_div]
    _ = T_ref * (Z / Z) := by simp [Z, dimWeightNormalizer]
    _ = T_ref := by field_simp [hZne]

theorem tempLadderConserved_dimShellWeight_R1 (T_ref : ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight 0 N m) = T_ref :=
  tempLadderConserved_dimShellWeight T_ref 0 N hN

theorem tempLadderConserved_dimShellWeight_R2 (T_ref : ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight 1 N m) = T_ref :=
  tempLadderConserved_dimShellWeight T_ref 1 N hN

theorem tempLadderConserved_dimShellWeight_R3 (T_ref : ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight 2 N m) = T_ref :=
  tempLadderConserved_dimShellWeight T_ref 2 N hN

theorem tempLadderConserved_dimShellWeight_R4 (T_ref : ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight 3 N m) = T_ref :=
  tempLadderConserved_dimShellWeight T_ref 3 N hN

theorem tempLadderConserved_dimShellWeight_R8 (T_ref : ℝ) (N : ℕ) (hN : 0 < N) :
    Finset.sum (Finset.range N) (fun m => tempLadderConserved T_ref m * dimShellWeight 7 N m) = T_ref :=
  tempLadderConserved_dimShellWeight T_ref 7 N hN

/-- Canonical concrete witness in dimension template `p = dim - 1` from explicit phase-lock data. -/
noncomputable def mkTempLadderFiniteWindowConcrete_dim
    (p N : ℕ) (T_ref : ℝ) (deltaEslot phi_t_from_ladder : ℕ → ℝ)
    (hT : T_ref ≠ 0) (hN : 0 < N)
    (hphase : ∀ m, m < N → phi_t_from_ladder m = (m : ℝ) * deltaEslot m / T_ref) :
    TempLadderFiniteWindowConcrete where
  N := N
  T_ref := T_ref
  shellWeight := dimShellWeight p N
  deltaEslot := deltaEslot
  phi_t_from_ladder := phi_t_from_ladder
  hT_nonzero := hT
  conservedEq := tempLadderConserved_dimShellWeight T_ref p N hN
  regularizedEq0 := tempLadderRegularized_zero T_ref
  phaseLockEq := hphase

/-!
### ℂ critical line ↔ ℚ tilt ↔ 𝕆 Fano-line index (probe only)

* **ℂ:** Classical RH language uses \(\Re(s)=\tfrac12\); `criticalLineReHalf` is that subset. The lattice
  amplitude `‖(eff)^{-s}‖` depends only on `s.re` (`norm_zetaR1_latticeTerm_eq`), so on the critical line
  the decay exponent is exactly `-(1/2)` (`norm_zetaR1_latticeTerm_eq_zpow_re_half`).
* **ℚ:** `rationalTilt` embeds rationals into ℝ as a **tilt** surrogate (e.g. rational rapidity steps in
  monogamic sums when you assume `∀ m, phi_t_step m = rationalTilt q`).
* **𝕆 / Fano:** `fano_prime` labels the seven lines; `fano_prime_pred_eq_val` is the shell index used in
  `zetaHQIVFormalEulerFactor` (`OctonionicZeta`). No claim that zeros of any HQIV sum lie on
  `criticalLineReHalf` or correlate with `qtilt` or `f`.
-/

/-- Classical RH **critical line** \(\Re z = 1/2\) as a subset of ℂ (no zeros proved here). -/
def criticalLineReHalf : Set ℂ :=
  { z | z.re = (1 / 2 : ℝ) }

@[simp]
theorem mem_criticalLineReHalf_iff (z : ℂ) : z ∈ criticalLineReHalf ↔ z.re = (1 / 2 : ℝ) :=
  Iff.rfl

/-- Embed `ℚ` into ℝ for rational **tilt** bookkeeping (no Diophantine or RH claim). -/
noncomputable def rationalTilt (q : ℚ) : ℝ :=
  (q : ℝ)

/-- On \(\Re(s)=1/2\), the ℝ¹ lattice term norm is `eff^{-1/2}` (specialization of `norm_zetaR1_latticeTerm_eq`). -/
theorem norm_zetaR1_latticeTerm_eq_zpow_re_half (δ : ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : s.re = (1 / 2 : ℝ)) :
    ‖zetaR1_latticeTerm δ s m‖ = (effCorrected δ m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_zetaR1_latticeTerm_eq δ s m hden, hs]

/-- Same decay exponent on the critical line when the `δ_E` phase is active (phase still unit modulus). -/
theorem norm_zetaR1_latticeTerm_deltaE_eq_zpow_re_half (δ : ℝ) (φ t : ℝ) (s : ℂ) (m : ℕ)
    (hden : ∀ m : ℕ, RindlerDenDeltaPos δ m) (hs : s.re = (1 / 2 : ℝ)) :
    ‖zetaR1_latticeTerm_deltaE δ φ t s m‖ = (effCorrected δ m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_zetaR1_latticeTerm_deltaE_eq δ φ t s m hden, hs]

/-- `zetaHQIVFormalEulerFactor` uses shell index `fano_prime f - 1`, i.e. `f.val` (`OctonionicZeta`). -/
theorem fano_prime_pred_eq_val (f : FanoVertex) : fano_prime f - 1 = f.val := by
  rw [fano_prime_eq_val_add_one, Nat.succ_sub_one]

/-- Agent-facing bundle: ℂ critical-line point + ℚ tilt + 𝕆 Fano vertex (no analytic bridge theorem). -/
structure CriticalLineRationalFanoOctonionProbe where
  /-- Point in ℂ with \(\Re = 1/2\) (RH literature). -/
  s : ℂ
  /-- Rational tilt, embedded by `rationalTilt` when used as a real surrogate. -/
  qtilt : ℚ
  /-- Octonionic Fano-line tag (`Fin 7`). -/
  f : FanoVertex
  /-- Membership in `criticalLineReHalf`. -/
  h_crit : s ∈ criticalLineReHalf

theorem CriticalLineRationalFanoOctonionProbe.re_eq_half (c : CriticalLineRationalFanoOctonionProbe) :
    c.s.re = (1 / 2 : ℝ) :=
  c.h_crit

theorem zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_of_const_rat_tilt (δ : ℝ) (δslot : ℕ → ℝ) (s : ℂ)
    (m : ℕ) (phi_t_step : ℕ → ℝ) (q : ℚ)
    (hconst : ∀ m : ℕ, phi_t_step m = rationalTilt q) :
    zetaR1_latticeTerm_monogamic3DRamanujanTerm δ phi_t_step δslot s m =
      zetaR1_latticeTerm_deltaESlot δ (rationalTilt q) 1 δslot s m :=
  zetaR1_latticeTerm_monogamic3DRamanujanTerm_eq_zetaR1_latticeTerm_deltaESlot_of_const_phi_t δ phi_t_step
    δslot s m (rationalTilt q) hconst

end

end Hqiv.Physics
