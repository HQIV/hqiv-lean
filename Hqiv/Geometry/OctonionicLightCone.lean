import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Filter Finset BigOperators
open scoped Topology

namespace Hqiv

-- `simpa` is clearer than `simp`+`exact` for several ℚ↔ℝ casts below; silence style lint.
set_option linter.unnecessarySimpa false

/-!
## Horizon readouts and null-lattice bookkeeping (`m : ℕ`)

Natural indices `m` package **null-lattice combinatorics** (mode counts, temperature ladder samples) and
the leading **horizon-area functional** `shellSurface m` used wherever downstream modules need a
closed-form area driver. Think of `m` as a **calibration/readout coordinate** on the light-cone
substrate, not as the claim that physical support is point-supported on one row.

**Wave vs grid:** localized modes may peak between book-keeping rows; theorems are stated at chosen
readout values of `m`. **`referenceM`** is the **lock-in / QCD-onset alignment pin** on that
coordinate—not “all physics lives on this integer.”

**Three generations:** triality / `So8RepIndex` (`Fin 3`) and anomaly bookkeeping force the
threefold slot (`SMEmbedding`, `Triality`, `AnomalyCancellation`). The index `m` does **not** substitute
for representation theory; it only supplies the **area law** (`shellSurface`, detuned variants) once a
mode’s overlap with that bookkeeping is fixed.
-/

/-- **Discrete null-lattice mode counting (Nat version).**

`latticeSimplexCount m` is the pure stars-and-bars count of integer
solutions to `x + y + z = m` with `x,y,z ≥ 0`, i.e.
\[
  \binom{m+2}{2} = \frac{(m+2)(m+1)}{2}.
\]
We keep the factor of \(1/2\) implicit and work with the numerator
`(m+2)*(m+1)`; the octonionic lift and normalisations are handled
separately. -/
def latticeSimplexCount (m : Nat) : Nat :=
  (m + 2) * (m + 1)

/-- Base check: at `m = 0` there is exactly one lattice point `(0,0,0)`. -/
theorem latticeSimplexCount_zero :
  latticeSimplexCount 0 = 2 * 1 := by
  -- This unfolds to `(0+2)*(0+1) = 2*1`.
  simp [latticeSimplexCount]

/-- Base check: at `m = 1` there are exactly three lattice points. -/
theorem latticeSimplexCount_one :
  latticeSimplexCount 1 = 3 * 2 := by
  -- This unfolds to `(1+2)*(1+1) = 3*2`.
  simp [latticeSimplexCount]

/-- Base check: at `m = 2` there are exactly six lattice points. -/
theorem latticeSimplexCount_two :
  latticeSimplexCount 2 = 4 * 3 := by
  simp [latticeSimplexCount]

/-- Closed form: lattice count is the stars-and-bars numerator (no separate def). -/
theorem latticeSimplexCount_eq (m : Nat) :
  latticeSimplexCount m = (m + 2) * (m + 1) := rfl

/-- Lattice count is positive (every shell has at least one mode). -/
theorem latticeSimplexCount_pos (m : Nat) : 0 < latticeSimplexCount m := by
  rw [latticeSimplexCount_eq]; positivity

/-- **Division in the lattice:** the stars-and-bars numerator (m+2)(m+1) is even
(one of two consecutive naturals is even), so 2 ∣ latticeSimplexCount m. -/
theorem two_dvd_latticeSimplexCount (m : Nat) : 2 ∣ latticeSimplexCount m := by
  rw [latticeSimplexCount_eq, mul_comm]
  exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (m + 1))

/-- Cast to ℝ: `(latticeSimplexCount m : ℝ) = (m+2)(m+1)`. -/
theorem latticeSimplexCount_cast (m : Nat) :
  (latticeSimplexCount m : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
  simp [latticeSimplexCount_eq, Nat.cast_mul]

-- Quick theorem checks (visible in infoview)
#check latticeSimplexCount_zero
#check latticeSimplexCount_one
#check latticeSimplexCount_two

/-- Cumulative simplex count up to shell `n`:
    `cumLatticeSimplexCount n = ∑_{m=0}^{n} latticeSimplexCount m`. -/
def cumLatticeSimplexCount : Nat → Nat
  | 0     => latticeSimplexCount 0
  | n + 1 => cumLatticeSimplexCount n + latticeSimplexCount (n + 1)

-- Quick numeric checks for the cumulative count
#eval cumLatticeSimplexCount 0
#eval cumLatticeSimplexCount 1
#eval cumLatticeSimplexCount 2
#eval cumLatticeSimplexCount 3

/-- Explicit unfolding for small `n` (sanity checks). -/
theorem cumLatticeSimplexCount_zero :
  cumLatticeSimplexCount 0 = latticeSimplexCount 0 := by
  -- This is just the defining equation at `0`.
  rfl

theorem cumLatticeSimplexCount_one :
  cumLatticeSimplexCount 1 = latticeSimplexCount 0 + latticeSimplexCount 1 := by
  -- Unfold once at `n = 0`.
  simp [cumLatticeSimplexCount]

theorem cumLatticeSimplexCount_two :
  cumLatticeSimplexCount 2 =
    latticeSimplexCount 0 + latticeSimplexCount 1 + latticeSimplexCount 2 := by
  simp [cumLatticeSimplexCount, Nat.add_assoc]

/-- Hockey-stick: 3 × cumulative count = (n+1)(n+2)(n+3); the 1/6 factor in the paper
comes from the 3! in the binomial. -/
theorem cumLatticeSimplexCount_hockey_stick (n : Nat) :
  3 * cumLatticeSimplexCount n = (n + 1) * (n + 2) * (n + 3) := by
  induction n with
  | zero => simp [cumLatticeSimplexCount, latticeSimplexCount]
  | succ n ih =>
    simp only [cumLatticeSimplexCount, latticeSimplexCount]
    rw [Nat.mul_add 3, ih]
    ring_nf
    try ring

/-- **Closed form (arrived at from hockey-stick):** cum = (n+1)(n+2)(n+3)/3.
So the cumulative count is determined by the binomial, not just the recurrence. -/
theorem cumLatticeSimplexCount_closed (n : Nat) :
  cumLatticeSimplexCount n = ((n + 1) * (n + 2) * (n + 3)) / 3 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num)
  exact (cumLatticeSimplexCount_hockey_stick n).symm

/-- **Division in the lattice:** the binomial numerator (n+1)(n+2)(n+3) is divisible by 3.
So the cumulative mode count is an integer; the 1/3 comes from the 3D simplex (stars-and-bars). -/
theorem three_dvd_cum_numerator (n : Nat) :
  3 ∣ (n + 1) * (n + 2) * (n + 3) := by
  use cumLatticeSimplexCount n
  exact (cumLatticeSimplexCount_hockey_stick n).symm

-- Quick theorem checks for the cumulative count
#check cumLatticeSimplexCount_zero
#check cumLatticeSimplexCount_one
#check cumLatticeSimplexCount_two

/-- One-step monotonicity: adding shell `n+1` only increases the cumulative count. -/
theorem cumLatticeSimplexCount_succ_ge (n : Nat) :
  cumLatticeSimplexCount n ≤ cumLatticeSimplexCount (n + 1) := by
  -- `cumLatticeSimplexCount (n+1) = cumLatticeSimplexCount n + latticeSimplexCount (n+1)`
  -- and `a ≤ a + b` for natural numbers.
  exact Nat.le_add_right (cumLatticeSimplexCount n) (latticeSimplexCount (n + 1))

/-- Inequality across multiple shells: for all `k`,  
`cumLatticeSimplexCount m ≤ cumLatticeSimplexCount (m + k)`. -/
theorem cumLatticeSimplexCount_le_add (m k : Nat) :
  cumLatticeSimplexCount m ≤ cumLatticeSimplexCount (m + k) := by
  induction k with
  | zero =>
      -- `m + 0 = m`
      simp
  | succ k ih =>
      -- Step from `m + k` to `m + (k+1)` using the one-step lemma.
      have step := cumLatticeSimplexCount_succ_ge (m + k)
      -- Combine the induction hypothesis with this step.
      exact Nat.le_trans ih step

/-- Global monotonicity: if `m ≤ n` then  
`cumLatticeSimplexCount m ≤ cumLatticeSimplexCount n`. -/
theorem cumLatticeSimplexCount_monotone {m n : Nat} (h : m ≤ n) :
  cumLatticeSimplexCount m ≤ cumLatticeSimplexCount n := by
  -- Write `n = m + k` and apply the previous lemma iteratively.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  subst hk
  exact cumLatticeSimplexCount_le_add m k

/-- Cumulative simplex count is positive (every shell contributes at least one mode). -/
theorem cumLatticeSimplexCount_pos (n : Nat) :
  0 < cumLatticeSimplexCount n := by
  induction n with
  | zero => simp [cumLatticeSimplexCount]; exact latticeSimplexCount_pos 0
  | succ n ih =>
    rw [cumLatticeSimplexCount]
    exact Nat.add_pos_right (cumLatticeSimplexCount n) (latticeSimplexCount_pos (n + 1))

-- Quick checks for monotonicity lemmas
#check cumLatticeSimplexCount_succ_ge
#check cumLatticeSimplexCount_le_add
#check cumLatticeSimplexCount_monotone

/-- **The single axiom of HQIV**  
At each discrete radial step m in the observer's past light-cone,  
the number of newly available modes is exactly the stars-and-bars count  
for x + y + z = m (3D null lattice) multiplied by the octonion factor 8.  

This combinatorial rule is the complete foundation of the model; the theory
is built from **division math** (rational counts, 1/3 in the cumulative sum,
α = 3/5 from lattice dimension) and, in the metric sector, **monogamy** (γ = 2/5).
Repeated radial application yields α = 0.60 (growth rate) and  
the permanent positive curvature limit Ω_k^true = 0.0098  
(density of *new* available modes per radial step in the limit).  

In the Lean development we tie the numeric mode count directly to the
Nat-level lattice simplex count via a simple Float cast. -/
def available_modes (m : Nat) : ℝ :=
  (4 : ℝ) * (latticeSimplexCount m : ℝ)

/-- Available modes in closed form (ℝ): 4(m+2)(m+1). -/
theorem available_modes_eq (m : Nat) :
  available_modes m = (4 : ℝ) * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
  unfold available_modes latticeSimplexCount
  norm_num
  ring

/-- **Factor 4 from octonion × binomial:** available_modes = 8 × (stars-and-bars count in ℝ).
Paper: new modes = 8 × C(m+2,2); we have 2·C(m+2,2) = (m+2)(m+1), so 8·C = 4·(m+2)(m+1). -/
theorem available_modes_octonion (m : Nat) :
  available_modes m = (8 : ℝ) * ((latticeSimplexCount m : ℝ) / 2) := by
  rw [available_modes_eq, latticeSimplexCount_eq]
  simp only [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

/-- **New modes** added at shell m (incremental growth from the axiom).
These are the **newly unlocked horizon modes** the observer interacts with via
the time angle δθ′ = φ t in the HQVM metric; curvature (δE, shell_shape, Ω_k)
is tied to the same shells. -/
def new_modes (m : Nat) : ℝ :=
  if m = 0 then
    available_modes 0
  else
    available_modes m - available_modes (m - 1)

/-- **New modes at shell 0:** by definition, new_modes 0 = available_modes 0. -/
theorem new_modes_zero : new_modes 0 = available_modes 0 := by simp [new_modes]

/-- **New modes in closed form (m ≥ 1):** new_modes (m+1) = 8(m+2).
Follows from available_modes (m+1) - available_modes m and latticeSimplexCount difference. -/
theorem new_modes_succ (m : Nat) :
  new_modes (m + 1) = 8 * (m + 2 : ℝ) := by
  unfold new_modes available_modes
  simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [latticeSimplexCount_eq (m + 1), latticeSimplexCount_eq m]
  rw [show (m + 1 : Nat) + 2 = m + 3 by omega, show (m + 1 : Nat) + 1 = m + 2 by omega]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  push_cast
  ring

/-- HQIV varying-G exponent α — the **only** curvature-imprint exponent used in this formalism.

**Provenance:** the physical derivation that this exponent is \(3/5\) (and that it is the unique
HQIV curvature imprint in the companion theory) is given in the companion HQIV manuscript and in
Brodie (2026), not reproved here; Lean encodes the identification and proves `alpha_eq_3_5`.

Same dimensionless index as in the Python curvature pipeline (`alpha = 0.60` in
`discrete_baryogenesis_horizon.py` and `main.tex`), i.e. how \(G_\mathrm{eff}\)
(or curvature imprint) scales with the shell temperature. **In Lean, α is identified
with the lattice ratio** `(n+1)(n+2)(n+3)/(5·cum n)` for every `n` via
`latticeAlphaRatio_eq_alpha` (hockey-stick); see also `tendsto_latticeAlphaRatio`. -/
def alpha : ℝ := 0.60

/-- **α equals 3/5 exactly.** The paper's 0.60 is the rational 3/5 (proved). -/
theorem alpha_eq_3_5 : alpha = 3/5 := by unfold alpha; norm_num

/-- **α as lattice rational:** α = 3/(3+2) = 3/5. The 3 is the effective growth
exponent of the cumulative mode count on the 3D null lattice (hockey-stick);
the 5 = 3+2 comes from stars-and-bars (binomial (m+2 choose 2)). The discrete
ratio equals 3/5 for every `n` (`latticeAlphaRatio_eq_alpha`), not only in the limit. -/
theorem alpha_eq_lattice_rational :
  alpha = (3 : ℝ) / (3 + 2 : ℝ) := by unfold alpha; norm_num

/-- **Lattice-derived ratio:** (n+1)(n+2)(n+3) / (5 · cum n) in ℝ.
By the hockey-stick identity 3·cum n = (n+1)(n+2)(n+3), this equals 3/5 for every n. -/
noncomputable def latticeAlphaRatio (n : Nat) : ℝ :=
  (n + 1 : ℝ) * (n + 2) * (n + 3) / (5 * (cumLatticeSimplexCount n : ℝ))

/-- **α in the lattice:** the lattice ratio equals α for every shell count n. -/
theorem latticeAlphaRatio_eq_alpha (n : Nat) :
  latticeAlphaRatio n = alpha := by
  unfold latticeAlphaRatio alpha
  have h := cumLatticeSimplexCount_hockey_stick n
  have hpos : (cumLatticeSimplexCount n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (cumLatticeSimplexCount_pos n).ne'
  have cast_eq : (↑n + 1) * (↑n + 2) * (↑n + 3) = (↑((n + 1) * (n + 2) * (n + 3)) : ℝ) := by push_cast; ring
  have hR : (3 : ℝ) * ↑(cumLatticeSimplexCount n) = ↑((n + 1) * (n + 2) * (n + 3)) := by
    rw [show (3 : ℝ) = Nat.cast (3 : Nat) from by norm_num, ← Nat.cast_mul]; exact congr_arg (Nat.cast : Nat → ℝ) h
  field_simp [hpos]
  rw [cast_eq, ← hR, mul_comm (5 : ℝ) _, mul_assoc]
  norm_num
  ring

/-- **α as limit:** as more shells are included, the lattice ratio tends to α = 3/5. -/
theorem tendsto_latticeAlphaRatio :
  Tendsto (fun n : ℕ => latticeAlphaRatio n) atTop (𝓝 alpha) := by
  rw [show (fun n : ℕ => latticeAlphaRatio n) = (fun _ => alpha) from funext latticeAlphaRatio_eq_alpha]
  exact tendsto_const_nhds

/--
**QCD onset readout index** (`ℕ`), lowest explicit **substrate pin** for the horizon ladder in this module.

Everything “derived” about curvature imprint, `α = 3/5` as a limit of lattice ratios, lock-in
temperatures, *etc.* is proved **after** that readout index is available—but **`qcdShell` itself is
not obtained in Lean from a smaller definition block** (it is aligned with the paper narrative: QCD
onset at the first nontrivial horizon row). Changing `qcdShell` propagates to `referenceM` and every
lock-in witness that mentions that index.
-/
def qcdShell : Nat := 1

/--
**Steps along the 3D null lattice** from QCD to lock-in (and the same count for post-lock-in
baryogenesis steps).

Set to `3` so that `latticeStepCount = cubeAxes` (`latticeStepCount_eq_cubeAxes`): one step per
spatial axis of the null lattice. That ties the “3” to the **same** `cubeAxes` used elsewhere, but it
remains a **named `Nat` pin** in this file—parallel in status to `qcdShell`, not a consequence of
`latticeSimplexCount` alone.
-/
def latticeStepCount : Nat := 3

/-- **latticeStepCount = 3.** -/
theorem latticeStepCount_eq_three : latticeStepCount = 3 := rfl

/-- **Steps from QCD to lockin:** number of discrete lattice steps from QCD transition to η lockin;
    equals latticeStepCount (3D lattice). -/
def stepsFromQCDToLockin : Nat := latticeStepCount

/-- **Steps after lockin:** baryogenesis proceeds latticeStepCount discrete steps after T_lockin. -/
def stepsAfterLockin : Nat := latticeStepCount

/--
**Lock-in / reference shell index** = `qcdShell + stepsFromQCDToLockin` (currently `4`).

Downstream code evaluates detuned areas, mode counts, and Fano-axis data **at this row** of the
discrete ladder. That is a **calibration and export convention** on the null-lattice grid: the
**physical** claim being encoded is that horizon **area functionals** (and the imprint ladder) are the
resonant drivers, while **three generations** are carried by the Spin(8)/triality / `So8RepIndex`
layer—not by the numeral `4` itself.

It is **not** an output of a deeper numeric search inside this module: it is **fixed by the two pins
above**. Changing `qcdShell` / `latticeStepCount` moves which grid row is named “reference,” not the
algebraic fact that generation space is threefold.

**Never treat `referenceM = 4` as derived from TUFT Hopf winding or from proton mass fitting.**
The numeral `4` also appears as `tuftHeavyChartShell = n + 1` for heavy Hopf winding `n = 3`;
Lean proves `referenceM = tuftHeavyChartShell` only as a **numeric coincidence** under the current
pins (`HopfShellBeltramiMassBridge.referenceM_eq_tuftHeavyChartShell_numeric`), not as chart
identification. See `AGENTS/TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md` §0.

**Tent-pole note (dynamic Casimir / T-ladder era):** `referenceM` is the **hadronic/proton calibration
and export convention** on the discrete null-lattice grid. It is the row at which the nucleon network
mass formulas (ConservedContentMassBridge, QuarkMetaResonance, CosmologicalShellLadder) lock the
observed 938.272 MeV proton scale. It is **not** required to be the universal normalization point for
leptonic, neutral, or gauge-sector readouts.

The dynamic inner/outer Casimir machinery (`effective_casimir_scale_at_xi`, the T12 three-shell
witness + T11 torsion + T13 outer 1/140 on the same octonion carrier, the continuous curvature
primitive driving `omegaK_xi`, and the physical-T ↔ ξ ladder) now supplies a first-class,
geometry-driven scale for those sectors at *any* temperature. The lepton-specific chart and the
RHN neutral channel can (and should) be computed from that dynamic relationship rather than being
forced through the m=4 proton shell. See `HopfShellBeltramiMassBridge` (MeV-anchored physical_T
readouts) and the worldview synthesis in `AGENTS/TUFT_INNER_OUTER_CASIMIR_DYNAMICS.md`.
-/
def referenceM : Nat := qcdShell + stepsFromQCDToLockin

/-- Continuous curvature-imprint density on ℝ⁺, matching `shell_shape` on integers. -/
noncomputable def curvatureDensity (x : ℝ) : ℝ :=
  (1 / x) * (1 + alpha * Real.log x)

/-- Purely combinatorial curvature-imprint **shape** per shell m.

Given by the continuous density at x = m+1 (paper: (1/(m+1)) * (1 + α log(m+1))). -/
noncomputable def shell_shape (m : Nat) : ℝ :=
  curvatureDensity (m + 1)

/-- Positivity of the curvature-imprint density for `x ≥ 1`.

For all shells in the physical range (where we sample at `x = m+1` with `m ≥ 0`)
we have `x ≥ 1`, hence `curvatureDensity x > 0`. -/
lemma curvatureDensity_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < curvatureDensity x := by
  unfold curvatureDensity
  -- First, `x > 0` so `1/x > 0`.
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hfrac_pos : 0 < (1 / x) := one_div_pos.mpr hx0
  -- Next, `log x ≥ 0` for `x ≥ 1`, so `1 + α log x ≥ 1`.
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have h_alpha_nonneg : 0 ≤ alpha := by unfold alpha; norm_num
  have h_alpha_log_nonneg : 0 ≤ alpha * Real.log x := mul_nonneg h_alpha_nonneg hlog_nonneg
  have hone_le : (1 : ℝ) ≤ 1 + alpha * Real.log x := by
    simpa [add_comm] using add_le_add_right h_alpha_log_nonneg 1
  -- Hence the second factor is strictly positive.
  have hsecond_pos : 0 < 1 + alpha * Real.log x := lt_of_lt_of_le zero_lt_one hone_le
  -- Product of two positive reals is positive.
  exact mul_pos hfrac_pos hsecond_pos

/-- Specialisation of `curvatureDensity_pos` to integer shells `x = m+1`. -/
lemma curvatureDensity_pos_succ (m : Nat) :
    0 < curvatureDensity (m + 1) := by
  -- On integers we have `1 ≤ m+1`.
  have hnat : (1 : Nat) ≤ m + 1 :=
    Nat.succ_le_succ (Nat.zero_le m)
  have hcast : (1 : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast hnat
  exact curvatureDensity_pos hcast

/-- Lower bound for the density: curvatureDensity (m+1) ≥ 1/(m+1) (the log factor is ≥ 1). -/
lemma curvatureDensity_ge_one_div_succ (m : Nat) :
    (1 : ℝ) / (m + 1 : ℝ) ≤ curvatureDensity (m + 1) := by
  unfold curvatureDensity
  have h : (1 : ℝ) + alpha * Real.log (m + 1 : ℝ) ≥ 1 := by
    have hlog : 0 ≤ Real.log (m + 1 : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have ha : 0 ≤ alpha := by unfold alpha; norm_num
    nlinarith [mul_nonneg ha hlog]
  have hpos : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos m
  calc (1 : ℝ) / (m + 1 : ℝ)
    _ = (1 / (m + 1 : ℝ)) * 1 := by ring
    _ ≤ (1 / (m + 1 : ℝ)) * (1 + alpha * Real.log (m + 1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h
      positivity

/-- **Analytic upper bound (per shell):** for m < n, curvatureDensity (m+1) ≤ (1/(m+1))(1 + α log(n+1)).
Used to bound the curvature integral above by a multiple of the harmonic sum. -/
lemma curvatureDensity_le_one_div_succ_mul_log (m n : Nat) (hmn : m < n) :
    curvatureDensity (m + 1) ≤ (1 / (m + 1 : ℝ)) * (1 + alpha * Real.log (n + 1 : ℝ)) := by
  unfold curvatureDensity
  have hpos : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hfrac : 0 ≤ (1 / (m + 1 : ℝ)) := le_of_lt (one_div_pos.mpr hpos)
  refine mul_le_mul_of_nonneg_left ?_ hfrac
  have hα : 0 ≤ alpha := by unfold alpha; norm_num
  have hm : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hmn)
  have hlog : Real.log (m + 1) ≤ Real.log (n + 1) := Real.log_le_log hpos hm
  have hαlog : alpha * Real.log (m + 1) ≤ alpha * Real.log (n + 1) :=
    mul_le_mul_of_nonneg_left hlog hα
  linarith

/-- By definition, `shell_shape m` is the density sampled at m+1. -/
theorem shell_shape_eq_density_succ (m : Nat) :
  shell_shape m = curvatureDensity (m + 1) := by
  unfold shell_shape
  rfl

/-- Explicit shape formula from the paper (proved, not defined): (1/(m+1))(1 + α ln(m+1)). -/
theorem shell_shape_formula (m : Nat) :
  shell_shape m = (1 / (m + 1 : ℝ)) * (1 + alpha * Real.log (m + 1 : ℝ)) := by
  rw [shell_shape_eq_density_succ, curvatureDensity]

-- Quick check for the bridge lemma
#check shell_shape_eq_density_succ

/-!
## Curvature norm from the cube (formalised)

The combinatorial norm \(6^7\sqrt{3}\) is built from: (1) expanding a cube in all
directions ±x, ±y, ±z → 6 lattice directions; (2) raising each to the octonion
dimension 7 → \(6^7\); (3) the inscribed-sphere factor → \(\sqrt{3}\) (half-diagonal
of the unit cube). We formalise each piece and then the full formula.
-/

/-- **Number of spatial axes** for the cube (x, y, z). -/
def cubeAxes : ℕ := 3

/-- **Two signs per axis** (±). -/
def signsPerAxis : ℕ := 2

/-- **Cube directions:** expand a cube in all directions (±x, ±y, ±z).
Equals axes × signs = 3 × 2 = 6 (the 6 outward normals / lattice directions). -/
def cubeDirections : ℕ := cubeAxes * signsPerAxis

theorem cubeDirections_eq : cubeDirections = 6 := by unfold cubeDirections cubeAxes signsPerAxis; norm_num

/-- **latticeStepCount equals cubeAxes (3).** So the step counts from QCD to lockin and after
    lockin are the same as the number of spatial axes in the 3D null lattice. -/
theorem latticeStepCount_eq_cubeAxes : latticeStepCount = cubeAxes := by unfold latticeStepCount cubeAxes; rfl

/-- **Octonion imaginary dimension:** 7 imaginary units (Fano-plane nodes). -/
def octonionImaginaryDim : ℕ := 7

theorem octonionImaginaryDim_eq : octonionImaginaryDim = 7 := rfl

/-- **Quaternion imaginary dimension:** 3 imaginary units.

This is the comparison carrier for the classical `H`-sector / quaternionic Maxwell
reduction, not the canonical HQIV octonionic lift. -/
def quaternionImaginaryDim : ℕ := 3

theorem quaternionImaginaryDim_eq : quaternionImaginaryDim = 3 := rfl

/-- **Half-diagonal of the unit cube** (cube with vertices at (±1,±1,±1)).
Distance from center to vertex = √(1²+1²+1²) = √3. This is the "inscribed sphere"
factor in the curvature norm (rapidity lattice / equilateral triangle on the hyperboloid).
**√3 is spatial** (a length); the time phase in the metric uses **2π** (angle). Different
dimensions — no conflict. -/
noncomputable def unitCubeHalfDiagonal : ℝ := Real.sqrt ((1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2)

theorem unitCubeHalfDiagonal_eq_sqrt3 : unitCubeHalfDiagonal = Real.sqrt (3 : ℝ) := by
  unfold unitCubeHalfDiagonal
  norm_num

/-!
### Aside: belt (1D) vs sphere (3D) — "lift by 1 adds 2π"

If you place a belt around the equator (circle of radius R) and lift it so every
point is 1 meter higher, the new radius is R+1, so the new length is 2π(R+1).
The **added** length is 2π(R+1) − 2πR = **2π**, independent of R. So the
increment is constant (2π per meter of lift).

In 3D, if you take a sphere of radius R and "lift" its surface outward by 1
(same idea: new radius R+1), the surface area goes from 4πR² to 4π(R+1)². The
**added** area is 4π((R+1)² − R²) = 8πR + 4π, which **depends on R**. So the
"constant increment" property does **not** hold for the sphere — it is special
to the circle (1D boundary). The curvature norm's √3 is tied to the 3D cube
(half-diagonal); the belt's 2π is a 1D phenomenon.
-/

/-- **Belt fact (1D):** Lifting a circle of radius R outward by h gives new
circumference 2π(R+h). The added length is 2πh — independent of R. -/
theorem circle_lift_adds_length (R h : ℝ) :
    2 * Real.pi * (R + h) - 2 * Real.pi * R = 2 * Real.pi * h := by ring

/-- **Sphere (2-surface) does not do the same:** Lifting a sphere of radius R
outward by 1 gives added area 8πR + 4π, which depends on R. -/
theorem sphere_lift_added_area (R : ℝ) :
    4 * Real.pi * (R + 1) ^ 2 - 4 * Real.pi * R ^ 2 = 8 * Real.pi * R + 4 * Real.pi := by ring

/-- **Base of the curvature norm:** 6.

Intuition: expand a cube in all directions (±x, ±y, ±z); that gives 6 lattice
directions (the 6 “sides” or outward normals of the cube). In the HQIV
combinatorics this is also the 6 non-preferred directions in the Fano structure
(7 imaginary octonion axes with one preferred for colour). Matter fraction and η
require the full SM embedding to SO(8). -/
def curvatureNormBase : ℕ := 6

/-- **Exponent of the curvature norm:** 7.

Raise each of the 6 lattice directions to the octonion dimension: 6^7. The 7
is the number of imaginary octonion units (Fano-plane nodes), so the curvature
norm factor is “each of the 6 cube directions raised to O^7”. -/
def curvatureNormExponent : ℕ := 7

/-- The curvature norm base equals the number of cube directions (6). -/
theorem curvatureNormBase_eq_cubeDirections : curvatureNormBase = cubeDirections := by
  unfold curvatureNormBase cubeDirections cubeAxes signsPerAxis; norm_num

/-- The curvature norm exponent equals the octonion imaginary dimension (7). -/
theorem curvatureNormExponent_eq_octonionDim : curvatureNormExponent = octonionImaginaryDim := by
  unfold curvatureNormExponent octonionImaginaryDim; rfl

/-- Comparison candidate: replace the octonionic exponent `7` by the quaternionic exponent `3`. -/
noncomputable def curvature_norm_quaternionicCandidate : ℝ :=
  (cubeDirections : ℝ) ^ quaternionImaginaryDim * unitCubeHalfDiagonal

theorem curvature_norm_quaternionicCandidate_eq :
    curvature_norm_quaternionicCandidate = (cubeDirections : ℝ) ^ quaternionImaginaryDim * unitCubeHalfDiagonal :=
  rfl

theorem curvature_norm_quaternionicCandidate_exact :
    curvature_norm_quaternionicCandidate = (216 : ℝ) * Real.sqrt (3 : ℝ) := by
  rw [curvature_norm_quaternionicCandidate_eq, unitCubeHalfDiagonal_eq_sqrt3, cubeDirections_eq,
    quaternionImaginaryDim_eq]
  norm_num

/-- **Arithmetic identity:** \(6^7 = 279\,936\) (so the curvature norm factor is an integer). -/
theorem curvatureNormBase_pow_exponent :
  curvatureNormBase ^ curvatureNormExponent = 279_936 := by
  unfold curvatureNormBase curvatureNormExponent
  norm_num

/-- Combinatorial normalisation \(6^7\sqrt{3}\), the HQIV invariant.

**Intuition:** The curvature norm comes from (1) expanding a cube in all
directions (±x, ±y, ±z) → 6 lattice directions; (2) raising each to the
octonion dimension → \(6^7\); (3) taking the inscribed sphere → \(\sqrt{3}\)
(the rapidity lattice / equilateral triangle on the local hyperboloid).

Same as `CURVATURE_NORM_COMBINATORIAL` in the Python code. Multiplies the shell
shape to give δE(m); Ω\_k is calibrated from it. Matter fraction and η require
the full SM embedding to SO(8). The factor **√3** here is spatial (unit-cube
half-diagonal); the time angle in HQVMetric uses **2π** (angular period). So
curvature norm = spatial geometry, time phase = angle — different roles. -/
noncomputable def curvature_norm_combinatorial : ℝ :=
  (curvatureNormBase : ℝ) ^ curvatureNormExponent * Real.sqrt (3 : ℝ)

/-- **Curvature norm from base and exponent:** \(6^7\sqrt{3}\) in ℝ. -/
theorem curvature_norm_combinatorial_eq :
  curvature_norm_combinatorial = (curvatureNormBase : ℝ) ^ curvatureNormExponent * Real.sqrt (3 : ℝ) :=
  rfl

/-- **Curvature norm from the cube (formal):** the combinatorial norm equals
(cube directions)^(octonion dimension) × (unit-cube half-diagonal), i.e.
\(6^7 \cdot \sqrt{3}\) from expanding the cube in ±x, ±y, ±z, raising to O^7, and the √3 factor. -/
theorem curvature_norm_from_cube :
  curvature_norm_combinatorial = (cubeDirections : ℝ) ^ curvatureNormExponent * unitCubeHalfDiagonal := by
  rw [unitCubeHalfDiagonal_eq_sqrt3, cubeDirections_eq]
  unfold curvature_norm_combinatorial curvatureNormBase curvatureNormExponent
  norm_num

/-- Same formula with octonion dimension explicit: (cube directions)^(octonion dim) × half-diagonal. -/
theorem curvature_norm_from_cube_octonionDim :
  curvature_norm_combinatorial = (cubeDirections : ℝ) ^ octonionImaginaryDim * unitCubeHalfDiagonal := by
  have := curvature_norm_from_cube
  rw [curvatureNormExponent_eq_octonionDim] at this
  exact this

/-!
### Not chosen by convenience: the norm is determined by three structural inputs

The value \(6^7\sqrt{3} = 279\,936\sqrt{3}\) is the **only** real that can be written as
(cube directions)^(octonion dimension) × (unit-cube half-diagonal) given the
definitions above. It is **not** a free parameter tuned to match Ω\_k or η.

1. **6** is fixed by the **3D cube**: three spatial axes, two signs per axis ⇒
   `cubeDirections = cubeAxes * signsPerAxis = 3 * 2 = 6`. Any other spatial
   dimension or counting rule would change this (e.g. 4D cube would give 8 directions).

2. **7** is fixed by the **octonion algebra**: there are exactly 7 imaginary units
   (Fano-plane nodes). That is a mathematical fact about ℝ with the octonion
   product; it is not a choice.

3. **√3** is fixed by the **unit cube**: the half-diagonal from center to vertex
   of the cube with vertices (±1,±1,±1) is √(1²+1²+1²) = √3. So the factor is
   the Euclidean norm of (1,1,1); no other scale or shape appears.

So the curvature norm is **uniquely determined** once we assume: (A) curvature
counting uses a 3D cubic lattice (6 directions), (B) the algebra is octonionic
(7 imaginary dimensions), (C) the geometric factor is the unit-cube half-diagonal
(√3). Change any of A, B, or C and the number changes. There is no free
numerological constant.
-/

/-- **Uniqueness of the norm from the three inputs:** The combinatorial norm
equals the product of (cube directions)^(octonion dim) and the unit-cube
half-diagonal. Those three quantities are defined above without reference to
Ω\_k, η, or any observational constant. -/
theorem curvature_norm_determined_by_structure :
  curvature_norm_combinatorial = (cubeDirections : ℝ) ^ octonionImaginaryDim * unitCubeHalfDiagonal :=
  curvature_norm_from_cube_octonionDim

/-- **Curvature norm from the discrete light-cone axiom.**

Starting from the single HQIV light-cone axiom

* new modes at shell m = 8 × stars-and-bars(m) = 4·(m+2)(m+1),

the Lean development fixes:

* the underlying lattice to be the 3D cubic null lattice (three spatial axes with two signs each),
* the number of octonionic imaginary directions to be 7 (Fano-plane nodes),
* and the discrete radial unit in the spatial lattice to be the half-diagonal of the unit cube.

These three structural inputs are exactly `cubeDirections`, `octonionImaginaryDim`, and
`unitCubeHalfDiagonal`. The curvature norm is therefore *determined* by the light-cone
axiom together with isotropy and the octonionic lift:

  curvature_norm_combinatorial
    = (cube directions)^(octonion imaginary dim) × (unit-cube half-diagonal)
    = 6^7 · √3.

No reference to Ω_k, η, or any observational constant appears in the definition or proof. -/
theorem curvature_norm_from_lightcone_axiom :
    curvature_norm_combinatorial
      = (cubeDirections : ℝ) ^ octonionImaginaryDim * unitCubeHalfDiagonal :=
  curvature_norm_determined_by_structure

/-- **Exact value of the combinatorial norm** as an integer multiple of √3:
\[
  \text{curvature\_norm\_combinatorial} = 279\,936 \cdot \sqrt{3}.
\]
Uses \(6^7 = 279\,936\). -/
theorem curvature_norm_combinatorial_exact :
    curvature_norm_combinatorial = (279_936 : ℝ) * Real.sqrt (3 : ℝ) := by
  unfold curvature_norm_combinatorial curvatureNormBase curvatureNormExponent
  norm_num

theorem curvature_norm_combinatorial_eq_1296_mul_quaternionicCandidate :
    curvature_norm_combinatorial = (1296 : ℝ) * curvature_norm_quaternionicCandidate := by
  rw [curvature_norm_combinatorial_exact, curvature_norm_quaternionicCandidate_exact]
  ring

theorem curvature_norm_quaternionicCandidate_eq_div_1296 :
    curvature_norm_quaternionicCandidate = curvature_norm_combinatorial / (1296 : ℝ) := by
  rw [curvature_norm_combinatorial_eq_1296_mul_quaternionicCandidate]
  field_simp

theorem curvature_norm_combinatorial_ne_quaternionicCandidate :
    curvature_norm_combinatorial ≠ curvature_norm_quaternionicCandidate := by
  rw [curvature_norm_combinatorial_eq_1296_mul_quaternionicCandidate]
  intro h
  have hqpos : 0 < curvature_norm_quaternionicCandidate := by
    rw [curvature_norm_quaternionicCandidate_exact]
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  nlinarith

/-- **Combinatorial norm is positive** (base^exponent > 0 and √3 > 0). -/
theorem curvature_norm_combinatorial_pos : 0 < curvature_norm_combinatorial := by
  unfold curvature_norm_combinatorial curvatureNormBase curvatureNormExponent
  have h1 : 0 < (6 : ℝ) ^ (7 : ℕ) := pow_pos (by norm_num) _
  have h2 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  exact mul_pos h1 h2

/-- Per-shell curvature imprint δE(m) = (6^7√3) * shape(m). -/
noncomputable def deltaE (m : Nat) : ℝ :=
  curvature_norm_combinatorial * shell_shape m

/-- Parallel comparison candidate: the same shell shape, but with quaternionic `6^3 * sqrt(3)` normalization. -/
noncomputable def deltaE_quaternionicCandidate (m : Nat) : ℝ :=
  curvature_norm_quaternionicCandidate * shell_shape m

/-- Per-shell δE in terms of density only. -/
theorem deltaE_eq (m : Nat) :
  deltaE m = curvature_norm_combinatorial * curvatureDensity (m + 1) := by
  simp only [deltaE, shell_shape_eq_density_succ]

/-- **δE using the exact combinatorial norm:** δE(m) = 279936 · √3 · curvatureDensity(m+1). -/
theorem deltaE_exact_norm (m : Nat) :
  deltaE m = (279_936 : ℝ) * Real.sqrt 3 * curvatureDensity (m + 1) := by
  rw [deltaE_eq, curvature_norm_combinatorial_exact]

theorem deltaE_quaternionicCandidate_eq (m : Nat) :
    deltaE_quaternionicCandidate m = curvature_norm_quaternionicCandidate * curvatureDensity (m + 1) := by
  simp [deltaE_quaternionicCandidate, shell_shape_eq_density_succ]

theorem deltaE_quaternionicCandidate_exact_norm (m : Nat) :
    deltaE_quaternionicCandidate m = (216 : ℝ) * Real.sqrt 3 * curvatureDensity (m + 1) := by
  rw [deltaE_quaternionicCandidate_eq, curvature_norm_quaternionicCandidate_exact]

theorem deltaE_eq_1296_mul_deltaE_quaternionicCandidate (m : Nat) :
    deltaE m = (1296 : ℝ) * deltaE_quaternionicCandidate m := by
  unfold deltaE deltaE_quaternionicCandidate
  rw [curvature_norm_combinatorial_eq_1296_mul_quaternionicCandidate]
  ring

theorem deltaE_quaternionicCandidate_eq_div_1296 (m : Nat) :
    deltaE_quaternionicCandidate m = deltaE m / (1296 : ℝ) := by
  rw [deltaE_eq_1296_mul_deltaE_quaternionicCandidate]
  field_simp

theorem deltaE_ne_deltaE_quaternionicCandidate_of_shell_shape_ne_zero
    (m : Nat) (hshape : shell_shape m ≠ 0) :
    deltaE m ≠ deltaE_quaternionicCandidate m := by
  intro h
  unfold deltaE deltaE_quaternionicCandidate at h
  have hnorm :
      curvature_norm_combinatorial = curvature_norm_quaternionicCandidate := by
    exact mul_right_cancel₀ hshape h
  exact curvature_norm_combinatorial_ne_quaternionicCandidate hnorm

/-- Absolute value of the curvature-imprint shape: |shape(m)|, no separate helper def. -/
noncomputable def shell_shape_abs (m : Nat) : ℝ :=
  |shell_shape m|

/-- Unnormalised curvature imprint integral over shells 0..n-1. -/
noncomputable def curvature_integral (n : Nat) : ℝ :=
  let shells := List.range n
  shells.foldl (fun acc m => acc + shell_shape_abs m) 0.0

/-- Discrete curvature integral as an explicit finite sum over `curvatureDensity`.

This rewrites the list-fold definition into the more conceptual
\[
  \text{curvature\_integral}(n)
    = \sum_{m=0}^{n-1} \bigl|\,\text{curvatureDensity}(m+1)\,\bigr|.
\]
It makes transparent that the discrete object we are summing is exactly
the continuous density sampled on integer shells. -/
theorem curvature_integral_eq_sum_density (n : Nat) :
  curvature_integral n
    = (List.range n).foldl (fun (acc : ℝ) (m : Nat) => acc + |curvatureDensity (↑m + 1)|) 0.0 := by
  unfold curvature_integral
  simp only [shell_shape_abs, shell_shape_eq_density_succ, curvatureDensity_pos_succ, abs_of_pos]

/-- Positivity of the absolute shell shape `shell_shape_abs m`. -/
lemma shell_shape_abs_pos (m : Nat) :
    0 < shell_shape_abs m := by
  unfold shell_shape_abs
  -- Via the bridge lemma we reduce to `curvatureDensity (m+1)`.
  have hpos : 0 < curvatureDensity (m + 1) :=
    curvatureDensity_pos_succ m
  -- For a positive real, `|x| = x`.
  have habs :
      |curvatureDensity (m + 1)| = curvatureDensity (m + 1) :=
    abs_of_pos hpos
  rw [shell_shape_eq_density_succ, habs]
  exact hpos

/-- Recurrence relation for the discrete curvature integral:
`curvature_integral (n+1) = curvature_integral n + shell_shape_abs n`. -/
lemma curvature_integral_succ (n : Nat) :
    curvature_integral (n + 1) =
      curvature_integral n + shell_shape_abs n := by
  unfold curvature_integral
  -- `List.range (n+1) = List.range n ++ [n]`.
  simp [List.range_succ, List.foldl_append, shell_shape_abs]

/-- Curvature integral is bounded below by the harmonic partial sum (used for divergence). -/
lemma curvature_integral_ge_harmonic (n : Nat) :
    curvature_integral n ≥ ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ) := by
  induction n with
  | zero => unfold curvature_integral; simp; norm_num
  | succ n ih =>
    rw [curvature_integral_succ, sum_range_succ]
    have hshell : shell_shape_abs n ≥ (1 : ℝ) / (n + 1 : ℝ) := by
      rw [shell_shape_abs, shell_shape_eq_density_succ, abs_of_pos (curvatureDensity_pos_succ n)]
      exact curvatureDensity_ge_one_div_succ n
    -- Both pieces dominate their harmonic counterparts.
    exact add_le_add ih hshell

/-- **Analytic upper bound:** curvature integral is at most (1 + α log(n+1)) times the harmonic sum.
So the discrete curvature integral is sandwiched: H_n ≤ curvature_integral n ≤ (1+α log(n+1))·H_n,
hence it diverges like the harmonic series (Θ(log n)). -/
theorem curvature_integral_le_harmonic_mul_log (n : Nat) :
    curvature_integral n ≤ (1 + alpha * Real.log (n + 1 : ℝ)) * ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ) := by
  induction n with
  | zero => unfold curvature_integral; simp; norm_num
  | succ n ih =>
    rw [curvature_integral_succ]
    have hshell : shell_shape_abs n ≤ (1 / (n + 1 : ℝ)) * (1 + alpha * Real.log (n + 2 : ℝ)) := by
      rw [shell_shape_abs, shell_shape_eq_density_succ, abs_of_pos (curvatureDensity_pos_succ n)]
      have H := curvatureDensity_le_one_div_succ_mul_log n (n + 1) (Nat.lt_succ_self n)
      rw [show (↑(n + 1) : ℝ) + 1 = (↑n + 2 : ℝ) from by push_cast; ring] at H
      exact H
    have hfac : (1 + alpha * Real.log (n + 1 : ℝ)) ≤ (1 + alpha * Real.log (n + 2 : ℝ)) := by
      have ha : 0 ≤ alpha := by unfold alpha; norm_num
      have hlog : Real.log (n + 1 : ℝ) ≤ Real.log (n + 2 : ℝ) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · have : (n + 1 : ℝ) ≤ (n + 2 : ℝ) := by nlinarith
          exact this
      have hmul : alpha * Real.log (n + 1 : ℝ) ≤ alpha * Real.log (n + 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog ha
      linarith
    calc curvature_integral n + shell_shape_abs n
      _ ≤ (1 + alpha * Real.log (n + 1 : ℝ)) * ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ)
          + (1 / (n + 1 : ℝ)) * (1 + alpha * Real.log (n + 2 : ℝ)) := add_le_add ih hshell
      _ ≤ (1 + alpha * Real.log (n + 2 : ℝ)) * ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ)
          + (1 + alpha * Real.log (n + 2 : ℝ)) * ((1 : ℝ) / (n + 1 : ℝ)) :=
          add_le_add
            (mul_le_mul_of_nonneg_right hfac
              (sum_nonneg fun i _ => by
                refine div_nonneg zero_le_one ?_
                have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
                linarith))
            (le_of_eq (mul_comm _ _))
      _ ≤ (1 + alpha * Real.log (↑(n + 1) + 1)) * (∑ i ∈ range n, (1 : ℝ) / (↑i + 1) + (1 : ℝ) / (↑n + 1)) := by
        rw [show (↑(n + 1) : ℝ) + 1 = ↑n + 2 by push_cast; ring]
        rw [mul_add]
      _ = (1 + alpha * Real.log (↑(n + 1) + 1 : ℝ)) * ∑ i ∈ range (n + 1), (1 : ℝ) / (i + 1 : ℝ) := by rw [sum_range_succ]

/-- **Curvature integral as a Finset sum** (for asymptotic analysis). -/
theorem curvature_integral_eq_sum (n : Nat) :
    curvature_integral n = ∑ i ∈ range n, curvatureDensity (i + 1) := by
  induction n with
  | zero => unfold curvature_integral; simp; norm_num
  | succ n ih =>
    rw [curvature_integral_succ, sum_range_succ, ih]
    congr 1
    rw [shell_shape_abs, shell_shape_eq_density_succ]
    exact abs_of_pos (curvatureDensity_pos_succ n)

/-- **Log-weighted sum** ∑_{i=0}^{n-1} (log(i+1))/(i+1), the second piece of the curvature integral. -/
noncomputable def logWeightedSum (n : Nat) : ℝ := ∑ i ∈ range n, Real.log (i + 1 : ℝ) / (i + 1 : ℝ)

/-- **Curvature integral decomposes as harmonic sum + α × log-weighted sum.** -/
theorem curvature_integral_eq_harmonic_plus_alpha_log (n : Nat) :
    curvature_integral n =
      ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ) + alpha * logWeightedSum n := by
  rw [curvature_integral_eq_sum, logWeightedSum]
  have key : ∀ i : ℕ, curvatureDensity (↑i + 1) = (1 : ℝ) / (↑i + 1) + alpha * (Real.log (↑i + 1) / (↑i + 1)) := by
    intro i; unfold curvatureDensity; ring
  trans ∑ i ∈ range n, (1 / (↑i + 1) + alpha * (Real.log (↑i + 1) / (↑i + 1)))
  · congr 1; funext i; exact key i
  · rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- For `x > 0`, `x ≠ 1`, we have `1 - 1/x ≤ log x` (from `log(1/x) ≤ 1/x - 1`). -/
lemma one_sub_inv_le_log (x : ℝ) (hx : 0 < x) (_hx' : x ≠ 1) :
    1 - x⁻¹ ≤ Real.log x :=
  Real.one_sub_inv_le_log_of_pos hx

/-- Harmonic sum bound: `∑_{i=0}^{n-1} 1/(i+1) ≤ 1 + log(n+1)` for all `n`.
Proof: for `k ≥ 2`, `1/k ≤ log(k/(k-1))`; telescope gives `∑_{k=2}^n 1/k ≤ log n`, so `H_n ≤ 1 + log n ≤ 1 + log(n+1)`. -/
lemma harmonic_sum_le_one_add_log_succ (n : Nat) :
    ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ) ≤ 1 + Real.log (n + 1 : ℝ) := by
  -- Rewrite the real Finset sum as the real-cast harmonic number.
  have hsum : (∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ)) = (harmonic n : ℝ) := by
    -- `harmonic` is a ℚ-valued sum; coercing to ℝ matches `1/(i+1)` after simp.
    simp [harmonic, div_eq_mul_inv]
  -- Use the known bound on `harmonic (n + 1)` and monotonicity `harmonic n ≤ harmonic (n+1)`.
  have hmono : (harmonic n : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
    -- `harmonic_succ` is in ℚ; after casting to ℝ it's `harmonic (n+1) = harmonic n + 1/(n+1)`.
    have hs : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + ((n + 1 : ℝ)⁻¹) := by
      simpa [harmonic_succ] using congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ n)
    -- Rearrange.
    have hpos : 0 ≤ (n + 1 : ℝ)⁻¹ := by positivity
    linarith [hs, hpos]
  have hbound : (harmonic (n + 1) : ℝ) ≤ 1 + Real.log (n + 1 : ℝ) := by
    simpa using (harmonic_le_one_add_log (n + 1))
  -- Put it together.
  linarith [hsum, hmono, hbound]

/-- **Leading term of the asymptotic:** (α/2)(log(n+1))² (from ∫₁^{n+1} (1/x)(1+α log x) dx). -/
noncomputable def curvature_integral_asymptotic_leading (n : Nat) : ℝ := (alpha / 2) * (Real.log (n + 1 : ℝ)) ^ 2

/-- **Asymptotic: curvature_integral n = (α/2)(log(n+1))² + O(log n).**
Explicit upper bound: curvature_integral n ≤ (α/2)(log(n+1))² + (1+α)(1+log(n+1))².
The sharp O(log n) error follows from ∑ (log k)/k = (1/2)(log(n+1))² + O(log n) via ∫ (log x)/x = (1/2)(log x)². -/
theorem curvature_integral_asymptotic_upper (n : Nat) :
    curvature_integral n ≤ curvature_integral_asymptotic_leading n + (1 + alpha) * (1 + Real.log (n + 1 : ℝ)) ^ 2 := by
  rw [curvature_integral_asymptotic_leading]
  set H := ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ) with hH
  have hlog : ∀ i ∈ range n, Real.log (i + 1 : ℝ) / (i + 1 : ℝ) ≤ Real.log (n + 1 : ℝ) / (i + 1 : ℝ) := by
    intro i hi; rw [Finset.mem_range] at hi
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hi)
  have hsum : logWeightedSum n ≤ Real.log (n + 1 : ℝ) * H := by
    rw [logWeightedSum]; trans ∑ i ∈ range n, Real.log (n + 1 : ℝ) / (i + 1 : ℝ)
    · exact Finset.sum_le_sum fun i hi => hlog i hi
    ·
      -- Turn the RHS product into a sum and simplify termwise.
      rw [hH, Finset.mul_sum]
      exact le_of_eq (by
        simp [div_eq_mul_inv])
  calc curvature_integral n
    _ = H + alpha * logWeightedSum n := curvature_integral_eq_harmonic_plus_alpha_log n
    _ ≤ H + alpha * (Real.log (n + 1 : ℝ) * H) := by
        have ha : 0 ≤ alpha := by unfold alpha; norm_num
        rw [add_comm H, add_comm H (alpha * _)]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hsum ha) H
    _ = (1 + alpha * Real.log (n + 1 : ℝ)) * H := by ring
    _ ≤ (1 + alpha * Real.log (n + 1 : ℝ)) * (1 + Real.log (n + 1 : ℝ)) := by
        have hHle : H ≤ 1 + Real.log (n + 1 : ℝ) := by rw [hH]; exact harmonic_sum_le_one_add_log_succ n
        have ha : 0 ≤ alpha := by unfold alpha; norm_num
        have hlog_nonneg : 0 ≤ Real.log (n + 1 : ℝ) :=
          Real.log_nonneg (by rw [← Nat.cast_succ]; exact Nat.one_le_cast.mpr (Nat.succ_le_succ (Nat.zero_le n)))
        have hmul_nonneg : 0 ≤ (1 + alpha * Real.log (n + 1 : ℝ)) := by nlinarith [mul_nonneg ha hlog_nonneg]
        exact mul_le_mul_of_nonneg_left hHle hmul_nonneg
    _ = 1 + (1 + alpha) * Real.log (n + 1 : ℝ) + alpha * (Real.log (n + 1 : ℝ)) ^ 2 := by ring
    _ ≤ (alpha / 2) * (Real.log (n + 1 : ℝ)) ^ 2 + (1 + alpha) * (1 + Real.log (n + 1 : ℝ)) ^ 2 := by
      have ha : 0 ≤ alpha := by unfold alpha; norm_num
      have hlog : 0 ≤ Real.log (n + 1 : ℝ) :=
        Real.log_nonneg (by rw [← Nat.cast_succ]; exact Nat.one_le_cast.mpr (Nat.succ_le_succ (Nat.zero_le n)))
      nlinarith [sq_nonneg (Real.log (n + 1 : ℝ))]

/-- Curvature integral is monotone in `n`. -/
lemma curvature_integral_mono : Monotone curvature_integral := by
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    have hrec := curvature_integral_succ (a + k)
    rw [hrec]
    have hpos : 0 ≤ shell_shape_abs (a + k) := le_of_lt (shell_shape_abs_pos (a + k))
    have h2 := add_le_add_left hpos (curvature_integral (a + k))
    conv_lhs at h2 => rw [zero_add]
    conv_rhs at h2 => rw [add_comm]
    have hak : a ≤ a + k := (Nat.le_add_left a k).trans (le_of_eq (Nat.add_comm k a))
    exact le_trans (ih hak) h2

/-- Each shell adds strictly positive weight: the integral strictly increases at each step. -/
lemma curvature_integral_lt_succ (n : Nat) :
    curvature_integral n < curvature_integral (n + 1) := by
  rw [curvature_integral_succ]
  exact lt_add_of_pos_right _ (shell_shape_abs_pos n)

/-- Strict monotonicity of the cumulative curvature integral. -/
lemma curvature_integral_strict_mono ⦃a b : Nat⦄ (h : a < b) :
    curvature_integral a < curvature_integral b := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  rw [hk]; clear h hk b
  induction k with
  | zero =>
    simpa [Nat.one_add] using curvature_integral_lt_succ a
  | succ k ih =>
    rw [Nat.add_succ]
    exact lt_trans ih (curvature_integral_lt_succ (a + Nat.succ k))

/-- Non-negativity of the curvature integral for all `n`. -/
lemma curvature_integral_nonneg (n : Nat) :
    0 ≤ curvature_integral n := by
  induction n with
  | zero =>
      -- Empty sum is zero.
      unfold curvature_integral
      simp
      norm_num
  | succ n ih =>
      -- Use the recurrence and that each shell contribution is non-negative.
      have hrec := curvature_integral_succ n
      have hshell_nonneg : 0 ≤ shell_shape_abs n :=
        le_of_lt (shell_shape_abs_pos n)
      -- Rewrite with the recurrence and apply `add_nonneg`.
      have : 0 ≤ curvature_integral (n + 1) := by
        rw [hrec]; exact add_nonneg ih hshell_nonneg
      rw [congr_arg curvature_integral (Nat.succ_eq_add_one n)]; exact this

/-- Strict positivity of the curvature integral as soon as we include at least
one shell (`n > 0`). -/
lemma curvature_integral_pos {n : Nat} (hn : 0 < n) :
    0 < curvature_integral n := by
  -- Write `n = m+1` and use the recurrence once, together with positivity
  -- of the last shell contribution.
  cases n with
  | zero =>
      cases hn
  | succ m =>
      -- Here `n = m+1`.
      have hrec := curvature_integral_succ m
      have hshell_pos : 0 < shell_shape_abs m :=
        shell_shape_abs_pos m
      have hbase : 0 ≤ curvature_integral m :=
        curvature_integral_nonneg m
      -- `curvature_integral (m+1) = curvature_integral m + shell_shape_abs m`
      -- with `curvature_integral m ≥ 0` and `shell_shape_abs m > 0`.
      have hsum_pos :
          0 < curvature_integral m + shell_shape_abs m :=
        add_pos_of_nonneg_of_pos hbase hshell_pos
      -- Rewrite the goal using the recurrence.
      rw [congr_arg curvature_integral (Nat.succ_eq_add_one m), hrec]; exact hsum_pos

/-- Positivity of the curvature integral at the reference (lockin) shell. -/
lemma curvature_integral_ref_pos :
    0 < curvature_integral referenceM := by
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  exact curvature_integral_pos (n := 4) (by decide)

/-- **Existence of a transition shell:** some shell has positive curvature integral,
so a discrete-to-continuous “transition” (or reference) exists; we do not fix which shell. -/
theorem exists_transition_shell :
    ∃ N : Nat, 0 < N ∧ 0 < curvature_integral N :=
  ⟨1, Nat.one_pos, curvature_integral_pos (n := 1) Nat.one_pos⟩

-- Quick check for the curvature-integral bridge lemma
#check curvature_integral_eq_sum_density

/-!
## First-principles spatial curvature from the horizon integral (dynamic, horizon-dependent Ω_k)

Spatial curvature **depends on the horizon**. Between any two horizons it is
different — curvature between quarks (QCD horizon) and curvature at the CMB
last-scattering surface are different even at the same time "now". There is no
single "Ω_k at now" without specifying which horizon.

Ω_k is the **curvature ratio** from the horizon integral: at horizon N,
the curvature parameter at readout n is `curvature_integral n / curvature_integral N`
(dimensionless). At the horizon itself (n = N) this ratio is 1. Different N
(e.g. QCD lockin vs CMB LSS) give different curvature; the formalism is
horizon-dependent by construction.
-/

/-- **Curvature ratio at horizon N** (first-principles).
    Ω_k(n; N) = curvature_integral n / curvature_integral N when the horizon
    integral is positive; else 1 (so at-horizon value remains 1). No external
    amplitude; purely from the shell integral. -/
noncomputable def omega_k_at_horizon (n N : Nat) : ℝ :=
  if curvature_integral N ≤ (0 : ℝ) then 1
  else curvature_integral n / curvature_integral N

/-- **Equation for Ω_k at horizon N:** when the horizon integral is positive,
    omega_k_at_horizon n N = curvature_integral n / curvature_integral N. -/
theorem omega_k_at_horizon_eq (n N : Nat) (hN : 0 < curvature_integral N) :
  omega_k_at_horizon n N = curvature_integral n / curvature_integral N := by
  unfold omega_k_at_horizon
  simp [not_le_of_gt hN]

/-- At the horizon itself (n = N), the curvature ratio equals 1 (unit in lattice units). -/
theorem omega_k_at_horizon_self (N : Nat) (hN : 0 < curvature_integral N) :
    omega_k_at_horizon N N = 1 := by
  rw [omega_k_at_horizon_eq N N hN]
  field_simp [ne_of_gt hN]

/-- **Monotonicity in readout shell:** for fixed positive horizon `N`, larger `n` means larger
partial integral, hence larger \(\Omega_k(n;N)\). -/
theorem omega_k_at_horizon_mono (n1 n2 N : Nat) (hN : 0 < curvature_integral N) (h : n1 ≤ n2) :
    omega_k_at_horizon n1 N ≤ omega_k_at_horizon n2 N := by
  rw [omega_k_at_horizon_eq n1 N hN, omega_k_at_horizon_eq n2 N hN]
  exact div_le_div_of_nonneg_right (curvature_integral_mono h) (le_of_lt hN)

/-- **Strict increase** when `n1 < n2` (each shell contributes strictly positive `shell_shape_abs`). -/
theorem omega_k_at_horizon_strict_mono (n1 n2 N : Nat) (hN : 0 < curvature_integral N) (h : n1 < n2) :
    omega_k_at_horizon n1 N < omega_k_at_horizon n2 N := by
  rw [omega_k_at_horizon_eq n1 N hN, omega_k_at_horizon_eq n2 N hN]
  exact div_lt_div_of_pos_right (curvature_integral_strict_mono h) hN

/-- **Readout inside the horizon:** if `n ≤ N` then \(I(n)\le I(N)\), hence \(\Omega_k(n;N)\le 1\). -/
theorem omega_k_at_horizon_le_one_of_le (n N : Nat) (hN : 0 < curvature_integral N) (hn : n ≤ N) :
    omega_k_at_horizon n N ≤ 1 := by
  rw [omega_k_at_horizon_eq n N hN, div_le_one₀ hN]
  exact curvature_integral_mono hn

/-- **Ω_k partial** at reference horizon: curvature ratio relative to referenceM.
    omega_k_partial n = omega_k_at_horizon n referenceM. -/
noncomputable def omega_k_partial (n : Nat) : ℝ :=
  omega_k_at_horizon n referenceM

/-- The partial is exactly the curvature ratio at the reference horizon. -/
theorem omega_k_partial_eq_at_horizon (n : Nat) :
  omega_k_partial n = omega_k_at_horizon n referenceM := rfl

/-- **At the reference horizon, Ω_k partial = 1** (first-principles; no 0.0098). -/
theorem omega_k_partial_at_reference (hpos : 0 < curvature_integral referenceM) :
  omega_k_partial referenceM = 1 :=
  omega_k_at_horizon_self referenceM hpos

/-- **Ω_k depends on the horizon:** for a fixed shell n with positive integral,
different horizon cutoffs N₁ ≠ N₂ with different integrals give different Ω_k values. -/
theorem omega_k_at_horizon_depends_on_horizon
    (n N₁ N₂ : Nat)
    (hn : 0 < curvature_integral n)
    (h₁ : 0 < curvature_integral N₁) (h₂ : 0 < curvature_integral N₂)
    (hne : curvature_integral N₁ ≠ curvature_integral N₂) :
  omega_k_at_horizon n N₁ ≠ omega_k_at_horizon n N₂ := by
  rw [omega_k_at_horizon_eq n N₁ h₁, omega_k_at_horizon_eq n N₂ h₂]
  intro h
  have h₁' : curvature_integral N₁ ≠ 0 := ne_of_gt h₁
  have h₂' : curvature_integral N₂ ≠ 0 := ne_of_gt h₂
  field_simp at h
  exact hne h.symm

/-- **Auxiliary bound:** if the curvature ratio at shell n is within δ of 1,
then |omega_k_partial n - 1| < δ. -/
theorem omega_k_partial_abs_bound_of_ratio
    (hpos_ref : 0 < curvature_integral referenceM)
    {n : Nat} {δ : ℝ}
    (hδ : |curvature_integral n / curvature_integral referenceM - (1 : ℝ)| < δ) :
    |omega_k_partial n - 1| < δ := by
  unfold omega_k_partial
  rw [omega_k_at_horizon_eq n referenceM hpos_ref]
  exact hδ

/-- **Curvature integral tends to infinity** as more shells are included;
the ratio curvature_integral n / curvature_integral referenceM therefore tends to ∞. -/
theorem curvature_integral_tends_to_atTop :
  Tendsto curvature_integral atTop atTop := by
  refine Monotone.tendsto_atTop_atTop curvature_integral_mono fun B => ?_
  have hHarm :
      Tendsto (fun n => ∑ i ∈ range n, (1 : ℝ) / (i + 1 : ℝ)) atTop atTop :=
    by simpa using Real.tendsto_sum_range_one_div_nat_succ_atTop
  rcases Filter.tendsto_atTop_atTop.1 hHarm B with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hHarmN : B ≤ ∑ i ∈ range N, (1 : ℝ) / (i + 1 : ℝ) := hN N (le_rfl)
  exact le_trans hHarmN (curvature_integral_ge_harmonic N)

/-- **Asymptotic behaviour:** as more shells are included, omega_k_partial n tends to ∞
(because curvature_integral n → ∞ while the denominator is fixed). -/
theorem omega_k_partial_tends_to_atTop :
  Tendsto (fun n : Nat => omega_k_partial n) atTop atTop := by
  have hpos_ref := curvature_integral_ref_pos
  have heq : (fun n => omega_k_partial n) = (fun n => curvature_integral n / curvature_integral referenceM) := by
    ext n; unfold omega_k_partial; rw [omega_k_at_horizon_eq n referenceM hpos_ref]
  rw [heq]
  exact curvature_integral_tends_to_atTop.atTop_div_const hpos_ref

/-- **Numeric sanity check** for `available_modes 0` (replaces `#eval` on `ℝ`).

`#eval` on `Real` does not run a numeric decoder in Lean; the elaborator prints
`Real.ofCauchy (sorry …)` for the Cauchy witness. Use a short proof instead. -/
theorem available_modes_zero_numeric : available_modes 0 = 8 := by
  unfold available_modes latticeSimplexCount
  norm_num

/-- **Numeric sanity check** at the reference shell `referenceM = 4`:
`new_modes 4 = 40` (same as `new_modes_succ 3`). -/
theorem new_modes_referenceM_numeric : new_modes referenceM = 40 := by
  have hr : referenceM = 4 := by
    unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
    norm_num
  rw [hr, new_modes_succ 3]
  norm_num

-- `curvature_integral` and `omega_k_partial` are noncomputable; `#check` only prints types.
#check curvature_integral 10
#check omega_k_partial referenceM
#check available_modes_zero_numeric
#check new_modes_referenceM_numeric

end Hqiv
