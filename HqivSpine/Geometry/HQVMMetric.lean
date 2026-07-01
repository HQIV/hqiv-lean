import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# `HqivSpine.Geometry.HQVMMetric` — synchronous HQVM metric and Christoffel jet

Mined from legacy `Hqiv.Geometry.HQVMetric`, disentangled onto the spine. The HQVM line element is
`ds² = -N² dt² + a²(1-2Φ) δᵢⱼ dxⁱ dxʲ` with ADM lapse `N = 1 + Φ + φ·t` (matches `NowSlice.lapse`).

Honest scope: **pointwise chart jet** — Christoffel symbols from frozen scalar jets `(N, a, Φ)` and
`(∂_κ N, ∂_κ a, ∂_κ Φ)` at one chart point. No `Manifold` instance; covariant O-Maxwell discharge
is in `Physics.CovariantOMaxwell`.
-/

namespace HqivSpine.Geometry.HQVMMetric

open BigOperators

/-- **ADM lapse** (determined by the informational-energy axiom): N = 1 + Φ + φ t.
Φ = Newtonian potential; φ = auxiliary field from the lattice (2/Θ); t = coordinate time.
The term φ t is the horizon contribution (time angle). So this def is the unique
lapse imposed by the axiom in synchronous-comoving gauge. -/
def hqvmLapse (Φ φ t : ℝ) : ℝ := 1 + Φ + φ * t

/-- **Time angle (δθ′)** from the observer: φ · t (natural units).

From the observer’s perspective, the time angle is the cumulative phase that
**allows interaction with newly unlocked horizon modes**. Those modes are the
ones from the curvature already proved in the light-cone module: shell-wise
mode count (`new_modes`, `available_modes`), curvature imprint (δE, `shell_shape`),
and curvature integral / Ω_k at the chosen horizon. So δθ′ = φ t is not an
extra degree of freedom: φ is tied to the lattice (e.g. φ(m) = 2/T(m) in
AuxiliaryField), and as t advances the observer couples to the next shell’s
unlocked modes from that curvature. -/
def timeAngle (φ t : ℝ) : ℝ := φ * t

/-- **Lapse equals 1 + Φ + time angle:** N = 1 + Φ + δθ′. -/
theorem hqvmLapse_eq_timeAngle (Φ φ t : ℝ) :
    hqvmLapse Φ φ t = 1 + Φ + timeAngle φ t := rfl

/-- **ADM lapse is the HQVM lapse:** In the HQVM line element
  ds² = -N² dt² + a(t)²(1 - 2Φ) δᵢⱼ dxⁱ dxʲ
with shift zero, the lapse function (the function N such that g_tt = -N²) is
N = 1 + Φ + φ t = 1 + Φ + timeAngle φ t. -/
theorem ADM_lapse_eq_hqvmLapse (Φ φ t : ℝ) :
    hqvmLapse Φ φ t = 1 + Φ + φ * t := rfl

/-- **Time jet of the lapse** `N = 1 + Φ + φ t`: `∂_0 N = ∂_0 Φ + φ ∂_0 t + t ∂_0 φ` (product rule on `φ t`). -/
def hqvmLapse_jet_d0 (d0Phi d0phi d0t φ t : ℝ) : ℝ := d0Phi + φ * d0t + t * d0phi

/-- **Synchronous chart** with `∂_0 t = 1`: `∂_0 N = ∂_0 Φ + φ + t ∂_0 φ`. -/
theorem hqvmLapse_jet_d0_comoving_dt (d0Phi d0phi φ t : ℝ) :
    hqvmLapse_jet_d0 d0Phi d0phi 1 φ t = d0Phi + φ + t * d0phi := by
  unfold hqvmLapse_jet_d0; ring

/-- **Time-time component** g_tt = -N². Determined by the ADM decomposition with
shift zero: the line element is -N² dt² + spatial, so g_tt is minus the lapse squared. -/
def hqvmGtt (N : ℝ) : ℝ := -N ^ 2

/-- **Spatial conformal factor** a²(1 - 2Φ). Determined by the ADM metric in
synchronous-comoving gauge: the spatial part is a(t)²(1 - 2Φ) δᵢⱼ, so this is
the coefficient of each dxⁱ dxⁱ (no free choice — just the gauge and potential Φ). -/
def hqvmSpatialCoeff (a Φ : ℝ) : ℝ := a ^ 2 * (1 - 2 * Φ)

/-- **g_tt is negative** whenever N ≠ 0, so the coordinate t is timelike
(Lorentzian time direction). -/
theorem hqvmGtt_neg (N : ℝ) (hN : N ≠ 0) :
    hqvmGtt N < 0 := by
  unfold hqvmGtt
  exact neg_lt_zero.mpr (sq_pos_of_ne_zero hN)

/-- **Spatial coefficient is positive** when a > 0 and Φ < 1/2 (weak-field regime:
the Newtonian potential does not dominate). So the spatial metric is Riemannian. -/
theorem hqvmSpatialCoeff_pos (a Φ : ℝ) (ha : 0 < a) (hΦ : Φ < 1/2) :
    0 < hqvmSpatialCoeff a Φ := by
  unfold hqvmSpatialCoeff
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have h : 0 < 1 - 2 * Φ := by linarith
  exact mul_pos ha2 h

/-- **ADM-style coefficient decomposition of the HQVM chart expression:** with lapse
`N = hqvmLapse Φ φ t` and shift zero, the scalar coefficients are `g_tt = -N²` and
spatial diagonal coefficient `a²(1 - 2Φ)`. This theorem packages those coefficients;
it does not by itself construct the foliation as a manifold object. -/
theorem HQVM_ADM_decomposition (Φ φ t a : ℝ) :
    hqvmGtt (hqvmLapse Φ φ t) = -(hqvmLapse Φ φ t) ^ 2 ∧
    hqvmSpatialCoeff a Φ = a ^ 2 * (1 - 2 * Φ) := by
  constructor
  · unfold hqvmGtt; rfl
  · unfold hqvmSpatialCoeff; rfl

/-- **Minkowski limit of the geometry:** Φ = 0, φ = 0, a = 1 gives g_tt = -1
and spatial coefficient 1 (flat spacetime). -/
theorem HQVM_geometry_Minkowski (t : ℝ) :
    hqvmGtt (hqvmLapse 0 0 t) = -1 ∧ hqvmSpatialCoeff 1 0 = 1 := by
  constructor
  · unfold hqvmGtt hqvmLapse; norm_num
  · unfold hqvmSpatialCoeff; norm_num

/-- **Scalar normalization check for the constant-`t` normal coefficient:** with shift zero,
the formal factor `(1 / N)` normalizes the `g_tt = -N²` coefficient to `-1`. This is the
algebraic normalization identity used by the narrative unit-normal discussion. -/
theorem HQVM_unit_normal_squared (N : ℝ) (hN : N ≠ 0) :
    hqvmGtt N * (1 / N) ^ 2 = -1 := by
  unfold hqvmGtt; field_simp [hN]

/-!
### Synchronous diagonal `g_{μν}` and `g^{μν}` on `Fin 4`

These are the **same** pointwise tensors used in `Hqiv.Physics.CovariantSolution` for raising
`F` and for `√(-g)`: one definition site keeps the metric, inverse, and volume element aligned
with `hqvmGtt` / `hqvmSpatialCoeff`.
-/

/-- **Covariant synchronous HQVM metric** (diagonal, shift zero): `g₀₀ = -N²`, `gᵢᵢ = a²(1-2Φ)`, off-diagonal `0`. -/
noncomputable def hqvmMetric (N a Φ : ℝ) (μ ν : Fin 4) : ℝ :=
  if _ : μ = 0 ∧ ν = 0 then hqvmGtt N
  else if _ : μ = ν ∧ μ ≠ 0 then hqvmSpatialCoeff a Φ
  else 0

/-- **Contravariant inverse metric** matching the diagonal line element. -/
noncomputable def hqvmInverseMetric (N a Φ : ℝ) (μ ν : Fin 4) : ℝ :=
  if _ : μ = 0 ∧ ν = 0 then -(1 / N ^ 2)
  else if _ : μ = ν ∧ μ ≠ 0 then 1 / hqvmSpatialCoeff a Φ
  else 0

/-- **Volume element** `√(-g)` in synchronous HQVM with diagonal spatial `a²(1-2Φ) δᵢⱼ`: `N a³ √(1-2Φ)`. -/
noncomputable def sqrtNegG (N a Φ : ℝ) : ℝ := N * (a ^ 3) * (1 - 2 * Φ).sqrt

theorem hqvmMetric_tt (N a Φ : ℝ) : hqvmMetric N a Φ 0 0 = hqvmGtt N := by
  simp [hqvmMetric]

theorem hqvmMetric_space_diag (N a Φ : ℝ) (i : Fin 3) :
    hqvmMetric N a Φ (Fin.succ i) (Fin.succ i) = hqvmSpatialCoeff a Φ := by
  simp [hqvmMetric, Fin.succ_ne_zero]

theorem hqvmMetric_off_diag (N a Φ : ℝ) {μ ν : Fin 4} (h : μ ≠ ν) :
    hqvmMetric N a Φ μ ν = 0 := by
  unfold hqvmMetric
  split_ifs <;> simp_all

theorem hqvmInverseMetric_tt (N a Φ : ℝ) : hqvmInverseMetric N a Φ 0 0 = -(1 / N ^ 2) := by
  simp [hqvmInverseMetric]

theorem hqvmInverseMetric_space_diag (N a Φ : ℝ) (i : Fin 3) :
    hqvmInverseMetric N a Φ (Fin.succ i) (Fin.succ i) = 1 / hqvmSpatialCoeff a Φ := by
  simp [hqvmInverseMetric, Fin.succ_ne_zero]

/-- **Quadratic invariant** `g_{μν} z^μ z^ν` for the diagonal synchronous HQVM metric. -/
noncomputable def hqvmIntervalSq (N a Φ : ℝ) (z : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, hqvmMetric N a Φ μ ν * z μ * z ν

theorem hqvmIntervalSq_eq (N a Φ : ℝ) (z : Fin 4 → ℝ) :
    hqvmIntervalSq N a Φ z =
      hqvmGtt N * z 0 ^ 2 + hqvmSpatialCoeff a Φ * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
  unfold hqvmIntervalSq hqvmSpatialCoeff
  have hrow (μ : Fin 4) :
      ∑ ν : Fin 4, hqvmMetric N a Φ μ ν * z μ * z ν = hqvmMetric N a Φ μ μ * z μ ^ 2 := by
    rw [Finset.sum_eq_single μ]
    · ring
    · intro ν _ hν; simp [hqvmMetric_off_diag N a Φ (Ne.symm hν)]
    · intro h; exact (h (Finset.mem_univ μ)).elim
  have h1 : hqvmMetric N a Φ 1 1 = hqvmSpatialCoeff a Φ := hqvmMetric_space_diag N a Φ 0
  have h2 : hqvmMetric N a Φ 2 2 = hqvmSpatialCoeff a Φ := hqvmMetric_space_diag N a Φ 1
  have h3 : hqvmMetric N a Φ 3 3 = hqvmSpatialCoeff a Φ := hqvmMetric_space_diag N a Φ 2
  rw [Fin.sum_univ_four, hrow 0, hrow 1, hrow 2, hrow 3, hqvmMetric_tt, h1, h2, h3]
  simp [hqvmGtt, hqvmSpatialCoeff]
  ring

theorem hqvmIntervalSq_minkowskiLimit (z : Fin 4 → ℝ) :
    hqvmIntervalSq 1 1 0 z = -(z 0 ^ 2) + (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
  rw [hqvmIntervalSq_eq]
  simp [hqvmGtt, hqvmSpatialCoeff]

open BigOperators

/-- **`g` times `g⁻¹` is identity** (matrix product on `Fin 4`). -/
theorem hqvmMetric_contract_inverse (N a Φ : ℝ) (hN : N ≠ 0) (hs : hqvmSpatialCoeff a Φ ≠ 0)
    (μ ν : Fin 4) :
    (∑ ρ : Fin 4, hqvmMetric N a Φ μ ρ * hqvmInverseMetric N a Φ ρ ν) =
      if μ = ν then 1 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, hqvmMetric, hqvmInverseMetric, hqvmGtt] <;>
    field_simp [hN, hs]

/-- **`g⁻¹` times `g` is identity** (matrix product on `Fin 4`). -/
theorem hqvmInverse_contractMetric (N a Φ : ℝ) (hN : N ≠ 0) (hs : hqvmSpatialCoeff a Φ ≠ 0)
    (μ ν : Fin 4) :
    (∑ ρ : Fin 4, hqvmInverseMetric N a Φ μ ρ * hqvmMetric N a Φ ρ ν) =
      if μ = ν then 1 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, hqvmMetric, hqvmInverseMetric, hqvmGtt] <;>
    field_simp [hN, hs]

/-- **Christoffel symbols** `Γ^ρ_{μν}` from inverse metric `g^{ρσ}` and metric partials `dg λ μ ν` (= ∂_λ g_{μν}). -/
noncomputable def christoffelLeviCivita (gInv : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  (1 / 2) * ∑ σ : Fin 4, gInv ρ σ * (dg μ ν σ + dg ν μ σ - dg σ μ ν)

theorem christoffelLeviCivita_zero_of_flat (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (gInv : Fin 4 → Fin 4 → ℝ)
    (ρ μ ν : Fin 4) (h : ∀ l m n, dg l m n = 0) : christoffelLeviCivita gInv dg ρ μ ν = 0 := by
  simp [christoffelLeviCivita, h]

/-!
### HQVM metric partials and Christoffels (scalar jet)

At a chart point, suppose the synchronous HQVM scalars have frozen first jets `dN κ = ∂_κ N`,
`da κ = ∂_κ a`, `dPhi κ = ∂_κ Φ`. The diagonal metric `hqvmMetric` then has
`∂_κ g_{00} = ∂_κ(-N²) = -2N ∂_κ N` and, for each spatial diagonal entry,
`∂_κ(a²(1-2Φ)) = 2a (∂_κ a)(1-2Φ) - 2a² ∂_κ Φ`. Off-diagonal components stay identically zero,
so their partials vanish.
-/

/-- **Metric partials** `∂_κ g_{μν}` from scalar jets in the synchronous diagonal HQVM ansatz. -/
noncomputable def hqvmMetric_partials (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ := fun κ μ ν =>
  if _ : μ = 0 ∧ ν = 0 then -2 * N * dN κ
  else if _ : μ = ν ∧ μ ≠ 0 then 2 * a * da κ * (1 - 2 * Φ) - 2 * a ^ 2 * dPhi κ
  else 0

theorem hqvmMetric_partials_tt (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ : Fin 4) :
    hqvmMetric_partials N a Φ dN da dPhi κ 0 0 = -2 * N * dN κ := by
  simp [hqvmMetric_partials]

theorem hqvmMetric_partials_space_diag (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ : Fin 4) (i : Fin 3) :
    hqvmMetric_partials N a Φ dN da dPhi κ (Fin.succ i) (Fin.succ i) =
      2 * a * da κ * (1 - 2 * Φ) - 2 * a ^ 2 * dPhi κ := by
  simp [hqvmMetric_partials, Fin.succ_ne_zero]

/-- **Spatial partial** `∂_j s` for `s = a²(1-2Φ)`, with `j : Fin 3` the spatial chart index (`x^j`). -/
noncomputable def hqvmSpatialCoeff_jet_space (a Φ : ℝ) (da dPhi : Fin 4 → ℝ) (j : Fin 3) : ℝ :=
  2 * a * da (Fin.succ j) * (1 - 2 * Φ) - 2 * a ^ 2 * dPhi (Fin.succ j)

theorem hqvmSpatialCoeff_jet_space_eq_metric_partial (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (j i : Fin 3) :
    hqvmSpatialCoeff_jet_space a Φ da dPhi j =
      hqvmMetric_partials N a Φ dN da dPhi (Fin.succ j) (Fin.succ i) (Fin.succ i) := by
  simp [hqvmSpatialCoeff_jet_space, hqvmMetric_partials, Fin.succ_ne_zero]

theorem hqvmMetric_partials_off_diag (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ μ ν : Fin 4)
    (h : μ ≠ ν) :
    hqvmMetric_partials N a Φ dN da dPhi κ μ ν = 0 := by
  unfold hqvmMetric_partials
  split_ifs <;> simp_all

theorem hqvmMetric_partials_vanish_if_jets (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ μ ν : Fin 4)
    (hN : dN κ = 0) (ha : da κ = 0) (hΦ : dPhi κ = 0) :
    hqvmMetric_partials N a Φ dN da dPhi κ μ ν = 0 := by
  unfold hqvmMetric_partials
  split_ifs <;> simp [hN, ha, hΦ, mul_zero, zero_mul]

/-- **Levi–Civita symbols** for the HQVM diagonal metric and a scalar jet. -/
noncomputable def christoffelHQVM (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  christoffelLeviCivita (hqvmInverseMetric N a Φ) (hqvmMetric_partials N a Φ dN da dPhi) ρ μ ν

theorem hqvmInverseMetric_0_off (N a Φ : ℝ) (σ : Fin 4) (hσ : σ ≠ 0) :
    hqvmInverseMetric N a Φ 0 σ = 0 := by
  fin_cases σ
  · exact False.elim (hσ rfl)
  · simp [hqvmInverseMetric]
  · simp [hqvmInverseMetric]
  · simp [hqvmInverseMetric]

theorem hqvmInverseMetric_off_diag (N a Φ : ℝ) {μ ν : Fin 4} (h : μ ≠ ν) :
    hqvmInverseMetric N a Φ μ ν = 0 := by
  unfold hqvmInverseMetric
  split_ifs <;> simp_all

theorem hqvmInverseMetric_space_diag_val (N a Φ : ℝ) (i : Fin 3) :
    hqvmInverseMetric N a Φ (Fin.succ i) (Fin.succ i) = 1 / hqvmSpatialCoeff a Φ := by
  simp [hqvmInverseMetric, Fin.succ_ne_zero]

/-- **Standard lapse connection:** for diagonal HQVM, `Γ^0_{00} = (∂_0 N) / N` (only `g^{00}` contributes). -/
theorem christoffelHQVM_000_eq (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (hN : N ≠ 0) :
    christoffelHQVM N a Φ dN da dPhi 0 0 0 = dN 0 / N := by
  unfold christoffelHQVM christoffelLeviCivita
  have g01 : hqvmInverseMetric N a Φ 0 1 = 0 := by simp [hqvmInverseMetric]
  have g02 : hqvmInverseMetric N a Φ 0 2 = 0 := by simp [hqvmInverseMetric]
  have g03 : hqvmInverseMetric N a Φ 0 3 = 0 := by simp [hqvmInverseMetric]
  rw [Fin.sum_univ_four]
  simp [g01, g02, g03, hqvmInverseMetric, hqvmMetric_partials]
  field_simp [hN]

/-- **`Γ^i_{00}`** for spatial `i = 1,2,3`: only `g^{ii}` contributes; yields `N (∂_i N) / (a²(1-2Φ))`. -/
theorem christoffelHQVM_succi_00_eq (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (i : Fin 3)
    (hs : hqvmSpatialCoeff a Φ ≠ 0) :
    christoffelHQVM N a Φ dN da dPhi (Fin.succ i) 0 0 =
      N * dN (Fin.succ i) / hqvmSpatialCoeff a Φ := by
  unfold christoffelHQVM christoffelLeviCivita
  rw [Fin.sum_univ_four]
  fin_cases i <;> (simp [hqvmInverseMetric, hqvmMetric_partials]; field_simp [hs])

/-- **`Γ^0_{0i}`** (spatial `i`): only `g^{00}` contributes; **`Γ^0_{0i} = (∂_i N)/N`**. -/
theorem christoffelHQVM_00_succi_eq (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (i : Fin 3)
    (hN : N ≠ 0) :
    christoffelHQVM N a Φ dN da dPhi 0 0 (Fin.succ i) = dN (Fin.succ i) / N := by
  unfold christoffelHQVM christoffelLeviCivita
  have g01 : hqvmInverseMetric N a Φ 0 1 = 0 := by simp [hqvmInverseMetric]
  have g02 : hqvmInverseMetric N a Φ 0 2 = 0 := by simp [hqvmInverseMetric]
  have g03 : hqvmInverseMetric N a Φ 0 3 = 0 := by simp [hqvmInverseMetric]
  rw [Fin.sum_univ_four]
  fin_cases i <;> (simp [g01, g02, g03, hqvmInverseMetric, hqvmMetric_partials]; field_simp [hN])

/-- **`Γ^i_{0j}`**: diagonal spatial inverse kills `σ ≠ i`; off-diagonal `i ≠ j` gives **0**;
    **`Γ^i_{0i} = (∂_0 s)/(2s)`** with `s = a²(1-2Φ)` = `(a ∂_0 a (1-2Φ) - a² ∂_0 Φ) / s`. -/
theorem christoffelHQVM_succi_0_succj_eq (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (i j : Fin 3)
    (hs : hqvmSpatialCoeff a Φ ≠ 0) :
    christoffelHQVM N a Φ dN da dPhi (Fin.succ i) 0 (Fin.succ j) =
      if i = j then
        (a * da 0 * (1 - 2 * Φ) - a ^ 2 * dPhi 0) / hqvmSpatialCoeff a Φ
      else 0 := by
  by_cases hij : i = j
  · subst hij
    unfold christoffelHQVM christoffelLeviCivita
    rw [Fin.sum_univ_four]
    fin_cases i <;> (simp [hqvmInverseMetric, hqvmMetric_partials]; field_simp [hs])
  · unfold christoffelHQVM christoffelLeviCivita
    rw [Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [hqvmInverseMetric, hqvmMetric_partials] at hij ⊢

/-- **Purely spatial** `Γ^i_{jk}`: `Γ^i_{jk} = (δ_{ki} ∂_j s + δ_{ji} ∂_k s - δ_{jk} ∂_i s) / (2s)`,
    `s = a²(1-2Φ)`, `∂_j s` packaged as `hqvmSpatialCoeff_jet_space`. -/
theorem christoffelHQVM_succi_succj_succk_eq (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (i j k : Fin 3)
    (hs : hqvmSpatialCoeff a Φ ≠ 0) :
    christoffelHQVM N a Φ dN da dPhi (Fin.succ i) (Fin.succ j) (Fin.succ k) =
      (1 / (2 * hqvmSpatialCoeff a Φ)) *
        ((if k = i then (1 : ℝ) else 0) * hqvmSpatialCoeff_jet_space a Φ da dPhi j
         + (if j = i then (1 : ℝ) else 0) * hqvmSpatialCoeff_jet_space a Φ da dPhi k
         - (if j = k then (1 : ℝ) else 0) * hqvmSpatialCoeff_jet_space a Φ da dPhi i) := by
  unfold christoffelHQVM christoffelLeviCivita hqvmSpatialCoeff_jet_space
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    (simp [hqvmInverseMetric, hqvmMetric_partials]; try field_simp [hs])

/-- **`Γ^0_{00}`** when `N = hqvmLapse Φ φ t`, comoving `∂_0 t = 1`, and `dN 0` matches the lapse time jet. -/
theorem christoffelHQVM_000_hqvmLapse_comoving (Φpot φaux t d0Phi d0phi : ℝ) (dN daJet dPhiJet : Fin 4 → ℝ)
    (aScale Φm : ℝ) (hN : hqvmLapse Φpot φaux t ≠ 0)
    (hjet : dN 0 = hqvmLapse_jet_d0 d0Phi d0phi 1 φaux t) :
    christoffelHQVM (hqvmLapse Φpot φaux t) aScale Φm dN daJet dPhiJet 0 0 0 =
      hqvmLapse_jet_d0 d0Phi d0phi 1 φaux t / hqvmLapse Φpot φaux t := by
  rw [← hjet, christoffelHQVM_000_eq (hqvmLapse Φpot φaux t) aScale Φm dN daJet dPhiJet hN]

theorem christoffelHQVM_zero_if_flat_jet (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (ρ μ ν : Fin 4)
    (h : ∀ κ μ' ν', hqvmMetric_partials N a Φ dN da dPhi κ μ' ν' = 0) :
    christoffelHQVM N a Φ dN da dPhi ρ μ ν = 0 :=
  christoffelLeviCivita_zero_of_flat _ _ ρ μ ν (fun κ μ' ν' => h κ μ' ν')

theorem christoffelHQVM_zero_of_vanishing_jets (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (ρ μ ν : Fin 4)
    (hN : ∀ κ, dN κ = 0) (ha : ∀ κ, da κ = 0) (hΦ : ∀ κ, dPhi κ = 0) :
    christoffelHQVM N a Φ dN da dPhi ρ μ ν = 0 := by
  refine christoffelHQVM_zero_if_flat_jet N a Φ dN da dPhi ρ μ ν ?_
  intro κ μ' ν'
  exact hqvmMetric_partials_vanish_if_jets N a Φ dN da dPhi κ μ' ν' (hN κ) (ha κ) (hΦ κ)

theorem hqvmMetricPartialsSymm (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (κ μ ν : Fin 4) :
    hqvmMetric_partials N a Φ dN da dPhi κ μ ν =
      hqvmMetric_partials N a Φ dN da dPhi κ ν μ := by
  by_cases h : μ = ν
  · subst h; rfl
  · rw [hqvmMetric_partials_off_diag N a Φ dN da dPhi κ μ ν h,
        hqvmMetric_partials_off_diag N a Φ dN da dPhi κ ν μ (Ne.symm h)]

theorem christoffelLeviCivitaSymmLower (gInv : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ κ μ ν : Fin 4, dg κ μ ν = dg κ ν μ) (ρ μ ν : Fin 4) :
    christoffelLeviCivita gInv dg ρ μ ν = christoffelLeviCivita gInv dg ρ ν μ := by
  unfold christoffelLeviCivita
  refine congrArg ((1 / 2) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [hsym σ μ ν]
  ring

theorem christoffelHQVMSymmLower (N a Φ : ℝ) (dN da dPhi : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
    christoffelHQVM N a Φ dN da dPhi ρ μ ν =
      christoffelHQVM N a Φ dN da dPhi ρ ν μ :=
  christoffelLeviCivitaSymmLower (hqvmInverseMetric N a Φ) (hqvmMetric_partials N a Φ dN da dPhi)
    (hqvmMetricPartialsSymm N a Φ dN da dPhi) ρ μ ν

theorem hqvmInverseMetricDiag (N a Φ : ℝ) :
    ∀ i j : Fin 4, i ≠ j → hqvmInverseMetric N a Φ i j = 0 :=
  fun _ _ hij => hqvmInverseMetric_off_diag N a Φ hij

end HqivSpine.Geometry.HQVMMetric
