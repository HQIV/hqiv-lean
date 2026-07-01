import HqivSpine.Physics.Blackbody
import HqivSpine.Physics.DiscreteHeat

/-!
# `HqivSpine.Physics.Thermodynamics` — the four laws from the shell ladder

The macroscopic laws of thermodynamics packaged from already-derived spine ingredients —
no new physics input, just the law-shaped statements:

* **Zeroth law.** Thermal equilibrium = equal shell temperature `T_m = ω_m = 1/(m+1)`. It is an
  equivalence relation, and because the ladder temperature is *injective* two shells are in
  equilibrium **iff** they are the same shell (`thermalEquilibrium_iff_eq`).
* **First law.** Energy bookkeeping. The microscopic zero-point slice `N_m·T_m = 8 =
  carrierMultiplicity` is the **same on every shell** (`firstLaw_zeroPointSlice_conserved`) — the
  incompressible lattice slice of `Blackbody`. Macroscopically the photon gas obeys the equation of
  state `U = 3P` (`firstLaw_equationOfState`) and the Euler relation `T·s = (4/3)U`
  (`firstLaw_euler_relation`).
* **Second law.** Entropy production is nonnegative: the discrete dissipation proxy
  `−⟨u,Δu⟩ ≥ 0` (`secondLaw_entropyProduction_nonneg`), the explicit-Euler step never increases the
  quadratic energy under the CFL bound (`secondLaw_euler_energy_nonincreasing`), and the equilibrium
  entropy density is nonnegative (`secondLaw_equilibrium_entropy_nonneg`).
* **Third law.** Unattainability / ladder cooling: for every `ε > 0` some shell has `T_m < ε`
  (`thirdLaw_unattainable_cooling`), and the temperature strictly drops outward — every inner shell
  is hotter (`thirdLaw_hotter_inside`).

Honest scope: the second-law dynamics live on the `C₃` toy mesh of `DiscreteHeat` (a parabolic
dissipation/CFL *sign*, not a continuum PDE claim); the photon-gas relations are the finite,
regulator-free `Blackbody` densities. Mathlib-only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`.
-/

namespace HqivSpine.Physics.Thermodynamics

open scoped BigOperators
open HqivSpine.Foundation HqivSpine.Physics

/-- **Shell temperature scale** in Planck units: `T_m = ω_m = 1/(m+1)`. -/
noncomputable def shellTemp (m : ℕ) : ℝ := shellOmega m

theorem shellTemp_pos (m : ℕ) : 0 < shellTemp m := shellOmega_pos m

/-! ## Zeroth law -/

/-- **Thermal equilibrium**: two shells share the same ladder temperature. -/
def thermalEquilibrium (m n : ℕ) : Prop := shellTemp m = shellTemp n

@[refl] theorem zerothLaw_refl (m : ℕ) : thermalEquilibrium m m := rfl

theorem zerothLaw_symm {m n : ℕ} (h : thermalEquilibrium m n) : thermalEquilibrium n m := h.symm

theorem zerothLaw_trans {m n k : ℕ}
    (hmn : thermalEquilibrium m n) (hnk : thermalEquilibrium n k) : thermalEquilibrium m k :=
  hmn.trans hnk

/-- The ladder temperature is **injective**: distinct shells have distinct temperatures. -/
theorem shellTemp_injective : Function.Injective shellTemp := by
  intro m n h
  unfold shellTemp shellOmega at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have : (m : ℝ) = (n : ℝ) := by linarith
  exact_mod_cast this

/-- **Zeroth law, sharp form**: equilibrium holds iff the shells coincide. -/
theorem thermalEquilibrium_iff_eq (m n : ℕ) : thermalEquilibrium m n ↔ m = n :=
  ⟨fun h => shellTemp_injective h, fun h => by rw [thermalEquilibrium, h]⟩

/-! ## First law -/

/-- The microscopic **zero-point energy slice** carried by shell `m`: `N_m · T_m`. -/
noncomputable def zeroPointSlice (m : ℕ) : ℝ := shellModeMultiplicity m * shellTemp m

/-- Each shell carries exactly one carrier's worth of zero-point: `N_m·T_m = 8`. -/
theorem firstLaw_zeroPointSlice_const (m : ℕ) :
    zeroPointSlice m = (carrierMultiplicity : ℝ) := by
  unfold zeroPointSlice shellTemp
  exact shell_zeroPoint_slice_const m

/-- **First law (microscopic)**: the zero-point slice is conserved across shells — no shell stores
more internal zero-point energy than another. -/
theorem firstLaw_zeroPointSlice_conserved (m n : ℕ) : zeroPointSlice m = zeroPointSlice n := by
  rw [firstLaw_zeroPointSlice_const, firstLaw_zeroPointSlice_const]

/-- **Internal energy** of the truncated photon gas on the shell window `[m_UV, m_IR]`. -/
noncomputable def internalEnergy (T : ℝ) (m_UV m_IR : ℕ) : ℝ := blackbodyEnergyDensity T m_UV m_IR

/-- **First law (equation of state)** for the massless photon gas: `U = 3P`. -/
theorem firstLaw_equationOfState (T : ℝ) (m_UV m_IR : ℕ) :
    internalEnergy T m_UV m_IR = 3 * radiationPressure T m_UV m_IR :=
  energyDensity_eq_three_pressure T m_UV m_IR

/-- **First law (Euler relation)** for radiation: `T·s = (4/3)U`. -/
theorem firstLaw_euler_relation (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    T * entropyDensity T m_UV m_IR = (4 / 3 : ℝ) * internalEnergy T m_UV m_IR :=
  T_times_entropy_eq T m_UV m_IR hT

/-! ## Second law -/

/-- **Entropy-production proxy** on the `C₃` heat mesh: `σ = −⟨u, Δu⟩`. -/
noncomputable def entropyProduction (u : Fin 3 → ℝ) : ℝ :=
  -∑ i : Fin 3, u i * DiscreteHeat.laplacianCycle3 u i

/-- **Second law (dissipation sign)**: entropy production is nonnegative. -/
theorem secondLaw_entropyProduction_nonneg (u : Fin 3 → ℝ) : 0 ≤ entropyProduction u :=
  neg_nonneg.mpr (DiscreteHeat.sum_u_laplacianCycle3_nonpos u)

/-- **Second law (monotone relaxation)**: under the CFL bound `3·dt·ν ≤ 2` the explicit-Euler heat
step never increases the quadratic energy — a discrete Lyapunov / entropy arrow. -/
theorem secondLaw_euler_energy_nonincreasing {ν dt : ℝ}
    (hν : 0 ≤ ν) (hdt : 0 ≤ dt) (hCFL : dt * ν * (3 : ℝ) ≤ 2) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, (DiscreteHeat.eulerHeatStep3 ν dt u i) ^ 2 ≤ ∑ i : Fin 3, (u i) ^ 2 :=
  DiscreteHeat.eulerHeatStep3_sum_sq_le_sum_sq_of_three_mul_dt_nu_le_two hν hdt hCFL u

/-- **Second law (equilibrium entropy)**: the photon-gas entropy density is nonnegative. -/
theorem secondLaw_equilibrium_entropy_nonneg (T : ℝ) (m_UV m_IR : ℕ) (hT : 0 < T) :
    0 ≤ entropyDensity T m_UV m_IR :=
  entropyDensity_nonneg T m_UV m_IR hT

/-! ## Third law -/

/-- **Third law (unattainability / ladder cooling)**: for every `ε > 0` there is a shell whose
temperature lies below `ε` — absolute zero is approached but only as `m → ∞`. -/
theorem thirdLaw_unattainable_cooling (ε : ℝ) (hε : 0 < ε) : ∃ m : ℕ, shellTemp m < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n, ?_⟩
  unfold shellTemp shellOmega
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hε] at hn
  nlinarith [hn, hε]

/-- **Third law (temperature gradient)**: every inner shell is strictly hotter than the next one
outward. -/
theorem thirdLaw_hotter_inside (m : ℕ) : shellTemp (m + 1) < shellTemp m := shellOmega_succ_lt m

end HqivSpine.Physics.Thermodynamics
