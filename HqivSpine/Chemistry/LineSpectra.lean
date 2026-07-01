import HqivSpine.Chemistry.Binding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# `HqivSpine.Chemistry.LineSpectra` — atomic line spectra from the hydrogenic ladder

The legacy `Hqiv.QuantumChemistry.AtomicExcitations` computed excitation energies through the heavy
`FiniteSiteQuantumChemistry` / `ProteinResearch` mode-budget scaffold and product hydrogenic
wavefunctions. The *physics that chemistry actually reports* — emission/absorption **line spectra** —
is simply the **difference of two hydrogenic levels**, and the spine already derives those levels in
`Chemistry.Binding.hydrogenicBindingHartree μ z n = μ z² / (2 n²)`. So the Rydberg/Bohr spectrum
drops out with no new constant.

What is proved:

* `transitionEnergy_eq_rydberg` — the **Rydberg formula** `ΔE = R z² (1/n_f² − 1/n_i²)` with the
  Rydberg energy `R = μ/2` read straight off the binding magnitude.
* `transitionEnergy_pos` — emission lines (`n_i > n_f`) carry positive energy.
* `transitionEnergy_scales_zEff` — lines scale as `z²` (the Moseley/Z² law: `z → 2z` quadruples ΔE).
* `lyman_gt_balmer` — for a common upper level the Lyman line (`n_f = 1`) is more energetic than the
  Balmer line (`n_f = 2`): the spectral-series ordering.
* `transitionEnergy_tendsto_seriesLimit` — as `n_i → ∞` the series converges to the **ionization
  limit** `R z² / n_f²`.
* numeric anchors: the hydrogen **Rydberg energy** `R = ½` Hartree `= 13.6057 eV`
  (`rydbergEv_eq`), and the **Balmer-α** line `n=3→2` at `5/72` Hartree `≈ 1.889 eV`
  (`balmer_alpha_energy`).

The only unit label is `Binding.hartreeToEv` (a CODATA reporting bridge, already on the spine).
Mathlib + spine only; no legacy `Hqiv.*`, no `sorry`, no new `axiom`, no `native_decide`.
-/

namespace HqivSpine.Chemistry.LineSpectra

open HqivSpine.Chemistry.Binding
open Filter Topology

noncomputable section

/-- The Rydberg energy `R = μ/2` (Hartree). For `μ = 1` this is `½` Hartree, the hydrogen
ground-state ionization energy. It is read off the binding magnitude `μ z²/(2n²)`, not posited. -/
def rydbergEnergy (μ : ℝ) : ℝ := μ / 2

/-- The bound-level (Bohr) energy `E_n = −μ z²/(2n²)` — the negative of the binding magnitude. -/
def bohrLevelEnergy (μ z n : ℝ) : ℝ := -hydrogenicBindingHartree μ z n

/-- The transition energy of the spectral line `n_i → n_f`: the difference of binding magnitudes
(= `E_{n_i} − E_{n_f}` up to sign), positive in emission. -/
def transitionEnergy (μ z nf ni : ℝ) : ℝ :=
  hydrogenicBindingHartree μ z nf - hydrogenicBindingHartree μ z ni

/-- **The Rydberg formula.** `ΔE(n_f, n_i) = R z² (1/n_f² − 1/n_i²)` with `R = μ/2`. A formal field
identity (the `a/0 = 0` convention makes it hold even at the degenerate `n = 0`). -/
theorem transitionEnergy_eq_rydberg (μ z nf ni : ℝ) :
    transitionEnergy μ z nf ni = rydbergEnergy μ * z ^ 2 * (1 / nf ^ 2 - 1 / ni ^ 2) := by
  unfold transitionEnergy hydrogenicBindingHartree rydbergEnergy; ring

/-- **Emission lines are positive.** A downward transition `n_i > n_f` releases energy. -/
theorem transitionEnergy_pos (μ z nf ni : ℝ) (hμ : 0 < μ) (hz : z ≠ 0)
    (hf : 0 < nf) (hfi : nf < ni) : 0 < transitionEnergy μ z nf ni := by
  rw [transitionEnergy_eq_rydberg]
  have hi : 0 < ni := by linarith
  have hsq : nf ^ 2 < ni ^ 2 := by nlinarith
  have hbracket : 0 < 1 / nf ^ 2 - 1 / ni ^ 2 := by
    have := one_div_lt_one_div_of_lt (show (0 : ℝ) < nf ^ 2 by positivity) hsq
    linarith
  have hR : 0 < rydbergEnergy μ := by unfold rydbergEnergy; linarith
  have hz2 : 0 < z ^ 2 := by positivity
  exact mul_pos (mul_pos hR hz2) hbracket

/-- **Moseley's `Z²` law.** Doubling the seen charge quadruples every line energy. -/
theorem transitionEnergy_scales_zEff (μ z nf ni : ℝ) :
    transitionEnergy μ (2 * z) nf ni = 4 * transitionEnergy μ z nf ni := by
  unfold transitionEnergy hydrogenicBindingHartree; ring

/-- **Spectral-series ordering.** For a common upper level `n_i > 2`, the Lyman line (`n_f = 1`,
UV) is more energetic than the Balmer line (`n_f = 2`, visible). -/
theorem lyman_gt_balmer (μ z ni : ℝ) (hμ : 0 < μ) (hz : z ≠ 0) (_hi : 2 < ni) :
    transitionEnergy μ z 2 ni < transitionEnergy μ z 1 ni := by
  rw [transitionEnergy_eq_rydberg, transitionEnergy_eq_rydberg]
  have hR : 0 < rydbergEnergy μ := by unfold rydbergEnergy; linarith
  have hz2 : 0 < z ^ 2 := by positivity
  have hRz : 0 < rydbergEnergy μ * z ^ 2 := by positivity
  nlinarith [hRz]

/-- **The series limit is the ionization energy.** As `n_i → ∞` the `n_f`-series of lines converges
to `R z² / n_f²` — removing the electron entirely from level `n_f`. -/
theorem transitionEnergy_tendsto_seriesLimit (μ z nf : ℝ) :
    Tendsto (fun ni : ℝ => transitionEnergy μ z nf ni) atTop
      (𝓝 (rydbergEnergy μ * z ^ 2 / nf ^ 2)) := by
  have hrw : (fun ni : ℝ => transitionEnergy μ z nf ni)
      = fun ni : ℝ => μ * z ^ 2 / (2 * nf ^ 2) - (μ * z ^ 2 / 2) * (1 / ni ^ 2) := by
    funext ni; unfold transitionEnergy hydrogenicBindingHartree; ring
  rw [hrw]
  have hzero : Tendsto (fun ni : ℝ => 1 / ni ^ 2) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_pow_atTop (n := 2) (by norm_num)).inv_tendsto_atTop
  have hmul : Tendsto (fun ni : ℝ => (μ * z ^ 2 / 2) * (1 / ni ^ 2)) atTop (𝓝 0) := by
    simpa using hzero.const_mul (μ * z ^ 2 / 2)
  have hlim := (tendsto_const_nhds (x := μ * z ^ 2 / (2 * nf ^ 2))
    (f := (atTop : Filter ℝ))).sub hmul
  have : μ * z ^ 2 / (2 * nf ^ 2) - 0 = rydbergEnergy μ * z ^ 2 / nf ^ 2 := by
    unfold rydbergEnergy; ring
  rwa [this] at hlim

/-! ## Numeric anchors -/

/-- The hydrogen Rydberg energy is `½` Hartree. -/
theorem rydbergEnergy_hydrogen : rydbergEnergy 1 = 1 / 2 := by unfold rydbergEnergy; norm_num

/-- The Rydberg energy in eV via the CODATA Hartree bridge: `13.6057 eV`. -/
def rydbergEv : ℝ := rydbergEnergy 1 * hartreeToEv

theorem rydbergEv_eq : rydbergEv = 13.605693122994 := by
  unfold rydbergEv rydbergEnergy hartreeToEv; norm_num

/-- The **Balmer-α** line (`n = 3 → 2`, hydrogen) is `5/72` Hartree. -/
theorem balmer_alpha_energy : transitionEnergy 1 1 2 3 = 5 / 72 := by
  unfold transitionEnergy hydrogenicBindingHartree; norm_num

/-- The **Lyman-α** line (`n = 2 → 1`, hydrogen) is `3/8` Hartree — five times the Balmer-α energy,
the UV vs visible split. -/
theorem lyman_alpha_energy : transitionEnergy 1 1 1 2 = 3 / 8 := by
  unfold transitionEnergy hydrogenicBindingHartree; norm_num

end

end HqivSpine.Chemistry.LineSpectra
