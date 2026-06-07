import Hqiv.Physics.BBNEpochEvolution
import Hqiv.Physics.ContinuousXiPath
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Geometry.AuxiliaryField

/-!
# BBN epoch network (rate scaffold, cooling in T)

Python integrator: `scripts/hqiv_bbn_epoch_network.py` (mirrors names here).

**Species (baryons per H):** neutron `n`, proton `p`, deuterium `D`, ³He, ⁴He, ⁷Be, ⁷Li.

**Lock-in inputs (fixed):** η, `derivedDeltaM`, `bbnDeuteronQAtLockin`, `bbnHelium4QAtLockin`.

**Epoch inputs (vary with universe age / T):**
* shell `m(T) = T_Pl_MeV/T − 1`;
* `alphaEffAtShell m`, `gammaEffAtShell m`, `T m`;
* shell reaction opportunity from `Δlog ξ`, curvature imprint, and lock-in separation.

**Reactions (schematic rates Γ ∝ η × α_eff(m(T)) × exp(Q/T) × T^n):**
1. `n + p → D + γ` with `Q_D`;
2. `D + p → ³He + γ` with `Q_3 − Q_D`;
3. `D + D → ⁴He + γ` with `Q_4 − 2 Q_D` (lock-in composite trace);
4. `³He + ⁴He → ⁷Be + γ` with `bbnBe7FormationQ`;
5. `⁷Be + e⁻ → ⁷Li + ν_e` with `bbnBe7ElectronCaptureQ`;
6. weak `n ↔ p` until the shell freeze-out readout `bbnFreezeoutTemperatureMeV η`.

`bbnHubbleRate` is retained below as a comparison diagnostic for standard BBN
language.  The native HQIV integrator advances by shell opportunity, not by
using `H` as an input clock.

**Not claimed:** full PRIMAT rate tables or post-BBN Li destruction (stellar depletion).

Python integrator adds ⁷Be / ⁷Li slots with `bbnBe7FormationQ` and `bbnBe7ElectronCaptureQ`
(`BBNNetworkFromWeights`); witness JSON fills `Be7H` and `Li7H`.
-/

namespace Hqiv.Physics

open Hqiv
open ContinuousXiPath

noncomputable section

/-- Standard g_* at BBN (photon + 3 neutrino). -/
def bbnGStar : ℝ := 10.75

/-- Planck mass in MeV (Hubble rate units). -/
def M_Pl_MeV : ℝ := 1.2209e22

/-- Radiation-dominated Hubble parameter `H(T)` in s⁻¹ (MeV units). -/
noncomputable def bbnHubbleRate (T_MeV : ℝ) : ℝ :=
  1.66 * Real.sqrt bbnGStar * T_MeV ^ 2 / M_Pl_MeV

/-- BBN horizon coordinate from the physical MeV temperature. -/
noncomputable def bbnShellXiFromT_MeV (T_MeV : ℝ) : ℝ :=
  T_Pl_MeV / T_MeV

/-- Strong-channel fraction of the octonion carrier used by the shell opportunity. -/
noncomputable def bbnNetworkStrongChannelFraction : ℝ := (4 : ℝ) / 8

/-- Homogeneous-era curvature budget at BBN temperatures (local ≈ global ⇒ unity).

The cumulative `omegaK_xi` ratio to lock-in is **not** used here; that chart compares
epochs, not same-time local vs global curvature. -/
noncomputable def bbnCurvatureBudgetAtT_MeV (_T_MeV : ℝ) : ℝ := 1

theorem bbnCurvatureBudgetAtT_MeV_eq_one (T_MeV : ℝ) : bbnCurvatureBudgetAtT_MeV T_MeV = 1 := rfl

/-- Curvature opportunity factor during homogeneous BBN (unity budget). -/
noncomputable def bbnCurvatureOpportunityFactor (T_MeV : ℝ) : ℝ :=
  bbnCurvatureBudgetAtT_MeV T_MeV

/-- Shell-native reaction opportunity for one cooling step `T_MeV → T_next_MeV`.

This replaces the old `dt = -dT/(T*H)` driver in the dynamic Python path:
`Δlog ξ · log(ξ/ξ_lock)^3 · Ω_k(ξ)^(γ*strong)`.
-/
noncomputable def bbnShellReactionOpportunity (T_MeV T_next_MeV : ℝ) : ℝ :=
  let ξ := bbnShellXiFromT_MeV T_MeV
  let ξNext := bbnShellXiFromT_MeV T_next_MeV
  Real.log (ξNext / ξ) * (Real.log (ξ / xiLockin)) ^ 3 *
    bbnCurvatureOpportunityFactor T_MeV

/-- HQIV coupling modulation on shell `m` relative to lock-in: `α_eff(m)/α_eff(lockin)`. -/
noncomputable def bbnAlphaEffRatio (m : ℕ) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c / alphaEffAtShell bbnBindingShell c

/-- Thermal formation exponent `exp(Q/T)` (dimensionless weight). -/
noncomputable def bbnFormationWeight (Q T_MeV : ℝ) : ℝ :=
  Real.exp (Q / T_MeV)

/-- Schematic D formation rate prefactor at epoch temperature. -/
noncomputable def bbnRate_np_to_D (η T_MeV : ℝ) (m : ℕ) (Q_D : ℝ) (c : ℝ := 1) : ℝ :=
  η * bbnAlphaEffRatio m c * bbnFormationWeight Q_D T_MeV * T_MeV ^ (3 / 2 : ℝ)

/-- Schematic photodissociation of D at epoch T. -/
noncomputable def bbnRate_D_destroy (T_MeV Q_D : ℝ) : ℝ :=
  bbnFormationWeight (-Q_D) T_MeV

/-- Weak freeze-out as a shell/temperature readout, not an `H` input clock. -/
def bbnWeakFrozen (T_MeV : ℝ) : Prop :=
  T_MeV ≤ bbnFreezeoutTemperatureMeV eta_paper

structure BBNNetworkState where
  n_n : ℝ
  n_p : ℝ
  n_D : ℝ
  n_He3 : ℝ
  n_He4 : ℝ
  n_Be7 : ℝ
  n_Li7 : ℝ

/-- Baryon budget per H (includes ⁷Be and ⁷Li). -/
def bbnBaryonBudget (s : BBNNetworkState) (_η : ℝ) : ℝ :=
  s.n_n + s.n_p + 2 * s.n_D + 3 * s.n_He3 + 4 * s.n_He4 + 7 * s.n_Be7 + 7 * s.n_Li7

/-- ⁴He mass fraction from network state: `Y_p = (4 n_He4 + 3 n_He3) / η`. -/
noncomputable def bbnYpFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else (4 * s.n_He4 + 3 * s.n_He3) / η

noncomputable def bbnDHFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_D / η

noncomputable def bbnHe3HFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_He3 / η

noncomputable def bbnBe7HFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_Be7 / η

noncomputable def bbnLi7HFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_Li7 / η

/-- Integrated readout slot (filled by Python witness JSON). -/
structure BBNIntegratedReadout where
  Yp : ℝ
  DH : ℝ
  He3H : ℝ
  Be7H : ℝ
  Li7H : ℝ
  T_freeze_MeV : ℝ
  n_steps : ℕ

theorem bbnHubbleRate_pos (T_MeV : ℝ) (hT : 0 < T_MeV) : 0 < bbnHubbleRate T_MeV := by
  unfold bbnHubbleRate M_Pl_MeV bbnGStar
  have hG : 0 < (10.75 : ℝ) := by norm_num
  have hs : 0 < Real.sqrt (10.75 : ℝ) := Real.sqrt_pos.mpr hG
  positivity

theorem bbnFormationWeight_pos (Q T_MeV : ℝ) : 0 < bbnFormationWeight Q T_MeV :=
  bbnBoltzmannWeight_pos Q T_MeV

noncomputable def bbnDDReactionQAtLockin : ℝ :=
  bbnDDReactionQ derivedProtonMass

theorem bbnDDReactionQAtLockin_eq :
    bbnDDReactionQAtLockin =
      bbnHelium4QAtLockin - 2 * bbnDeuteronQAtLockin := by
  unfold bbnDDReactionQAtLockin bbnDDReactionQ bbnDeuteronQAtLockin bbnHelium4QAtLockin
  rfl

theorem bbnWeakFrozen_freezeout_temperature :
    bbnWeakFrozen (bbnFreezeoutTemperatureMeV eta_paper) := by
  unfold bbnWeakFrozen
  exact le_rfl

end

end Hqiv.Physics
