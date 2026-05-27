import Hqiv.Physics.BBNEpochEvolution
import Hqiv.Physics.BaryogenesisWitness
import Hqiv.Geometry.AuxiliaryField

/-!
# BBN epoch network (rate scaffold, cooling in T)

Python integrator: `scripts/hqiv_bbn_epoch_network.py` (mirrors names here).

**Species (baryons per H):** neutron `n`, proton `p`, deuterium `D`, ³He, ⁴He.

**Lock-in inputs (fixed):** η, `derivedDeltaM`, `bbnDeuteronQAtLockin`, `bbnHelium4QAtLockin`.

**Epoch inputs (vary with universe age / T):**
* shell `m(T) = T_Pl_MeV/T − 1`;
* `alphaEffAtShell m`, `gammaEffAtShell m`, `T m`;
* Hubble `H(T) ∝ T²` (radiation-dominated BBN window).

**Reactions (schematic rates Γ ∝ η × α_eff(m(T)) × exp(Q/T) × T^n):**
1. `n + p → D + γ` with `Q_D`;
2. `D + p → ³He + γ` with `Q_3 − Q_D`;
3. `D + D → ⁴He + γ` with `Q_4 − 2 Q_D` (lock-in composite trace);
4. weak `n ↔ p` until `Γ_weak < H` at `bbnFreezeoutTemperatureMeV η`.

**Not claimed:** full PRIMAT rate tables, Be/B ladder, or Li destruction.
-/

namespace Hqiv.Physics

open Hqiv

noncomputable section

/-- Standard g_* at BBN (photon + 3 neutrino). -/
def bbnGStar : ℝ := 10.75

/-- Planck mass in MeV (Hubble rate units). -/
def M_Pl_MeV : ℝ := 1.2209e22

/-- Radiation-dominated Hubble parameter `H(T)` in s⁻¹ (MeV units). -/
noncomputable def bbnHubbleRate (T_MeV : ℝ) : ℝ :=
  1.66 * Real.sqrt bbnGStar * T_MeV ^ 2 / M_Pl_MeV

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

/-- Weak freeze-out when `Γ_weak ~ H` (scaffold inequality). -/
def bbnWeakFrozen (T_MeV : ℝ) : Prop :=
  T_MeV ≤ bbnFreezeoutTemperatureMeV eta_paper

structure BBNNetworkState where
  n_n : ℝ
  n_p : ℝ
  n_D : ℝ
  n_He3 : ℝ
  n_He4 : ℝ

/-- Baryon budget per H: `n_n + n_p + 2 n_D + 3 n_He3 + 4 n_He4 ≈ η`. -/
def bbnBaryonBudget (s : BBNNetworkState) (η : ℝ) : ℝ :=
  s.n_n + s.n_p + 2 * s.n_D + 3 * s.n_He3 + 4 * s.n_He4

/-- ⁴He mass fraction from network state: `Y_p = (4 n_He4 + 3 n_He3) / η`. -/
noncomputable def bbnYpFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else (4 * s.n_He4 + 3 * s.n_He3) / η

noncomputable def bbnDHFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_D / η

noncomputable def bbnHe3HFromNetworkState (s : BBNNetworkState) (η : ℝ) : ℝ :=
  if η = 0 then 0 else s.n_He3 / η

/-- Integrated readout slot (filled by Python witness JSON). -/
structure BBNIntegratedReadout where
  Yp : ℝ
  DH : ℝ
  He3H : ℝ
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
